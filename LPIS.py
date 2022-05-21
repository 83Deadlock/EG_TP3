from dataclasses import InitVar
from doctest import Example
from mimetypes import init
import sys
from lark import Discard
from lark import Lark,Token,Tree
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter

sys.path.append(".")

from LPIS3 import GraphInterpreter

class MyInterpreter (Interpreter):
    def __init__(self):
        # Dictionary where we'll store all relevant fields to return from the Interpreter
        self.output = {}
        # We'll keep two dictionaries (one for warnings, one for errors) where the key is the variable's name and the value is a list with warnings or errors on that variable.
        self.warnings = {}
        self.errors = {}
        # This flag indicates if the program's syntax or semanthics are correct
        self.correct = True
        # Dict where the keys are the type of instructions and the values are a simple counter, to know how many of each type of instruction we have in the current program 
        self.instructions = {}
        # Counter for flow control structures (if, while, for and repeat). Will serve as an ID
        self.controlID = 0
        # Key is ID of the control structure, value is a tuple with 3 fields: type (if/while/for/repeat), active (True/False) and Parents (list with higher hierarchy structure's IDs)
        self.controlStructs = {}
        # Flag to see if we're concatenating the boolean expressions from coditional control structures
        self.if_concat = False
        # String where we'll concat the boolean expressions from coditional control structures
        self.ifCat = ""
        # Flag to see if we're concatenating the body from coditional control structures
        self.body_cat = False
        # String where we'll concat the body from coditional control structures
        self.bodyCat = ""
        # Key will be the original version of a control structure, value will be a nested version of the key
        self.suggestions = {}
        # Keys are control structure IDs, values are tuples with two fields: ID's boolean expression, ID's body
        self.if_parts = {}
        # String used to reconstruct the code
        self.code = ""
        # String used to format the code to show erros and reconstruct the code
        self.html_body = ""
        # Used to determine the level of ident for each line of code
        self.ident_level = 0
        # Key is the name of an atomic variable, value is a tuple of 4 fields: Type (int/float/string), Value, Init (True/False), Used (True/False)
        self.atomic_vars = dict()
        # Key is the name of a structural variable, value is a tuple of 4 fields: Type (list/set/tuple/dict), Size (#elems), Value, Used (True/False)
        self.struct_vars = dict()
        # We used this dictionary to know how many of each type of conotrol structure we have in each program
        self.nrStructs = dict()

    def start(self,tree):
        self.code += "-{\n"
        self.html_body += "<pre><body>\n<p class=\"code\">\n-{\n</p>\n"
        self.ident_level += 1

        self.visit(tree.children[1])
        
        self.ident_level -= 1
        self.html_body += "<p class=\"code\">\n}-\n</p>\n"
        self.code += "}-\n"
        
        for var in self.atomic_vars.keys():
            if var not in self.warnings.keys():
                    self.warnings[var] = []

            if self.atomic_vars[var][2] == 0 and self.atomic_vars[var][3] == 0:
                self.warnings[var].append("Variable \"" + var + "\" was never initialized nor used.")

            elif self.atomic_vars[var][2] == 1 and self.atomic_vars[var][3] == 0:
                self.warnings[var].append("Variable \"" + var + "\" was never used.")

        for var in self.struct_vars.keys():
            if var not in self.warnings.keys():
                    self.warnings[var] = []

            if self.struct_vars[var][0] not in self.nrStructs.keys():
                self.nrStructs[self.struct_vars[var][0]] = 1
            
            else:
                self.nrStructs[self.struct_vars[var][0]] += 1

            if self.struct_vars[var][3] == 0:
                self.warnings[var].append("Variable \"" + var + "\" was never used.")

        self.output["atomic_vars"] = dict(self.atomic_vars)
        self.output["struct_vars"] = dict(self.struct_vars)

        self.output["correct"] = self.correct
        
        erros = dict()
        for k,v in self.errors.items():
            erros[k] = []
            for s in v:
                erros[k].append(s)

        warns = dict()
        for k,v in self.warnings.items():
            warns[k] = []
            for s in v:
                warns[k].append(s)

        self.output["errors"] = erros
        self.output["warnings"] = warns
        self.output["nrStructs"] = self.nrStructs
        self.output["instructions"] = dict(self.instructions)
        self.output["controlStructs"] = dict(self.controlStructs)
        self.output["code"] = self.code
        self.output["html_body"] = self.html_body
        self.output["suggestions"] = self.suggestions

        self.if_strings = {}
        self.if_bodys = {}

        # IF CONCAT

        for i in self.if_parts.keys():
            self.if_concat = True
            self.visit(self.if_parts[i][0])
            self.if_strings[i] = self.ifCat
            self.ifCat = ""

        self.if_concat = False
        

        for i in self.if_parts.keys():
            self.body_cat = True
            self.ident_level = 0
            self.visit(self.if_parts[i][1])
            self.if_bodys[i] = self.bodyCat
            self.bodyCat = ""

        self.body_cat = False

        aux = {}
        parentsSet = set()

        for k,v in self.controlStructs.items():
            l = v[2]
            flag = True
            parents = []
            if len(l) == 0 or v[0] != "if":
                flag = False
            for p in l:
                if self.controlStructs[p][0] != "if":
                    flag = False
                if p not in parentsSet:
                    parentsSet.add(p)
                    parents.append(p)

            if flag:
                aux[k] = tuple([v[0],v[1],parents])

        auxIfs = {}
        for k,t in aux.items():
            p = t[2][0]
            
            if p not in auxIfs.keys():
                auxIfs[p] = list()    
            auxIfs[p].append(k)
        
        removeKeys = set()

        for k,v in auxIfs.items():
            for v1 in v:
                if v1 in auxIfs.keys():
                    auxIfs[k].append(auxIfs[v1][0])
                    auxIfs[v1] = []
                    removeKeys.add(v1)

        for k in removeKeys:
            auxIfs.pop(k)

        
        finalDict = {}

        for k,l in auxIfs.items():
            last = False
            for v in l:
                if len(self.if_parts[v][1].children[1].children) > 1:
                    if k not in finalDict.keys():
                        finalDict[k] = []
                    finalDict[k].append(v)
                    last = True 
                elif not last:
                    if k not in finalDict.keys():
                        finalDict[k] = []
                    finalDict[k].append(v)

        for k,l in finalDict.items():
            condS = self.if_strings[k]

            for v in l:
                condS += " & " + self.if_strings[v]

        for k,v in finalDict.items():
            i = 1
            keyC = "if(" + self.if_strings[k] + "){\n"
            for elem in v:
                for t in range(i):
                    keyC += "\t"
                keyC += "if(" + self.if_strings[elem] + "){\n"
                i += 1


            body = self.if_bodys[max(v)][2:len(self.if_bodys[max(v)])-2]
            bodyLines = body.split("\n")

            for line in bodyLines:
                for t in range(i-1):
                    keyC += "\t"
                keyC += line + "\n"
            
            for elem in v:
                i -= 1
                for t in range(i):
                    keyC += "\t"
                keyC += "}\n"
            keyC += "}"

            valueC = "if((" + self.if_strings[k] + ")"

            for elem in v:
                valueC += " & (" + self.if_strings[elem] + ")"
            
            valueC += ")" + self.if_bodys[max(v)]

            self.suggestions[keyC] = valueC

        return self.output

    def program(self, tree):
        for c in tree.children:
            self.visit(c)
        pass

    def instruction(self,tree):
        self.visit(tree.children[0])

        pass

    def comment(self, tree):
        comment = tree.children[0].value
        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += comment + "\n"
        else:
            self.code += comment + "\n"
            self.html_body += "<p class=\"comment\">\n" 

            for i in range(self.ident_level):
                self.html_body += "\t"

            self.html_body += comment + "\n</p>\n"

        pass

    def declaration(self, tree):
        self.visit(tree.children[0])

        pass

    def atomic(self, tree):
        if "atomic_declaration" not in self.instructions.keys():
            self.instructions["atomic_declaration"] = 1
        else:
            self.instructions["atomic_declaration"] += 1

        var_type = tree.children[0].value        

        var_name = tree.children[1].value

        if var_name not in self.errors.keys():
            self.errors[var_name] = set()
        
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        flag = False

        if(var_name in self.atomic_vars.keys() or var_name in self.struct_vars.keys()):
            self.correct = False
            self.errors[var_name].add("Variable \"" + var_name + "\" declared more than once!")
            if not self.body_cat:
                self.html_body += "<div class=\"error\">"+var_type + " " + var_name
            flag = True

        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += var_type + " " + var_name
        else:
            self.code += var_type + " " + var_name
            if not flag:
                self.html_body += var_type + " " + var_name

        var_value = None
        if flag == True:
            var_value = self.atomic_vars[var_name][1]
        init = 0
        used = 0

        if(len(tree.children) > 3):
            if self.body_cat:
                self.bodyCat += " = "
            else:
                self.code += " = " 
                self.html_body += " = "
            var_value = self.visit(tree.children[3])
            #print("RETORNA => " + str(var_value))
            init = 1
            if "atrib" not in self.instructions.keys():
                self.instructions["atrib"] = 1
            else:
                self.instructions["atrib"] += 1


        val = (var_type,var_value,init,used)
        self.atomic_vars[var_name] = val

        if flag and not self.body_cat:
            self.html_body += "<span class=\"errortext\">Variable declared more than once!</span></div>"

        flag = False

        if self.body_cat:
            self.bodyCat += ";\n"
        else:
            self.code += ";\n"
            self.html_body += ";\n</p>\n"

        pass

    def elem(self, tree):

        if(not isinstance(tree.children[0], Tree)):
            if self.body_cat:
                self.bodyCat += str(tree.children[0])
            else:
                self.code += str(tree.children[0])
                self.html_body += str(tree.children[0])

            if(tree.children[0].type == "ESCAPED_STRING"):
                return str(tree.children[0].value[1:(len(tree.children[0].value)-1)])
            elif(tree.children[0].type == "DECIMAL"):
                return float(tree.children[0].value)
            elif(tree.children[0].type == "SIGNED_INT"):
                return int(tree.children[0].value)
        else:
            r = self.visit(tree.children[0])
            return r

    def structure(self, tree):
        if "structure_declaration" not in self.instructions.keys():
            self.instructions["structure_declaration"] = 1
        else:
            self.instructions["structure_declaration"] += 1

        self.visit(tree.children[0])

        pass
 
    def set(self, tree):
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        ret = set()
        childs = len(tree.children)
        sizeS = 0

        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "set " + tree.children[0].value
        else:
            self.code += "set " + tree.children[0].value
            self.html_body += "set " + tree.children[0].value

        if childs != 1 and childs != 4:
            if self.body_cat:
                self.bodyCat += " = "
            else:
                self.code += " = "
                self.html_body += " = "
            for c in tree.children[2:]:
                if c != "{" and c != "}" and c != ",":
                    ret.add(self.visit(c))
                if c == "{" or c == "}" or c == ",":
                    if self.body_cat:
                        self.bodyCat += c.value
                    else:
                        self.code += c.value
                        self.html_body += c.value
                    if c == ",":
                        if self.body_cat:
                            self.bodyCat += " "
                        else:
                            self.code += " "
                            self.html_body += " "
            sizeS = len(ret)            
        elif childs == 4:
            if self.body_cat:
                self.bodyCat += " = {}"
            else:
                self.code += " = {}"
                self.html_body += " = {}"

        if self.body_cat:
            self.bodyCat += ";\n"
        else:
            self.code += ";\n"
            self.html_body += ";\n</p>\n"

        self.struct_vars[tree.children[0].value] = ("set", sizeS, ret, 0)


        pass

    def list(self, tree):
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        ret = list()
        childs = len(tree.children)
        sizeL = 0
        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "list " + tree.children[0].value
        else:
            self.code += "list " + tree.children[0].value
            self.html_body += "list " + tree.children[0].value

        if childs != 1 and childs != 4:
            if self.body_cat:
                self.bodyCat += " = "
            else:
                self.code += " = "
                self.html_body += " = "
            for c in tree.children[2:]:
                if c != "[" and c != "]" and c != ",":
                    ret.append(self.visit(c))
                if c == "[" or c == "]" or c == ",":
                    if self.body_cat:
                        self.bodyCat += c.value
                    else:
                        self.code += c.value
                        self.html_body += c.value
                    if c == ",":
                        if self.body_cat:
                            self.bodyCat += " "
                        else:
                            self.code += " "
                            self.html_body += " "
            sizeL = len(ret)
        elif childs == 4:
            if self.body_cat:
                self.bodyCat += " = []"
            else:
                self.code += " = []"
                self.html_body += " = []"

        if self.body_cat:
            self.bodyCat += ";\n"
        else:
            self.code += ";\n"
            self.html_body += ";\n</p>\n"

        self.struct_vars[tree.children[0].value] = ("list", sizeL, ret, 0)

        pass

    def tuple(self, tree):
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        aux = list()
        ret = tuple()
        sizeT = 0
        childs = len(tree.children)
        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "tuple " + tree.children[0].value
        else:
            self.code += "tuple " + tree.children[0].value
            self.html_body += "tuple " + tree.children[0].value
        if childs != 1 and childs != 4:
            if self.body_cat:
                self.bodyCat += " = "
            else:
                self.code += " = "
                self.html_body += " = "
            for c in tree.children[2:]:
                if c != "(" and c != ")" and c != ",":
                    aux.append(self.visit(c))
                if c == "(" or c == ")" or c == ",":
                    if self.body_cat:
                        self.bodyCat += c.value
                    else:
                        self.code += c.value
                        self.html_body += c.value
                    if c == ",":
                        if self.body_cat:
                            self.bodyCat += " "
                        else:
                            self.code += " "
                            self.html_body += " "
            ret = tuple(aux)
            sizeT = len(ret)
        elif childs == 4:
            if self.body_cat:
                self.bodyCat += " = ()"
            else:
                self.code += " = ()"
                self.html_body += " = ()"

        if self.body_cat:
            self.bodyCat += ";\n"
        else:
            self.code += ";\n"
            self.html_body += ";\n</p>\n"

        self.struct_vars[tree.children[0].value] = ("tuple", sizeT, ret, 0)

        pass

    def dict(self, tree):
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        ret = dict()
        childs = len(tree.children)
        sizeD = 0
        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "dict " + tree.children[0].value
        else:
            self.code += "dict " + tree.children[0].value
            self.html_body += "dict " + tree.children[0].value
        if childs != 1 and childs != 4:
            if self.body_cat:
                self.bodyCat += " = {"
            else:
                self.code += " = {"
                self.html_body += " = {"
            start = 3
            while start < childs-1:
                key = self.visit(tree.children[start])
                if self.body_cat:
                    self.bodyCat += " : "
                else:
                    self.code += " : "
                    self.html_body += " : "
                value = self.visit(tree.children[start+2])
                if start + 4 < (childs-1):
                    if self.body_cat:
                        self.bodyCat += ", "
                    else:
                        self.code += ", "
                        self.html_body += ", "
                ret[key] = value 
                start += 4
            if self.body_cat:
                self.bodyCat += "}"
            else:
                self.code += "}"
                self.html_body += "}"
            sizeD = len(ret)
        elif childs == 4:
            if self.body_cat:
                self.bodyCat += " = {}"
            else:
                self.code += " = {}"
                self.html_body += " = {}"

        if self.body_cat:
            self.bodyCat += ";\n"
        else: 
            self.code += ";\n"
            self.html_body += ";\n</p>\n"
        
        self.struct_vars[tree.children[0].value] = ("dict", sizeD, ret, 0)

        pass

    def atrib(self,tree):

        if "atrib" not in self.instructions.keys():
            self.instructions["atrib"] = 1
        else:
            self.instructions["atrib"] += 1

        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"
            self.code += tree.children[0].value + " = "
        else:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += tree.children[0].value + " = "

        if str(tree.children[0]) not in self.errors.keys():
            self.errors[str(tree.children[0])] = set()

        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors[str(tree.children[0])].add("Variable \"" + tree.children[0] + "\" was not declared")
            self.correct = False
            typeV = "undefined"
            valueV = None
            if not self.body_cat:
                self.html_body += "<div class=\"error\">" + tree.children[0].value + " = "
            valueV = self.visit(tree.children[2])
            if not self.body_cat:
                self.html_body += "<span class=\"errortext\">Variable undeclared</span></div>"
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,0,1])

        else:
            typeV = self.atomic_vars[str(tree.children[0])][0]
            if not self.body_cat:
                self.html_body += tree.children[0].value + " = "
            valueV = self.visit(tree.children[2])
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])

        if self.body_cat:
            self.bodyCat += ";\n"
        else:
            self.html_body += ";\n</p>\n"
            self.code += ";\n"
            
        pass

    def initcicle(self, tree):
        if "atrib" not in self.instructions.keys():
            self.instructions["atrib"] = 1
        else:
            self.instructions["atrib"] += 1

        if self.body_cat:
            self.bodyCat += tree.children[0].value + " = "
        else: 
            self.code += tree.children[0].value + " = "

        if str(tree.children[0]) not in self.errors.keys():
            self.errors[str(tree.children[0])] = set()
        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors[str(tree.children[0])].add("Variable \"" + tree.children[0] + "\" was not declared")
            if not self.body_cat:
                self.html_body += "<div class=\"error\">"+tree.children[0].value + " = "
            valueV = self.visit(tree.children[2])
            if not self.body_cat:
                self.html_body += "<span class=\"errortext\">Variable was not declared</span></div>"
            self.correct = False
        else:
            typeV = self.atomic_vars[tree.children[0]][0]
            if not self.body_cat:
                self.html_body += tree.children[0].value + " = "
            valueV = self.visit(tree.children[2])
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,valueV,1,1])

        pass

    def print(self,tree):
        if "print" not in self.instructions.keys():
            self.instructions["print"] = 1
        else:
            self.instructions["print"] += 1

        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"
            self.html_body += "print("
            self.code += "print("
        else:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "print("

        if tree.children[1].type == "VARNAME":
            if self.body_cat:
                self.bodyCat += tree.children[1].value
            else:
                self.code += tree.children[1].value
            if str(tree.children[1]) not in self.errors.keys():
                self.errors[str(tree.children[1])] = set()
            if str(tree.children[1]) not in self.atomic_vars.keys():
                self.errors[str(tree.children[1])].add("Variable \"" + tree.children[1] + "\" was not declared")
                if not self.body_cat:
                    self.html_body += "<div class=\"error\">" + tree.children[0].value + "<span class=\"errortext\">Variable undeclared</span></div>"
                self.correct = False
            elif not self.atomic_vars[str(tree.children[1])][2]:
                self.errors[str(tree.children[1])].add("Variable \"" + tree.children[1] + "\" declared but not initialized")
                if not self.body_cat:
                    self.html_body += "<div class=\"error\">" + tree.children[0].value + "<span class=\"errortext\">Variable was never initialized</span></div>"
                self.correct = False
            else:
                if not self.body_cat:
                    self.html_body += tree.children[1].value
            
        elif tree.children[1].type == "ESCAPED_STRING":
            if self.body_cat:
                self.bodyCat += tree.children[1].value
            else: 
                self.code += tree.children[1].value
                self.html_body += tree.children[1].value
            s = tree.children[1]
            s = s.replace("\"","")
        
        if self.body_cat:
            self.bodyCat += ");\n"
        else:
            self.code += ");\n"
            self.html_body += ");\n</p>\n"
            
        pass

    def read(self,tree):
        if "read" not in self.instructions.keys():
            self.instructions["read"] = 1
        else:
            self.instructions["read"] += 1

        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"
            self.html_body += "read("
            self.code += "read(" + tree.children[1].value
        else:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "read(" + tree.children[1].value

        if str(tree.children[1]) not in self.errors.keys():
            self.errors[str(tree.children[1])] = set()

        if str(tree.children[1]) not in self.atomic_vars.keys():
            if str(tree.children[1]) in self.struct_vars.keys():
                self.errors[str(tree.children[1])].add("Variable \"" + tree.children[1] + "\" cannot be defined by user input.")
                if not self.body_cat:
                    self.html_body += "<div class=\"error\">" + tree.children[0].value + "<span class=\"errortext\">Variable is a structure</span></div>"
            else:
                self.errors[str(tree.children[1])].add("Variable \"" + tree.children[1] + "\" was not declared")
                if not self.body_cat:
                    self.html_body += "<div class=\"error\">" + tree.children[0].value + "<span class=\"errortext\">Variable undeclared</span></div>"
            self.correct = False
        
        else:
            if not self.body_cat:
                self.html_body += tree.children[1].value
            value = input("> ")
            typeV = self.atomic_vars[tree.children[1]][0]
            initV = 1
            usedV = 1
            val = int(value)
            self.atomic_vars[tree.children[1]] = tuple([typeV, val, initV, usedV])

        if self.body_cat:
            self.bodyCat += ");\n"
        else:
            self.code += ");\n"        
            self.html_body += ");\n</p>\n"

        pass

    def cond(self,tree):
        if "if" not in self.instructions.keys():
            self.instructions["if"] = 1
        else:
            self.instructions["if"] += 1

        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"


        # Get every active structures and consider the current as their child
        parents = []
        for id in self.controlStructs.keys():
            if self.controlStructs[id][1] == 1:
                parents.append(id)

        if not self.body_cat:
            self.if_parts[self.controlID] = (tree.children[2],tree.children[4])
            self.controlStructs[(self.controlID)] = tuple(["if",1,parents])
        self.controlID += 1

        l = len(tree.children)

        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "if("
        else:
            self.code += "if("
            self.html_body += "if("
        self.visit(tree.children[2])
        if self.body_cat:
            self.bodyCat += ")"
        else:
            self.code += ")"
            self.html_body += ")"

        self.visit(tree.children[4])     

        if(tree.children[(l-2)] == "else"):
            if self.body_cat:
                self.bodyCat += " else "
            else:
                self.code += " else "
                self.html_body += " else "
            self.visit(tree.children[(l-1)])

        pass

    def ciclewhile(self,tree):
        if "while" not in self.instructions.keys():
            self.instructions["while"] = 1
        else:
            self.instructions["while"] += 1

        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

        parents = []
        for id in self.controlStructs.keys():
            if self.controlStructs[id][1] == 1:
                parents.append(id)

        self.controlStructs[self.controlID] = tuple(["while",1,parents])
        self.controlID += 1

        if self.body_cat:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat +=  "while("
        else:
            self.code += "while("
            self.html_body += "while("

        self.visit(tree.children[2])

        if self.body_cat:
            self.bodyCat += ")"
        else:
            self.code += ")"
            self.html_body += ")"

        self.visit(tree.children[4])
        

        pass

    def ciclefor(self,tree):
        if "for" not in self.instructions.keys():
            self.instructions["for"] = 1
        else:
            self.instructions["for"] += 1

        parents = []
        for id in self.controlStructs.keys():
            if self.controlStructs[id][1] == 1:
                parents.append(id)

        self.controlStructs[self.controlID] = tuple(["for",1,parents])
        self.controlID += 1


        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"
        else:
            for i in range(self.ident_level):
                self.bodyCat += "\t"

        for c in tree.children:
            if c != "for" and c != "(" and c != ")" and c != ";" and c != ",":
                self.visit(c)
            if c == "for" or c == "(" or c == ")" or c == ";" or c == ",":
                if self.body_cat:
                    self.bodyCat += c.value
                else:
                    self.code += c.value
                    self.html_body += c.value
                if(c == ";" or c == ","):
                    if self.body_cat:
                        self.bodyCat += " "
                    else:
                        self.code += " "
                        self.html_body += " "
        

        pass

    def inc(self, tree):
        if self.body_cat:
            self.bodyCat += tree.children[0] + "++"
        else:
            self.code += tree.children[0] + "++"
            

        if str(tree.children[0]) not in self.errors.keys():
            self.erros[str(tree.children[0])] = set()

        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors[str(tree.children[0])].add("Undeclared variable \"" + str(tree.children[0]) + "\"")
            self.correct = False
            if not self.if_concat and not self.body_cat:
                self.html_body += "<div class=\"error\">"+tree.children[0]+"++<span class=\"errortext\">Undeclared Variable</span></div>"
            r = -1

        elif self.atomic_vars[str(tree.children[0])][2] == 0:
            self.errors[str(tree.children[0])].add("Variable \"" + str(tree.children[0]) + "\" was never initialized")
            if not self.if_concat and not self.body_cat:
                self.html_body += "<div class=\"error\">"+tree.children[0]+"++<span class=\"errortext\">Variable was never initialized</span></div>"
            self.correct = False
            r = self.atomic_vars[str(tree.children[0])][1]
            typeV = self.atomic_vars[str(tree.children[0])][0]
            initV = self.atomic_vars[str(tree.children[0])][2]
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])

        else:
            r = self.atomic_vars[str(tree.children[0])][1] + 1
            typeV = self.atomic_vars[str(tree.children[0])][0]
            initV = self.atomic_vars[str(tree.children[0])][2]
            if not self.if_concat and not self.body_cat:
                self.html_body += tree.children[0] + "++"
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])

        
        pass

    def dec(self, tree):
        if self.body_cat:
            self.bodyCat += tree.children[0] + "--"
        else:
            self.code += tree.children[0] + "--"
            

        if str(tree.children[0]) not in self.errors.keys():
            self.erros[str(tree.children[0])] = set()

        if str(tree.children[0]) not in self.atomic_vars.keys():
            self.errors[str(tree.children[0])].add("Undeclared variable \"" + str(tree.children[0]) + "\"")
            self.correct = False
            if not self.if_concat and not self.body_cat:
                self.html_body += "<div class=\"error\">"+tree.children[0]+"--<span class=\"errortext\">Undeclared Variable</span></div>"
            r = -1

        elif self.atomic_vars[str(tree.children[0])][2] == 0:
            self.errors[str(tree.children[0])].add("Variable \"" + str(tree.children[0]) + "\" was never initialized")
            if not self.if_concat and not self.body_cat:
                self.html_body += "<div class=\"error\">"+tree.children[0]+"--<span class=\"errortext\">Variable was never initialized</span></div>"
            self.correct = False
            r = self.atomic_vars[str(tree.children[0])][1]
            typeV = self.atomic_vars[str(tree.children[0])][0]
            initV = self.atomic_vars[str(tree.children[0])][2]
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])

        else:
            r = self.atomic_vars[str(tree.children[0])][1] - 1
            typeV = self.atomic_vars[str(tree.children[0])][0]
            initV = self.atomic_vars[str(tree.children[0])][2]
            if not self.if_concat and not self.body_cat:
                self.html_body += tree.children[0] + "--"
            self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])

        
        pass

    def ciclerepeat(self,tree):
        if "repeat" not in self.instructions.keys():
            self.instructions["repeat"] = 1
        else:
            self.instructions["repeat"] += 1

        parents = []
        for id in self.controlStructs.keys():
            if self.controlStructs[id][1] == 1:
                parents.append(id)

        self.controlStructs[self.controlID] = tuple(["repeat",1,parents])
        self.controlID += 1

        
        if not self.body_cat:
            self.html_body += "<p class=\"code\">\n"
            for i in range(self.ident_level):
                self.html_body += "\t"

            self.code += "repeat(" + tree.children[2].value + ")"
            self.html_body += "repeat(" + tree.children[2].value + ")"
        else:
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "repeat(" + tree.children[2].value + ")"

        self.visit(tree.children[4])
        

        pass

    def body(self,tree):

        self.visit_children(tree)

        pass

    def open(self,tree):
        if self.body_cat:
            self.bodyCat += "{\n"
            self.ident_level += 1
        else:
            self.code += "{\n"
            self.ident_level += 1
            self.html_body += "{\n</p>\n"

        pass

    def close(self,tree):
        newDict = dict(filter(lambda elem: elem[1][1] == 1, self.controlStructs.items()))

        if len(newDict.keys()) > 0:
            k = max(newDict.keys())
            self.controlStructs[k] = (self.controlStructs[k][0],0,self.controlStructs[k][2])

        if not self.body_cat:
            self.ident_level -= 1
            self.code += "}\n"
            if not self.body_cat:
                self.html_body += "<p class=\"code\">\n"
                for i in range(self.ident_level):
                    self.html_body += "\t"
            self.html_body += "}\n</p>\n"
        else: 
            self.ident_level -= 1
            for i in range(self.ident_level):
                self.bodyCat += "\t"
            self.bodyCat += "}\n"
        pass

    def op(self,tree):
        if(len(tree.children) > 1):
            if(tree.children[0] == "!"):
                
                if self.if_concat:
                    self.ifCat += "!"
                elif self.body_cat:
                    self.bodyCat += "!"
                else:
                    self.code += "!"
                    self.html_body += "!"
                r = int(self.visit(tree.children[1]))
                if r == 0: r = 1
                else: r = 0
            elif(tree.children[1] == "&"):
                t1 = self.visit(tree.children[0])
                
                if self.if_concat:
                    self.ifCat += " & "
                elif self.body_cat:
                    self.bodyCat += " & "
                else:
                    self.code += " & "
                    self.html_body += " & "

                t2 = self.visit(tree.children[2])
                if t1 and t2:
                    r = 1
                else:
                    r = 0
            elif(tree.children[1] == "#"):
                t1 = self.visit(tree.children[0])
                if self.if_concat:
                    self.ifCat += " # "
                elif self.body_cat:
                    self.bodyCat += " # "
                else:
                    self.html_body += " # "
                    self.code += " # "

                t2 = self.visit(tree.children[2])
                if t1 or t2:
                    r = 1
                else:
                    r = 0
        else:
            r = self.visit(tree.children[0])

        return r

    def factcond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            if self.if_concat:
                self.ifCat += " " + tree.children[1].value + " "
            elif self.body_cat:
                self.bodyCat += " " + tree.children[1].value + " "
            else:
                self.code += " " + tree.children[1].value + " "
                self.html_body += " " + tree.children[1].value + " "

            t2 = self.visit(tree.children[2])
            if tree.children[1] == "<=":
                if t1 <= t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "<":
                if t1 < t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == ">=":
                if t1 >= t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == ">":
                if t1 > t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "==":
                if t1 == t2:
                    r = 1
                else:
                    r = 0
            elif tree.children[1] == "!=":
                if t1 != t2:
                    r = 1
                else:
                    r = 0
        else:
            r = self.visit(tree.children[0])
        
        return r

    def expcond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            if self.if_concat:
                self.ifCat += " " + tree.children[1].value + " "
            elif self.body_cat:
                self.bodyCat += " " + tree.children[1].value + " "
            else:
                self.html_body += " " + tree.children[1].value + " "
                self.code += " " + tree.children[1].value + " "

            t2 = self.visit(tree.children[2])
            if(tree.children[1] == "+"):
                r = t1 + t2
            elif(tree.children[1] == "-"):
                r = t1 - t2
        else:
            r = self.visit(tree.children[0])

        return r

    def termocond(self,tree):
        if len(tree.children) > 1:
            t1 = self.visit(tree.children[0])
            if self.if_concat:
                self.ifCat += " " + tree.children[1].value + " "
            elif self.body_cat:
                self.bodyCat += " " + tree.children[1].value + " "
            else:
                self.code += " " + tree.children[1].value + " "
                self.html_body += " " + tree.children[1].value + " "

            t2 = self.visit(tree.children[2])
            if(tree.children[1] == "*"):
                r = t1 * t2
            elif(tree.children[1] == "/"):
                r = int(t1 / t2)
            elif(tree.children[1] == "%"):
                r = t1 % t2
        else:
            r = self.visit(tree.children[0])

        return r

    def factor(self,tree):
        r = None
        if tree.children[0].type == 'SIGNED_INT':
            r = int(tree.children[0])
            if self.if_concat:
                self.ifCat += str(r)
            elif self.body_cat:
                self.bodyCat += str(r)
            else:
                self.code += str(r)
                self.html_body += str(r)

        elif tree.children[0].type == 'VARNAME':

            if str(tree.children[0]) not in self.errors.keys():
                self.erros[str(tree.children[0])] = set()

            if str(tree.children[0]) not in self.atomic_vars.keys():
                self.errors[str(tree.children[0])].add("Undeclared variable \"" + str(tree.children[0]) + "\"")
                self.correct = False
                if not self.if_concat and not self.body_cat:
                    self.html_body += "<div class=\"error\">"+tree.children[0].value+"<span class=\"errortext\">Undeclared Variable</span></div>"
                r = -1
            elif self.atomic_vars[str(tree.children[0])][2] == 0:
                self.errors[str(tree.children[0])].add("Variable \"" + str(tree.children[0]) + "\" was never initialized")
                if not self.if_concat and not self.body_cat:
                    self.html_body += "<div class=\"error\">"+tree.children[0].value+"<span class=\"errortext\">Variable was never initialized</span></div>"
                self.correct = False
                r = self.atomic_vars[str(tree.children[0])][1]
                typeV = self.atomic_vars[str(tree.children[0])][0]
                initV = self.atomic_vars[str(tree.children[0])][2]
                self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])
            else:
                r = self.atomic_vars[str(tree.children[0])][1]
                typeV = self.atomic_vars[str(tree.children[0])][0]
                initV = self.atomic_vars[str(tree.children[0])][2]
                if not self.if_concat and not self.body_cat:
                    self.html_body += tree.children[0].value
                self.atomic_vars[str(tree.children[0])] = tuple([typeV,r,initV,1])

            if self.if_concat:
                self.ifCat += tree.children[0].value
            elif self.body_cat:
                self.bodyCat += tree.children[0].value
            else:
                self.code += tree.children[0].value


        elif tree.children[0] == "(":
            r = self.visit(tree.children[1])

        return r

grammar = '''
start: BEGIN program END
program: instruction+
instruction: declaration | comment | operation
declaration: atomic | structure
operation: atrib | print | read | cond | cicle
print: "print" PE (VARNAME | ESCAPED_STRING) PD PV
read: "read" PE VARNAME PD PV
cond: IF PE op PD body (ELSE body)?
cicle: ciclewhile | ciclefor | ciclerepeat
ciclewhile: WHILE PE op PD body
WHILE: "while"
ciclefor: FOR PE (initcicle (VIR initcicle)*)? PV op PV ((inc | dec) (VIR (inc | dec))*)? PD body
initcicle: VARNAME EQUAL op
FOR: "for"
ciclerepeat: REPEAT PE (SIGNED_INT | VARNAME) PD body
REPEAT: "repeat"
body: open program close
atrib: VARNAME EQUAL op PV
inc: VARNAME INC
INC: "++"
dec: VARNAME DEC
DEC: "--"
op: NOT op | op (AND | OR) factcond | factcond
NOT: "!"
AND: "&"
OR: "#"
factcond: factcond BINSREL expcond | expcond
BINSREL: LESSEQ | LESS | MOREEQ | MORE | EQ | DIFF
LESSEQ: "<="
LESS: "<"
MOREEQ: ">="
MORE: ">"
EQ: "=="
DIFF: "!="
expcond: expcond (PLUS | MINUS) termocond | termocond
PLUS: "+"
MINUS: "-"
termocond: termocond (MUL|DIV|MOD) factor | factor
MUL: "*"
DIV: "/"
MOD: "%"
factor: PE op PD | SIGNED_INT | VARNAME | DECIMAL
atomic: TYPEATOMIC VARNAME (EQUAL elem)? PV
structure: (set | list | dict | tuple) PV
set: "set" VARNAME (EQUAL OPENBRACKET (elem (VIR elem)*)? CLOSEBRACKET)?
dict: "dict" VARNAME (EQUAL OPENBRACKET (elem DD elem (VIR elem DD elem)*)? CLOSEBRACKET)?
list: "list" VARNAME (EQUAL OPENSQR (elem (VIR elem)*)? CLOSESQR)?
tuple: "tuple" VARNAME (EQUAL PE (elem (VIR elem)*)? PD)?
elem: ESCAPED_STRING | SIGNED_INT | DECIMAL | op
TYPEATOMIC: "int" | "float" | "string" 
VARNAME: WORD
comment: C_COMMENT
BEGIN: "-{"
END: "}-"
PV: ";"
VIR: ","
OPENBRACKET: "{"
CLOSEBRACKET: "}"
OPENSQR: "["
CLOSESQR: "]"
DD: ":"
PE: "("
PD: ")"
EQUAL: "="
open: OPEN
OPEN: "{"
close: CLOSE
CLOSE: "}"
IF: "if"
ELSE: "else"


%import common.WORD
%import common.SIGNED_INT
%import common.DECIMAL
%import common.WS
%import common.ESCAPED_STRING
%import common.C_COMMENT
%ignore WS
'''


def geraHTML(atomic_vars, struct_vars, warnings, errors, nrStructs, instrucoes, output_html, control):
    output_html.write("<!DOCTYPE html>")
    output_html.write("<html lang=\"pt\">")
    output_html.write("<head>")
    output_html.write("<meta charset=\"UTF-8\">")
    output_html.write("<link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">")
    output_html.write("<title>EG - TP3</title>")
    output_html.write("</head>")

    output_html.write("<body>")
    
    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    output_html.write(navbar)

    output_html.write("<h1>Table with program's atomic variables</h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>Variable</th>")
    output_html.write("<th>Type</th>")
    output_html.write("<th>Value</th>")
    output_html.write("<th>Warnings</th>")
    output_html.write("<th>Errors</th>")
    output_html.write("</tr>")

    for var in atomic_vars.keys():
        output_html.write("<tr>")
        output_html.write("<td>" + var + "</td>")
        output_html.write("<td>" + str(atomic_vars[var][0]) + "</td>")
        output_html.write("<td>" + str(atomic_vars[var][1]) + "</td>")
        if var in warnings.keys():
            if len(warnings[var]) == 0:
                output_html.write("<td>No warnings</td>")
            else:
                w = ""
                for string in warnings[var]:
                    w += string + "\n"
                output_html.write("<td>" + w + "</td>")
        
        if var in errors.keys():
            if len(errors[var]) == 0:
                output_html.write("<td>No errors</td>")
            else:
                erros = ""
                for erro in errors[var]:
                    erros += erro + " "
                    output_html.write("<td>" + erros + "</td>")
          
        output_html.write("</tr>")
    output_html.write("</table>")

    output_html.write("<h1>Tabel with program's structural variables</h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>Variable</th>")
    output_html.write("<th>Type</th>")
    output_html.write("<th>Size</th>")
    output_html.write("<th>Value</th>")
    output_html.write("<th>Warnings</th>")
    output_html.write("</tr>")

    for var in struct_vars.keys():
        output_html.write("<tr>")
        output_html.write("<td>" + var + "</td>")
        output_html.write("<td>" + str(struct_vars[var][0]) + "</td>")
        output_html.write("<td>" + str(struct_vars[var][1]) + "</td>")
        output_html.write("<td>" + str(struct_vars[var][2]) + "</td>")

        if var in warnings.keys():
            if len(warnings[var]) == 0:
                output_html.write("<td>No warnings</td>")
            else:
                w = ""
                for string in warnings[var]:
                    w += string + "\n"
                output_html.write("<td>" + w + "</td>")

        output_html.write("</tr>")

    output_html.write("</table>")

    output_html.write("<h1> Total number of program variables: " + str(len(atomic_vars.keys()) + len(struct_vars.keys())) + "</h1>")

    output_html.write("<h1> Structural data types used</h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>Type</th>")
    output_html.write("<th>Amount</th>")
    output_html.write("</tr>")

    for type in nrStructs.keys():
        output_html.write("<tr>")
        output_html.write("<td>" + type + "</td>")
        output_html.write("<td>" + str(nrStructs[type]) + "</td>")
        output_html.write("</tr>")

    output_html.write("</table>")

    output_html.write("<h1> Total amount of instructions </h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>Instruction</th>")
    output_html.write("<th>Amount</th>")
    output_html.write("</tr>")

    total = 0

    for instrucao in instrucoes.keys():
        output_html.write("<tr>")
        output_html.write("<td>" + instrucao + "</td>")
        output_html.write("<td>" + str(instrucoes[instrucao]) + "</td>")
        output_html.write("</tr>")
        total += instrucoes[instrucao]

    output_html.write("<td>Total</td>")
    output_html.write("<td>" + str(total) + "</td>")
    output_html.write("</table>")

    ##

    output_html.write("<h1> Control Structures </h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>ID</th>")
    output_html.write("<th>Type</th>")
    output_html.write("<th>Parents</th>")
    output_html.write("</tr>")

    total = 0

    for c in control.keys():
        output_html.write("<tr>")
        output_html.write("<td>" + str(c) + "</td>")
        output_html.write("<td>" + str(control[c][0]) + "</td>")
        if len(control[c][2]) == 0:
            output_html.write("<td>No parents</td>")
        else:
            id = ""
            for ids in control[c][2]:
                id += str(ids) + " | "
            output_html.write("<td>Parents' IDs: " + id + "</td>")
        output_html.write("</tr>")
        total += 1

    output_html.write("</body>")
    output_html.write("</html>")

def geraSugestao(sugestoes, output_html):
    output_html.write("<!DOCTYPE html>")
    output_html.write("<html lang=\"pt\">")
    output_html.write("<head>")
    output_html.write("<meta charset=\"UTF-8\">")
    output_html.write("<link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">")
    output_html.write("<title>EG - TP3</title>")
    output_html.write("</head>")

    output_html.write("<body>")
    
    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    output_html.write(navbar)

    output_html.write("<h1> Nested Ifs' Suggestions</h1>")
    output_html.write("<table class=\"w3-table w3-table-all w3-hoverable\">")
    output_html.write("<tr class=\"w3-yellow\">")
    output_html.write("<th>Original</th>")
    output_html.write("<th>Suggestion</th>")
    output_html.write("</tr>")

    for sugestao in sugestoes.keys():
        sug = sugestao.replace("\t","\" + \t \"")
        output_html.write("<tr>")
        output_html.write("<td><span style=\"white-space: pre-wrap\">" + sugestao + "</span></td>")
        output_html.write("<td><span style=\"white-space: pre-wrap\">" + sugestoes[sugestao] + "</span></td>")
        output_html.write("</tr>")

    output_html.write("</table>")
    output_html.write("</body>")
    output_html.write("</html>")

def geraSDG(sdg, sdg_html):
    sdg_html.write("<!DOCTYPE html>")
    sdg_html.write("<html lang=\"pt\">")
    sdg_html.write("<head>")
    sdg_html.write("<meta charset=\"UTF-8\">")
    sdg_html.write("<link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">")
    sdg_html.write("<title>EG - TP3</title>")
    sdg_html.write("</head>")

    sdg_html.write("<body>")
    
    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    sdg_html.write(navbar)

    sdg_html.write("<h1> SDG </h1>")
    sdg_html.write(sdg)
    sdg_html.write("</body>")
    sdg_html.write("</html>")

def geraCFG(cfg, cfg_html):
    cfg_html.write("<!DOCTYPE html>")
    cfg_html.write("<html lang=\"pt\">")
    cfg_html.write("<head>")
    cfg_html.write("<meta charset=\"UTF-8\">")
    cfg_html.write("<link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">")
    cfg_html.write("<title>EG - TP3</title>")
    cfg_html.write("</head>")

    cfg_html.write("<body>")
    
    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    cfg_html.write(navbar)
    cfg_html.write("<h1> CFG </h1>")
    cfg_html.write(cfg)
    cfg_html.write("</body>")
    cfg_html.write("</html>")

def geraMcCabe(mccabe, islands, mccabe_html):
    mccabe_html.write("<!DOCTYPE html>")
    mccabe_html.write("<html lang=\"pt\">")
    mccabe_html.write("<head>")
    mccabe_html.write("<meta charset=\"UTF-8\">")
    mccabe_html.write("<link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">")
    mccabe_html.write("<title>EG - TP3</title>")
    mccabe_html.write("</head>")

    mccabe_html.write("<body>")
    
    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    mccabe_html.write(navbar)
    mccabe_html.write("<h1> McCabe </h1>")
    mccabe_html.write("<h1> Islands </h1>")
    if len(islands) == 0:
        mccabe_html.write("There are no unreachable code!")
    else:
        for i in islands:
          mccabe_html.write("<p> " + i  + " </p>")  
    mccabe_html.write("<h1> McCabe </h1>")
    mccabe_html.write("<h2> McCabe Complexity = "  +str(mccabe) + "</h2>")
    mccabe_html.write("</body>")
    mccabe_html.write("</html>")


def main():

    parserLark = Lark(grammar)
    if len(sys.argv) == 1:
        print("Insufficient arguments. Please pass the file name as an argument.")
        return
    
    f = open(sys.argv[1])

    code = f.read()

    parse_tree = parserLark.parse(code)
    data = MyInterpreter().visit(parse_tree)

    graphs = GraphInterpreter().visit(parse_tree)

    sdg_html = open("sdg.html", "w")
    cfg_html = open("cfg.html", "w")
    mccabe_html = open("mccabe.html", "w")

    geraSDG(graphs["sdg"], sdg_html)
    geraCFG(graphs["cfg"], cfg_html)
    geraMcCabe(graphs["mccabe"], graphs["islands"], mccabe_html)
    
    output_html = open("output.html", "w")
    #1 e 2 e 3
    geraHTML(data["atomic_vars"],data["struct_vars"], data["warnings"], data["errors"], data["nrStructs"], data["instructions"], output_html, data["controlStructs"])

    html_header = '''<!DOCTYPE html>
    <html>
        <style>
            .error {
                position: relative;
                display: inline-block;
                border-bottom: 1px dotted black;
                color: red;
            }

            .code {
                position: relative;
                display: inline-block;
            }

            .comment {
                position: relative;
                display: inline-block;
                color: grey;
            }

            .error .errortext {
                visibility: hidden;
                width: 200px;
                background-color: #555;
                color: #fff;
                text-align: center;
                border-radius: 6px;
                padding: 5px 0;
                position: absolute;
                z-index: 1;
                bottom: 125%;
                left: 50%;
                margin-left: -40px;
                opacity: 0;
                transition: opacity 0.3s;
            }

            .error .errortext::after {
                content: "";
                position: absolute;
                top: 100%;
                left: 20%;
                margin-left: -5px;
                border-width: 5px;
                border-style: solid;
                border-color: #555 transparent transparent transparent;
            }

            .error:hover .errortext {
                visibility: visible;
                opacity: 1;
            }
        </style>
        <head>
            <link rel=\"stylesheet\" href=\"https://www.w3schools.com/w3css/4/w3.css\">
            <title>EG - TP3</title>
        </head>
        '''

    navbar = '''
    <div class="w3-top">
            <div class="w3-bar w3-yellow intronav">
                <header>
                        <a href="output.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Code Analysis</a>
                        <a href="codeHTML.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Original Code</a>   
                        <a href="sugestao.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">Nested If's Suggestions</a>
                        <a href="sdg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">SDG</a>
                        <a href="cfg.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">CFG</a>
                        <a href="mccabe.html" class="w3-bar-item w3-button w3-hover-black w3-padding-16 w3-text-black w3-hover-text-white w3-xlarge">McCabe Complexity and Islands</a>
                </header>
            </div>
        </div>
    '''

    html = html_header + "<body>\n" + navbar + data["html_body"] + "\n</body></html>"

    with open("codeHTML.html","w") as out:
        out.write(html)

    output_html = open("sugestao.html", "w")
    geraSugestao(data["suggestions"], output_html)

if __name__ == "__main__":
    main()