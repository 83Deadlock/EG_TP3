import chunk
from dataclasses import InitVar
from doctest import Example
from mimetypes import init
import re
import sys
from lark import Discard
from lark import Lark,Token,Tree
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter

class GraphInterpreter (Interpreter):
    def __init__(self):
        self.cfg = "digraph G {\n\t\"entry\" -> "
        self.sdg = "digraph G {\n\t"
        self.statements = set()
        self.ifID = -1
        self.structureID = -1
        self.atomicID = -1
        self.atribID = -1
        self.printID = -1
        self.readID = -1
        self.whileID = -1
        self.repeatID = -1
        self.forID = -1
        self.initcicleID = -1
        self.incID = -1
        self.decID = -1
        self.output = {}
        self.second = False
        self.incicle = False
        self.only = False
        self.islands = set()
        self.mccabe = 0

    def start(self,tree):
        #print("comecei")
        self.visit(tree.children[1])
        self.cfg += "\"fim\"\n"

        lines = self.cfg.splitlines()
        lines2 = self.sdg.splitlines()
        #print(lines)
        #print(lines2[1:len(lines2)-1])

        statements = set()
        statements2 = set()
        chunks = {}

        for line in lines:
            aux = line.split(" -> ")
            for c in aux:
                c = c.replace("\t","")
                statements.add(c)

        for line in lines2[1:len(lines2)-1]:
            aux = line.split(" -> ")

            aux[0] = aux[0].replace("\t","")
            aux[1] = aux[1].replace("\t","")

            aux[0] = aux[0].replace("\"","")
            aux[1] = aux[1].replace("\"","")

            if aux[0] not in chunks.keys():
                chunks[aux[0]] = []    
            chunks[aux[0]].append(aux[1])

            statements2.add(aux[0])
            statements2.add(aux[1])



        ks = set()
        for k in chunks.keys():
            ks.add(k)
            self.islands.add(k)

        for k in ks:
            for t,v in chunks.items():
                if k != t:
                    if k in v:
                        self.islands.remove(k)
        self.islands.remove("entry")

        for c in statements:
            i = 0
            while i <= self.ifID:
                s = "if_" + str(i) + "_start"
                if s in c:                    
                    if c[0] != "\t":
                        c = "\t" + c
                    self.cfg += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.whileID:
                s = "while_" + str(i) + "_start"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.cfg += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.repeatID:
                s = "repeat_" + str(i) + "_start"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.cfg += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.forID:
                s = "for_" + str(i) + "_cond"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.cfg += c + " [shape=diamond]\n"
                i = i + 1

        self.cfg += "}"

        self.sdg += "\n}"
        #print(self.cfg)
        #print(self.sdg)
        #print(self.islands)

        edges = len(lines2[1:len(lines2)-1])
        nodes = len(statements2)

        self.mccabe = edges - nodes + 2

        self.output["cfg"] = self.cfg
        self.output["sdg"] = self.sdg
        self.output["islands"] = self.islands
        self.output["mccabe"] = self.mccabe

        return self.output

    def program(self,tree):

        for c in tree.children:
            if not self.incicle and c.children[0].data != "comment":
                self.sdg += "\"entry\" -> "
            if c.children[0].data != "comment":
                self.visit(c)                            
        pass

    def instruction(self,tree):
        self.visit(tree.children[0])

        pass

    def declaration(self, tree):
        self.visit(tree.children[0])

        pass

    def atomic(self,tree):
        if not self.second:
            self.atomicID += 1

        var_type = tree.children[0].value        

        var_name = tree.children[1].value

        self.cfg += "\"atomic_" + str(self.atomicID) + " " + var_type + " " + var_name
        self.sdg += "\"atomic_" + str(self.atomicID) + " " + var_type + " " + var_name

        if(len(tree.children) > 3):            
            self.cfg += " = " 
            self.sdg += " = "
            self.visit(tree.children[3])

        self.cfg += "\"\n\t" + "\"atomic_" + str(self.atomicID) + " " + var_type + " " + var_name
        self.sdg += "\"\n\t"

        if(len(tree.children) > 3):            
            self.cfg += " = " 
            self.second = True
            self.visit(tree.children[3])
            self.second = False
        
        self.cfg += "\" -> "

    def elem(self, tree):
        if(not isinstance(tree.children[0], Tree)):
            if(tree.children[0].type == "ESCAPED_STRING"):
                self.cfg += tree.children[0].replace('\"','\'')
                if not self.second:
                    self.sdg += tree.children[0].replace('\"','\'')
            else:
                self.cfg += str(tree.children[0])
                if not self.second:
                    self.sdg += str(tree.children[0])
        else:
            r = self.visit(tree.children[0])
            return r

    def structure(self, tree):
        if not self.second:
            self.structureID += 1

        self.cfg += "\"structure_" + str(self.structureID) + " "
        self.sdg += "\"structure_" + str(self.structureID) + " "

        self.visit(tree.children[0])

        self.second = True

        self.cfg += "\"\n\t\"structure_" + str(self.structureID) + " "
        self.sdg += "\"\n\t"

        self.visit(tree.children[0])
        
        self.cfg += "\" -> "

        self.second = False

        pass

    def set(self, tree):
        childs = len(tree.children)

        self.cfg += "set " + tree.children[0].value
        if not self.second:
            self.sdg += "set " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.cfg += " = "
            if not self.second:
                    self.sdg += " = "

            for c in tree.children[2:]:
                if c != "{" and c != "}" and c != ",":
                    self.visit(c)
                if c == "{" or c == "}" or c == ",":
                    self.cfg += c.value
                    if not self.second:
                        self.sdg += c.value
                    if c == ",":
                        self.cfg += " "
                        if not self.second:
                            self.sdg += " "
        elif childs == 4:
            self.cfg += " = {}"
            if not self.second:
                    self.sdg += " = {}"

        pass

    def list(self, tree):
        childs = len(tree.children)

        self.cfg += "list " + tree.children[0].value
        if not self.second:
            self.sdg += "list " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.cfg += " = "
            if not self.second:
                self.sdg += " = "

            for c in tree.children[2:]:
                if c != "[" and c != "]" and c != ",":
                    self.visit(c)
                if c == "[" or c == "]" or c == ",":
                    self.cfg += c.value
                    if not self.second:
                        self.sdg += c.value
                    if c == ",":
                        self.cfg += " "
                        if not self.second:
                            self.sdg += " "
        elif childs == 4:
            self.cfg += " = []"
            if not self.second:
                self.sdg += " = []"
        pass

    def tuple(self, tree):
        childs = len(tree.children)

        self.cfg += "tuple " + tree.children[0].value
        if not self.second:
            self.sdg += "tuple " + tree.children[0].value
        if childs != 1 and childs != 4:
            self.cfg += " = "
            if not self.second:
                self.sdg += " = "
            for c in tree.children[2:]:
                if c != "(" and c != ")" and c != ",":
                    self.visit(c)
                if c == "(" or c == ")" or c == ",":
                    self.cfg += c.value
                    if not self.second:
                        self.sdg += c.value
                    if c == ",":
                        self.cfg += " "
                        if not self.second:
                            self.sdg += " "
        elif childs == 4:
            self.cfg += " = ()"
            if not self.second:
                self.sdg += " = ()"
        pass

    def dict(self, tree):
        childs = len(tree.children)

        self.cfg += "dict " + tree.children[0].value
        if not self.second:
            self.sdg += "dict " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.cfg += " = {"
            if not self.second:
                self.sdg += " = {"
            start = 3
            while start < childs-1:
                key = self.visit(tree.children[start])
                self.cfg += " : "
                if not self.second:
                    self.sdg += " : "
                value = self.visit(tree.children[start+2])
                if start + 4 < (childs-1):
                    self.cfg += ", "
                    if not self.second:
                        self.sdg += ", "
                start += 4
            self.cfg += "}"
            if not self.second:
                self.sdg  += "}"
        elif childs == 4:
            self.cfg += " = {}"
            if not self.second:
                self.sdg += " = {}"
        pass

    def atrib(self,tree):
        if not self.second:
            self.atribID += 1
        self.cfg += "\"atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "
        self.sdg += "\"atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "

        self.visit(tree.children[2])

        self.second = True
        self.cfg += "\"\n\t\"atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "
        self.sdg += "\"\n\t"
        self.visit(tree.children[2])
        self.cfg += "\" -> "
        self.second = False

        pass

    def initcicle(self, tree):
        if not self.second:
            self.initcicleID += 1
        self.cfg += "initcicle_" + str(self.initcicleID) + " " + tree.children[0].value + " = "
        #self.visit(tree.children[2])
        if not self.second:
            self.sdg += "initcicle_" + str(self.initcicleID) + " " + tree.children[0].value + " = "
        self.visit(tree.children[2])

        pass

    def print(self,tree):

        if not self.second:
            self.printID += 1

        s = tree.children[1].value.replace('\"','\'')

        self.cfg += "\"print_" + str(self.printID) + " print(" + s + ")\"\n\t"
        self.sdg += "\"print_" + str(self.printID) + " print(" + s + ")\"\n\t"

        self.cfg += "\"print_" + str(self.printID) + " print(" + s + ")\" -> "
            
        pass

    def read(self,tree):

        if not self.second:
            self.readID += 1

        self.cfg += "\"read_" + str(self.readID) + " read(" + tree.children[1].value + ")\"\n\t"
        self.sdg += "\"read_" + str(self.readID) + " read(" + tree.children[1].value + ")\"\n\t"

        self.cfg += "\"read_" + str(self.readID) + " read(" + tree.children[1].value + ")\" -> "
        pass

    def cond(self,tree):
        self.incicle = True

        if not self.second:
            self.ifID += 1
        self.cfg += "\"if_" + str(self.ifID) + "_start if("
        self.sdg += "\"if_" + str(self.ifID) + " if("

        l = len(tree.children)
        self.visit(tree.children[2])

        self.cfg += ")\"\n\t\"if_" + str(self.ifID) + "_start if("
        self.sdg += ")\"\n\t\"if_" + str(self.ifID) + " if("

        #self.second = True
        self.visit(tree.children[2])
        #self.second = False

        self.cfg += ")\" -> "
        self.sdg += ")\" -> \"then" + str(self.ifID) + "\"\n\t"
 
        self.incicle = True
        # body
        #self.visit(tree.children[4].children[1])
        for c in tree.children[4].children[1].children:
            #print(c.pretty())
            self.sdg += "\"then" + str(self.ifID) + "\" -> "
            self.visit(c)
        #fim do if
        self.incicle = False


        self.cfg += "\"if_" + str(self.ifID) + "_end if("
        self.second = True
        self.visit(tree.children[2])

        self.cfg += ")\"\n\t"
        self.second = False
        
        if(tree.children[(l-2)] == "else"):
            self.cfg += "\"if_" + str(self.ifID) + "_start if("
            self.sdg += "\"if_" + str(self.ifID) + " if("
            self.visit(tree.children[2])
            self.cfg += ")\" -> "
            self.sdg += ")\" -> \"else" + str(self.ifID) + "\"\n\t"

            self.incicle = True
            for c in tree.children[(l-1)].children[1].children:
                self.sdg += "\"else" + str(self.ifID) + "\" -> "
                self.visit(c)
            #self.visit(tree.children[(l-1)])
            self.incicle = False

            self.second = True
            self.cfg += "\"if_" + str(self.ifID) + "_end if("
            self.visit(tree.children[2])
            self.cfg += ")\"\n\t"
            self.second = False

        else:
            self.second = True
            self.cfg += "\"if_" + str(self.ifID) + "_start if("
            self.visit(tree.children[2])
            self.cfg += ")\" -> \"if_" + str(self.ifID) + "_end if("
            self.visit(tree.children[2])
            self.cfg += ")\"\n\t"
            self.second = False

        self.second = True
        self.cfg += "\"if_" + str(self.ifID) + "_end if("

        self.visit(tree.children[2])

        self.cfg += ")\" -> "
        self.second = False

        pass

    def ciclewhile(self,tree):
        self.whileID += 1

        self.cfg += "\"while_" + str(self.whileID) + "_start while("
        self.sdg += "\"while_" + str(self.whileID) + " while("
        self.visit(tree.children[2])
        self.cfg += ")\"\n\t\"while_" + str(self.whileID) + "_start while("
        self.sdg += ")\"\n\t"
        self.second = True
        self.visit(tree.children[2])
        self.cfg += ")\" -> \"while_" + str(self.whileID) + "_end while("
        self.visit(tree.children[2])
        self.cfg += ")\"\n\t\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.cfg += ")\" -> "
        self.second = False

        for c in tree.children[4].children[1].children:
            self.sdg += "\"while_" + str(self.whileID) + " while("
            self.visit(tree.children[2])
            self.sdg += ")\" -> "
            self.visit(c)

        self.second = True
        self.cfg += "\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.cfg += ")\"\n\t\"while_" + str(self.whileID) + "_end while("
        self.visit(tree.children[2])
        self.cfg += ")\" -> "
        self.second = False


        pass

    def ciclerepeat(self,tree):
        if not self.second:
            self.repeatID += 1

        self.cfg += "\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.sdg += "\"repeat_" + str(self.repeatID) + " repeat(" + tree.children[2].value + ")\"\n\t"
        self.cfg += ")\"\n\t\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.cfg += ")\" -> \"repeat_" + str(self.repeatID) + "_end repeat(" + tree.children[2].value
        self.cfg += ")\"\n\t\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.cfg += ")\" -> "

        for c in tree.children[4].children[1].children:
            self.sdg += "\"repeat_" + str(self.repeatID) + " repeat(" + tree.children[2] + ")\" -> "
            self.visit(c)
        
        self.cfg += "\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.cfg += ")\"\n\t\"repeat_" + str(self.whileID) + "_end repeat(" + tree.children[2].value
        self.cfg += ")\" -> "        

        pass

    def ciclefor(self,tree):
        if not self.second:
            self.forID += 1

        self.cfg += "\"for_" + str(self.forID) + "_start\"\n\t\"for_" + str(self.forID) + "_start\" -> "

        forcicle = {}

        forcicle["op"] = []
        forcicle["initcicle"] = []
        forcicle["body"] = []
        forcicle["inc"] = []
        forcicle["dec"] = []

        for c in tree.children:
            if c != "for" and c != "(" and c != ")" and c != ";" and c != ",":
                forcicle[c.data].append(c)
        
        for c in forcicle["initcicle"]:
            self.cfg += "\""
            self.sdg += "\""
            self.visit(c)
            self.cfg += "\"\n\t\""
            self.sdg += "\"\n\t\"entry\" -> "
            self.second = True
            self.visit(c)
            self.cfg += "\" -> "
            self.second = False
        
        
        self.sdg += "\"for_" + str(self.forID) + " for("
        self.only = True
        self.visit(forcicle["op"][0])
        self.only = False
        self.sdg += ")\"\n\t"

        for c in forcicle["op"]:
            self.second = True
            self.cfg += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.cfg += ")\"\n\t\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.cfg += ")\" -> \"for_" + str(self.forID) + "_end\"\n\t"
            self.cfg += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.cfg += ")\" -> "
            self.second = False

        for c in forcicle["body"]:
            for t in c.children[1].children:
                self.sdg += "\"for_" + str(self.forID) + " for("
                self.only = True
                self.visit(forcicle["op"][0])
                self.sdg += ")\" -> "
                self.only = False
                self.visit(t)
        i = 0
        for c in forcicle["inc"]:
            if i == 0:
                self.sdg += "\"for_" + str(self.forID) + " for("
            else:
                self.sdg += "\n\t\"for_" + str(self.forID) + " for("
            self.only = True
            self.visit(forcicle["op"][0])
            self.only = False
            self.sdg += ")\" -> \""
            self.cfg += "\""
            self.visit(c)
            self.cfg += "\"\n\t\""
            self.sdg += "\""
            self.second = True
            self.visit(c)
            self.cfg += "\" -> "
            self.second = False

        
        for c in forcicle["dec"]:
            self.sdg += "\n\t\"for_" + str(self.forID) + " for("
            self.only = True
            self.visit(forcicle["op"][0])
            self.only = False
            self.sdg += ")\" -> \""
            self.cfg += "\""
            self.visit(c)
            self.cfg += "\"\n\t\""
            self.sdg += "\""
            self.second = True
            self.visit(c)
            self.cfg += "\" -> "
            self.second = False

        for c in forcicle["op"]:
            self.second = True
            self.cfg += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.cfg += ")\"\n\t\"for_" + str(self.forID) + "_end\" -> "
            self.second = False
        
        pass
    
    def inc(self, tree):
        if not self.second:
            self.incID += 1
        self.cfg += "inc_" + str(self.incID) + " " + tree.children[0] + "++" 
        if not self.second:
            self.sdg += "inc_" + str(self.incID) + " " + tree.children[0] + "++" 

        pass

    def dec(self, tree):
        if not self.second:
            self.decID += 1
        self.cfg += "dec_" + str(self.decID) + " " + tree.children[0] + "--"
        if not self.second:
            self.sdg += "dec_" + str(self.decID) + " " + tree.children[0] + "--" 

        pass

    def op(self,tree):
        if(len(tree.children) > 1):
            if(tree.children[0] == "!"):
                if not self.only:
                    self.cfg += "!"
                if not self.second:
                    self.sdg += "!"
                self.visit(tree.children[1])
            elif(tree.children[1] == "&"):
                self.visit(tree.children[0])
                if not self.only:
                    self.cfg += " & "
                if not self.second:
                    self.sdg += " & "
                self.visit(tree.children[2])
            elif(tree.children[1] == "#"):
                t1 = self.visit(tree.children[0])
                if not self.only:
                    self.cfg += " # "
                if not self.second:
                    self.sdg += " # "
                t2 = self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            if not self.only:
                self.cfg += " " + tree.children[1].value + " "
            if not self.second:
                    self.sdg += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def expcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            if not self.only:
                self.cfg += " " + tree.children[1].value + " "
            if not self.second:
                    self.sdg += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def termocond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            if not self.only:
                self.cfg += " " + tree.children[1].value + " "
            if not self.second:
                    self.sdg += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factor(self,tree):
        r = None
        if tree.children[0].type == 'SIGNED_INT':
            r = int(tree.children[0])
            if not self.only:
                self.cfg += str(r)
            if not self.second:
                self.sdg += str(r)
        elif tree.children[0].type == 'VARNAME':
            if not self.only:
                self.cfg += tree.children[0].value
            if not self.second:
                self.sdg += tree.children[0].value
        elif tree.children[0].type == 'DECIMAL':
            r = float(tree.children[0])
            if not self.only:
                self.cfg += str(r)
            if not self.second:
                self.sdg += str(r)
        elif tree.children[0] == "(":
            self.visit(tree.children[1])