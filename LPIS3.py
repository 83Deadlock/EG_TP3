from dataclasses import InitVar
from doctest import Example
from mimetypes import init
import re
import sys
from lark import Discard
from lark import Lark,Token,Tree
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter

class MyInterpreter (Interpreter):
    def __init__(self):
        self.output = "digraph G {\n\t" + "\"entry\" -> "
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

    def start(self,tree):
        self.visit(tree.children[1])
        self.output += "\"fim\"\n"

        lines = self.output.splitlines()
        #print(lines)

        statements = set()

        for line in lines:
            aux = line.split(" -> ")
            for c in aux:
                c = c.replace("\t","")
                statements.add(c)

        #print(statements)

        for c in statements:
            i = 0
            while i <= self.ifID:
                s = "if_" + str(i) + "_start"
                if s in c:                    
                    if c[0] != "\t":
                        c = "\t" + c
                    self.output += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.whileID:
                s = "while_" + str(i) + "_start"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.output += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.repeatID:
                s = "repeat_" + str(i) + "_start"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.output += c + " [shape=diamond]\n"
                i = i + 1

            i = 0
            while i <= self.forID:
                s = "for_" + str(i) + "_cond"
                if s in c:
                    if c[0] != "\t":
                        c = "\t" + c
                    self.output += c + " [shape=diamond]\n"
                i = i + 1

        self.output += "}"
        print(self.output)

    def program(self,tree):
        for c in tree.children:
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
        self.atomicID += 1

        var_type = tree.children[0].value        

        var_name = tree.children[1].value

        self.output += "\"atomic_" + str(self.atomicID) + " " + var_type + " " + var_name

        if(len(tree.children) > 3):            
            self.output += " = " 
            self.visit(tree.children[3])

        self.output += "\"\n\t" + "\"atomic_" + str(self.atomicID) + " " + var_type + " " + var_name

        if(len(tree.children) > 3):            
            self.output += " = " 
            self.visit(tree.children[3])
        
        self.output += "\" -> "


    def elem(self, tree):
        if(not isinstance(tree.children[0], Tree)):
            if(tree.children[0].type == "ESCAPED_STRING"):
                self.output += tree.children[0].replace('\"','\'')
            else:
                self.output += str(tree.children[0])
        else:
            r = self.visit(tree.children[0])
            return r

    def structure(self, tree):
        self.structureID += 1

        self.output += "\"structure_" + str(self.structureID) + " "

        self.visit(tree.children[0])

        self.output += "\"\n\t\"structure_" + str(self.structureID) + " "

        self.visit(tree.children[0])
        
        self.output += "\" -> "

        pass

    def set(self, tree):
        childs = len(tree.children)

        self.output += "set " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.output += " = "

            for c in tree.children[2:]:
                if c != "{" and c != "}" and c != ",":
                    self.visit(c)
                if c == "{" or c == "}" or c == ",":
                    self.output += c.value
                    if c == ",":
                        self.output += " "
        elif childs == 4:
            self.output += " = {}"

        pass

    def list(self, tree):
        childs = len(tree.children)

        self.output += "list " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.output += " = "

            for c in tree.children[2:]:
                if c != "[" and c != "]" and c != ",":
                    self.visit(c)
                if c == "[" or c == "]" or c == ",":
                    self.output += c.value
                    if c == ",":
                        self.output += " "
        elif childs == 4:
            self.output += " = []"
        pass

    def tuple(self, tree):
        childs = len(tree.children)

        self.output += "tuple " + tree.children[0].value
        if childs != 1 and childs != 4:
            self.output += " = "
            for c in tree.children[2:]:
                if c != "(" and c != ")" and c != ",":
                    self.visit(c)
                if c == "(" or c == ")" or c == ",":
                    self.output += c.value
                    if c == ",":
                        self.output += " "
        elif childs == 4:
            self.output += " = ()"
        pass

    def dict(self, tree):
        childs = len(tree.children)

        self.output += "dict " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.output += " = {"
            start = 3
            while start < childs-1:
                key = self.visit(tree.children[start])
                self.output += " : "
                value = self.visit(tree.children[start+2])
                if start + 4 < (childs-1):
                    self.output += ", "
                start += 4
            self.output += "}"
        elif childs == 4:
            self.output += " = {}"
        pass

    def atrib(self,tree):
        self.atribID += 1
        self.output += "\"atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "
        self.visit(tree.children[2])
        self.output += "\"\n\t\"atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "
        self.visit(tree.children[2])
        self.output += "\" -> "

        pass

    def initcicle(self, tree):

        self.output += tree.children[0].value + " = "
        self.visit(tree.children[2])

        pass

    def print(self,tree):

        self.printID += 1

        s = tree.children[1].value.replace('\"','\'')

        self.output += "\"print_" + str(self.printID) + " print(" + s + ")\"\n\t"

        self.output += "\"print_" + str(self.printID) + " print(" + s + ")\" -> "
            
        pass

    def read(self,tree):

        self.readID += 1

        self.output += "\"read_" + str(self.readID) + " read(" + tree.children[1].value + ")\"\n\t"
        self.output += "\"read_" + str(self.readID) + " read(" + tree.children[1].value + ")\" -> "
        pass

    def cond(self,tree):
        self.incicle = True

        self.ifID += 1
        self.output += "\"if_" + str(self.ifID) + "_start if("

        l = len(tree.children)
        self.visit(tree.children[2])

        self.output += ")\"\n\t\"if_" + str(self.ifID) + "_start if("

        self.visit(tree.children[2])

        self.output += ")\" -> "
 
        # body
        self.visit(tree.children[4])

        #fim do if
        self.output += "\"if_" + str(self.ifID) + "_end if("

        self.visit(tree.children[2])

        self.output += ")\"\n\t"

        if(tree.children[(l-2)] == "else"):
            self.output += "\"if_" + str(self.ifID) + "_start if("
            self.visit(tree.children[2])
            self.output += ")\" -> "
            self.visit(tree.children[(l-1)])
            self.output += "\"if_" + str(self.ifID) + "_end if("
            self.visit(tree.children[2])
            self.output += ")\"\n\t"

        else:
            self.output += "\"if_" + str(self.ifID) + "_start if("
            self.visit(tree.children[2])
            self.output += ")\" -> \"if_" + str(self.ifID) + "_end if("
            self.visit(tree.children[2])
            self.output += ")\"\n\t"

        self.output += "\"if_" + str(self.ifID) + "_end if("

        self.visit(tree.children[2])

        self.output += ")\" -> "

        pass

    def ciclewhile(self,tree):
        self.whileID += 1

        self.output += "\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.output += ")\"\n\t\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.output += ")\" -> \"while_" + str(self.whileID) + "_end while("
        self.visit(tree.children[2])
        self.output += ")\"\n\t\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.output += ")\" -> "

        self.visit(tree.children[4])

        self.output += "\"while_" + str(self.whileID) + "_start while("
        self.visit(tree.children[2])
        self.output += ")\"\n\t\"while_" + str(self.whileID) + "_end while("
        self.visit(tree.children[2])
        self.output += ")\" -> "

        pass

    def ciclerepeat(self,tree):
        self.repeatID += 1

        self.output += "\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.output += ")\"\n\t\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.output += ")\" -> \"repeat_" + str(self.repeatID) + "_end repeat(" + tree.children[2].value
        self.output += ")\"\n\t\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.output += ")\" -> "

        self.visit(tree.children[4])

        self.output += "\"repeat_" + str(self.repeatID) + "_start repeat(" + tree.children[2].value
        self.output += ")\"\n\t\"repeat_" + str(self.whileID) + "_end repeat(" + tree.children[2].value
        self.output += ")\" -> "        

        pass

    def ciclefor(self,tree):
        self.forID += 1

        self.output += "\"for_" + str(self.forID) + "_start\"\n\t\"for_" + str(self.forID) + "_start\" -> "

        forcicle = {}

        forcicle["op"] = []
        forcicle["initcicle"] = []
        forcicle["body"] = []
        forcicle["inc"] = []
        forcicle["dec"] = []

        for c in tree.children:
            if c != "for" and c != "(" and c != ")" and c != ";" and c != ",":
                forcicle[c.data].append(c)

        #print(forcicle)

        for c in forcicle["initcicle"]:
            self.output += "\""
            self.visit(c)
            self.output += "\"\n\t\""
            self.visit(c)
            self.output += "\" -> "

        for c in forcicle["op"]:
            self.output += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.output += ")\"\n\t\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.output += ")\" -> \"for_" + str(self.forID) + "_end\"\n\t"
            self.output += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.output += ")\" -> "

        for c in forcicle["body"]:
            self.visit(c)

        for c in forcicle["inc"]:
            self.output += "\""
            self.visit(c)
            self.output += "\"\n\t\""
            self.visit(c)
            self.output += "\" -> "

        for c in forcicle["dec"]:
            self.output += "\""
            self.visit(c)
            self.output += "\"\n\t\""
            self.visit(c)
            self.output += "\" -> "

        for c in forcicle["op"]:
            self.output += "\"for_" + str(self.forID) + "_cond ("
            self.visit(c)
            self.output += ")\"\n\t\"for_" + str(self.forID) + "_end\" -> "

        #for c in tree.children:
        #    if c != "for" and c != "(" and c != ")" and c != ";" and c != ",":
        #        print(c.data)
        #        if c.data == "initcicle":
        #            self.output += "\""
        #            self.visit(c)
        #            self.output += "\"\n\t\""
        #            self.visit(c)
        #            self.output += "\" -> "
        #        elif c.data == "op":
        #            self.output += "\"for_" + str(self.forID) + "_cond ("
        #            self.visit(c)
        #            self.output += ")\"\n\t\"for_" + str(self.forID) + "_cond ("
        #            self.visit(c)
        #            self.output += ")\" -> for_" + str(self.forID) + "_end\"\n\t"
        #            self.output += "\"for_" + str(self.forID) + "_cond ("
        #            self.visit(c)
        #            self.output += ")\" -> "
        #        elif c.data == 
        
        #self.output += "\"for_" + str(self.forID) + "_end\"\n\t\"for_" + str(self.forID) + "_end\" -> "
        

        pass
    
    def inc(self, tree):
        self.output += tree.children[0] + "++"  
        pass

    def dec(self, tree):
        self.output += tree.children[0] + "--"

        pass

    def op(self,tree):
        if(len(tree.children) > 1):
            if(tree.children[0] == "!"):
                self.output += "!"
                self.visit(tree.children[1])
            elif(tree.children[1] == "&"):
                self.visit(tree.children[0])
                self.output += " & "
                self.visit(tree.children[2])
            elif(tree.children[1] == "#"):
                t1 = self.visit(tree.children[0])
                self.output += " # "
                t2 = self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.output += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def expcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.output += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def termocond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.output += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factor(self,tree):
        r = None
        if tree.children[0].type == 'SIGNED_INT':
            r = int(tree.children[0])
            self.output += str(r)
        elif tree.children[0].type == 'VARNAME':
            self.output += tree.children[0].value
        elif tree.children[0].type == 'DECIMAL':
            r = float(tree.children[0])
            self.output += str(r)
        elif tree.children[0] == "(":
            self.visit(tree.children[1])

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
atrib: VARNAME EQUAL elem PV
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

def main():

    parserLark = Lark(grammar)
    if len(sys.argv) == 1:
        print("Insufficient arguments. Please pass the file name as an argument.")
        return
    
    f = open(sys.argv[1])

    code = f.read()

    parse_tree = parserLark.parse(code)
    data = MyInterpreter().visit(parse_tree)

if __name__ == "__main__":
    main()