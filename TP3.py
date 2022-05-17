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
        self.next = ""
        self.insts = 0
        self.statements = set()
        self.ifID = -1
        self.structureID = -1
        self.atomicID = -1
        self.atribID = -1
        self.printID = -1
        self.readID = -1

    def start(self,tree):
        self.visit(tree.children[1])
        self.output += "\"fim\"\n}"
        print(self.output)

    def program(self,tree):
        for c in tree.children:
            if c.children[0].data != "comment":
                self.next = ""
                self.visit(c)
                self.output += "\"" + self.next + "\"\n\t\"" + self.next + "\" -> "
                self.statements.add(self.next)
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

        self.next += "atomic_" + str(self.atomicID) + " " + var_type + " " + var_name

        if(len(tree.children) > 3):            
            self.next += " = " 
            self.visit(tree.children[3])

    def elem(self, tree):

        if(not isinstance(tree.children[0], Tree)):
            self.next += str(tree.children[0])
        else:
            r = self.visit(tree.children[0])
            return r

    def structure(self, tree):
        self.structureID += 1

        self.next += "structure_" + str(self.structureID) + " "

        self.visit(tree.children[0])

        pass

    def set(self, tree):
        childs = len(tree.children)

        self.next += "set " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.next += " = "

            for c in tree.children[2:]:
                if c != "{" and c != "}" and c != ",":
                    self.visit(c)
                if c == "{" or c == "}" or c == ",":
                    self.next += c.value
                    if c == ",":
                        self.next += " "
        elif childs == 4:
            self.next += " = {}"

        pass

    def list(self, tree):
        childs = len(tree.children)

        self.next += "list " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.next += " = "

            for c in tree.children[2:]:
                if c != "[" and c != "]" and c != ",":
                    self.visit(c)
                if c == "[" or c == "]" or c == ",":
                    self.next += c.value
                    if c == ",":
                        self.next += " "
        elif childs == 4:
            self.next += " = []"
        pass

    def tuple(self, tree):
        childs = len(tree.children)

        self.next += "tuple " + tree.children[0].value
        if childs != 1 and childs != 4:
            self.next += " = "
            for c in tree.children[2:]:
                if c != "(" and c != ")" and c != ",":
                    self.visit(c)
                if c == "(" or c == ")" or c == ",":
                    self.next += c.value
                    if c == ",":
                        self.next += " "
        elif childs == 4:
            self.next += " = ()"
        pass

    def dict(self, tree):
        childs = len(tree.children)

        self.next += "dict " + tree.children[0].value

        if childs != 1 and childs != 4:
            self.next += " = {"
            start = 3
            while start < childs-1:
                key = self.visit(tree.children[start])
                self.next += " : "
                value = self.visit(tree.children[start+2])
                if start + 4 < (childs-1):
                    self.next += ", "
                start += 4
            self.next += "}"
        elif childs == 4:
            self.next += " = {}"
        pass

    def atrib(self,tree):
        self.atribID += 1
        self.next += "atrib_" + str(self.atribID) + " " + tree.children[0].value + " = "
        self.visit(tree.children[2])

        pass

    def initcicle(self, tree):

        self.next += tree.children[0].value + " = "
        self.visit(tree.children[2])

        pass

    def print(self,tree):

        self.printID += 1

        self.next += "print_" + str(self.printID) + " print(" + tree.children[1].value + ")"
            
        pass

    def read(self,tree):

        self.readID += 1

        self.next += "read_" + str(self.readID) + " read(" + tree.children[1].value + ")"
            
        pass

    #def cond(self,tree):
    #    self.ifID += 1
    #    self.next += "if_" + str(self.ifID) + "_start if("
#
    #    l = len(tree.children)
#
    #    self.visit(tree.children[2])
    #    
    #    self.next += ")"
#
    #    self.visit(tree.children[4])     
#
    #    if(tree.children[(l-2)] == "else"):
    #        self.next += "if_" + str(self.ifID) + "_start if("
    #        self.visit(tree.children[(l-1)])
#
    #    pass














    def op(self,tree):
        if(len(tree.children) > 1):
            if(tree.children[0] == "!"):
                self.next += "!"
                self.visit(tree.children[1])
            elif(tree.children[1] == "&"):
                self.visit(tree.children[0])
                self.next += " & "
                self.visit(tree.children[2])
            elif(tree.children[1] == "#"):
                t1 = self.visit(tree.children[0])
                self.next += " # "
                t2 = self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.next += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def expcond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.next += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def termocond(self,tree):
        if len(tree.children) > 1:
            self.visit(tree.children[0])
            self.next += " " + tree.children[1].value + " "
            self.visit(tree.children[2])
        else:
            self.visit(tree.children[0])

    def factor(self,tree):
        r = None
        if tree.children[0].type == 'SIGNED_INT':
            r = int(tree.children[0])
            self.next += str(r)
        elif tree.children[0].type == 'VARNAME':
            self.next += tree.children[0].value
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
ciclefor: FOR PE (initcicle (VIR initcicle)*)? PV op PV (inc | dec (VIR (inc | dec))*)? PD body
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