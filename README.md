# Practical assignment on Language Engineering. Static code analyzer, code-flow graphs and statistical analysis.

This assignment comes as the next step to the work done on my repository - ["EG_TP2"](https://github.com/83Deadlock/EG_TP2).

The first phase of this assignment was to use [lark-parser](https://github.com/lark-parser/lark) to define the grammar of a programming language that allowed for a few simple instructions and variable assignments - definition and declaration of both atomic and structural variables, flow-control structures such as "while", "for" and "if", and basic arithmetic instructions. Visit the testeX.txt files in this repository to get code samples of the language we defined and used on this assignment.

Second phase was to build a code analyzer that should be able to statically get some information about the code we're compiling. Information such as number of instructions of each type, defined variables, declared variables aswell as report to the user some errors and warnings such as unitialized variables or re-declaration of variables among some others. This phase was completed successfully on the ["EG_TP2"](https://github.com/83Deadlock/EG_TP2) assignment.

The last part of this assignment was to generate code flow graphs and system dependency graphs from the given code, aswell as reporting about the existence of unreachable code and the [McCabe Complexity](https://en.wikipedia.org/wiki/Cyclomatic_complexity). We also added the extra feature to be able to view the code, showing the warnings and errors to the user.

The LPIS.py file will be the executable for this project and will receive an argument which will be the file name. It will import the GraphInterpreter class com LPIS3.py and run it as if it were a module. This was done in order to mantain a cleaner code, considering the code on LPIS.py was a result of a previous assignment.

The output will consist of a few html files containing every single bit of information described above.
