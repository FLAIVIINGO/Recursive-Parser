Did not make a make file for this unfortunately
Written in C
Commands in Order:
flex p2.l
bison -d p2.y
gcc -o run p2.tab.c lex.yy.c -ly -ll
./run < ../class_sol/test1
