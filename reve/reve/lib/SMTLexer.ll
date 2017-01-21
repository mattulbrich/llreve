%option noyywrap
%option prefix="smt"
%{
#include <iostream>
#include "SMT.h"
#include "SMTParser.hpp"
extern "C" {
int smtlex(void);
}
extern int readInputForLexer(char* buffer,int *numBytesRead,int maxBytesToRead);
#undef YY_INPUT
#define YY_INPUT(b,r,s) readInputForLexer(b,&r,s)
using namespace std;
%}
%%
[ \t\n]         ;
\(              { return LPAR; }
\)              { return RPAR; }
[0-9]+          { smtlval.number = strtoul(yytext, NULL, 10); return NUMBER; }
true            { return TRUE; }
false           { return FALSE; }
forall          { return FORALL; }
Int             { return INT; }
HEAP$(1|2)      { smtlval.heapName = new std::string(yytext); return HEAP; }
(and|=|>=|or|select|store|distinct|\<=|\<|>|\+|-) {
    smtlval.opName = new std::string(yytext);
    return OPNAME;
}
[\_[:alnum:]][\_\|.$[:alnum:]]* {
    smtlval.identifier = new std::string(yytext);
    return IDENTIFIER;
}
%%
