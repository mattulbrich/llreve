%option noyywrap
%{
#include <iostream>
#include "SMT.h"
#include "SMTParser.hpp"
extern "C" {
int yylex(void);
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
[0-9]+          { yylval.number = strtoul(yytext, NULL, 10); return NUMBER; }
true            { return TRUE; }
false           { return FALSE; }
(and|=|>=|or|select|store|distinct|\<=|\<|>) {
    yylval.opName = new std::string(yytext);
    return OPNAME;
}
[\_[:alnum:]][\_\|.$[:alnum:]]* {
    yylval.identifier = new std::string(yytext);
    return IDENTIFIER;
}
%%
