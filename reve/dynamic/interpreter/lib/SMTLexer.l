%option noyywrap
%option prefix="smt"
%{
#include <iostream>
#include "Model.h"
#include "SMTParser.hpp"
extern "C" {
int smtlex(void);
}
using namespace std;
%}
%%
[ \t\n]         ;
\(              { return LPAR; }
\)              { return RPAR; }
=               { return EQ; }
-               { return MINUS; }
[0-9]+          { smtlval.constantVal = strtol(yytext, NULL, 10); return NUMBER; }
sat             { return SAT; }
unsat           { return UNSAT; }
model           { return MODEL; }
define-fun      { return DEFINE_FUN; }
as-array        { return AS_ARRAY; }
error           { return ERROR; }
ite             { return ITE; }
\"[^\"]*\"       { smtlval.str = new std::string(yytext,1,yyleng-2); return STRING; }
_               { return UNDERSCORE; }
Int             { return INT; }
Array           { return ARRAY; }
[a-zA-Z_!\.][a-zA-Z0-9$_!\.]*  { smtlval.str = new std::string(yytext); return IDENTIFIER; }
%%
