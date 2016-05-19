%option noyywrap
%{
#include <iostream>
#include "HeapPattern.h"
#include "PatternParser.hpp"
extern "C" {
int yylex(void);
}
using namespace std;
%}
%%
[ \t\n]         ;
\(              { return LPAR; }
\)              { return RPAR; }
\<              { return LE; }
\<=             { return LT; }
=               { return EQ; }
>=              { return GE; }
>               { return GT; }
i_[0-9]+        { yylval.boundVarIndex = strtoul(yytext+2, NULL, 10); return BOUNDVAR; }
heap\$(1|2)     { if (strcmp(yytext, "heap$1") == 0) {
                      yylval.progIndex = ProgramIndex::First;
                  } else {
                      yylval.progIndex = ProgramIndex::Second;
                  }
                  return HEAP;
                }
_               { return PLACEHOLDER; }
\[              { return LBRACK; }
\]              { return RBRACK; }
;               { return SEMICOLON; }
\+              { return PLUS; }
\*              { return STAR; }
\-              { return MINUS; }
∀               { return FORALL; }
∃               { return EXISTS; }
\.              { return DOT; }
,               { return COMMA; }
[0-9]+          { yylval.constantVal = strtoul(yytext, NULL, 10); return NUMBER; }
%%
