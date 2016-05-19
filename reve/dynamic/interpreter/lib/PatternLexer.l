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
[=]             { if (strcmp(yytext,"=") == 0) {
                      yylval.intBinprop = BinaryIntProp::EQ;
                  }
                  return BINARYINTPROP;
                }

i_[0-9]+        { cout << "Found bound var:" << yytext << endl; }
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
[\+\-\*]           { if (strcmp(yytext,"+") == 0) {
                      yylval.intBinop = BinaryIntOp::Add;
                  } else if (strcmp(yytext,"-") == 0) {
                      yylval.intBinop = BinaryIntOp::Subtract;
                  } else if (strcmp(yytext,"*") == 0) {
                      yylval.intBinop = BinaryIntOp::Mul;
                  }
                  return BINARYINTOP;
                }
%%
