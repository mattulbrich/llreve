%option noyywrap
%{
#include <iostream>
extern "C" {
int yylex(void);
}
using namespace std;
%}
%%
[ \t\n]         ;
\(               { cout << "Found a lpar:" << yytext << endl; }
\)               { cout << "Found a rpar:" << yytext << endl; }
[=]             { cout << "Found intpropop:" << yytext << endl; }
i_[0-9]+        { cout << "Found bound var:" << yytext << endl; }
heap\$(1|2)     { cout << "Found heap:" << yytext << endl; }
_               { cout << "Found var:" << yytext << endl; }
\[               { cout << "Found lbrack:" << yytext << endl; }
\]               { cout << "Found rbrack:" << yytext << endl; }
%%
