%{
#include "HeapPattern.h"
static std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> patterns;
extern "C" int yylex(void);
extern FILE* yyin;
void yyerror(const char* s) {
     std::cerr << s << "\n";
}
%}
%start stmts
%union {
  HeapPattern<VariablePlaceholder>* patternPtr;
  HeapExpr<VariablePlaceholder>* exprPtr;
  BinaryBooleanOp boolBinop;
  BinaryIntProp intBinprop;
  ProgramIndex progIndex;
}
%type <patternPtr> pattern binaryHeapPattern heapExprProp
%type <exprPtr> expr
%token LPAR RPAR LBRACK RBRACK
%token NUMBER
%token <boolBinop> BINARYBOOLOP
%token <intBinprop> BINARYINTPROP
%token UNARYBOOLOP
%token PROPOP
%token SEMICOLON
%token PLACEHOLDER
%token <progIndex> HEAP
%left '='
%left '-' '+'
%left '*'
%%
stmts : /* empty */ {}
      | pattern SEMICOLON stmts {patterns.push_back(std::shared_ptr<HeapPattern<VariablePlaceholder>>($1)); }
;
pattern : binaryHeapPattern { $$ = $1; }
        | heapExprProp      { $$ = $1; }
        | LPAR pattern RPAR { $$ = $2; }
;

binaryHeapPattern : LPAR pattern BINARYBOOLOP pattern RPAR
  { $$ = new BinaryHeapPattern<VariablePlaceholder>($3,
               makeMonoPair(std::shared_ptr<HeapPattern<VariablePlaceholder>>($2),
                            std::shared_ptr<HeapPattern<VariablePlaceholder>>($4))); }
;

heapExprProp : expr BINARYINTPROP expr
  { $$ = new HeapExprProp<VariablePlaceholder>($2,
               makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                            std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
;

expr : PLACEHOLDER { $$ = new Variable<VariablePlaceholder>(VariablePlaceholder()); }
     | HEAP LBRACK expr RBRACK { $$ = new HeapAccess<VariablePlaceholder>($1,
                                            std::shared_ptr<HeapExpr<VariablePlaceholder>>($3)); }
     | LPAR expr RPAR { $$ = $2; }
;
%%

std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> parsePatterns(FILE* stream) {
    yyin = stream;
    yyparse();
    return std::move(patterns);
}
