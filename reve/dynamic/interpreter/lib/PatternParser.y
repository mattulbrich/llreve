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
  ProgramIndex progIndex;
  unsigned long constantVal;
  size_t boundVarIndex;
}
%type <patternPtr> pattern binaryHeapPattern heapExprProp range
%type <exprPtr> expr binaryIntExpr
%token LPAR RPAR LBRACK RBRACK
%token <constantVal> NUMBER
%token SEMICOLON
%token PLACEHOLDER
%token DOT
%token COMMA
%token FORALL
%token EXISTS
%token <progIndex> HEAP
%token <boundVarIndex> BOUNDVAR
%token EQUALHEAPS
%left IMPL
%left OR
%left AND
%left LT LE GE GT EQ
%left PLUS MINUS
%left STAR
%%
stmts : /* empty */ {}
      | stmts pattern SEMICOLON {patterns.push_back(std::shared_ptr<HeapPattern<VariablePlaceholder>>($2)); }
;
pattern : binaryHeapPattern { $$ = $1; }
        | heapExprProp      { $$ = $1; }
        | LPAR pattern RPAR { $$ = $2; }
        | range { $$ = $1; }
        | EQUALHEAPS { $$ = new HeapEqual<VariablePlaceholder>(); }
;

range :
    LPAR FORALL BOUNDVAR DOT expr LE BOUNDVAR LE expr COMMA pattern RPAR
      { $$ = new RangeProp<VariablePlaceholder>(RangeQuantifier::All,
                       makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($5),
                                    std::shared_ptr<HeapExpr<VariablePlaceholder>>($9)),
                       $3,
                       std::shared_ptr<HeapPattern<VariablePlaceholder>>($11)); }
  | LPAR EXISTS BOUNDVAR DOT expr LE BOUNDVAR LE expr COMMA pattern RPAR
      { $$ = new RangeProp<VariablePlaceholder>(RangeQuantifier::Any,
                       makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($5),
                                    std::shared_ptr<HeapExpr<VariablePlaceholder>>($9)),
                       $3,
                       std::shared_ptr<HeapPattern<VariablePlaceholder>>($11)); }

binaryHeapPattern :
    pattern AND pattern
      { $$ = new BinaryHeapPattern<VariablePlaceholder>(BinaryBooleanOp::And,
                   makeMonoPair(std::shared_ptr<HeapPattern<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapPattern<VariablePlaceholder>>($3))); }
  | pattern OR pattern
      { $$ = new BinaryHeapPattern<VariablePlaceholder>(BinaryBooleanOp::Or,
                   makeMonoPair(std::shared_ptr<HeapPattern<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapPattern<VariablePlaceholder>>($3))); }
  | pattern IMPL pattern
      { $$ = new BinaryHeapPattern<VariablePlaceholder>(BinaryBooleanOp::Impl,
                   makeMonoPair(std::shared_ptr<HeapPattern<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapPattern<VariablePlaceholder>>($3))); }
;

heapExprProp :
    expr LT expr
    { $$ = new HeapExprProp<VariablePlaceholder>(BinaryIntProp::LT,
                 makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                              std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr LE expr
    { $$ = new HeapExprProp<VariablePlaceholder>(BinaryIntProp::LE,
                 makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                              std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr EQ expr
    { $$ = new HeapExprProp<VariablePlaceholder>(BinaryIntProp::EQ,
                 makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                              std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr GE expr
    { $$ = new HeapExprProp<VariablePlaceholder>(BinaryIntProp::GE,
                 makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                              std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr GT expr
    { $$ = new HeapExprProp<VariablePlaceholder>(BinaryIntProp::GT,
                 makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                              std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
;

expr : PLACEHOLDER { $$ = new Variable<VariablePlaceholder>(VariablePlaceholder()); }
     | HEAP LBRACK expr RBRACK { $$ = new HeapAccess<VariablePlaceholder>($1,
                                            std::shared_ptr<HeapExpr<VariablePlaceholder>>($3)); }
     | LPAR expr RPAR { $$ = $2; }
     | binaryIntExpr { $$ = $1; }
     | NUMBER { $$ = new Constant<VariablePlaceholder>(Integer(mpz_class($1))); }
     | BOUNDVAR { $$ = new Hole<VariablePlaceholder>($1); }
;
binaryIntExpr :
    expr STAR expr
      { $$ = new BinaryIntExpr<VariablePlaceholder>(BinaryIntOp::Mul,
                   makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr PLUS expr
      { $$ = new BinaryIntExpr<VariablePlaceholder>(BinaryIntOp::Add,
                   makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }
  | expr MINUS expr
      { $$ = new BinaryIntExpr<VariablePlaceholder>(BinaryIntOp::Subtract,
                   makeMonoPair(std::shared_ptr<HeapExpr<VariablePlaceholder>>($1),
                                std::shared_ptr<HeapExpr<VariablePlaceholder>>($3))); }

;
%%

std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>> parsePatterns(FILE* stream) {
    yyin = stream;
    yyparse();
    return std::move(patterns);
}
