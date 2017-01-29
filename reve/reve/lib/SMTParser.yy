%define parse.error verbose
%define parse.lac full
%define api.prefix {smt}
%{
#include <vector>
#include "SMT.h"
#include "Logging.h"

extern "C" int smtlex(void);

static smt::SharedSMTRef parsedExpr;
void smterror(const char* s) {
     std::cout << "error: " << s << "\n";
}
%}
%start ToplevelExpr
%union {
    smt::SMTExpr* smtExpr;
    unsigned long number;
    std::string* identifier;
    std::string* opName;
    std::string* sortName;
    std::vector<smt::SharedSMTRef>* exprList;
    std::vector<smt::SortedVar>* sortedVars;
    smt::SortedVar* sortedVar;
    smt::Type* type;
    std::string *heapName;
}
%type <smtExpr> Expr
%type <exprList> Exprs
%type <sortedVars> TypeList
%type <sortedVar> SortedVar
%type <type> Sort
%token LPAR RPAR TRUE FALSE FORALL INT
%token <number> NUMBER
%token <identifier> IDENTIFIER
%token <opName> OPNAME
%token <heapName> HEAP
%%
ToplevelExpr : Expr { parsedExpr = smt::SharedSMTRef($1); }
Expr : NUMBER { $$ = new smt::ConstantInt(llvm::APInt(32, $1)); }
     | TRUE { $$ = new smt::ConstantBool(true); }
     | FALSE { $$ = new smt::ConstantBool(false); }
     | HEAP { $$ = new smt::TypedVariable(*$1, smt::memoryType()); delete $1; }
     | IDENTIFIER {
         if (*$1 != "result$1" && *$1 != "result$2") {
           $$ = new smt::ConstantString(*$1 + "_0");
         } else {
           $$ = new smt::ConstantString(*$1);
         }
         delete $1;
       }
     | LPAR Expr RPAR { $$ = $2; }
     | LPAR OPNAME Exprs RPAR { $$ = new smt::Op(*$2, *$3); delete $2; delete $3; }
     | LPAR FORALL LPAR TypeList RPAR Expr RPAR { $$ = new smt::Forall(*$4, smt::SharedSMTRef($6)); delete $4; }
;
Exprs : Expr { $$ = new std::vector<smt::SharedSMTRef>({ smt::SharedSMTRef($1) }); }
      | Exprs Expr { $1->push_back(smt::SharedSMTRef($2)); $$ = $1; }
TypeList : SortedVar { $$ = new std::vector<smt::SortedVar>({ *$1 }); delete $1; }
         | TypeList SortedVar { $1->push_back(*$2); delete $2; $$ = $1; }
SortedVar : LPAR IDENTIFIER Sort RPAR { $$ = new smt::SortedVar(*$2 + "_0", std::unique_ptr<smt::Type>($3)); delete $2; }
Sort : INT { $$ = new smt::IntType(32); }
%%

smt::SharedSMTRef parseSMT(const std::string& input) {
    setSMTLexerInput(input.c_str());
    int result = smtparse();
    if (result != 0) {
        logError("Parse error\n");
        exit(1);
    }
    return std::move(parsedExpr);
}
