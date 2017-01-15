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
    std::vector<smt::SharedSMTRef>* exprList;
}
%type <smtExpr> Expr
%type <exprList> Exprs
%token LPAR RPAR TRUE FALSE
%token <number> NUMBER
%token <identifier> IDENTIFIER
%token <opName> OPNAME
%%
ToplevelExpr : Expr { parsedExpr = smt::SharedSMTRef($1); }
Expr : NUMBER { $$ = new smt::ConstantInt(llvm::APInt(32, $1)); }
     | TRUE { $$ = new smt::ConstantBool(true); }
     | FALSE { $$ = new smt::ConstantBool(false); }
     | IDENTIFIER { $$ = new smt::ConstantString(*$1); delete $1; }
     | LPAR Expr RPAR { $$ = $2; }
     | LPAR OPNAME Exprs RPAR { $$ = new smt::Op(*$2, *$3); delete $2; delete $3; }
;
Exprs : Expr { $$ = new std::vector<smt::SharedSMTRef>({ smt::SharedSMTRef($1) }); }
      | Exprs Expr { $1->push_back(smt::SharedSMTRef($2)); $$ = $1; }

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
