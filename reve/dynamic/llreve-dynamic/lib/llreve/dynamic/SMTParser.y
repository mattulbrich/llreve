%define api.prefix {smt}
%define parse.error verbose
%{
#include "llreve/dynamic/Model.h"
#include <iostream>
static std::shared_ptr<Result> result;
extern "C" int smtlex(void);
extern FILE* smtin;
void smterror(const char* s) {
     std::cerr << s << "\n";
}
%}
%start result
%union {
  TopLevelExpr* topLevelPtr;
  SMTExpr* exprPtr;
  Result* resultPtr;
  long constantVal;
  Model* model;
  Type type;
  TypedArg* typedArg;
  std::vector<TypedArg>* argTypes;
  std::string* str;
}
%type <topLevelPtr> defineFun topLevel
%type <exprPtr> expr
%type <resultPtr> result sat unsat
%type <model> model;
%type <argTypes> argTypes;
%type <typedArg> typedArg;
%type <type> type;
%token ERROR
%token LPAR RPAR
%token EQ UNDERSCORE MINUS
%token <constantVal> NUMBER
%token <str>         STRING
%token <str>         IDENTIFIER
%token UNSAT SAT MODEL AS_ARRAY DEFINE_FUN
%token INT ARRAY
%token ITE
%%
result : sat { result = std::shared_ptr<Result>($1); }
       | unsat { result = std::shared_ptr<Result>($1); }

sat : SAT LPAR MODEL model RPAR { $$ = new Sat(*$4); delete $4; }

unsat : UNSAT error_ { $$ = new Unsat(); }

error_ : LPAR ERROR STRING RPAR {}

model : topLevel { $$ = new Model({std::shared_ptr<TopLevelExpr>($1)}); }
      | model topLevel { std::vector<std::shared_ptr<TopLevelExpr>> exprs = $1->exprs;
                         exprs.push_back(std::shared_ptr<TopLevelExpr>($2));
                         delete $1;
                         $$ = new Model(exprs);
                       }

topLevel : defineFun

defineFun : LPAR DEFINE_FUN IDENTIFIER LPAR argTypes RPAR type expr RPAR
               { $$ = new DefineFun(*$3, *$5, $7,
                                    std::shared_ptr<SMTExpr>($8));
                 delete $3;
                 delete $5;
               }

type : INT { $$ = Type::Int; }
     | LPAR ARRAY INT INT RPAR { $$ = Type::IntArray; }
argTypes : /* empty */ { $$ =  new std::vector<TypedArg>(); }
         | argTypes typedArg { $1->push_back(*$2); $$ = $1; delete $2; }

typedArg : LPAR IDENTIFIER type RPAR { $$ = new std::pair<std::string, Type>(*$2, $3); delete $2; }

expr : IDENTIFIER { $$ = new Identifier(*$1); delete $1; }
     | NUMBER { $$ = new Int($1); }
     | LPAR MINUS NUMBER RPAR { $$ = new Int(-$3); }
     | LPAR EQ expr expr RPAR { $$ = new Eq(std::shared_ptr<SMTExpr>($3),
                                            std::shared_ptr<SMTExpr>($4)); }
     | LPAR ITE expr expr expr RPAR
         { $$ = new struct ITE(std::shared_ptr<SMTExpr>($3),
                        std::shared_ptr<SMTExpr>($4),
                        std::shared_ptr<SMTExpr>($5)); }
     | LPAR UNDERSCORE AS_ARRAY IDENTIFIER RPAR
         { $$ = new AsArray(*$4); delete $4; }

%%

std::shared_ptr<Result> parseResult(FILE* stream) {
    smtin = stream;
    smtparse();
    return std::move(result);
}
