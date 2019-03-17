{
module Parser where
import Lex
import MyData
}


%tokentype { Token }
%name      parseExpression Expr
%name      parseFirstLine FstLine
%error     { parseError }


%token VAR  { TVar $$ }
%token OPENP  { TOpenB }
%token CLOSEP { TCloseB }
%token IMPL   { TImpl }
%token OR     { TOr }
%token AND    { TAnd }
%token NOT    { TNot }
%token DEQ    { TDeq }
%token COMMA  { TComma }


%%

FstLine
  : Exprs DEQ Expr          { ($1, $3) }
  | DEQ Expr                { ([], $2) }

Exprs
  : Expr                    { [$1] }
  | Exprs COMMA Expr        { $3 : $1 }

Expr
  : DisjExpr                { $1 }
  | DisjExpr IMPL Expr      { Bin Impl $1 $3 }

DisjExpr
  : ConjExpr                { $1 }
  | DisjExpr OR ConjExpr    { Bin Or $1 $3 }

ConjExpr
  : TermExpr                { $1 }
  | ConjExpr AND TermExpr   { Bin And $1 $3 }

TermExpr
  : VAR                     { Var $1 }
  | NOT TermExpr            { Not $2 }
  | OPENP Expr CLOSEP       { $2 }


{

parseError =  error "Parse error"

}
