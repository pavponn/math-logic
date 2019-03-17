{
module Parser where
import Lex
}

%name      parseExpression
%tokentype { Token }
%error     { parseError }


%token VAR  { TVar $$ }
%token OPENP  { TOpenB }
%token CLOSEP { TCloseB }
%token IMPL   { TImpl }
%token OR     { TOr }
%token AND    { TAnd }
%token NOT    { TNot }


%%

Expression
  : DisjExpr                     { $1 }
  | DisjExpr IMPL Expression     { Binary Impl $1 $3 }

DisjExpr
  : ConjExpr                        { $1 }
  | DisjExpr OR ConjExpr            { Binary Or $1 $3 }

ConjExpr
  : TermExpr                         { $1 }
  | ConjExpr AND TermExpr            { Binary And $1 $3 }

TermExpr
  : VAR                      { Var $1 }
  | NOT TermExpr             { Not $2 }
  | OPENP Expression CLOSEP  { $2 }


{

parseError =  fail "Parse error"

data Operation = Or | Impl | And deriving (Eq)

data Expression = Binary Operation Expression Expression | Not Expression | Var String deriving (Eq)


instance Show Operation where
 show And  = "&"
 show Or   = "|"
 show _    = "->"
 
instance Show Expression where
 show (Binary operation exp1 exp2) = "(" ++ show operation ++ "," ++ show exp1 ++ "," ++ show exp2 ++ ")"
 show (Not expression)                      = "(!" ++ show expression ++ ")"
 show (Var variable)               = variable


}
