{
module Lex where
import Numeric
}

%wrapper "basic"

$alpha = [A-Z]
$digit = [0-9]

tokens :-

  $white+                     ;
  "#".*                       ;
  "&"          { \_  -> TAnd }
  "|"          { \_  -> TOr }
  "->"         { \_  -> TImpl }
  "!"          { \_  -> TNot }
  "("          { \_  -> TOpenB }
  ")"          { \_  -> TCloseB }
  "|-"         { \_  -> TDeq }
  ","          { \_  -> TComma }
  $alpha[$alpha $digit \' \’]*    { \s ->TVar s }
 
{

data Token = 
  TVar String | TAnd | TOr | TImpl | TOpenB | TCloseB | TNot | TDeq | TComma | TEOF 
  deriving (Eq)

instance Show Token where
  show x = case x of
    TVar s -> s
    TAnd -> "&"
    TOr -> "|"
    TImpl -> "->"
    TOpenB -> "("
    TCloseB -> ")"
    TNot -> "!"
    TComma -> ","
    TDeq -> "|-"
    TEOF -> "(EOF)"

}
