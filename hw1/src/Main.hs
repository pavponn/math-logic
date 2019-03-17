module Main where

import Lex 
import Parser


main = do
  contents <- getContents
  putStrLn $ show $ parseExpression $ alexScanTokens $ init $ lines contents
  
    

infixl 1 &
x & f = f x

