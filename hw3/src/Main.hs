module Main where

import Lex 
import Parser
import Checker
import MyData
import Data.List 
import System.IO
import qualified Data.Map.Strict as Map
   
main = do 
  line <- getLine
  let (asspms, expr) = parseFirstLine $ alexScanTokens line
  let newExpr = Not (Not expr)
  let reversedAsspms = ($!) reverse asspms
  let assMap = createMap Map.empty (reversedAsspms) 1
  proof <- readProof
  if (length proof < 1) then  putStrLn "NO PROOF" else do
    printFirstLine (reversedAsspms) newExpr
    printNewProof proof assMap Map.empty Map.empty

readProof = do
  contents <- getContents
  let proof = ($!)map (parseExpression . alexScanTokens) (filter  (/=[]) (lines contents))
  return proof

createMap resultMap [] _ = resultMap
createMap resultMap (x:xs) index = do
  case (Map.lookup x resultMap) of
    Just _ -> createMap resultMap xs (index + 1)
    _ -> do
      let newMap = Map.insert x index resultMap
      createMap newMap xs (index + 1)

printFirstLine [] expr = putStrLn $ "|- " ++ show expr
printFirstLine !(x : xs) !expr = do
  putStr $ show x
  case (xs) of
    [] -> putStrLn $! " |- " ++ show expr
    _ -> do
      putStr ", " 
      printFirstLine xs expr