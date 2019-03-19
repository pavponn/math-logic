module Main where

import Lex 
import Parser
import Checker
import Data.List 
import qualified Data.Map.Strict as Map
   
main = do 
  line <- getLine
  let (asspms, expr) = parseFirstLine $ alexScanTokens line

  let assMap = createMap Map.empty (reverse asspms) 1
  
  proof <- readProof
  let res = checkLast expr proof
  let (isOk, exprMap) = ($!) filterExpr assMap Map.empty Map.empty proof 1 expr
  case (isOk && res) of 
    True -> do
      let list = sortOn (fst . snd) (Map.toList  exprMap)
      let indMap = ($!) fillIndMap (Map.fromList [(Map.size exprMap, 0)]) (reverse list)
      let trueMap = ($!) mapIndexes indMap list 1 1
      let resultList = ($!) updateList trueMap [] list
      printFirstLine (reverse asspms) expr
      printProof resultList 1 
    False -> putStrLn "Proof is incorrect"

readProof = do
  contents <- getContents
  let proof = ($!)map (parseExpression . alexScanTokens) (filter  (/=[]) (lines contents))
  return proof

printProof [] _ = putStr ""
printProof (expWithType : others) n = do
  let curExp = fst expWithType
  let curType = snd expWithType
  putStrLn $ "[" ++ show n ++ ". " ++ show curType ++ "] " ++ show curExp
  printProof others (n + 1)

printFirstLine [] expr = putStrLn $ "|- " ++ show expr
printFirstLine (x : xs) expr = do
  putStr $ show x
  case (xs) of
    [] -> putStrLn $! " |- " ++ show expr
    _ -> do
      putStr ", " 
      printFirstLine xs expr

createMap resultMap [] _ = resultMap
createMap resultMap (x:xs) index = do
  case (Map.lookup x resultMap) of
    Just _ -> createMap resultMap xs (index + 1)
    _ -> do
      let newMap = Map.insert x index resultMap
      createMap newMap xs (index + 1)

checkLast _ [] = False
checkLast !expr [!x] = if (expr == x) then True else False
checkLast !expr !(x:xs) = checkLast expr xs
