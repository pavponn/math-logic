module Checker where
import MyData
import Data.Maybe
import qualified Data.Map.Strict as Map

printNewProof::[Expression] -> (Map.Map Expression Int) -> (Map.Map Expression Int) -> (Map.Map Expression [Expression]) -> IO() 
printNewProof [] _ _ _ = putStrLn ""

printNewProof !(expr : exprs) !assMap !proofedMap !implMap = do
  case (checkAxiomsAndAssumptions expr assMap) of
    Just _ -> do
      case (expr) of
        (Bin Impl a b) -> do
          let newImplMap = ($!) updateMap implMap b a 1
          let newProofedMap = ($!) Map.insert expr 1 proofedMap
          printProofForAssumtionsAndAxioms expr
          printNewProof exprs assMap newProofedMap newImplMap
        _ -> do
          let newProofedMap = ($!) Map.insert expr 1 proofedMap
          printProofForAssumtionsAndAxioms expr
          printNewProof exprs assMap newProofedMap implMap
    Nothing -> do
      case (checkLastAxiom expr) of
        Just _ -> do
          case (expr) of
            (Bin Impl a b) -> do
              let newImplMap = ($!) updateMap implMap b a 1
              let newProofedMap = ($!) Map.insert expr 1 proofedMap
              printProofForLastAxiom expr
              printNewProof exprs assMap newProofedMap newImplMap
            _ -> do
              let newProofedMap = ($!) Map.insert expr 1 proofedMap
              printProofForLastAxiom expr
              printNewProof exprs assMap newProofedMap implMap
        Nothing -> do
          case (checkIfPresent expr implMap) of
            Just x -> do
              case (findLeft proofedMap x) of
                Just y -> do
                  case (expr) of
                    (Bin Impl a b) -> do
                      let newImplMap = ($!) updateMap implMap b a 1
                      let newProofedMap = ($!) Map.insert expr 1 proofedMap
                      printProofForMP expr y
                      printNewProof exprs assMap newProofedMap newImplMap
                    _ -> do
                    let newProofedMap = ($!) Map.insert expr 1 proofedMap
                    printProofForMP expr y
                    printNewProof exprs assMap newProofedMap implMap
                Nothing -> putStrLn $  "WTF"
            Nothing -> putStrLn $ "WTF"

findLeft:: (Map.Map Expression Int) -> [Expression] -> Maybe Expression
findLeft _ [] = Nothing
findLeft !exprMap !(expr : exprs) = do
  case (Map.lookup expr exprMap) of
    Just _ -> Just expr
    Nothing -> findLeft exprMap exprs
    

updateMap implMap rightExp leftExp index = do
  case (Map.lookup rightExp implMap) of 
    Just x -> do
      ($!) Map.insert rightExp ( ($) (:) (leftExp) x) implMap
    Nothing -> do
      ($!) Map.insert rightExp [leftExp] implMap

checkAxiomsAndAssumptions expr assMap =  do
  case (checkAxioms expr) of
    Just x -> Just x
    Nothing -> do 
      case (checkIfPresent expr assMap) of
        Just x -> Just x
        Nothing -> Nothing


-- for assumptions
checkIfPresent expr myMap =  Map.lookup expr myMap

-- check 1 - 9 axioms
checkAxioms :: Expression -> Maybe Int
checkAxioms expr = 
    case expr of 
         (Bin Impl a1 (Bin Impl b1 a2)) 
           | a1 == a2 -> Just 1
         (Bin Impl (Bin Impl a1 b1) (Bin Impl (Bin Impl a2 (Bin Impl b2 c1)) (Bin Impl a3 c2)))  
           | a1 == a2 && a2 == a3 && b1 == b2 && c1 == c2 -> Just 2
         (Bin Impl a1 (Bin Impl b1 (Bin And a2 b2)))
           | a1 == a2 && b1 == b2 -> Just 3
         (Bin Impl (Bin And a1 b) a2) 
           | a1 == a2 -> Just 4
         (Bin Impl (Bin And a b1) b2)
           | b1 == b2 -> Just 5
         (Bin Impl a1 (Bin Or a2 b1))
           | a1 == a2 -> Just 6
         (Bin Impl b1 (Bin Or a1 b2))
           | b1 == b2 -> Just 7
         (Bin Impl (Bin Impl a1 c1) (Bin Impl (Bin Impl b1 c2) (Bin Impl (Bin Or a2 b2) c3)))
           | a1 == a2 && b1 == b2 && c1 == c2 && c2 == c3 -> Just 8
         (Bin Impl (Bin Impl a1 b1) (Bin Impl (Bin Impl a2 (Not b2)) (Not a3)))
           | a1 == a2 && a2 == a3 && b1 == b2 -> Just 9
         _ -> Nothing



-- check axiom 10
checkLastAxiom :: Expression -> Maybe Int
checkLastAxiom expr =
  case expr of
       (Bin Impl (Not (Not a1)) a2)
         | a1 == a2 -> Just 10
       _ -> Nothing


{-
1. A -> B -> A
2. (A -> B) -> (A -> B -> C) -> (A -> C)
3. A -> B -> A & B
4. A & B -> A
5. A & B -> B 
6. A -> A | B
7. B -> A | B
8. (A -> C) -> (B -> C) -> (A | B -> C)
9. (A -> B) -> (A -> !B) -> !A
10. !!A -> A
-}

printProofForAssumtionsAndAxioms a = do
  putStrLn $ show a
  putStrLn $ show (Bin Impl a (Bin Impl (Not a) a))
  putStrLn $ show (Bin Impl (Not a) a)
  putStrLn $ show (Bin Impl (Not a) (Bin Impl (Not a) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Bin Impl (Not a) (Not a))) (Bin Impl (Bin Impl (Not a) (Bin Impl (Bin Impl (Not a) (Not a)) (Not a))) (Bin Impl (Not a) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Bin Impl (Bin Impl (Not a) (Not a)) (Not a))) (Bin Impl (Not a) (Not a)))
  putStrLn $ show (Bin Impl (Not a) (Bin Impl (Bin Impl (Not a) (Not a)) (Not a)))
  putStrLn $ show (Bin Impl (Not a) (Not a))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) a) (Bin Impl (Bin Impl (Not a) (Not a)) (Not (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Not a)) (Not (Not a)))
  putStrLn $ show (Not (Not a))


printProofForLastAxiom (Bin Impl (Not (Not a)) a2) = do
  putStrLn $ show (Bin Impl a (Bin Impl (Not (Not a)) a))
  putStrLn $ show (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl a (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl a (Bin Impl (Not (Not a)) a)))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl a (Not (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))) (Not (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a)))) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))) (Not (Bin Impl (Not (Not a)) a)))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))) (Not (Bin Impl (Not (Not a)) a)))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a)))
  putStrLn $ show (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl a (Bin Impl (Not (Not a)) a))) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl a (Not (Bin Impl (Not (Not a)) a)))) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl a (Not (Bin Impl (Not (Not a)) a))) (Not a))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not a)))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not a))
  putStrLn $ show (Bin Impl (Not a) (Bin Impl (Not (Not a)) a))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not a) (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not a) (Bin Impl (Not (Not a)) a)))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not a)) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not a) (Bin Impl (Not (Not a)) a))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not a) (Bin Impl (Not (Not a)) a))) (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Not a)) a)))
  putStrLn $ show (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Not a)) a))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Bin Impl (Not (Not a)) a)) (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))) (Not (Not (Bin Impl (Not (Not a)) a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl (Not (Not a)) a)) (Not (Bin Impl (Not (Not a)) a))) (Not (Not (Bin Impl (Not (Not a)) a))))
  putStrLn $ show (Not (Not (Bin Impl (Not (Not a)) a)))

printProofForLastAxiom _ = putStrLn "Fail"

printProofForMP b a = do
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not b)))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl a (Not b)))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Not b) (Bin Impl (Not b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not b) (Bin Impl a (Not b))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Not b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not b))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not b)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b))))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))))
  putStrLn $ show (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a)))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl a (Not b)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl a (Not b))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a)))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Bin Impl a (Not b)) (Not a))) (Bin Impl (Bin Impl a b) (Not a)))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not a))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not a)))
  putStrLn $ show (Not (Not a))
  putStrLn $ show (Bin Impl (Not (Not a)) (Bin Impl (Not b) (Not (Not a))))
  putStrLn $ show (Bin Impl (Not b) (Not (Not a)))
  putStrLn $ show (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a)))) (Bin Impl (Not b) (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not (Not a))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not a))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not a)) (Bin Impl (Bin Impl a b) (Not (Not a))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not a)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not a))))
  putStrLn $ show (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Not b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not a))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not a)) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not a) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not a)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not a))) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b))))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Bin Impl (Not (Not a)) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))))
  putStrLn $ show (Not (Not (Bin Impl a b)))
  putStrLn $ show (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Not b) (Not (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Not b) (Not (Not (Bin Impl a b))))
  putStrLn $ show (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not (Not (Bin Impl a b)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))) (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))
  putStrLn $ show (Bin Impl (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b)))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Bin Impl a b)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))) (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b))))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b)))) (Bin Impl (Not b) (Not (Bin Impl a b)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Bin Impl (Bin Impl a b) (Not (Not (Bin Impl a b)))) (Not (Bin Impl a b)))) (Bin Impl (Not b) (Not (Bin Impl a b))))
  putStrLn $ show (Bin Impl (Not b) (Not (Bin Impl a b)))
  putStrLn $ show (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a))) (Bin Impl (Not b) (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not (Bin Impl a b))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))) (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Bin Impl a b)) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))) (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Not a))))
  putStrLn $ show (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Not a)))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not (Not (Bin Impl a b)))) (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Not a))) (Bin Impl (Not b) (Not a))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Bin Impl (Not (Not (Bin Impl a b))) (Not a))) (Bin Impl (Not b) (Not a)))
  putStrLn $ show (Bin Impl (Not b) (Not a))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not a)) (Bin Impl (Bin Impl (Not b) (Not (Not a))) (Not (Not b))))
  putStrLn $ show (Bin Impl (Bin Impl (Not b) (Not (Not a))) (Not (Not b)))
  putStrLn $ show (Not (Not b))
