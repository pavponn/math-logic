module Checker where
import MyData
import Data.Maybe
import qualified Data.Map.Strict as Map

{- берем недоделанный список и делаем из него нормальный
-}
updateList _  newList []  = newList 

updateList mapOfInd newList (expWithType : others) = do
  let curExp = fst expWithType
  let curIndex = fst $ snd expWithType 
  let curType = snd $ snd expWithType
  case (checkIfIndex curIndex mapOfInd) of
    Just realIndex -> do
      case (curType) of 
        (ModusPonens x y) -> do
          let realX = fromMaybe 0 (Map.lookup x mapOfInd)
          let realY = fromMaybe 0 (Map.lookup y mapOfInd)
          let updNewList = ($!) (++) newList [(curExp, (ModusPonens realX realY))]
          updateList mapOfInd updNewList others
        _ -> do
          let updNewList = ($!) (++) newList [(curExp, curType)]
          updateList mapOfInd updNewList others
    Nothing -> updateList mapOfInd newList others


{- после расставления зависимостей мы мапим индексы в правильные 
-}

mapIndexes mapOfInd [] _ _ = mapOfInd

mapIndexes mapOfInd (x : xs) trueIndex simpleIndex = do
  case (checkIfIndex simpleIndex mapOfInd) of 
    Just _ -> do
      let newMap = ($!) Map.insert simpleIndex trueIndex mapOfInd
      mapIndexes newMap xs (trueIndex + 1) (simpleIndex + 1)
    Nothing -> mapIndexes mapOfInd xs trueIndex (simpleIndex + 1)



{- расставляем зависимости, которые нужны
-}
fillIndMap mapOfInd [] = mapOfInd

fillIndMap mapOfInd (exp : exps) = do
  let curIndex = fst $ snd exp
  let typeOfExpr = snd $ snd exp
  case (typeOfExpr) of
    (ModusPonens x y) -> do
      case (checkIfIndex curIndex mapOfInd) of
        Just _ -> do
          let updMap = Map.insert x 0 mapOfInd
          let newMap = ($!) Map.insert y 0 updMap
          fillIndMap newMap exps
        Nothing -> do
          fillIndMap mapOfInd exps
    _ -> fillIndMap mapOfInd exps


{- хотим отсеить все повторяющиеся, а также недоказанные выражения
 принимает:
 -мапу гипотез
 -мапу выражений
 -текущий список правильных выражений
 -список оставшихся для проверки выражений
 -текущий индекс "правильного выражения"
-}

filterExpr _ exprMap implMap [] _ _ = (False, exprMap)
filterExpr assMap exprMap implMap (exp : exps) index expr = 
  case (checkIfPresent exp exprMap) of
    Just _ -> do
      if (exp == expr) then (True, exprMap) 
        else ($!) filterExpr assMap exprMap implMap exps index expr
    Nothing -> do 
      case (checkAss exp assMap) of 
        Just x -> do
          let newMap = Map.insert exp (index, (Assumption x)) exprMap
          case (exp) of
            (Bin Impl a b) -> do
              let newImplMap = updateMap implMap b a index
              if (exp == expr) then checkKukarek newMap assMap newMap newImplMap exps (index + 1)
                else ($!) filterExpr assMap newMap newImplMap exps (index + 1) expr
            _ -> if (exp == expr) then checkKukarek newMap assMap newMap implMap exps (index + 1)
                   else ($!) filterExpr assMap newMap implMap exps (index + 1) expr
        Nothing -> do
          case (checkAxioms exp) of 
            Just x -> do
              let newMap = ($!) Map.insert exp (index, (Axiom x)) exprMap
              case exp of
                (Bin Impl a b) -> do
                  let newImplMap = updateMap implMap b a index
                  if (exp == expr) then checkKukarek newMap assMap newMap newImplMap exps (index + 1)
                    else ($!) filterExpr assMap newMap newImplMap exps (index + 1) expr
                _ -> if (exp == expr) then checkKukarek newMap assMap newMap implMap exps (index + 1)
                      else ($!) filterExpr assMap newMap implMap exps (index + 1) expr
            Nothing -> do
              case (checkIfPresentImpl exp implMap) of
                Just listForRight -> do
                  case (checkModusPonensNew exprMap listForRight) of
                    Just (index1, index2) -> do
                      let newMap = ($!) Map.insert exp (index, (ModusPonens index1 index2)) exprMap
                      case (exp) of 
                        (Bin Impl a b) -> do
                          let newImplMap = updateMap implMap b a index
                          if (exp == expr) then checkKukarek newMap assMap newMap newImplMap exps (index + 1)
                            else ($!) filterExpr assMap newMap newImplMap exps (index + 1) expr
                        _ -> if (exp == expr) then checkKukarek newMap assMap newMap implMap exps (index + 1)
                              else ($!) filterExpr assMap newMap implMap exps (index + 1) expr
                    Nothing -> (False, exprMap)
                Nothing -> (False, exprMap)

checkKukarek exprMapToReturn _ _ _ [] _ = (True, exprMapToReturn)

checkKukarek exprMapToReturn assMap exprMap implMap (exp : exps) index = 
  case (checkIfPresent exp exprMap) of
    Just _ -> checkKukarek exprMapToReturn assMap exprMap implMap exps index
    Nothing -> do
      case (checkAss exp assMap) of
        Just x -> do
          let newMap = ($!) Map.insert exp (index, (Assumption x)) exprMap
          case exp of
            (Bin Impl a b) -> do
              let newImplMap = updateMap implMap b a index
              checkKukarek exprMapToReturn assMap newMap newImplMap exps (index + 1)
            _ -> checkKukarek exprMapToReturn assMap newMap implMap exps (index + 1)
        Nothing -> do
          case (checkAxioms exp) of
           Just x -> do
             let newMap = ($!) Map.insert exp (index, (Axiom x)) exprMap
             case exp of
               (Bin Impl a b) -> do
                 let newImplMap = updateMap implMap b a index
                 checkKukarek exprMapToReturn assMap newMap newImplMap exps (index + 1)
               _ -> checkKukarek exprMapToReturn assMap newMap implMap exps (index + 1)
           Nothing -> do
             case (checkIfPresentImpl exp implMap) of
               Just listForRight -> do
                 case (checkModusPonensNew exprMap listForRight) of
                   Just (index1, index2) -> do
                     let newMap = ($!) Map.insert exp (index, (ModusPonens index1 index2)) exprMap
                     case exp of
                       (Bin Impl a b) -> do
                         let newImplMap = updateMap implMap b a index
                         checkKukarek exprMapToReturn assMap newMap newImplMap exps (index + 1)
                       _ -> checkKukarek exprMapToReturn assMap newMap implMap exps (index + 1)
                   Nothing -> (False, exprMapToReturn)
               Nothing -> (False, exprMapToReturn)


{-
 обновляет переданную ей мапу импликаций. Если  rightExp лежало в мапе, 
 дописываем в начало списка, иначе просто добавляем
-}

updateMap implMap rightExp leftExp index = do
  case (Map.lookup rightExp implMap) of 
    Just x -> do
      let newMap = ($!) Map.insert rightExp ( ($) (:) (leftExp, index) x) implMap
      newMap
    Nothing -> do
      let newMap  = ($!) Map.insert rightExp [(leftExp, index)] implMap
      newMap
      

{-
есть ли в мапе нужный индекс
-}
checkIfIndex ind myMap = Map.lookup ind myMap


{- есть ли в мапе доказанных утверждений, возвращает Nothing, если нет или 
Just ((index, Type)), если есть
-}
checkIfPresent expr myMap =  Map.lookup expr myMap
  

-- возвращает Nothing, если это не гипотеза, иначе возврашает Just (номер гипотезы)
checkAss expr assMap = Map.lookup expr assMap

--проверяет, было ли такое выражение как правая часть импликации

checkIfPresentImpl expr implMap = Map.lookup expr implMap

{- проверка M.P. новая, 
принимает мапу правильных высказываний, список левых частей для конкретной правой части 
-}

checkModusPonensNew _ [] = Nothing
checkModusPonensNew exprMap (exp : exps) = do
  let index = snd exp
  let curExp = fst exp
  case (Map.lookup curExp exprMap) of
    Just (indexL, _) -> Just (index, indexL)
    Nothing -> checkModusPonensNew exprMap exps


{- проверка на M.P.
 принимает:
 -выражение, которое надо. проверить на то, является ли оно результатом M.P
 -мапу доказанных выражений 
 -список выражений
 -индекс текущего выражения из списка
-}
checkModusPonens _ _ [] = Nothing 

checkModusPonens expr exprMap (exp : exps) = do
  let index = fst $ snd exp 
  case (fst exp) of 
    (Bin Impl a b) | b == expr -> do
      case (checkIfPresent a exprMap) of
        Just ((index2, _)) -> Just (index, index2)
        Nothing -> checkModusPonens expr exprMap exps 
    _ -> checkModusPonens expr exprMap exps 





-- проверка на аксиомы 

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


