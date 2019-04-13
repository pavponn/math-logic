module  MyData where

data Operation = Or | Impl | And deriving (Eq)

data Expression = Bin Operation Expression Expression 
                  | Not Expression
                  | Var String 
                  deriving (Eq)

data Type = Axiom Int | Assumption Int | ModusPonens Int Int

instance Show Operation where
 show And  = "&"
 show Or   = "|"
 show _    = "->"

instance Show Expression where
 show (Bin operation exp1 exp2) = "(" ++ show exp1 ++ " " ++ show operation ++ " " ++ show exp2 ++ ")"
 show (Not expression) = "!" ++ show expression
 show (Var variable) = variable


instance Ord Expression where
    compare exp1 exp2 = compare (show exp1) (show exp2)

instance Show Type where
     show (Axiom num) = "Ax. sch. " ++ show num
     show (Assumption num) = "Hypothesis " ++ show num
     show (ModusPonens i j) = "M.P. " ++ show i ++ ", " ++ show j