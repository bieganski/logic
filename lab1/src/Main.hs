{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Main where

import Control.Monad
import Data.List
import Test.QuickCheck
import Utils

-- Variable names are just strings
type VarName = String

-- having a specific instance for "show" removes the quotation marks when printing
instance {-# OVERLAPPING #-} Show VarName where
  show x = x

-- our inductive type for propositional formulas
data Formula = T | F | Var VarName | Not Formula | And Formula Formula | Or Formula Formula | Implies Formula Formula | Iff Formula Formula deriving (Eq)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

-- some examples of formulas
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
satisfiable_formulas = [p /\ q /\ s /\ p, T, p, Not p, (p \/ q /\ r) /\ (Not p \/ Not r), (p \/ q) /\ (Not p \/ Not q)]
unsatisfiable_formulas = [p /\ q /\ s /\ Not p, T /\ F, F, (p \/ q /\ r) /\ Not p /\ Not r, (p <--> q) /\ (q <--> r) /\ (r <--> s) /\ (s <--> Not p)]

-- formulas are shown with full parenthesisation
instance Show Formula where
  show T = "⊤"
  show F = "⊥"
  show (Var x) = x
  show (Not phi) = "(Not " ++ show phi ++ ")" -- ¬
  show (And phi psi) = "(" ++ show phi ++ " ∧ " ++ show psi ++ ")"
  show (Or phi psi) = "(" ++ show phi ++ " ∨ " ++ show psi ++ ")"
  show (Implies phi psi) = "(" ++ show phi ++ " → " ++ show psi ++ ")"
  show (Iff phi psi) = "(" ++ show phi ++ " ↔ " ++ show psi ++ ")"

-- generation of random formulas, used for testing
instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ (map Var ["p", "q", "r", "s", "t"]) ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f $ size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- finds all variables occurring in the formula (sorted, without duplicates)
variables :: Formula -> [VarName]
variables = rmdups . go where
  go T = []
  go F = []
  go (Var x) = [x]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

-- truth valuations
type Valuation = VarName -> Bool

-- the evaluation function (TODO)
eval :: Formula -> Valuation -> Bool
eval T rho = True
eval F rho = False
eval (Var x) rho = rho x
eval (Not phi) rho = undefined
eval (And phi psi) rho = undefined
eval (Or phi psi) rho = undefined
eval (Implies phi psi) rho = undefined
eval (Iff phi psi) rho = undefined

-- updating a truth valuation
extend :: Valuation -> VarName -> Bool -> Valuation
extend rho x v y
  | x == y = v
  | otherwise = rho y

helperTrue :: VarName -> [Valuation] -> [Valuation]
helperTrue x lst = map f lst where f = \fun -> \y -> if x == y then True else fun y

helperFalse :: VarName -> [Valuation] -> [Valuation]
helperFalse x lst = map f lst where f = \fun -> \y -> if x == y then False else fun y

-- the list of all valuations on a given list of variables (TODO)
valuations :: [VarName] -> [Valuation]
valuations [] = [\x -> error "undefined variable usage"]
valuations (x : xs) = let lst = valuations xs in (helperTrue x lst)++(helperFalse x lst)

-- check that all valuations are returned
prop_valuations :: [VarName] -> Property
prop_valuations xs = length xs <= 5 ==> length (valuations xs) == 2^length xs

-- satisfiability checker based on truth tables (TODO)
-- our first (trivial) sat solver
satisfiable :: Formula -> Bool
satisfiable phi = undefined

-- tautology checker based on truth tables (TODO)
tautology :: Formula -> Bool
tautology phi = undefined

-- =============== formula simpification

simplify :: Formula -> Formula

simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- Question: Find an example where deep_simplify is necessary to find the simplest formula

prop_simplify :: Formula -> Bool
prop_simplify phi = tautology $ Iff phi (simplify phi)

-- keep simplifying until no more simplifications are possible
deep_simplify :: Formula -> Formula
deep_simplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deep_simplify psi

prop_deep_simplify :: Formula -> Bool
prop_deep_simplify phi = tautology $ Iff phi (simplify phi)

-- ============ normal forms

-- negation normal form (negation is only applied to variables)
-- Question: What is complexity of this transformation in terms of formula size?
nnf :: Formula -> Formula
nnf = undefined

-- checks that the input is in nnf
is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Var _) = True
is_nnf (Not (Var _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False

prop_nnf :: Formula -> Bool
prop_nnf phi = let psi = nnf phi in is_nnf psi && (tautology $ Iff phi psi)

-- ================= literals, clauses, cnf, dnf

data Literal = Pos VarName | Neg VarName deriving (Eq, Show)

literal2var :: Literal -> VarName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

-- transform a formula to equivalent dnf (exponential)
dnf :: Formula -> [[Literal]]
dnf phi = go $ nnf phi where
  go T = undefined
  go F = undefined
  go (Var x) = undefined
  go (Not (Var x)) = undefined
  go (Or phi psi) = undefined
  go (And phi psi) = undefined

dnf2formula :: [[Literal]] -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos x) = Var x
  go2 (Neg x) = Not (Var x)

test_dnf :: Formula -> Bool
test_dnf phi = tautology (Iff phi (dnf2formula (dnf phi)))

-- ========= DNF SAT 

positive_literals :: [Literal] -> [VarName]
positive_literals ls = [ p | Pos p <- ls]

negative_literals :: [Literal] -> [VarName]
negative_literals ls = [ p | Neg p <- ls]

literals :: [Literal] -> [VarName]
literals ls = rmdups $ positive_literals ls ++ negative_literals ls

type SatSolver = Formula -> Bool

-- our second (still fairly trivial) sat solver
-- idea: compute the DNF and return "satisfiable" if it contains a satisfiable clause
-- Question: Considering that Haskell has a lazy evaluation strategy, what is the performance of "sat_dnf" vs. "satisfiable" (based on truth tables)?
-- Question: What is the performance of "sat_dnf" on unsatisfiable formulas?
sat_dnf :: SatSolver
sat_dnf = undefined

-- tests on random formulas
prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi

test_solver :: SatSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

-- tests on fixed formulas
prop_sat_dnf2 :: Bool
prop_sat_dnf2 = test_solver sat_dnf

-- the following is a hard unsatisfiable formula (obtained from ramsey 3 3 below)
-- 15 variables
x_1_2 = Var "x12"
x_1_3 = Var "x13"
x_1_4 = Var "x14"
x_1_5 = Var "x15"
x_1_6 = Var "x16"
x_2_3 = Var "x23"
x_2_4 = Var "x24"
x_2_5 = Var "x25"
x_2_6 = Var "x26"
x_3_4 = Var "x34"
x_3_5 = Var "x35"
x_3_6 = Var "x36"
x_4_5 = Var "x45"
x_4_6 = Var "x46"
x_5_6 = Var "x56"

-- try to run both sat_dnf and satisfiable and discuss their respective running times
hard_unsat_formula = (Not (((x_1_2 ∧ (x_1_3 ∧ x_2_3)) ∨ ((x_1_2 ∧ (x_1_4 ∧ x_2_4)) ∨ ((x_1_2 ∧ (x_1_5 ∧ x_2_5)) ∨ ((x_1_2 ∧ (x_1_6 ∧ x_2_6)) ∨ ((x_1_3 ∧ (x_1_4 ∧ x_3_4)) ∨ ((x_1_3 ∧ (x_1_5 ∧ x_3_5)) ∨ ((x_1_3 ∧ (x_1_6 ∧ x_3_6)) ∨ ((x_1_4 ∧ (x_1_5 ∧ x_4_5)) ∨ ((x_1_4 ∧ (x_1_6 ∧ x_4_6)) ∨ ((x_1_5 ∧ (x_1_6 ∧ x_5_6)) ∨ ((x_2_3 ∧ (x_2_4 ∧ x_3_4)) ∨ ((x_2_3 ∧ (x_2_5 ∧ x_3_5)) ∨ ((x_2_3 ∧ (x_2_6 ∧ x_3_6)) ∨ ((x_2_4 ∧ (x_2_5 ∧ x_4_5)) ∨ ((x_2_4 ∧ (x_2_6 ∧ x_4_6)) ∨ ((x_2_5 ∧ (x_2_6 ∧ x_5_6)) ∨ ((x_3_4 ∧ (x_3_5 ∧ x_4_5)) ∨ ((x_3_4 ∧ (x_3_6 ∧ x_4_6)) ∨ ((x_3_5 ∧ (x_3_6 ∧ x_5_6)) ∨ (x_4_5 ∧ (x_4_6 ∧ x_5_6))))))))))))))))))))) ∨ (((Not x_1_2) ∧ ((Not x_1_3) ∧ (Not x_2_3))) ∨ (((Not x_1_2) ∧ ((Not x_1_4) ∧ (Not x_2_4))) ∨ (((Not x_1_2) ∧ ((Not x_1_5) ∧ (Not x_2_5))) ∨ (((Not x_1_2) ∧ ((Not x_1_6) ∧ (Not x_2_6))) ∨ (((Not x_1_3) ∧ ((Not x_1_4) ∧ (Not x_3_4))) ∨ (((Not x_1_3) ∧ ((Not x_1_5) ∧ (Not x_3_5))) ∨ (((Not x_1_3) ∧ ((Not x_1_6) ∧ (Not x_3_6))) ∨ (((Not x_1_4) ∧ ((Not x_1_5) ∧ (Not x_4_5))) ∨ (((Not x_1_4) ∧ ((Not x_1_6) ∧ (Not x_4_6))) ∨ (((Not x_1_5) ∧ ((Not x_1_6) ∧ (Not x_5_6))) ∨ (((Not x_2_3) ∧ ((Not x_2_4) ∧ (Not x_3_4))) ∨ (((Not x_2_3) ∧ ((Not x_2_5) ∧ (Not x_3_5))) ∨ (((Not x_2_3) ∧ ((Not x_2_6) ∧ (Not x_3_6))) ∨ (((Not x_2_4) ∧ ((Not x_2_5) ∧ (Not x_4_5))) ∨ (((Not x_2_4) ∧ ((Not x_2_6) ∧ (Not x_4_6))) ∨ (((Not x_2_5) ∧ ((Not x_2_6) ∧ (Not x_5_6))) ∨ (((Not x_3_4) ∧ ((Not x_3_5) ∧ (Not x_4_5))) ∨ (((Not x_3_4) ∧ ((Not x_3_6) ∧ (Not x_4_6))) ∨ (((Not x_3_5) ∧ ((Not x_3_6) ∧ (Not x_5_6))) ∨ ((Not x_4_5) ∧ ((Not x_4_6) ∧ (Not x_5_6))))))))))))))))))))))))

-- =================
-- Example application of propositional SAT solving (BONUS):
-- compute the Ramsey numbers R(m, n)
-- m: size of clique
-- n: size of anticlique (independent set)
ramsey :: Int -> Int -> Int
ramsey m n = undefined

-- simple sanity checks on very small ramsey numbers
prop_ramsey1 :: Int -> Property
prop_ramsey1 n = n >= 1 ==> ramsey 1 n == 1 && ramsey n 1 == 1

prop_ramsey2 :: Int -> Property
prop_ramsey2 n = n >= 1 && n <= 20 ==> ramsey 2 n == n && ramsey n 2 == n

-- all those tests must pass
main = do 
  quickCheck prop_valuations
  quickCheck prop_simplify
  quickCheck prop_deep_simplify
  quickCheck prop_nnf
  quickCheck prop_distribute
  quickCheckWith (stdArgs {maxSize = 10}) test_dnf -- we need to limit the size of formulas with this one to avoid blowup
  quickCheckWith (stdArgs {maxSize = 17}) prop_sat_dnf
  quickCheck prop_sat_dnf2
  -- optional
  -- quickCheck prop_ramsey1
  -- quickCheck prop_ramsey2
