module GeneralizingInductionHypothesis

-- Exercises on Generalizing the Induction Hypothesis by James Wilcox
-- https://jamesrwilcox.com/InductionExercises.html

import Data.List
import Data.Nat

-- 1 Summing lists

sum : (l : List Nat) -> Nat
sum [] = 0
sum (x :: xs) = x + sum xs

-- 1.1 Tail-recursive sum

sum_tail' : (l : List Nat) -> (acc : Nat) -> Nat
sum_tail' [] acc = acc
sum_tail' (x :: xs) acc = sum_tail' xs (x + acc)

sum_tail : (l : List Nat) -> Nat
sum_tail l = sum_tail' l 0

{-
sum_tail_correct : (l : List Nat) -> sum_tail l = sum l
sum_tail_correct [] = Refl
sum_tail_correct (x :: xs) = let iy = sum_tail_correct xs in ?sum_tail_correct_rhs_2
-}

lemma_sum_tail' : (l : List Nat) -> (y : Nat) 
                    -> sum_tail' l y = y + sum l
lemma_sum_tail' [] y 
  = sym $ plusZeroRightNeutral y 
lemma_sum_tail' (x :: xs) y 
  = rewrite plusAssociative y x (sum xs) in 
    rewrite plusCommutative x y in 
    lemma_sum_tail' xs (y + x)

sum_tail_correct : (l : List Nat) -> sum_tail l = sum l
sum_tail_correct l = lemma_sum_tail' l 0 

-- 1.2 Continuation-passing style sum

sum_cont' : (l : List Nat) -> (k : Nat -> a) -> a
sum_cont' [] k = k 0
sum_cont' (x :: xs) k = sum_cont' xs (\ans => k (x + ans))

sum_cont : (l : List Nat) -> Nat
sum_cont l = sum_cont' l id

{-
sum_cont_correct : (l : List Nat) -> sum_cont l = sum l
sum_cont_correct [] = Refl
sum_cont_correct (x :: xs) = ?sum_cont_correct_rhs_2
-}

lemma_sum_cont' : (l : List Nat) -> (k : Nat -> Nat) 
                    -> sum_cont' l k = k (sum l)
lemma_sum_cont' [] k 
  = Refl
lemma_sum_cont' (x :: xs) k 
  = lemma_sum_cont' xs (\ans => k (x + ans)) 

sum_cont_correct : (l : List Nat) -> sum_cont l = sum l
sum_cont_correct l = lemma_sum_cont' l id

-- 2 Manipulating lists with tail recursion

-- 2.1 Reverse

rev : (l : List a) -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

rev_tail' : (l : List a) -> (acc : List a) -> List a
rev_tail' [] acc = acc
rev_tail' (x :: xs) acc = rev_tail' xs (x :: acc)

rev_tail : (l : List a) -> List a
rev_tail l = rev_tail' l []

{-
rev_tail_correct : (l : List a) -> rev_tail l = rev l
rev_tail_correct [] = Refl
rev_tail_correct (x :: xs) = ?rev_tail_correct_rhs_2
-}

lemma_rev_tail' : (l : List a) -> (acc : List a) 
                    -> rev_tail' l acc = rev l ++ acc
lemma_rev_tail' [] acc 
  = Refl
lemma_rev_tail' (x :: xs) acc 
  = rewrite sym $ appendAssociative (rev xs) [x] acc in 
    lemma_rev_tail' xs (x :: acc)

rev_tail_correct : (l : List a) -> rev_tail l = rev l
rev_tail_correct l 
  = rewrite sym $ appendNilRightNeutral (rev l) in 
    lemma_rev_tail' l []

-- 2.2 Map

{-
map : (f : a -> b) -> (l : List a) -> List b
map f [] = []
map f (x :: xs) = f x : map f xs
-}

map_tail' : (f : a -> b) -> (l : List a) -> (acc : List b) -> List b
map_tail' f [] acc = rev_tail acc
map_tail' f (x :: xs) acc = map_tail' f xs (f x :: acc)

map_tail : (f : a -> b) -> (l : List a) -> List b
map_tail f l = map_tail' f l []

{-
map_tail_correct : (f : a -> b) -> (l : List a) -> map_tail f l = map f l
map_tail_correct f [] = Refl
map_tail_correct f (x :: xs) = ?map_tail_correct_rhs_2
-}

lemma_map_tail' : (f : a -> b) -> (l : List a) -> (acc : List b) 
                    -> map_tail' f l acc = rev acc ++ map f l
lemma_map_tail' f [] acc 
  = rewrite appendNilRightNeutral (rev acc) in 
    rev_tail_correct acc
lemma_map_tail' f (x :: xs) acc 
  = rewrite lemma_map_tail' f xs (f x :: acc) in 
    sym $ appendAssociative (rev acc) [f x] (map f xs) 

map_tail_correct : (f : a -> b) -> (l : List a) -> map_tail f l = map f l
map_tail_correct f l = lemma_map_tail' f l []

-- 3 Arithmetic expression languages

data Expr : Type where
  Const : Nat -> Expr
  Plus : Expr -> Expr -> Expr

eval_expr : Expr -> Nat
eval_expr (Const n) = n
eval_expr (Plus e1 e2) = eval_expr e1 + eval_expr e2

-- 3.1 Accumulator-based evaluator

-- NOTE: Not a tail-recursiv funcion in spite of the name

eval_expr_tail' : (e : Expr) -> (acc : Nat) -> Nat 
eval_expr_tail' (Const n) acc = n + acc
eval_expr_tail' (Plus e1 e2) acc = eval_expr_tail' e2 (eval_expr_tail' e1 acc)

eval_expr_tail : (e : Expr) -> Nat
eval_expr_tail e = eval_expr_tail' e 0

{-
eval_expr_tail_correct : (e : Expr) -> eval_expr_tail e = eval_expr e
eval_expr_tail_correct (Const n) = plusZeroRightNeutral n
eval_expr_tail_correct (Plus e1 e2) = ?eval_expr_tail_correct_rhs_2
-}

lemma_eval_expr_tail' : (e : Expr) -> (acc : Nat) 
                          -> eval_expr_tail' e acc = acc + eval_expr e
lemma_eval_expr_tail' (Const k) acc 
  = plusCommutative _ _
lemma_eval_expr_tail' (Plus e1 e2) acc 
  = rewrite lemma_eval_expr_tail' e2 (eval_expr_tail' e1 acc) in 
    rewrite lemma_eval_expr_tail' e1 acc in 
    sym $ plusAssociative _ _ _ 

eval_expr_tail_correct : (e : Expr) -> eval_expr_tail e = eval_expr e
eval_expr_tail_correct e = lemma_eval_expr_tail' e 0

-- 3.2 Continuation-passing style evaluator

eval_expr_cont' : (e : Expr) -> (k : Nat -> a) -> a
eval_expr_cont' (Const n) k = k n
eval_expr_cont' (Plus e1 e2) k = eval_expr_cont' e2 (\n2 =>
                                 eval_expr_cont' e1 (\n1 =>
                                 k (n1 + n2)))

eval_expr_cont : (e : Expr) -> Nat
eval_expr_cont e = eval_expr_cont' e id

{-
eval_expr_cont_correct : (e : Expr) -> eval_expr_cont e = eval_expr e
eval_expr_cont_correct (Const n) = Refl
eval_expr_cont_correct (Plus e1 e2) = ?eval_expr_cont_correct_rhs_2
-}

lemma_eval_expr_cont' : (e : Expr) -> (k : Nat -> Nat) 
                          -> eval_expr_cont' e k = k (eval_expr e)
lemma_eval_expr_cont' (Const n) k 
  = Refl
lemma_eval_expr_cont' (Plus e1 e2) k 
  = rewrite lemma_eval_expr_cont' e2 (\n2 => eval_expr_cont' e1 (\n1 => k (n1 + n2))) in
    lemma_eval_expr_cont' e1 (\n1 => k (n1 + (eval_expr e2))) 

eval_expr_cont_correct : (e : Expr) -> eval_expr_cont e = eval_expr e
eval_expr_cont_correct e = lemma_eval_expr_cont' e id

-- 3.3 Compiling arithmetic expressions to a stack language

data Instr : Type where
  Push : (n : Nat) -> Instr
  Add : Instr

Prog : Type
Prog = List Instr

Stack : Type
Stack = List Nat

run : (p : Prog) -> (s : Stack) -> Stack
run [] s = s
run (i :: p') s 
  = let s' = case i of
               Push n => n :: s
               Add    => case s of
                            a1 :: a2 :: s' => a1 + a2 :: s'
                            otherwise => s
    in run p' s'

compile : (e : Expr) -> Prog
compile (Const n) = [Push n]
compile (Plus e1 e2) = compile e1 ++ compile e2 ++ [Add]

compile_correct : run (compile e) [] = [eval_expr e]

-- TODO

-- 4 Efficient Fibonacci

fib : (n : Nat) -> Nat
fib 0 = 1
fib (S n') 
  = case n' of
      0 => 1
      (S n'') => fib n' + fib n''

fib_tail' : (n, a, b : Nat) -> Nat
fib_tail' 0 _ b = b
fib_tail' (S n') a b = fib_tail' n' (a + b) a

fib_tail : (n : Nat) -> Nat
fib_tail n = fib_tail' n 1 1

fib_tail_correct : (n : Nat) -> fib_tail n = fib n 
fib_tail_correct 0 = Refl
fib_tail_correct (S 0) = Refl
fib_tail_correct (S (S k)) = ?fib_tail_correct_rhs_4

-- TODO


