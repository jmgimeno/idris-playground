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

lemma_sum_tail' : (l : List Nat) -> (y : Nat) -> sum_tail' l y = y + sum l
lemma_sum_tail' [] y = sym $ plusZeroRightNeutral y 
lemma_sum_tail' (x :: xs) y = rewrite plusAssociative y x (sum xs) in 
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

lemma_sum_cont' : (l : List Nat) -> (k : Nat -> Nat) -> sum_cont' l k = k (sum l)
lemma_sum_cont' [] k = Refl
lemma_sum_cont' (x :: xs) k = lemma_sum_cont' xs (\ans => k (x + ans)) 

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

lemma_rev_tail' : (l : List a) -> (acc : List a) -> rev_tail' l acc = rev l ++ acc
lemma_rev_tail' [] acc = Refl
lemma_rev_tail' (x :: xs) acc = rewrite sym $ appendAssociative (rev xs) [x] acc in 
                                        lemma_rev_tail' xs (x :: acc)

rev_tail_correct : (l : List a) -> rev_tail l = rev l
rev_tail_correct l = rewrite sym $ appendNilRightNeutral (rev l) in 
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

lemma_map_tail' : (f : a -> b) -> (l : List a) -> (acc : List b) -> map_tail' f l acc = rev acc ++ map f l
lemma_map_tail' f [] acc =  rewrite appendNilRightNeutral (rev acc) in 
                                    rev_tail_correct acc
lemma_map_tail' f (x :: xs) acc = rewrite lemma_map_tail' f xs (f x :: acc) in 
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



