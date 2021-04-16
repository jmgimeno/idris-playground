module SumHomo

import Data.Nat 
import Syntax.PreorderReasoning

homoProof : (xs : List Nat) 
            -> (ys : List Nat) 
            -> sum (xs ++ ys) = sum xs + sum ys
homoProof [] ys = Refl
homoProof (x :: xs) ys = 
    rewrite homoProof xs ys in -- induction hypothesis
        rewrite plusAssociative x (sum xs) (sum ys) in 
            Refl

homoProof' : (xs : List Nat) 
             -> (ys : List Nat) 
             -> sum (xs ++ ys) = sum xs + sum ys

homoProof' [] ys = Calc $
    |~ sum ([] ++ ys)
    ~~ sum ys                  ...(Refl) -- ++ definition
    ~~ 0 + sum ys              ...(Refl) -- + definition 
    ~~ sum [] + sum ys         ...(Refl) -- sum definition

homoProof' (x' :: xs') ys = Calc $
    |~ sum ((x' :: xs') ++ ys)
    ~~ sum (x' :: xs' ++ ys)    ...(Refl) -- ++ definition
    ~~ x' + sum (xs' ++ ys)     ...(Refl) -- sum definition
    ~~ x' + (sum xs' + sum ys)  ...(cong2 (+) Refl (homoProof' _ _)) 
                                          -- x' is not modified
                                          -- inductive hypothesis
    ~~ (x' + sum xs') + sum ys  ...(plusAssociative _ _ _)
                                          -- associativity
    ~~ sum (x' :: xs') + sum ys ...(Refl) -- sum definition
