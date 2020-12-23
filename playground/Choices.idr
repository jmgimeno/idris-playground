module Choices

import Data.Vect

choose : Nat -> Nat -> Nat
choose _ 0 = 1
choose 0 (S k) = 0
choose (S n) (S k) = choose n k + choose n (S k)

choices : (k: Nat) -> Vect n a -> Vect (choose n k) (Vect k a)
choices 0 _ = [[]]
choices (S n) [] = []
choices (S n) (x :: xs) = map (x::) (choices n xs) ++ choices (S n) xs
