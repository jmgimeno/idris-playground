-- Type-Driven Develoment - Section 8.2

module Vectors

import Data.Nat
import Data.Vect

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = let result = myReverse xs ++ [x] in
                                    rewrite plusCommutative 1 k in result


reverseProof : Vect (k + 1) elem -> Vect (S k) elem
reverseProof result = rewrite plusCommutative 1 k in result

myReverse' : Vect n elem -> Vect n elem
myReverse' [] = []
myReverse' (x :: xs) = reverseProof $ myReverse' xs ++ [x]


append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


append_nil : Vect m elem -> Vect (m + 0) elem
append_nil xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + k)) elem -> Vect (m + (S k)) elem
append_xs xs = rewrite sym (plusSuccRightSucc m k) in xs

append' : Vect n elem -> Vect m elem -> Vect (m + n) elem
append' [] ys = append_nil ys
append' (x :: xs) ys = append_xs $ x :: append' xs ys

-- Exercise 1

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes 0 m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in
                           rewrite plusSuccRightSucc m k in Refl

-- Exercise 2

reverseProof_nil : Vect n elem -> Vect (n + 0) elem
reverseProof_nil xs = rewrite plusZeroRightNeutral n in xs

reverseProof_xs : Vect (S (n + m)) elem -> Vect (n + (S m)) elem
reverseProof_xs xs = rewrite sym (plusSuccRightSucc n m) in xs

myReverse'' : Vect n elem -> Vect n elem
myReverse'' xs = go [] xs
where go : {n : Nat} -> Vect n elem -> Vect m elem -> Vect (n + m) elem
      go acc [] = reverseProof_nil acc
      go acc (x :: xs) = reverseProof_xs $ go (x :: acc) xs

