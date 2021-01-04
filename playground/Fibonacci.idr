module Fibonacci

import Data.Nat

-- original code on slack

fib : (n : Nat) -> Int
fib Z = 0
fib (S Z) = 1
fib (S (S k)) = fib k + fib (S k)

fibc : (n : Nat) -> Int
fibc n = loop n 0 1
  where
    loop : (n : Nat) -> (f0 : Int) -> (f1 : Int) -> Int
    loop Z     f0 _  = f0
    loop (S n) f0 f1 = loop n f1 (f0 + f1)

data Fib : Nat -> Int -> Type where
  Fib0 : Fib 0 0
  Fib1 : Fib 1 1
  FibN : {n : Nat} -> {r0, r1 : Int} -> Fib n r0 -> Fib (S n) r1 -> Fib (S (S n)) (r0 + r1)

fibCert : (n : Nat) -> (r : Int ** Fib n r)
fibCert 0         = (0 ** Fib0)
fibCert (S 0)     = (1 ** Fib1)
fibCert (S (S k)) =
  case (fibCert k , fibCert (S k)) of
    ((r0 ** p0) , (r1 ** p1)) => (r0 + r1 ** FibN p0 p1)

-- The question was: can be do a certified version of the loop solution?

{-
-- a pain to work with (due to minus) TODO?

loop' : {n : _ } -> (k : Nat) -> {f0 : _} -> Fib (n `minus` k) f0 -> {f1 : _} -> Fib (S (n `minus` k)) f1 -> (r ** Fib n r) 
loop' 0     p0 p1 = rewrite sym (minusZeroRight n) in MkDPair f0 p0
loop' (S k) p0 p1 = let p2 = FibN p0 p1 in ?loop'_rhs_2

-}

-- adding a new variable to be n_k = n - k => n_k + k = n

loop' : {n, f0, f1 : _} -> (k : Nat) -> (n_k : Nat) -> n_k + k = n -> Fib n_k f0 -> Fib (S n_k) f1 -> (r ** Fib n r)
loop' 0 n_k eq fib0 _ = rewrite sym eq in 
                        rewrite plusZeroRightNeutral n_k 
                        in (_ ** fib0)
loop' (S k) n_k eq fib0 fib1 = loop' k (S n_k) (trans (plusSuccRightSucc n_k k) eq) fib1 (FibN fib0 fib1)

fibcCert : (n : Nat) -> (r ** Fib n r)
fibcCert n = loop' n 0 Refl Fib0 Fib1

-- a simpler solution (also posted on the channel)

data Fib' : (prev, curr : Nat) -> Type where
Initial : Fib' 1 1
Next : Fib' p c -> Fib' c (c + p)

genFib : Nat -> (a ** b ** Fib' a b)
genFib 0 = (_ ** _ ** Initial)
genFib (S k) = let (p ** c ** f) = genFib k in (c ** c + p ** Next f)

