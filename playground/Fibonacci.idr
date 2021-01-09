module Fibonacci

import Control.Algebra
import Data.DPair -- Subset(Element)
import Data.Nat   -- lemmas
import Data.Nat.Views
import Syntax.PreorderReasoning

-- problem proposed by @sverien
-- Fib n r = r is the fibonacci of n

-- TODO Use Int instead of Nat for the result

data Fib : (0 _ : Nat) -> Nat -> Type where
  Fib0 : Fib 0 0
  Fib1 : Fib 1 1
  FibN :  {0 n : Nat}
       -> {r0, r1 : Nat}
       -> (0 _ : Fib n r0) -> (0 _ : Fib (S n) r1)
       -> Fib (S (S n)) (r0 + r1)
 
-- recursive implementation

fib : (n : Nat) -> Nat
fib Z = 0
fib (S Z) = 1
fib (S (S k)) = fib k + fib (S k)

fibCert : (n : Nat) -> (r : Nat ** Fib n r)
fibCert 0         = (0 ** Fib0)
fibCert (S 0)     = (1 ** Fib1)
fibCert (S (S k)) =
  case (fibCert k , fibCert (S k)) of
    ((r0 ** p0) , (r1 ** p1)) => (r0 + r1 ** FibN p0 p1)

-- iterative implemetation (@sverien)

fibc : (n : Nat) -> Nat
fibc n = loop n 0 1
  where
    loop : (n : Nat) -> (f0 : Nat) -> (f1 : Nat) -> Nat
    loop Z     f0 _  = f0
    loop (S n) f0 f1 = loop n f1 (f0 + f1)

-- mine

fibcCert : (n : Nat) -> (r ** Fib n r)
fibcCert n = loop n 0 Refl Fib0 Fib1
  where -- adding a new variable to be n_k = n - k => n_k + k = n
    loop : {n, f0, f1 : _} -> (k : Nat) -> (n_k : Nat) -> n_k + k = n -> 
            Fib n_k f0 -> Fib (S n_k) f1 -> (r ** Fib n r)
    loop 0 n_k eq fib0 _ 
      = rewrite sym eq in 
        rewrite plusZeroRightNeutral n_k 
        in (_ ** fib0)
    loop (S k) n_k eq fib0 fib1 
      = loop k (S n_k) (trans (plusSuccRightSucc n_k k) eq) fib1 (FibN fib0 fib1)

-- @sverien's solution:

fibcCert' : (n : Nat) -> Nat
fibcCert' n = fst calc
  where
    loop : {r0, r1 : Nat} -> (i : Nat) -> (ni : Nat) -> Fib i r0 -> Fib (S i) r1 -> Subset Nat (Fib (ni + i))
    loop i Z     pf0 pf1 = (Element _ pf0)
    loop i (S k) pf0 pf1 = rewrite (plusSuccRightSucc k i) in loop (S i) k pf1 (FibN pf0 pf1)

    calc : Subset Nat (Fib n)
    calc = rewrite (sym (plusZeroRightNeutral n)) in loop 0 n Fib0 Fib1

{-
-- a pain to work with (due to minus) and needs k <= n 

-- TODO It can be interesting to work with it

loop' : {n : _ } -> (k : Nat) -> {f0 : _} -> 
        Fib (n `minus` k) f0 -> {f1 : _} -> Fib (S (n `minus` k)) f1 -> (r ** Fib n r) 
loop' 0     p0 p1 = rewrite sym (minusZeroRight n) in MkDPair f0 p0
loop' (S k) p0 p1 = let p2 = FibN p0 p1 in ?loop'_rhs_2
-}

-- a simpler NO solution working with pairs (and also posted on the channel by @Andre)
-- but as it pointed @gallais, as it drops the information about n, then a valid 
-- definition of genFib could be \ _ => (1 ** 1 ** Initial)

data Fib' : (prev, curr : Nat) -> Type where
  Initial : Fib' 1 1
  Next : Fib' p c -> Fib' c (c + p)

genFib : Nat -> (a ** b ** Fib' a b)
genFib 0 = (_ ** _ ** Initial)
genFib (S k) = let (p ** c ** f) = genFib k in (c ** c + p ** Next f)
    
-- a simpler solution from @Jake

fibJ : (n : Nat) -> (k ** Fib n k)
fibJ 0 = (0 ** Fib0)
fibJ (S 0) = (1 ** Fib1)
fibJ (S (S j)) = case fibJ (S j) of
                  (1 ** Fib1) => (1 ** FibN Fib0 Fib1)
                  (k + j ** (FibN x y)) => (j + (k + j) ** FibN y (FibN x y))

-- For more fibonacci proofs:
-- https://github.com/idris-lang/Idris2/blob/master/libs/contrib/Data/Nat/Fib.idr

-- a version with matrices aimed to a logarithmic solution

data Mat = MkMat Nat Nat Nat Nat

Semigroup Mat where
  (MkMat a b c d) <+> (MkMat a' b' c' d')
    = MkMat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')

-- TODO: Prove associativity (but it is not needed yet)

SemigroupV Mat where
  semigroupOpIsAssociative l c r = ?assoc
  
Monoid Mat where
  neutral = MkMat 1 0 0 1

neutral_lemma1 : (a : Nat) -> (b : Nat) -> a * 1 + b * 0 = a
neutral_lemma1 a b = Calc $
  |~ a * 1 + b * 0
  ~~ a + b * 0     ... ( cong (+ (b * 0)) $ multOneRightNeutral a )
  ~~ a + 0         ... ( cong (a +) $ multZeroRightZero b )
  ~~ a             ... ( plusZeroRightNeutral a )

neutral_lemma2 : (a : Nat) -> (b : Nat) -> a * 0 + b * 1 = b
neutral_lemma2 a b = Calc $
  |~ a * 0 + b * 1
  ~~ b * 1 + a * 0 ... ( plusCommutative (a * 0) (b * 1) ) 
  ~~ b             ... ( neutral_lemma1 b a ) 

MonoidV Mat where
  monoidNeutralIsNeutralL (MkMat a b c d) 
    = rewrite neutral_lemma1 a b in
      rewrite neutral_lemma2 a b in
      rewrite neutral_lemma1 c d in
      rewrite neutral_lemma2 c d in
      Refl 
    
  monoidNeutralIsNeutralR (MkMat a b c d) 
    = rewrite plusZeroRightNeutral a in
      rewrite plusZeroRightNeutral a in
      rewrite plusZeroRightNeutral b in
      rewrite plusZeroRightNeutral b in
      rewrite plusZeroRightNeutral c in
      rewrite plusZeroRightNeutral d in       
      Refl

data Exp : (m : Mat) -> (n : Nat) -> (r : Mat) -> Type where
  ExpZ    : Exp m Z (MkMat 1 0 0 1) 
  ExpEven : Exp m k r -> Exp m (k + k) (r <+> r)
  ExpOdd  : Exp m k r -> Exp m (S (k + k)) (m <+> (r <+> r))

exp : (m : Mat) -> (n : Nat) -> (r ** Exp m n r)
exp m n with (halfRec n)
  exp m 0 | HalfRecZ 
    = MkDPair (let z = neutral in z) ExpZ
  exp m (plus k k) | (HalfRecEven k rec) 
    = let (_ ** rk) = (exp m k | rec) in 
          (_ ** ExpEven rk)
  exp m (S (k + k)) | (HalfRecOdd k rec) 
    = let (_ ** rk) = (exp m k | rec) in
          (_ ** ExpOdd rk)

FibExp : (n : Nat) -> (r : Mat) -> Type
FibExp = Exp (MkMat 0 1 1 1)

-- We can compute the fibonacci via exp and we certify it by the property of the FibExp matrix

fiblCert : (n : Nat) -> (r **  FibExp n r)
fiblCert = exp (MkMat 0 1 1 1) 

-- I can link one step at a time Exp

step_exp : Exp m k r -> Exp m (S k) (m <+> r)
step_exp ExpZ        = ExpOdd ExpZ 
step_exp (ExpEven x) = ExpOdd x 
step_exp (ExpOdd x)  = step_exp $ ExpOdd x

-- I can link FibExp and Fib via existentials

step_fib : FibExp n (MkMat a b b c) -> FibExp (S n) (MkMat b c c (b + c))
step_fib ExpZ = ExpOdd ExpZ

fib_lemma : (n : Nat) -> 
            (a ** b ** c ** (FibExp (S n) (MkMat a b b c), 
                             Fib n a, Fib (S n) b, Fib (S (S n)) c))
fib_lemma 0 
  = (_ ** _ ** _ ** (ExpOdd ExpZ, Fib0, Fib1, FibN Fib0 Fib1))
fib_lemma (S k) 
  = let (a ** b ** c ** (fe, f, f1, f2)) = fib_lemma k in 
        (_ ** _ ** _ ** (step_fib fe, f1, f2, FibN f1 f2))
    
-- FibExp acts as a  "proof template" that transforms a pair of proofs of consecutive Fibs
-- into a pair of proofs n-steps ahead

fibexp_lemma : {a, b : _} -> FibExp n m -> Fib i a -> Fib (S i) b -> 
               (r0 ** r1 ** (Fib (i + n) r0, Fib (S (i + n)) r1))
fibexp_lemma ExpZ f0 f1 
  = rewrite plusZeroRightNeutral i in 
            (_ ** _ ** (f0, f1))
fibexp_lemma (ExpEven {k} x) f0 f1 
  = let (_ ** _ ** (f2, f3)) = fibexp_lemma x f0 f1
        (_ ** _ ** (f4, f5)) = fibexp_lemma x f2 f3 in
        rewrite plusAssociative i k k in
        (_ ** _ ** (f4, f5))
fibexp_lemma (ExpOdd {k} x) f0 f1 
  = let (_ ** _ ** (f2, f3)) = fibexp_lemma x f0 f1
        (_ ** _ ** (f4, f5)) = fibexp_lemma x f2 f3 in
        rewrite sym $ plusSuccRightSucc i (k + k) in 
        rewrite plusAssociative i k k in 
        (_ ** _ ** (f5, FibN f4 f5))

-- Does this work? 

fiblCert' : (n : Nat) -> (r ** Fib n r)
fiblCert' n = let (_ ** fe) = exp (MkMat 0 1 1 1) n
                  (r ** _ ** (f, _)) = fibexp_lemma fe Fib0 Fib1 in
                  (r ** f)

-- TODO TO BE CONTINUED ....

