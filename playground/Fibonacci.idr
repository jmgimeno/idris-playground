module Fibonacci

import Control.Algebra
import Data.DPair -- Subset(Element)
import Data.Nat   -- lemmas
import Data.Nat.Views
import Syntax.PreorderReasoning

-- problem proposed by @sverien
-- Fib n r = r is the fibonacci of n

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
-- a pain to work with (due to minus) and needs k <= n TODO?

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
-- it is not because the FibMat matrices are defined step-by-step via succ
-- TODO: can define fib to be the element at matriz (0, 1) and do it logarithmically

data Mat = MkMat Nat Nat Nat Nat

Semigroup Mat where
  (MkMat a b c d) <+> (MkMat a' b' c' d')
    = MkMat (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')

SemigroupV Mat where
  -- semigroupOpIsAssociative : (l, c, r : ty) -> l <+> (c <+> r) = (l <+> c) <+> r
  semigroupOpIsAssociative l c r = ?assoc
  
Monoid Mat where
  neutral = MkMat 1 0 0 1

neutral_lemma1 : (a : Nat) -> (b : Nat) -> a * 1 + b * 0 = a
neutral_lemma1 a b = Calc $
  |~ a * 1 + b * 0
  ~~ a + b * 0     ... ( cong (+(b * 0)) $ multOneRightNeutral a )
  ~~ a + 0         ... ( cong (a+) $ multZeroRightZero b )
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

data FibMat : (n : Nat) -> (m : Mat) -> Type where
  FibMatZ : FibMat Z (let z = neutral in z) 
  FibMatSucc : FibMat k m -> FibMat (S k) ((MkMat 0 1 1 1) <+> m)

(<*>) : FibMat i mi -> FibMat j mj -> FibMat (i + j) (mi <+> mj)
(<*>) FibMatZ y 
  = rewrite monoidNeutralIsNeutralR mj in 
    y 
(<*>) (FibMatSucc {m} x) y 
  = let xy = x <*> y in 
    let sxy = FibMatSucc xy in 
    rewrite sym $ semigroupOpIsAssociative (MkMat 0 1 1 1) m mj in
    sxy

mat : (n : Nat) -> (m : Mat ** FibMat n m)
mat n with (halfRec n)
  mat 0 | HalfRecZ 
    = MkDPair (MkMat 1 0 0 1) FibMatZ
  mat (plus k k) | (HalfRecEven k rec) 
    = let (_ ** fk) = (mat k | rec) in 
      (_ ** fk <*> fk)
  mat (S (k + k)) | (HalfRecOdd k rec) 
    = let (_ ** fk) = (mat k | rec) in
      (_ ** FibMatSucc (fk <*> fk))

fibl : (n : Nat) -> Nat
fibl n = let (MkMat _ r _ _ ** _) = mat n in r

lemma : {a, b, c, d : _} -> m = MkMat a b c d -> (x ** z ** (MkMat 0 1 1 1) <+> m = MkMat x d z (b + d))
lemma Refl = rewrite plusZeroRightNeutral b in
             rewrite plusZeroRightNeutral d in
             (_ ** _ ** Refl)

thm : {n : _ } -> FibMat n m -> (a ** b **c ** d ** (Fib n b, Fib (S n) d, m = MkMat a b c d))
thm FibMatZ = (_ ** _ ** _ ** _ ** (Fib0, Fib1, Refl))
thm (FibMatSucc x) = let (_ ** _ ** _ ** _ ** (fk', fsk', prf')) = thm x in 
                     let (_ ** _ ** prf) = lemma prf' in
                     (_ ** _ ** _ ** _ ** (fsk', FibN fk' fsk', prf))

fiblCert : (n : Nat) -> (r : Nat ** Fib n r)
fiblCert n = let (_ ** r ** _ ** _ ** (f, _, _)) = thm $ snd $ mat n in
                (r ** f)


