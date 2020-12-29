module HalfRecView

import Control.WellFounded
import Data.Nat
import Data.Nat.Views

halfRec' : (n : Nat) -> HalfRec n
halfRec' 0 = HalfRecZ
halfRec' (S n) with (half n)
  halfRec' (S (S (k + k))) | (HalfOdd k) 
    = rewrite plusSuccRightSucc (S k) k in 
              HalfRecEven (S k) (halfRec' (S k)) 
  halfRec' (S (plus k k)) | (HalfEven k) 
    = HalfRecOdd k (halfRec' k)

-- We need the trickery from Control.WellFoundness to guarantee totality !!!

total
halfRec'' : (n : Nat) -> HalfRec n
halfRec'' n with (sizeAccessible n)
  halfRec'' 0 | acc = HalfRecZ
  halfRec'' (S n) | acc with (half n)
    halfRec'' (S (S (k + k))) | (Access rec) | (HalfOdd k) 
      = rewrite plusSuccRightSucc (S k) k in
                HalfRecEven (S k) (halfRec'' (S k) | rec (S k) (LTESucc (LTESucc (lteAddRight k))))
    halfRec'' (S (plus k k)) | (Access rec) | (HalfEven k) 
      = HalfRecOdd k (halfRec'' k | rec k (LTESucc (lteAddRight k)))

-- Proof that 0 is SizeAccessible

accZ : SizeAccessible Z
accZ = Access rec
  where
    rec : (y : Nat) -> LTE (S y) 0 -> Accessible Smaller y
    rec 0 LTEZero impossible
    rec 0 (LTESucc x) impossible
    rec (S _) LTEZero impossible
    rec (S _) (LTESucc x) impossible
