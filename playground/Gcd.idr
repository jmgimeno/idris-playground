-- https://github.com/edwinb/oplss-notes-2017/blob/master/Brady/code/Lecture2/total5-gcd.idr

module Gcd

import Control.WellFounded
import Data.Nat

gcdp : Nat -> Nat -> Nat
gcdp m Z = m
gcdp Z n = n
gcdp (S m) (S n)
    = if m > n then gcdp (minus m n) (S n)
               else gcdp (S m) (minus n m)

-- Ugh
minusSmaller_1 : (m, n : _) ->
                 LTE (S (plus (minus m n) (S n)))
                     (S (plus m (S n)))
minusSmaller_1 Z Z = LTESucc (LTESucc lteRefl)
minusSmaller_1 (S k) Z = LTESucc (LTESucc lteRefl)
minusSmaller_1 Z (S k) = LTESucc (LTESucc (LTESucc lteRefl))
minusSmaller_1 (S k) (S m)
     = lteSuccRight (rewrite sym (plusSuccRightSucc k (S m)) in
                     rewrite sym (plusSuccRightSucc (minus k m) (S m)) in
                    LTESucc (minusSmaller_1 _ _))

-- More ugh
minusSmaller_2 : (m, n : _) ->
                 LTE (S (S (plus m (minus n m))))
                     (S (plus m (S n)))
minusSmaller_2 Z Z = LTESucc (LTESucc LTEZero)
minusSmaller_2 Z (S k) = LTESucc (LTESucc (LTESucc lteRefl))
minusSmaller_2 (S k) Z
    = LTESucc (LTESucc (rewrite sym (plusSuccRightSucc k 0) in lteRefl))
minusSmaller_2 (S k) (S j)
    = rewrite sym (plusSuccRightSucc k (S j)) in
              lteSuccLeft (LTESucc (LTESucc (minusSmaller_2 _ _)))

gcdt : Nat -> Nat -> Nat
gcdt m n with (sizeAccessible (m + n))
  gcdt m Z | acc = m
  gcdt Z n | acc = n
  gcdt (S m) (S n) | (Access rec)
       = if m > n
            then gcdt (minus m n) (S n) | rec _ (minusSmaller_1 _ _)
            else gcdt (S m) (minus n m) | rec _ (minusSmaller_2 _ _)
