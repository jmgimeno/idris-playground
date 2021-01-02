module VerifiedSum

import Control.Algebra
import Data.List

namespace Naturals

  sum : List Nat -> Nat
  sum = foldr (+) 0

  data Sum : (s : Nat) -> (l : List Nat) -> Type where
    SNull : Sum 0 []
    SCons : {s : _} -> Sum s xs -> Sum (x + s) (x :: xs)

  spec : (l : List Nat) -> (s : Nat) -> Sum s l -> s = sum l
  spec [] 0 SNull = Refl
  spec (x :: xs) (x + s) (SCons rec) = let ih = spec xs s rec in 
                                        rewrite sym ih in    
                                        Refl

  thm : Sum s l -> s = sum l
  thm SNull = Refl
  thm (SCons rec) = let ih = thm rec in rewrite ih in Refl

  sumP : (l : List Nat) -> (s : Nat ** Sum s l)
  sumP [] = (_ ** SNull)
  sumP (x :: xs) = let (_ ** rec) = sumP xs in (_ ** SCons rec)

namespace Monoid -- thanks to @gallais for the multiple hints

  sumM : Monoid a => List a -> a
  sumM = foldr (<+>) neutral

  data SumM : Monoid a -> a -> List a -> Type where
    SNullM : (mon : Monoid a) => SumM mon (neutral @{mon}) []
    SConsM : (mon : Monoid a) => SumM mon s xs -> SumM mon (x <+> s) (x :: xs)

  it : a => a -- reifying a constraint?
  it @{a} = a
  
  theMonoid : MonoidV a => Monoid a -- In this case I don't need it but it's a neat trick
  theMonoid = it

  thm : (mon : Monoid a) => SumM mon s l -> sumM @{mon} l = s -- my solution
  thm SNullM = Refl
  thm (SConsM rec) = let ih = thm rec in rewrite ih in Refl

  thm' : (mon : Monoid a) => SumM mon s l -> sumM @{mon} l = s -- gallais'
  thm' SNullM = Refl
  thm' {l = x :: xs} (SConsM p) = cong (x <+>) (thm' p)

