module VerifiedSum

import Control.Algebra
import Data.List
import Data.Nat
import Syntax.PreorderReasoning


namespace Naturals

  sum : List Nat -> Nat
  sum = foldr (+) 0

  data Sum : (s : Nat) -> (l : List Nat) -> Type where
    SNull : Sum 0 []
    SCons : {s : _} -> Sum s xs -> Sum (x + s) (x :: xs)

  thm : Sum s l -> s = sum l
  thm SNull = Refl
  thm (SCons rec) = let ih = thm rec in rewrite ih in Refl

  sumV : (l : List Nat) -> (s : Nat ** Sum s l)
  sumV [] = (_ ** SNull)
  sumV (x :: xs) = let (_ ** rec) = sumV xs in (_ ** SCons rec)

namespace Monoid -- thanks to @gallais for the multiple hints

  sum : Monoid a => List a -> a
  sum = foldr (<+>) neutral

  data Sum : Monoid a -> a -> List a -> Type where
    SNull : (mon : Monoid a) => Sum mon (neutral @{mon}) []
    SCons : (mon : Monoid a) => Sum mon s xs -> Sum mon (x <+> s) (x :: xs)

  thm : (mon : Monoid a) => Sum mon s l -> sum @{mon} l = s -- my solution
  thm SNull = Refl
  thm (SCons rec) = let ih = thm rec in rewrite ih in Refl

  thm' : (mon : Monoid a) => Sum mon s l -> sum @{mon} l = s -- gallais'
  thm' SNull = Refl
  thm' {l = x :: xs} (SCons p) = cong (x <+>) (thm' p)
  
  sumV : (mon : Monoid a) -> (l : List a) -> (s : a ** Sum mon s l)
  sumV mon [] = (_ ** SNull)
  sumV mon (x :: xs) = let (_ ** rec) = sumV mon xs in (_ ** SCons rec) 

namespace LeftFoldNaturals

  sum' : List Nat -> Nat
  sum' = foldl (+) 0

  data Sum : (s : Nat) -> (l : List Nat) -> Type where
    SNull : Sum 0 []
    SCons : {s : _} -> Sum s xs -> Sum (x + s) (x :: xs)

  lemma : {x, y : _} -> {xs : List Nat} -> x + (foldl (+) y xs) = foldl (+) (x + y) xs
  lemma {xs = []} = Refl 
  lemma {xs = z :: zs} = let ih = lemma {x=x} {y=y+z} {xs=zs} in 
                         rewrite ih in 
                         rewrite plusAssociative x y z in 
                         Refl

  thm : Sum s l -> s = sum' l
  thm SNull = Refl
  thm {l = x :: xs} (SCons rec) = let ih = thm rec in 
                                  rewrite ih in  
                                  rewrite lemma {x=x} {y=0} {xs=xs} in 
                                  rewrite plusZeroRightNeutral x in 
                                  Refl

namespace LeftFoldMonoid

  sum' : Monoid a => List a -> a
  sum' = foldl (<+>) neutral

  data Sum : Monoid a -> a -> List a -> Type where
    SNull : (mon : Monoid a) => Sum mon (neutral @{mon}) []
    SCons : (mon : Monoid a) => Sum mon s xs -> Sum mon (x <+> s) (x :: xs)

  it : a => a -- reifying a constraint?
  it @{a} = a
  
  theMonoid : MonoidV a => Monoid a 
  theMonoid = it

  theSemigroupV : MonoidV a => SemigroupV a
  theSemigroupV = it

  lemma : (mon : MonoidV a) -> {x, y : _} -> {xs : List a} -> x <+> (foldl (<+>) y xs) = foldl (<+>) (x <+> y) xs
  lemma mon {xs = []} = Refl
  lemma mon {xs = (z :: zs)} = let ih = lemma mon {x=x} {y=y<+>z} {xs=zs} in 
                               rewrite ih in    
                               rewrite semigroupOpIsAssociative @{theSemigroupV} x y z in
                               Refl

  thm : (mon : MonoidV a) -> {l: _} ->Sum (theMonoid @{mon}) s l -> s = sum' l
  thm mon SNull = Refl
  thm mon {l = x :: xs} (SCons rec) = let ih = thm mon rec in
                                      let lem = lemma mon {x=x} {y=(neutral @{theMonoid})} {xs=xs} in
                                      rewrite ih in
                                      --rewrite lem in -- It seems idris does not use the same <+> in different paths
                                      ?foo   

namespace EquationalReasoning

  data Sum : (0 a : Type) -> a -> (a -> a -> a) -> a -> List a -> Type where
     SNull : Sum a ne op ne []
     SCons : Sum a ne op s xs -> Sum a ne op (op x s) (x :: xs)
  
  0 thm : MonoidV a => Sum a Prelude.neutral (<+>) s l -> foldl (<+>) acc l = acc <+> s
  thm {acc} SNull = rewrite monoidNeutralIsNeutralL acc in Refl
  thm (SCons {s} {xs} {x} rec) = Calc $
    |~ foldl (<+>) acc (x :: xs)
    ~~ foldl (<+>) (acc <+> x) xs ...( Refl )
    ~~ (acc <+> x) <+> s          ...( thm rec )
    ~~ acc <+> (x <+> s)          ...( sym (semigroupOpIsAssociative acc x s) )

