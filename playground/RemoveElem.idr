-- Type-Driven Development - Section 9.1

module RemoveElem

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

-- as execise

removeElem1 : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Maybe (Vect n a)
removeElem1 value (x :: xs) 
  = case decEq value x of
      (Yes prf)   => Just xs
      (No contra) => case xs of
                        [] => Nothing
                        xs'@(_ :: _) => case removeElem1 value xs' of
                                             Nothing => Nothing
                                             Just ys => Just $ x :: ys

-- as exercise
removeElem2 : DecEq a => {n: _} -> (value : a) -> (xs : Vect n a) -> (len ** Vect len a)
removeElem2 value [] = MkDPair 0 []
removeElem2 value (x :: xs) = case decEq value x of
                                  Yes prf   => (_ ** xs)
                                  No contra => let (_ ** ys) = removeElem2 value xs in
                                                     (_ ** x :: ys)

--

removeElem : {n: _} -> (value : a) -> (xs : Vect (S n) a) -> (prf: Elem value xs) -> Vect n a
removeElem value (value :: xs) Here = xs
--removeElem {n = 0} value (_ :: []) (There later) = absurd later
removeElem {n = (S k)} value (x :: xs) (There later) = x :: removeElem value xs later

removeElem_auto : {n: _} -> (value : a) -> (xs : Vect (S n) a) -> {auto prf: Elem value xs} -> Vect n a
removeElem_auto value xs = removeElem value xs prf

removeElem' : {n: _} -> (value : a) -> (xs : Vect (S n) a) -> {auto prf: Elem value xs} -> Vect n a
removeElem' value (value :: xs) {prf = Here} = xs
removeElem' {n = (S k)} value (x :: xs) {prf = There later} = x :: removeElem' value xs


notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There later) impossible

notInTail : (notHere : value = x -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = case decEq value x of
                              Yes Refl   => Yes Here
                              No notHere => case isElem' value xs of
                                                Yes prf     => Yes $ There prf
                                                No notThere => No  $ notInTail notHere notThere

-- Exercise 1

data Elem' : a -> List a -> Type where
  Here : Elem' x (x :: xs)
  There : Elem' x xs -> Elem' x (y :: xs)

-- Exercise 2

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notLastInNil : Last [] value -> Void
notLastInNil LastOne impossible
notLastInNil (LastCons prf) impossible

notTheOne : (notOne : x = value -> Void) -> Last [x] value -> Void
notTheOne notOne LastOne = notOne Refl
notTheOne _ (LastCons LastOne) impossible
notTheOne _ (LastCons (LastCons prf)) impossible


notTheCons : (notCons : Last (y :: ys) value -> Void) -> Last (_ :: (y :: ys)) value -> Void
notTheCons notCons (LastCons prf) = notCons prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notLastInNil
isLast (x :: []) value = case decEq x value of
                              Yes Refl  => Yes LastOne
                              No notOne => No $ notTheOne notOne
isLast (_ :: y :: ys) value = case isLast (y :: ys) value of
                              Yes prf    => Yes $ LastCons prf
                              No notCons => No  $ notTheCons notCons

