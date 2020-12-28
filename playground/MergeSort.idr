-- Type-Driven Development - section 10.2.4

import Data.List
import Data.List.Views
import Data.List.Views.Extra
import Data.Nat.Views
import Data.Vect

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | (SplitRecOne x) = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec) 
    = merge (mergeSort lefts | lrec) (mergeSort rights | rrec) 

-- Exercise 1

{-
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | (Snoc x zs rec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc x zs rec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc x zs rec) | (Snoc y xs z) 
      = if x == y then (equalSuffix zs xs | rec | z) ++ [x] else []
-}

partial
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (MkPair (snocList xs) (snocList ys)) 
  equalSuffix [] ys | (Empty, y) = []
  equalSuffix (xs ++ [x]) [] | ((Snoc x xs xsrec), Empty) = []
  equalSuffix (xs ++ [x]) (ys ++ [y]) | ((Snoc x xs xsrec), (Snoc y ys ysrec)) 
    = if x == y then (equalsSuffix xs ys | MkPair xsrec ysrec) ++ [x] else []

-- Exercise 2

-- It's supposed to use a view called SplitRec in Data.Vect.Views which do not exist

-- I'll need to study Data.List.View in order to adapt the views for vectors !!!

data SplitRec' : (xs : Vect n a) -> Type where
  SplitRecNil' : SplitRec' []
  SplitRecOne' : SplitRec' [x]
  SplitRecPair' : (lefts : Vect l a) -> 
                  (rights : Vect r a) -> 
                  (lrec : Lazy (SplitRec' lefts)) ->
                  (rrec : Lazy (SplitRec' rights)) ->
                  SplitRec' (lefts ++ rights)

splitRec' : (xs : Vect n a) -> SplitRec' xs

mergeSort' : Ord a => Vect n a -> Vect n a

-- Exercise 3

-- use HalfRec view in Data.Nat.Views
-- it is allowed to return "" for 0

toBinary : Nat -> String 
toBinary k with (halfRec k)
  toBinary 0 | HalfRecZ = ""
  toBinary (plus n n) | (HalfRecEven n rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd n rec) = (toBinary n | rec) ++ "1"

-- Exercise 4

-- use VList view from Data.List.Views.Extra

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec) = x == y && palindrome xs | rec

