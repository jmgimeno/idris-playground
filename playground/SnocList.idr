-- Type-Driven Development - section 10.2

module SnocList

import Data.List

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : {x, xs : _} -> (rec : SnocList xs) -> SnocList (xs ++ [x])

rewriteNil : SnocList input -> SnocList (input ++ [])
rewriteNil snoc = rewrite appendNilRightNeutral input in snoc

rewriteCons : SnocList ((input ++ [x]) ++ xs) -> SnocList (input ++ (x :: xs))
rewriteCons snoc = rewrite appendAssociative input [x] xs in snoc

snocListHelper : {input : _} -> (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelper snoc [] = rewriteNil snoc
snocListHelper snoc (x :: xs) = rewriteCons $ snocListHelper (Snoc snoc) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelper Empty xs

myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

total
myReverse : List a -> List a
myReverse input = myReverseHelper input (snocList input)

partial
myReverse' : List a -> List a
myReverse' xs with (snocList xs) -- but here we call snocList at every call !!!
  myReverse' [] | Empty = []
  myReverse' (xs ++ [x]) | (Snoc rec) = x :: myReverse' xs

total
myReverse'' : List a -> List a
myReverse'' input with (snocList input)
  myReverse'' [] | Empty = []
  myReverse'' (xs ++ [x]) | (Snoc rec) = x :: myReverse'' xs | rec -- we call bypassing with block

partial
isSuffix : Eq a => List a -> List a -> Bool 
isSuffix xs ys with (MkPair (snocList xs) (snocList ys))
  isSuffix [] ys | (Empty, y) = True
  isSuffix (xs ++ [x]) [] | ((Snoc xsrec), Empty) = False
  isSuffix (xs ++ [x]) (ys ++ [y]) | ((Snoc xsrec), (Snoc ysrec)) 
    = if x == y then isSuffix xs ys | (MkPair xsrec ysrec) else False


