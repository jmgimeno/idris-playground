-- Type-Driven Development - section 10.1

module DescribeList

import Data.List
import Data.Nat

describeList : Show a => List a -> String
describeList [] = "Empty"
describeList (x :: xs) = "non-empty, tail = " ++ show xs
describeList xs = ?describeList_rhs

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : Show a => (input : List a) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) 
  = "Non-empty, initial portion = " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

{-
describeListEnd : List a -> String
describeListEnd xs = describeHelper xs (listLast xs)
-}

describeListEnd : Show a => List a -> String
describeListEnd input with (listLast input)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (xs ++ [x]) | (NonEmpty xs x) 
    = "Non-empty, initial portion = " ++ show xs

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total 
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items) -- counters goes 2-by-2 
      = case splitListHelp counter items of
             SplitNil => SplitOne 
             SplitOne {x} => SplitPair [item] [x] 
             SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items -- items is half of the list

mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) 
    = merge (mergeSort lefts) (mergeSort rights)

-- Exercise 1

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : {rest : _} -> (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN 0 _ = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

-- Exercise 2

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

