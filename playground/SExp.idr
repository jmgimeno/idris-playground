-- https://github.com/abailly/hsgames/blob/master/bautzen1945/idris/Bautzen/SExp.idr

module SExp

import Data.List
import Data.Nat
import Data.Vect
import Control.WellFounded


public export
data SExp : Type where
  SList : List SExp -> SExp
  SSym : String -> SExp
  SStr : String -> SExp
  SInt : Int -> SExp

||| Conversion utility from a type to a `SExp`
public export
interface ToSExp a where
  toSExp : a -> SExp

export
ToSExp SExp where
  toSExp = id

export
ToSExp Unit where
  toSExp () = SList []

export
ToSExp String where
  toSExp = SStr

export
ToSExp Int where
  toSExp = SInt

export
ToSExp Bool where
  toSExp True = SSym "t"
  toSExp False = SSym "nil"

export
ToSExp Integer where
  toSExp = SInt . fromInteger

export
ToSExp Nat where
  toSExp = SInt . cast

export
ToSExp (Fin n) where
  toSExp = SInt . fromInteger . cast

export
(ToSExp a, ToSExp b) => ToSExp (a, b) where
  toSExp (a, b) = SList [ toSExp a, toSExp b ]

export
ToSExp a => ToSExp (Maybe a) where
  toSExp Nothing = SSym "nil"
  toSExp (Just a) = toSExp a

export
ToSExp a => ToSExp (List a) where
  toSExp = SList . map toSExp

export
ToSExp a => ToSExp (Vect n a) where
  toSExp = toSExp . toList

export
(ToSExp a, ToSExp b) => ToSExp (Either a b) where
  toSExp (Left l) = SList [ SSym ":error", toSExp l ]
  toSExp (Right r) = SList [ SSym ":ok", toSExp r ]

export
Show SExp where
  show (SList xs) = "(" ++ showList xs ++ ")"
    where
      showList : List SExp -> String
      showList [] = ""
      showList [x] = show x
      showList (x :: xs) = show x ++ " " ++ showList xs
  show (SStr x)   = show x
  show (SSym x)   = ":" ++ x
  show (SInt x)   = show x

export
Eq SExp where
  (SList []) == (SList []) = True
  (SList (x :: xs)) == (SList (x' :: xs')) = x == x' && equal xs xs'
    where
      equal : List SExp -> List SExp -> Bool
      equal [] [] = True
      equal (x :: xs) (y :: ys) = x == y && equal xs ys
      equal _ _ = False

  (SStr x) == (SStr x') = x == x'
  (SSym x) == (SSym x') = x == x'
  (SInt x) == (SInt x') = x == x'
  _ == _ = True

---

Sized SExp where
  size (SList []) = 1
  size (SList (x :: xs)) = size x + size (SList xs)
  size (SSym x) = 1
  size (SStr x) = 1
  size (SInt x) = 1

oneLTESize : (s : SExp) -> LTE (S Z) (size s)
oneLTESize (SList []) = LTESucc LTEZero
oneLTESize (SList (x :: xs)) = let rec = oneLTESize x in 
                                   lteTransitive rec (lteAddRight _)
oneLTESize (SSym x) = LTESucc LTEZero
oneLTESize (SStr x) = LTESucc LTEZero
oneLTESize (SInt x) = LTESucc LTEZero

total 
lemma1 : (n : Nat) -> (m : Nat) -> LTE 1 m -> LTE (S n) (n + m) 
lemma1 n (S right) (LTESucc x) = rewrite plusCommutative n (S right) in 
                                   rewrite plusCommutative right n in 
                                      LTESucc (lteAddRight n)

total
lemma2 : (n : Nat) -> (m : Nat) -> LTE 1 m -> LTE (S n) (m + n) 
lemma2 n (S right) (LTESucc x) = rewrite plusCommutative right n in 
                                      LTESucc (lteAddRight n)

step : (x : SExp) -> ((y : SExp) -> LTE (S (size y)) (size x) -> Either String (List String)) -> Either String (List String)
step (SSym x) f = Left $ "Unexpected symbol "++ x ++ ", wanted a string"
step (SStr x) f = Right [x]
step (SInt x) f = Left $ "Unexpected int "++ show x ++ ", wanted a string"
step (SList []) f = Right []
step (SList (x :: xs)) f = do s <- f x $ lemma1 _ _ (oneLTESize (SList xs))
                              ss <- f (SList xs) $ lemma2 _ _ (oneLTESize x)
                              Right $ s ++ ss

toStrings : SExp -> Either String (List String)
toStrings sexpr = sizeRec step sexpr

