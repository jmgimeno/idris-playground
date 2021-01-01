-- Gentle Introduction to Dependent Types with Idris - chapter 5

module Gidti

import Data.Nat
import Data.Vect
import Decidable.Equality
import Syntax.WithProof

namespace Weekdays

  -- section 5.1

  data Weekday = Mon | Tue | Wed | Thu | Fri | Sat | Sun

  next_day : Weekday -> Weekday
  next_day Mon = Tue
  next_day Tue = Wed
  next_day Wed = Thu
  next_day Thu = Fri
  next_day Fri = Sat
  next_day Sat = Sun
  next_day Sun = Mon

  our_first_proof : next_day Mon = Tue
  our_first_proof = Refl

  is_it_monday : Weekday -> Bool
  is_it_monday Mon = True
  is_it_monday _   = False

  our_second_proof : (day : Weekday) -> day = Mon -> is_it_monday day = True
  our_second_proof day prf = rewrite prf in Refl

  extra_proof : (day : Weekday) -> Not (day = Mon) -> is_it_monday day = False
  extra_proof Mon f = absurd $ f Refl
  extra_proof Tue _ = Refl
  extra_proof Wed _ = Refl
  extra_proof Thu _ = Refl
  extra_proof Fri _ = Refl
  extra_proof Sat _ = Refl
  extra_proof Sun _ = Refl

  our_third_proof : Not (is_it_monday Tue = True)
  our_third_proof Refl impossible

namespace Maximun

  -- section 5.2.6

  total
  our_proof : (a : Nat) -> (b : Nat) -> LTE a b -> maximum a b = b
  our_proof 0 0 a_lte_b = Refl
  our_proof 0 (S k) a_lte_b = Refl
  --our_proof (S k) 0 a_lte_b impossible
  our_proof (S k) (S j) a_lte_b 
    = let fls = fromLteSucc a_lte_b in 
      let ih = our_proof k j fls in 
      rewrite ih in
      Refl

namespace ListOfEven

  -- section 5.2.7 

  total
  even : Nat -> Bool
  even 0 = True
  even (S k) = not (even k)

  total
  has_odd : List Nat -> Bool
  has_odd [] = False
  has_odd (x :: xs) = if even x then has_odd xs else True

  total
  even_members : List Nat -> List Nat
  even_members [] = []
  even_members (x :: xs) with (@@(even x))
    even_members (x :: xs) | (MkDPair True _) = x :: even_members xs
    even_members (x :: xs) | (MkDPair False _) = even_members xs

  total
  even_members_list_only_even : (l : List Nat) -> has_odd (even_members l) = False
  even_members_list_only_even [] = Refl
  even_members_list_only_even (x :: xs) with (@@(even x))
    even_members_list_only_even (x :: xs) | (MkDPair True even_x) 
      =  let ih = even_members_list_only_even xs in
         rewrite sym ih in 
         rewrite even_x in Refl
    even_members_list_only_even (x :: xs) | (MkDPair False _) 
      = even_members_list_only_even xs

namespace ListOfEven'

  total
  even : Nat -> Bool
  even 0 = True
  even (S k) = not (even k)

  total
  has_odd : List Nat -> Bool
  has_odd [] = False
  has_odd (x :: xs) = if (even x) then has_odd xs else True
  
  total
  even_members : List Nat -> List Nat
  even_members [] = []
  even_members (x :: xs) = if (even x) then x :: even_members xs else even_members xs
  
  total
  even_members_list_only_even : (l : List Nat) -> has_odd (even_members l) = False
  even_members_list_only_even [] = Refl
  even_members_list_only_even (x :: xs) with (@@(even x))
    even_members_list_only_even (x :: xs) | (MkDPair True even_x) 
      =  rewrite even_x in 
         rewrite even_x in 
         even_members_list_only_even xs
    even_members_list_only_even (x :: xs) | (MkDPair False odd_x) 
      = rewrite odd_x in
        even_members_list_only_even xs

namespace Poset

  -- section 5.2.8

  interface Porder (a : Type) (Order : a -> a -> Type) | Order where
    total proofR : {n : _} -> Order n n
    total proofT : {n, m, p : _} -> Order n m -> Order m p -> Order n p
    total proofA : {n, m : _ } -> Order n m -> Order m n -> n = m

  Porder Nat LTE where
    proofR {n = 0} = LTEZero
    proofR {n = (S k)} = LTESucc proofR

    proofT LTEZero _ = LTEZero
    proofT (LTESucc x) (LTESucc y) = LTESucc $ proofT x y

    proofA LTEZero LTEZero = Refl
    proofA (LTESucc x) (LTESucc y) = let IH = proofA x y in rewrite IH in Refl

namespace AllSame

  -- section 5.3

  allSame : Eq a => (xs : Vect n a) -> Bool
  allSame [] = True
  allSame (x :: []) = True
  allSame (x :: (y :: xs)) = x == y && allSame (y :: xs)

  data AllSame : (xs : Vect n a) -> Type where
    AllSameZero : AllSame []
    AllSameOne  : (x : _) -> AllSame [x]
    AllSameMany : Eq a => (x : a) -> (y : a) -> (ys : Vect _ a) -> 
                          (x == y) = True -> AllSame (y :: xs) -> 
                          AllSame (x :: y :: xs)

  mkAllSame : Eq a => (xs : Vect n a) -> Maybe (AllSame xs)
  mkAllSame [] = Just AllSameZero
  mkAllSame (x :: []) = Just $ AllSameOne x
  mkAllSame (x :: (y :: xs)) with (@@(x == y))
    mkAllSame (x :: (y :: xs)) | (MkDPair True x_equal_y) 
      = case mkAllSame (y :: xs) of
             Nothing => Nothing
             (Just y_same_xs) => Just $ AllSameMany x y xs x_equal_y y_same_xs
    mkAllSame (x :: (y :: xs)) | (MkDPair False not_equal) 
      = Nothing

  allSame' : Eq a => Vect n a -> Bool
  allSame' xs = case mkAllSame xs of
                     Nothing => False
                     (Just _) => True

namespace Trees

  -- section 5.4

  data Tree a = Leaf | Node (Tree a) a (Tree a)

  depth : Tree a -> Nat  
  depth Leaf = 0
  depth (Node l _ r) = 1 + maximum (depth l) (depth r)

  depth_tree_gte_0 : (tr : Tree a) -> GTE (depth tr) 0
  depth_tree_gte_0 Leaf = LTEZero
  depth_tree_gte_0 (Node l _ r) = LTEZero

  map_tree : (a -> b) -> Tree a -> Tree b
  map_tree _ Leaf = Leaf
  map_tree f (Node l x r) = Node (map_tree f l) (f x) (map_tree f r)

  size_tree : Tree a -> Nat
  size_tree Leaf = 0
  size_tree (Node l _ r) = 1 + size_tree l + size_tree r

  proof_1 : (tr : Tree a) -> (f : a -> b) -> size_tree tr = size_tree (map_tree f tr)  
  proof_1 Leaf f = Refl
  proof_1 (Node l _ r) f = let ih_l = proof_1 l f in
                           let ih_r = proof_1 r f in
                           rewrite ih_l in
                           rewrite ih_r in
                           Refl

namespace TypeChecker

  -- appendix A (translated from haskell)
  
  public export
  data Term = T
            | F
            | O
            | IfThenElse Term Term Term
            | Succ Term
            | Pred Term
            | IsZero Term
            | TVar String
            | Let String Term Term

  public export
  data Type' = TBool | TNat

  export
  Eq Type' where
    TBool == TBool = True
    TNat  == TNat  = True
    _     == _     = False

  export
  TyEnv : Type
  TyEnv = List (String, Type') -- Type env

  export
  TeEnv : Type
  TeEnv = List (String, Term)  -- Term env

  addType : String -> Type' -> TyEnv -> TyEnv
  addType v t env = (v, t) :: env

  getTypeFromEnv : TyEnv -> String -> Maybe Type'
  getTypeFromEnv [] _ = Nothing
  getTypeFromEnv ((v', t) :: env) v = if v' == v then Just t else getTypeFromEnv env v

  addTerm : String -> Term -> TeEnv -> TeEnv
  addTerm v t env = (v, t) :: env

  getTermFromEnv : TeEnv -> String -> Maybe Term
  getTermFromEnv [] _ = Nothing
  getTermFromEnv ((v', t) :: env) v = if v' == v then Just t else getTermFromEnv env v
  
  export
  eval : TeEnv -> Term -> Either String Term
  eval _   (IfThenElse T t _) = Right t
  eval _   (IfThenElse F _ e) = Right e
  eval env (IfThenElse c t e) = do c' <- eval env c
                                   pure $ IfThenElse c' t e
  eval env (Succ t) = do t' <- eval env t
                         pure $ Succ t'
  eval _   (Pred O) = Right O
  eval _   (Pred (Succ k)) = Right k
  eval env (Pred t) = do t' <- eval env t
                         pure $ Pred t'
  eval _   (IsZero O) = Right T
  eval _   (IsZero (Succ _)) = Right F
  eval env (IsZero t) = do t' <- eval env t
                           pure $ IsZero t'
  eval env (TVar v) = case getTermFromEnv env v of
                        Just t => Right t
                        _      => Left "No var found in env" 
  eval env (Let v t t') = do t'' <- eval env t
                             eval (addTerm v t'' env) t'
  eval _ _ = Left "No rule applies"

  export
  typeOf : TyEnv -> Term -> Either String Type'
  typeOf _   T = Right TBool
  typeOf _   F = Right TBool
  typeOf _   O = Right TNat
  typeOf env (IfThenElse c t e) 
    = case typeOf env c of
        Right TBool => let tt = typeOf env t
                           te = typeOf env e in
                         if tt == te then tt
                                     else Left "Types mismatch"
        _ => Left "Unsupported type for IfThenElse"
  typeOf env (Succ k) = case typeOf env k of
                          Right TNat => Right TNat
                          _          => Left "Unsupported type for Succ"
  typeOf env (Pred k) = case typeOf env k of
                          Right TNat => Right TNat
                          _          => Left "Unsupported type for Pred"
  typeOf env (IsZero k) = case typeOf env k of
                            Right TNat => Right TBool
                            _          => Left "Unsupported type for IsZero"
  typeOf env (TVar v) = case getTypeFromEnv env v of
                          Just t => Right t
                          _      => Left "No type found in env"
  typeOf env (Let v t t') = case typeOf env t of
                              Right t'' => typeOf (addType v t'' env) t'
                              _         => Left "Unsupported type for Let"                  
  
