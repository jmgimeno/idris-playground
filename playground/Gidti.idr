-- Gentle Introduction to Dependent Types with Idris - chapter 5

module Gidti

import Data.Nat
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


