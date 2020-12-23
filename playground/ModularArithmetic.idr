-- https://blog.cofree.coffee/2020-12-22-finally-modular-arithmetic/

module ModularArithmetic

import Data.Fin
import Data.Vect

{-

data Fin : (n : Nat) -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)

index : Fin len -> Vect len elem -> elem
index FZ (x :: xs) = x
index (FS x) (y :: xs) = index x xs

weaken : Fin n -> Fin (S n)
weaken FZ = FZ
weaken (FS x) = FS (weaken x)

strengthen : {n : Nat} -> Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = 0} FZ = Left FZ
strengthen {n = 0} (FS _) impossible
strengthen {n = (S k)} FZ = Right FZ
strengthen {n = (S k)} (FS x) = case strengthen x of
                                     Left l => Left (FS l)
                                     Right r => Right (FS r)

-- return the largest element in a Fin
total
last : Fin (S n)
last {n = Z} = FZ
last {n = (S k)} = FS last
-}

{-
-- this version in the article does not pass totality check

add : {n: _} -> Fin n -> Fin n -> Fin n
add FZ y = y
add (FS x) y =
  case strengthen y of
    Left _ => add (weaken x) FZ
    Right y' => FS (add x y')

-}

-- addition modulo n (my version)

export total add' : {n : _} -> Fin n -> Fin n -> Fin n
add' FZ y = y
add' (FS x) y = case strengthen y of
                    Left _   => weaken x
                    Right y' => FS (add' x y')

-- recursion principles

total nat_rec : (r -> r) -> r -> Nat -> r
nat_rec f x 0 = x
nat_rec f x (S k) = nat_rec f (f x) k

total fin_rec : {n : _} -> (r -> r) -> r -> Fin n -> r
fin_rec {n = 0} f x y impossible
fin_rec {n = (S k)} f x FZ = x
fin_rec {n = (S k)} f x (FS y) = fin_rec f (f x) y

total inc : {n : _} -> Fin n -> Fin n
inc {n = 0} x impossible
inc {n = (S k)} x = case strengthen x of
                        Left l =>  FZ
                        Right r => FS r

total
add : {n : _} -> Fin n -> Fin n -> Fin n
add x y = fin_rec inc y x

total
mul : {n : Nat} -> Fin n -> Fin n -> Fin n
mul {n = Z} x y impossible
mul {n = (S k)} x y = fin_rec (add y) FZ x

total
decr : {n : Nat} -> Fin n -> Fin n
decr {n = 0} x impossible
decr {n = (S k)} FZ = last
decr {n = (S k)} (FS x) = weaken x

total
inv : {n : Nat} -> Fin n -> Fin n
inv {n = 0} x impossible
inv {n = (S k)} x = fin_rec decr FZ x
