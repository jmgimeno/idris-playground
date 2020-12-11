-- Type-Driven Develoment - Section 8.1

module EqNat

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : EqNat k j -> EqNat (S k) (S j)
sameS (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat 0 0 = Just $ Same 0
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just eq) => Just $ sameS eq

exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case checkEqNat m len of
                             Nothing => Nothing
                             (Just (Same m)) => Just input

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat' 0 0 = Just Refl
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               Nothing => Nothing
                               (Just prf) => Just $ cong S prf 

-- Exercise 1

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

-- Exercise 2

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

-- Exercise 3

data ThreeEq : a -> b -> c -> Type where
  Trio : a = b -> b = c -> ThreeEq a b c

data ThreeEq' : (num1 : Nat) -> (num2 : Nat) -> (num3 : Nat) -> Type where
  Trio' : (num1 : Nat) -> ThreeEq' num num num

-- official solution:

data ThreeEq'' : a -> b -> c -> Type where
   AllSame : ThreeEq'' x x x

-- Exercise 4

allSameS : ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS (Trio xy yz) = Trio (cong S xy) (cong S yz)

allSameaS' : ThreeEq' x y z -> ThreeEq' (S x) (S y) (S z)
allSameaS' (Trio' num) = Trio' (S num)

-- official solution:

allSameS''' : (x, y, z : Nat) -> ThreeEq'' x y z -> ThreeEq'' (S x) (S y) (S z)
allSameS''' x x x AllSame = AllSame
