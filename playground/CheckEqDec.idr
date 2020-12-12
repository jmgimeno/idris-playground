-- Type-Driven Development - Section 8.3

module CheckEqDec

import Data.Vect
import Decidable.Equality

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNoZero : S k = 0 -> Void
succNoZero Refl impossible

noRec : (k = j -> Void) -> S k = S j -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc
checkEqNat (S k) 0 = No succNoZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Yes Refl  => Yes Refl
                              No contra => No $ noRec contra


exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case decEq m len of
                             Yes Refl  => Just input
                             No contra => Nothing

