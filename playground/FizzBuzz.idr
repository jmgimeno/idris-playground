module FizzBuzz 

import Data.Nat

data Divides : Nat -> Nat -> Type where
  IsDivByN : (prf : mod m n = 0) -> Divides n m

prefix 10 @@

--to carry around proofs

(@@) : (t : a) -> (u : a ** t = u)
(@@) x = (x ** Refl)

divides : (divisor : Nat) -> (n : Nat) -> Maybe (Divides divisor n)
divides 0 n = Nothing --cant divide by 0 (if you chose 0 as one of the multiples)
divides (S divisor) n
  = case @@(mod n (S divisor)) of
      (0 ** prf) => Just (IsDivByN prf)
      _ => Nothing

parameters (fizzNum : Nat, buzzNum : Nat)

  data FizzBuzzView : Nat -> Type where
    Fizz : Divides fizzNum n -> FizzBuzzView n
    Buzz : Divides buzzNum n -> FizzBuzzView n
    FizzBuzz : Divides fizzNum n -> Divides buzzNum n -> FizzBuzzView n
    Neither : (n : Nat) -> FizzBuzzView n
  
  fizzBuzzView : (n : Nat) -> FizzBuzzView n
  fizzBuzzView n =
    case (divides fizzNum n, divides buzzNum n) of
       (Nothing, Nothing) => Neither n
       (Nothing, (Just x)) => Buzz x
       ((Just x), Nothing) => Fizz x
       ((Just x), (Just y)) => FizzBuzz x y
  
  fizzBuzz : (n : Nat) -> String
  fizzBuzz n with (fizzBuzzView n)
    fizzBuzz n | (Fizz _) = "fizz"
    fizzBuzz n | (Buzz _) = "buzz"
    fizzBuzz n | (FizzBuzz _ _) = "fizzbuzz"
    fizzBuzz n | (Neither n) = show n


