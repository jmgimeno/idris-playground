module EquationalReasoning

import Data.Nat
import Syntax.PreorderReasoning

-- example from slack by Ohad Kammad

skn_minus_n_eq_kn : {k, n : _} -> (1 + k) * n `minus` n = k * n
skn_minus_n_eq_kn = Calc $
  |~ ((1 + k) * n `minus` n)
  ~~ ((1 + k) * n `minus` (n + 0)) ...( cong (( 1 + k ) * n `minus`) $ sym $ plusZeroRightNeutral n )
  ~~ (n + k * n `minus` (n + 0))   ...( Refl )
  ~~ (k*n `minus` 0)               ...( plusMinusLeftCancel n (k * n) 0 )
  ~~ k * n                         ...( minusZeroRight (k * n) )
