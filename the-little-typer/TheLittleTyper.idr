
module TheLittleTyper

-- Chapter 2

which_nat : (target : Nat) -> (base : ty) -> (step : Nat -> ty) -> ty  
which_nat 0     base step = base
which_nat (S n) base step = step n 

--gauss : (n : Nat) -> Nat
--gauss n = which_nat n 0 (\ n_1 => S n_1 + gauss n_1)

Pear : Type
Pear = Pair Nat Nat

Pear_maker : Type
Pear_maker = Nat -> Nat -> Pear

elim_Pear : (pear : Pear) -> (maker : Pear_maker) -> Pear
elim_Pear pear maker = maker (fst pear) (snd pear)

pairwise_plus : (anjou : Pear) -> (bosc :Pear) -> Pear
pairwise_plus anjou bosc 
  = elim_Pear anjou
      (\a1, d1 => 
         elim_Pear bosc
           (\a2, d2 => 
              (a1 + a2, d1 + d2)))

-- Chapter 3

iter_nat : (target : Nat) -> (base : ty) -> (step : ty -> ty) -> ty
iter_nat 0     base step = base
iter_nat (S n) base step = step $ iter_nat n base step

step_plus : (plus_n_1 : Nat) -> Nat
step_plus plus_n_1 = S plus_n_1

plus' : (n : Nat) -> (j : Nat) -> Nat
plus' n j = iter_nat n j step_plus

rec_nat : (target : Nat) -> (base : ty) -> (step : Nat -> ty -> ty) -> ty
rec_nat 0     base step = base
rec_nat (S n) base step = step n $ rec_nat n base step

step_zerop : (n_1 : Nat) -> (zerop_n_1 : Bool) -> Bool
step_zerop _ _ = False

zerop : (n : Nat) -> Bool
zerop n = rec_nat n True step_zerop

step_gauss : (n_1 : Nat) -> (gauss_n_1 : Nat) -> Nat 
step_gauss n_1 gauss_n_1 = S n_1 `plus'` gauss_n_1

gauss : (n : Nat) -> Nat
gauss n = rec_nat n 0 step_gauss

make_step_mult : (j : Nat) -> (n_1 : Nat) -> (mult_n_1 : Nat) -> Nat
make_step_mult j _ mult_n_1 = j `plus'` mult_n_1

mult' : (n : Nat) -> (j : Nat) -> Nat
mult' n j = rec_nat n 0 (make_step_mult j)

-- Chapter 4

elim_Pair : (p : Pair a d) -> (f : a -> d -> ty) -> ty
elim_Pair p f = f (fst p) (snd p)

kar : (p : Pair Nat Nat) -> Nat
kar p = elim_Pair p (\a, _ => a)

kdr : (p : Pair Nat Nat) -> Nat
kdr p = elim_Pair p (\_, d => d)

Atom : Type
Atom = String

swap : (p : Pair Nat Atom) -> Pair Atom Nat
swap p = elim_Pair p (\a, d => MkPair d a)

flip : (p : Pair a d) -> Pair d a
flip p = MkPair (snd p) (fst p)

twin_Nat : (x : Nat) -> Pair Nat Nat
twin_Nat x = MkPair x x

twin_Atom : (x : Atom) -> Pair Atom Atom
twin_Atom x = MkPair x x

twin : (x : y) -> Pair y y
twin x = MkPair x x


