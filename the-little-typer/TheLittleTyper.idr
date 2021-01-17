
module TheLittleTyper

import Data.Vect

-- Chapter 2

which_Nat : (target : Nat) -> (base : ty) -> (step : Nat -> ty) -> ty  
which_Nat 0     base step = base
which_Nat (S n) base step = step n 

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

iter_Nat : (target : Nat) -> (base : ty) -> (step : ty -> ty) -> ty
iter_Nat 0     base step = base
iter_Nat (S n) base step = step $ iter_Nat n base step

step_plus : (plus_n_1 : Nat) -> Nat
step_plus plus_n_1 = S plus_n_1

plus' : (n : Nat) -> (j : Nat) -> Nat
plus' n j = iter_Nat n j step_plus

rec_Nat : (target : Nat) -> (base : ty) -> (step : Nat -> ty -> ty) -> ty
rec_Nat 0     base step = base
rec_Nat (S n) base step = step n $ rec_Nat n base step

step_zerop : (n_1 : Nat) -> (zerop_n_1 : Bool) -> Bool
step_zerop _ _ = False

zerop : (n : Nat) -> Bool
zerop n = rec_Nat n True step_zerop

step_gauss : (n_1 : Nat) -> (gauss_n_1 : Nat) -> Nat 
step_gauss n_1 gauss_n_1 = S n_1 `plus'` gauss_n_1

gauss : (n : Nat) -> Nat
gauss n = rec_Nat n 0 step_gauss

make_step_mult : (j : Nat) -> (n_1 : Nat) -> (mult_n_1 : Nat) -> Nat
make_step_mult j _ mult_n_1 = j `plus'` mult_n_1

mult' : (n : Nat) -> (j : Nat) -> Nat
mult' n j = rec_Nat n 0 (make_step_mult j)

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

-- Chapter 5

rugbrod : List Atom
rugbrod = "rye-flour" :: "rye-kernels" :: "water" :: "sourdough" :: "salt" :: Nil

toppings : List Atom
toppings = "potato" :: "butter" :: Nil

condiments : List Atom
condiments = "chives" :: "mayonnaise" :: Nil

rec_List : (target : List ty) -> (base : x) -> (step : ty -> List ty -> x -> x) -> x
rec_List []        base step = base
rec_List (e :: es) base step = step e es $ rec_List es base step

step_length : (e : ty) -> (es : List ty) -> (length_es : Nat) -> Nat
step_length _ _ length_es = S length_es

length' : (es : List ty) -> Nat
length' es = rec_List es 0 step_length

step_append : (e : ty) -> (es : List ty) -> (append_es : List ty) -> List ty
step_append e _ append_es = e :: append_es

append : (start : List ty) -> (end : List ty) -> List ty
append start end = rec_List start end step_append

snoc : (start : List ty) -> (e : ty) -> List ty
snoc start e = rec_List start (e :: Nil) step_append

step_concat : (e : ty) -> (es : List ty) -> (concat_es : List ty) -> List ty
step_concat e _ concat_es = snoc concat_es e

concat' : (start : List ty) -> (end : List ty) -> List ty
concat' start end = rec_List end start step_concat

step_reverse : (e : ty) -> (es : List ty) -> (reverse_es : List ty) -> List ty
step_reverse e _ reverse_es = snoc reverse_es e

reverse' : (es : List ty) -> List ty
reverse' es = rec_List es Nil step_reverse

kartoffelmad : List Atom
kartoffelmad = append (concat' condiments toppings) (reverse' ("plate" :: "rye-bread" :: Nil))

-- Chapter 6

first_of_one : (es : Vect 1 ty) -> ty
first_of_one es = head es

first_of_two : (es : Vect 2 ty) -> ty
first_of_two es = head es

first : (es : Vect (S l) ty) -> ty
first es = head es

rest : (es : Vect (S l) ty) -> Vect l ty
rest es = tail es

-- Chapter 7

ind_Nat : (target : Nat) -> 
          (mot : Nat -> Type) -> 
          (base : mot 0) -> 
          (step : (n_1 : Nat) -> mot n_1 -> mot (S n_1)) 
          -> mot target
ind_Nat 0     mot base step = base
ind_Nat (S n) mot base step = step n $ ind_Nat n mot base step

mot_peas : (k : Nat) -> Type
mot_peas k = Vect k Atom 

step_peas : (l_1 : Nat) -> (peas_l_1 : mot_peas l_1) -> mot_peas (S l_1)
step_peas l_1 peas_l_1 = "pea" :: peas_l_1

peas : (how_many_peas : Nat) -> Vect how_many_peas Atom 
peas how_many_peas = ind_Nat how_many_peas mot_peas Nil step_peas

also_rec_Nat : {ty : Type} -> (target : Nat) -> (base : ty) -> (step : Nat -> ty -> ty) -> ty
also_rec_Nat target base step = ind_Nat target (\_ => ty) base step

mot_last : (ty : Type) -> (k : Nat) -> Type
mot_last ty k = Vect (S k) ty -> ty

base_last : (es : Vect (S 0) ty) -> ty
base_last es = head es

step_last : (l_1 : Nat) -> (last_l_1 : mot_last ty l_1) -> mot_last ty (S l_1)
step_last l_1 last_l_1 = \es => last_l_1 (tail es)

last' : {l : Nat} -> {ty : Type} -> Vect (S l) ty -> ty
last' = ind_Nat l (mot_last ty) base_last step_last 

mot_drop_last : (ty : Type) -> (k : Nat) -> Type
mot_drop_last ty k = Vect (S k) ty -> Vect k ty

base_drop_last : (es : Vect (S 0) ty) -> Vect 0 ty
base_drop_last es = Nil

step_drop_last : (l_1 : Nat) -> (drop_last_l_1 : mot_drop_last ty l_1) -> mot_drop_last ty (S l_1)
step_drop_last l_1 drop_last_l_1 = \es => head es :: drop_last_l_1 (tail es) 

drop_last : {l : Nat} -> {ty : Type} -> Vect (S l) ty -> Vect l ty
drop_last = ind_Nat l (mot_drop_last ty) base_drop_last step_drop_last

-- Chapter 8

incr : (n : Nat) -> Nat
incr n = iter_Nat n 1 (plus' 1)

plus_1_eq_add1 : (n : Nat) -> plus' 1 n = S n
plus_1_eq_add1 n = Refl

mot_incr_eq_add1 : (k : Nat) -> Type
mot_incr_eq_add1 k = incr k = S k

base_incr_eq_add1 : incr 0 = S 0
base_incr_eq_add1 = Refl

step_incr_eq_add1 : (n_1 : Nat) -> 
                    (incr_eq_add1_n_1 : mot_incr_eq_add1 n_1) -> 
                    mot_incr_eq_add1 (S n_1)
step_incr_eq_add1 n_1 incr_eq_add1_n_1 = cong (plus' 1) incr_eq_add1_n_1 -- or S

incr_eq_add1 : (n : Nat) -> incr n = S n
incr_eq_add1 n = ind_Nat n mot_incr_eq_add1 base_incr_eq_add1 step_incr_eq_add1


