
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

-- Chapter 9

mot_step_incr_eq_add1' : (n_1 : Nat) -> (k : Nat) -> Type
mot_step_incr_eq_add1' n_1 k = S (incr n_1) = S k

step_incr_eq_add1' : (n_1 : Nat) -> 
                     (incr_eq_add1_n_1 : mot_incr_eq_add1 n_1) -> 
                     mot_incr_eq_add1 (S n_1)
step_incr_eq_add1' n_1 incr_eq_add1_n_1 
  = replace {p = mot_step_incr_eq_add1' n_1} incr_eq_add1_n_1 Refl 

double : (n : Nat) -> Nat
double n = iter_Nat n 0 (plus' 2)

twice : (n : Nat) -> Nat
twice n = n `plus'` n

mot_add1_plus_eq_plus_add1 : (j : Nat) -> (k : Nat) -> Type
mot_add1_plus_eq_plus_add1 j k = S (k `plus'` j) = k `plus'` S j

step_add1_plus_eq_plus_add1 : (j : Nat) -> 
                              (n_1 : Nat) -> 
                              (add1_plus_eq_plus_add1_n_1 : mot_add1_plus_eq_plus_add1 j n_1) ->
                              mot_add1_plus_eq_plus_add1 j (S n_1)
step_add1_plus_eq_plus_add1 j n_1 add1_plus_eq_plus_add1_n_1 
  = cong S add1_plus_eq_plus_add1_n_1

add1_plus_eq_plus_add1 : (n : Nat) -> (j : Nat) -> S (n `plus'` j) = n `plus'` S j
add1_plus_eq_plus_add1 n j = ind_Nat n 
                                    (mot_add1_plus_eq_plus_add1 j) 
                                    Refl 
                                    (step_add1_plus_eq_plus_add1 j)

mot_twice_eq_double : (k : Nat) -> Type
mot_twice_eq_double k = twice k = double k

mot_step_twice_eq_double : (n_1 : Nat) -> (k : Nat) -> Type
mot_step_twice_eq_double n_1 k = S k = S (S (double n_1))

step_twice_eq_double : (n_1 : Nat) ->
                       (twice_eq_double_n_1 : mot_twice_eq_double n_1) ->
                       mot_twice_eq_double (S n_1)
step_twice_eq_double n_1 twice_eq_double_n_1 
  = replace {p = mot_step_twice_eq_double n_1} 
            (add1_plus_eq_plus_add1 n_1 n_1)
            (cong (plus' 2) twice_eq_double_n_1)

twice_eq_double : (n : Nat) -> twice n = double n
twice_eq_double n = ind_Nat n mot_twice_eq_double Refl step_twice_eq_double

mot_double_Vec : (ty : Type) -> (k : Nat) -> Type
mot_double_Vec ty k = Vect k ty -> Vect (double k) ty

base_double_Vec : (es : Vect 0 ty) -> Vect (double 0) ty
base_double_Vec _ = Nil

step_double_Vec : (l_1 : Nat) -> 
                  (double_Vect_l_1 : mot_double_Vec ty l_1) ->
                  mot_double_Vec ty (S l_1)
step_double_Vec _ double_Vect_l_1 es 
  = head es :: head es :: double_Vect_l_1 (tail es)

double_Vec : {l : Nat} -> {ty : Type} -> (es : Vect l ty) -> Vect (double l) ty
double_Vec = ind_Nat l (mot_double_Vec ty) base_double_Vec step_double_Vec

twice_Vec : {ty: Type} -> {l : Nat} -> (es : Vect l ty) -> Vect (twice l) ty
twice_Vec es = replace {p = \k => Vect k ty}
                       (sym $ twice_eq_double l)
                       (double_Vec es)

-- Chapter 10

more_expectations : Vect 3 Atom
more_expectations = "need-induction" :: "Understood-induction" :: "built-function" :: Nil

frame_10_8 : (bread : Atom ** bread = "bagel")
frame_10_8 = ("bagel" ** Refl {x = "bagel"})

frame_10_11 : (food : Atom ** the (List Atom) [food] = ["toast"])
frame_10_11 = ("toast" ** Refl)

frame_10_13 : (l : Nat ** Vect l Atom)
frame_10_13 = (17 ** peas 17)

frame_10_19 : (es : List Atom ** es = reverse' es)
frame_10_19 = (Nil ** Refl)

frame_10_20 : (es : List Atom ** es = reverse' es)
frame_10_20 = (["bialy", "schmear", "bialy"] ** Refl)

frame_10_21 : (es : List Atom ** snoc es "grape" = "grape" :: es)
frame_10_21 = (Nil ** Refl)

frame_10_23 : (es : List Atom ** snoc es "grape" = "grape" :: es)
frame_10_23 = (["grape", "grape", "grape"] ** Refl)

step_list_to_vec_no : (e: ty) -> 
                      (es : List ty) -> 
                      (list_to_vec_es : (l ** Vect l ty)) -> 
                      (l ** Vect l ty)
step_list_to_vec_no e _ list_to_vec_es 
  = (S (fst list_to_vec_es) ** e :: snd list_to_vec_es)

list_to_vec_no1 : (es : List ty) -> (l ** Vect l ty)
list_to_vec_no1 es = rec_List es (0 ** Nil) step_list_to_vec_no

list_to_vec_no2 : (es : List ty) -> (l ** Vect l ty)
list_to_vec_no2 _ = (0 ** Nil)

mot_replicate : (ty : Type) -> (k : Nat) -> Type
mot_replicate ty k = Vect k ty

step_replicate : (e : ty) -> 
                 (l_1 : Nat) -> 
                 (step_replicate_l_1 : mot_replicate ty l_1) -> 
                 mot_replicate ty (S l_1)
step_replicate e _ step_replicate_l_1 = e :: step_replicate_l_1

replicate' : {ty: Type} -> (l : Nat) -> (e : ty) -> Vect l ty
replicate' l e = ind_Nat l (mot_replicate ty) Nil (step_replicate e)

copy_52_times : {ty : Type} ->
                (e : ty) -> 
                (es : List ty) -> 
                (copy_52_times_es : (l ** Vect l ty)) -> 
                (l ** Vect l ty) 
copy_52_times e _ _ = (52 ** replicate' 52 e)

list_to_vec_no3 : {ty : Type} -> (es : List ty) -> (l ** Vect l ty)
list_to_vec_no3 es = rec_List es (0 ** Nil) copy_52_times 

ind_List : (target : List ty) ->
           (mot : List ty -> Type) ->
           (base : mot Nil) ->
           (step : (e : ty) -> (es : List ty) -> mot es -> mot (e :: es)) ->
           mot target
ind_List []        mot base step = base
ind_List (e :: es) mot base step = step e es $ ind_List es mot base step

mot_list_to_vec : (ty: Type) -> (es : List ty) -> Type
mot_list_to_vec ty es = Vect (length' es) ty

step_list_to_vec : (e : ty) -> 
                   (es : List ty) -> 
                   (list_to_vec_es : mot_list_to_vec ty es) -> 
                   mot_list_to_vec ty (e :: es)
step_list_to_vec e _ list_to_vec_es = e :: list_to_vec_es

list_to_vec : (ty : Type) -> (es : List ty) -> Vect (length' es) ty
list_to_vec ty es = ind_List es (mot_list_to_vec ty) Nil step_list_to_vec

step_list_to_vec_no4 : {ty : Type} ->
                       (e : ty) -> 
                       (es : List ty) -> 
                       (list_to_vec_es : mot_list_to_vec ty es) -> 
                       mot_list_to_vec ty (e :: es)
step_list_to_vec_no4 e es _ = replicate' (length' (e :: es)) e

list_to_vec_no4 : {ty : Type} -> (es : List ty) -> Vect (length' es) ty
list_to_vec_no4 es = ind_List es (mot_list_to_vec ty) Nil step_list_to_vec_no4

-- Chapter 11

treats : Vect 3 Atom
treats = "kanelbullar" :: "plättar" :: "prinsesstärta" :: Nil

drinks : List Atom
drinks = "coffe" :: "cocoa" :: Nil

ind_Vec : (n : Nat) ->
          (target : Vect n ty) ->
          (mot : (k : Nat) -> (es : Vect k ty) -> Type) ->
          (base : mot 0 Nil) ->
          (step : (k : Nat) -> (h : ty) -> (t : Vect k ty) -> mot k t -> mot (S k) (h :: t)) ->
          mot n target
ind_Vec 0     []       mot base step = base
ind_Vec (S k) (h :: t) mot base step = step k h t $ ind_Vec k t mot base step

mot_vec_append : (ty : Type) -> (j : Nat) -> (k : Nat) -> (es : Vect k ty) -> Type
mot_vec_append ty j k _ = Vect (k + j) ty

step_vec_append : (ty : Type) -> 
                  (j : Nat) -> 
                  (l_1 : Nat) -> 
                  (e : ty) -> 
                  (es : Vect l_1 ty) ->
                  (vec_append_es : mot_vec_append ty j l_1 es) ->
                  mot_vec_append ty j (S l_1) (e :: es)
step_vec_append _ _ _ e _ vec_append_es = e :: vec_append_es

vec_append : (ty : Type) -> (l : Nat) -> (j : Nat) -> Vect l ty -> Vect j ty -> Vect (l + j) ty
vec_append ty l j es end = ind_Vec l es (mot_vec_append ty j) end (step_vec_append ty j)

fika : Vect 5 Atom
fika = vec_append Atom 3 2 treats (list_to_vec Atom drinks)

mot_vec_to_list : (ty : Type) -> (l : Nat) -> (es : Vect l ty) -> Type
mot_vec_to_list ty _ _ = List ty

step_vec_to_list : (ty : Type) ->
                   (l_1 : Nat) ->
                   (e : ty) ->
                   (es : Vect l_1 ty) ->
                   (vec_to_list_es : mot_vec_to_list ty l_1 es) ->
                   mot_vec_to_list ty (S l_1) (e :: es)
step_vec_to_list _ _ e _ vec_to_list_es = e :: vec_to_list_es

vec_to_list : (ty : Type) -> (l : Nat) -> (es : Vect l ty) -> List ty
vec_to_list ty l es = ind_Vec l es (mot_vec_to_list ty) Nil (step_vec_to_list ty)

mot_list_to_vec_to_list_equal : (ty : Type) -> (es : List ty) -> Type
mot_list_to_vec_to_list_equal ty es = es = vec_to_list ty (length' es) (list_to_vec ty es)

step_list_to_vec_to_list_equal : (ty : Type) ->
                                 (e : ty) -> 
                                 (es : List ty) ->
                                 (list_to_vec_to_list_equal_es : mot_list_to_vec_to_list_equal ty es) ->
                                 mot_list_to_vec_to_list_equal ty (e :: es)
step_list_to_vec_to_list_equal _ e _ list_to_vec_to_list_equal_es = cong (e ::) list_to_vec_to_list_equal_es
 

list_to_vec_to_list_equal : (ty : Type) -> 
                            (es : List ty) -> 
                            es = vec_to_list ty (length' es) (list_to_vec ty es)
list_to_vec_to_list_equal ty es = ind_List es
                                           (mot_list_to_vec_to_list_equal ty)
                                           Refl
                                           (step_list_to_vec_to_list_equal ty)

-- Chapter 12

Even : (n : Nat) -> Type
Even n = (half : Nat ** n = double half)

even_10 : Even 10
even_10 = (5 ** Refl {x = 10})

zero_is_even : Even 0
zero_is_even = (0 ** Refl {x = 0})

plus_two_even : (n : Nat) -> Even n -> Even (plus' 2 n)
plus_two_even _ e_n = (S (fst e_n) ** cong (plus' 2) (snd e_n))

two_is_even : Even 2
two_is_even = plus_two_even 0 zero_is_even

Odd : (n : Nat) -> Type
Odd n = (haf : Nat ** n = S (double haf))

one_is_odd : Odd 1
one_is_odd = (0 ** Refl {x = 1})

thirteen_is_odd : Odd 13
thirteen_is_odd = (6 ** Refl {x = 13})

add1_even_is_odd : (n : Nat) -> (e_n : Even n) -> Odd (S n)
add1_even_is_odd _ e_n = (fst e_n ** cong (plus' 1) (snd e_n))

add1_odd_is_even : (n : Nat) -> (o_n : Odd n) -> Even (S n)
add1_odd_is_even _ o_n = (S (fst o_n) ** cong (plus' 1) (snd o_n))

repeat : (f : Nat -> Nat) -> (n : Nat) -> Nat
repeat f n = iter_Nat n (f 1) (\iter_f_n_1 => f iter_f_n_1)

ackermann : (n : Nat) -> Nat -> Nat
ackermann n = iter_Nat n (plus' 1) (\ackerman_n_1 => repeat ackerman_n_1)

-- Chapter 13

ind_Either : (target : Either l r) -> 
             (mot : Either l r -> Type) -> 
             (base_left : (x : l) -> mot (Left x)) ->
             (base_right : (x : r) -> mot (Right x)) ->
             mot target
ind_Either (Left x)  _ base_left _          = base_left  x
ind_Either (Right y) _ _         base_right = base_right y

mot_even_or_odd : (k : Nat) -> Type
mot_even_or_odd k = Either (Even k) (Odd k)

step_even_or_odd : (n_1 : Nat) -> 
                   (even_or_odd_n_1 : mot_even_or_odd n_1) -> 
                   mot_even_or_odd (S n_1)
step_even_or_odd n_1 even_or_odd_n_1 = ind_Either even_or_odd_n_1
                                                  (\_ => mot_even_or_odd (S n_1))
                                                  (\e_n_1 => Right $ add1_even_is_odd n_1 e_n_1)
                                                  (\o_n_1 => Left  $ add1_odd_is_even n_1 o_n_1)

even_or_odd : (n : Nat) -> Either (Even n) (Odd n)
even_or_odd n = ind_Nat n
                        mot_even_or_odd
                        (Left zero_is_even)
                        step_even_or_odd

-- Chapter 14

Trivial : Type
Trivial = Unit

sole : Trivial
sole = MkUnit

Maybe' : Type -> Type
Maybe' x = Either x Trivial

nothing : (ty : Type) -> Maybe' ty
nothing _ = Right sole

just : (ty : Type) -> (x : ty) -> Maybe' ty
just _ x = Left x

maybe_head : (ty : Type) -> (es : List ty) -> Maybe' ty
maybe_head ty es = rec_List es (nothing ty) (\hd, _, _ => just ty hd)

maybe_tail : (ty : Type) -> (es : List ty) -> Maybe' (List ty)
maybe_tail ty es = rec_List es (nothing (List ty)) (\_, tl, _ => just (List ty) tl)

step_list_ref : (ty : Type) -> 
                (n_1 : Nat) -> 
                (list_ref_n_1 : List ty -> Maybe' ty) -> 
                (es : List ty) -> 
                Maybe' ty
step_list_ref ty _ list_ref_n_1 es = ind_Either (maybe_tail ty es)
                                                (\_ => Maybe' ty)
                                                (\tl => list_ref_n_1 tl)
                                                (\_ => nothing ty) 

list_ref : (ty : Type) -> (n : Nat) -> (es : List ty) -> Maybe' ty
list_ref ty n = rec_Nat n (maybe_head ty) (step_list_ref ty)

frame_14_19 : Maybe' Atom
frame_14_19 = list_ref Atom 0 ("ratatuille" :: "kartoffelmad" :: "hero" :: "prinsesstarta" :: Nil)

menu : Vect 4 Atom
menu = "ratatuille" :: "kartoffelmad" :: "hero" :: "prinsesstarta" :: Nil

Absurd : Type
Absurd = Void

similarly_absurd : (x : Absurd) -> Absurd
similarly_absurd x = x

ind_Absurd : (target : Absurd) -> (mot : Type) -> mot
ind_Absurd target mot = absurd target

Fin' : (n : Nat) -> Type
Fin' n = iter_Nat n Absurd Maybe'

fzero : (n : Nat) -> Fin' (S n)
fzero n = nothing $ Fin' n

fadd1 : (n : Nat) -> (i_1 : Fin' n) -> Fin' (S n)
fadd1 n i_1 = just (Fin' n) i_1

base_vec_ref : (ty : Type) -> (no_value_ever : Fin' 0) -> (es : Vect 0 ty) -> ty
base_vec_ref ty no_value_ever _ = ind_Absurd no_value_ever ty

step_vec_ref : (ty : Type) -> 
               (l_1 : Nat) -> 
               (vec_ref_l_1 : Fin' l_1 -> Vect l_1 ty -> ty) -> 
               (i : Fin' (S l_1)) -> 
               (es : Vect (S l_1) ty) -> 
               ty
step_vec_ref ty l_1 vec_ref_l_1 i es = ind_Either i
                                                  (\_ => ty)
                                                  (\i_1 => vec_ref_l_1 i_1 (tail es))
                                                  (\triv => head es)

vec_ref : (ty : Type) -> (l : Nat) -> (Fin' l) -> (Vect l ty) -> ty
vec_ref ty l = ind_Nat l 
                       (\k => (Fin' k) -> (Vect k ty) -> ty)
                       (base_vec_ref ty)
                       (step_vec_ref ty)

frame_14_74 : Atom
frame_14_74 = ?frame_14_74_rhs

Two : Type
Two = Either Trivial Trivial

Two_Fun : (n : Nat) -> Type
Two_Fun n = iter_Nat n
                     Two
                     (\type => Two -> type)

both_left : (a : Two) -> (b : Two) -> Two
both_left a b = ind_Either a
                           (\_ => Two)
                           (\_ => b)
                           (\_ => Right sole)

step_taut : (n_1 : Nat) -> (taut_n_1 : Two_Fun n_1 -> Two) -> Two_Fun (S n_1) -> Two
step_taut n_1 taut_n_1 f = both_left (taut_n_1 (f (Left sole))) (taut_n_1 (f (Right sole)))

taut : (n : Nat) -> Two_Fun n -> Two
taut n = ind_Nat n (\k => Two_Fun k -> Two) (\x => x) step_taut

