module BinTrees

import Data.Nat

data BinTree : (ty : Type) -> Type where
  Empty : BinTree ty
  Node : (left : BinTree ty) -> (root : ty) -> (right : BinTree ty) -> BinTree ty

||| Number of 0-degree nodes (leaves)
n0 : BinTree ty -> Nat
n0 Empty = 0
n0 (Node Empty _ Empty) = 1 
n0 (Node left  _ right) = n0 left + n0 right

||| Number of 2-degree nodes
n2 : BinTree ty -> Nat
n2 Empty = 0
n2 (Node left@(Node _ _ _) _ right@(Node _ _ _)) = 1 + n2 left + n2 right
n2 (Node left _ right) = n2 left + n2 right

||| In a non-empty tree the number of leaves is the number of 2-degree nodes plus one
prop_tree : (t : BinTree ty) -> Not (t = Empty) -> n0 t = n2 t + 1
prop_tree Empty f = absurd $ f Refl
prop_tree (Node Empty _ Empty) f = Refl
prop_tree (Node Empty _ right@(Node _ _ _)) f 
  = prop_tree right (\case Refl impossible)
prop_tree (Node left@(Node _ _ _) _ Empty) f
  = let ih_left = prop_tree left (\case Refl impossible) in
      rewrite plusZeroRightNeutral (n0 left) in 
      rewrite plusZeroRightNeutral (n2 left) in 
      ih_left
prop_tree (Node left@(Node _ _ _) _ right@(Node _ _ _)) f 
  = let ih_left = prop_tree left (\case Refl impossible) 
        ih_right = prop_tree right (\case Refl impossible) in
      rewrite ih_left in
      rewrite ih_right in
      rewrite plusCommutative (n2 left) 1 in
      rewrite plusAssociative (n2 left) (n2 right) 1 in
      Refl

