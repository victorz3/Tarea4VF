From Tarea3VF Require Export Defs_BN.

(* Definition of binary trees and some of their properties  *)

Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).

(* Binary trees defined here*)
Inductive BTree : Type :=
    E : BTree
  | N : A -> BTree  -> BTree  -> BTree.

(*size on binary trees defined next*)
Fixpoint bsize (t:BTree): BN :=
 match t with
  E => Z
 |N x s t =>  sucBN ((bsize s) ⊞ (bsize t))
 end.

(* Balance condition on Braun trees *)
Inductive bbal : BTree -> Prop:= 
 |bbalE : bbal E 
 |bbalN : forall (a: A) (s t: BTree), bbal s -> bbal t -> (bsize t) ≤BN (bsize s) -> (
                                      bsize s) ≤BN (sucBN (bsize t)) -> 
                                      bbal (N a s t).



