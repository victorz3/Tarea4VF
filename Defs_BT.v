From Tarea3VF Require Export Defs_BN.

(* Definition of binary trees and some of their properties  *)

Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).

(* Binary trees defined here*)
Inductive BTree : Type :=
    E : BTree
  | N : A -> BTree  -> BTree  -> BTree.

Parameter (undefBTree : BTree).

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

Fixpoint lookup_bn (t:BTree) (b: BN) : A :=
 match t,b with
  |E, b => undefA
  |N x s t,Z => x 
  |N x s t, U a => lookup_bn s a   (* U a = 2a+1 *)
  |N x s t, D a => lookup_bn t a   (* D a = 2a + 2 *) 
 end.


Fixpoint update (t:BTree) (b: BN) (x : A) : BTree :=
 match t,b with
  |E, b => undefBTree
  |N y s t, Z =>  N x s t
  |N y s t, U a => N y (update s a x) t
  |N y s t, D a => N y s (update t a x)
 end.

Fixpoint le (x:A) (t:BTree) : BTree :=
 match t with
    E => N x E E
  | N y s t => N x (le y t) s
 end.

Fixpoint he (x:A) (t:BTree) : BTree  :=
 match t with
  |E => N x E E
  |N y l r => match bsize t with
               |U b => N y (he x l) r
               |D b => N y l (he x r)
               |  Z => undefBTree 
              end
 end.

(* Obtiene el último elemento de un árbol de Braun *)
Fixpoint last (t: BTree) : A :=
match t with
| E => undefA
| N x E E => x
| N x t1 t2 => match bsize t with
             | U b => last t2
             | D b => last t1
             | Z => undefA
             end
end.

(* Operador lr *)
Fixpoint lr (t: BTree) : BTree :=
match t with
| E => undefBTree
| N x t1 t2 => match t1 with
               | E => E
               | N y t3 t4 => N y t2 (lr t1)
               end
end.

(* Operador hr *)
Fixpoint hr (t:BTree) :BTree :=
match t with
| E => undefBTree
| N _ E _ => E
| N y l r => match bsize t with
             | U b => N y l (hr r)
             | D b => N y (hr l) r
             | Z => undefBTree
             end
end.







