
From Tarea3VF Require Export Defs_BT.
From Tarea3VF Require Export Props_BN.

Theorem eq_btree_dec: forall (s t:BTree), {s=t} + {s<>t}.
Proof.
intros.
decide equality.
apply eq_dec_A.
Qed.


Lemma nonE_tree: forall (t:BTree), t <> E -> exists (a:A) (t1 t2:BTree), t = N a t1 t2.
Proof.
intros.
destruct t.
intuition.
exists a.
exists t1.
exists t2.
trivial.
Qed.


Lemma bsize_Z: forall (t:BTree), bsize t = Z -> t = E.
Proof.
intros t0.
destruct t0.
intuition.
intros.
simpl in H.
symmetry in H.
contradict H.
apply ZnotSucBN.
Qed.

Lemma bsize_nonZ: forall (t:BTree), t <> E -> bsize t <> Z.
Proof.
intros.
contradict H.
apply bsize_Z.
trivial.
Qed.


Lemma btNonE: forall (t:BTree) (b:BN), t <> E -> 
                       exists (b:BN), bsize t = U b \/ bsize t = D b.
Proof.
intros.
apply bsize_nonZ in H.
apply (bnNonZ (bsize t)) in H.
trivial.
Qed.


Parameter (allBal: forall (t:BTree), bbal t).

Lemma prop_0_U : forall (a:A) (s t:BTree) (b:BN), 
                  bbal (N a s t) -> bsize(N a s t) = U b -> 
                  bsize s = b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_U in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0.
apply addition_a_a in H0.
rewrite <- H8.
intuition.
rewrite H8 in H0b.
rewrite plus_D in H0b.
inversion H0b.
Qed.


Lemma prop_0_D : forall (a:A) (s t:BTree) (b:BN), bbal (N a s t) 
                         -> bsize(N a s t) = D b -> 
                            bsize s = sucBN b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_D in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0b.
rewrite plus_U in H0b.
inversion H0b.
rewrite H8 in H0.
apply addition_SucBNa_a in H0.
rewrite <- H0.
intuition.
Qed.

Corollary size_caseU: forall (a:A) (l r:BTree) (b:BN), 
                        bsize (N a l r) = U b -> bsize l = bsize r.
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_U a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary size_caseD: forall (a:A) (l r:BTree) (b:BN), 
                        bsize (N a l r) = D b 
                           -> bsize l = sucBN (bsize r).
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_D a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary size_case_comb: forall a l r, bbal (N a l r) -> bsize l = bsize r \/ bsize l = sucBN (bsize r).
Proof.
intros.
destruct (bsize (N a l r)) eqn:Size.
+ simpl in Size.
  apply suc_not_z in Size; contradiction.
+ apply size_caseU in Size.
  left; trivial.
+ apply size_caseD in Size.
  right; trivial.
Qed.

Corollary bbal_size_r: forall (a:A) (l r:BTree), 
                          bsize (N a l r) = U (bsize r) \/ 
                          bsize (N a l r) = D (bsize r).
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
simpl.
assert (Z <> sucBN (bsize l ⊞ bsize r)).
apply ZnotSucBN.
intuition.
destruct H.
apply prop_0_U in H.
simpl.
destruct H.
rewrite H.
rewrite H0.
rewrite plus_U.
intuition.
trivial.
apply prop_0_D in H.
destruct H.
simpl.
rewrite H.
rewrite H0.
rewrite plus_D.
intuition.
trivial.
Qed.

Theorem bbal_size_r2: forall (a:A) (l r:BTree), (bsize (N a l r)) ≤BN (D (bsize r)). 
Proof.
intros a l r.
destruct (bbal_size_r a l r).
constructor.
rewrite H.
constructor.
rewrite H.
constructor.
Qed.

Theorem bbal_size_l: forall (a:A) (l r:BTree), (bsize (N a l r)) ≤BN (U (bsize l)). 
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
- simpl.
  assert (Z <> sucBN (bsize l ⊞ bsize r)).
  apply ZnotSucBN.
  intuition.
- destruct H.
  + apply prop_0_U in H.
    * simpl.
      destruct H.
      subst.
      rewrite H0. 
      rewrite plus_U.
      constructor.
    * assumption.
  +  apply prop_0_D in H.
    * simpl.
      destruct H.
rewrite H.
rewrite H0.
rewrite plus_D.
constructor.
constructor.
apply lts.
* trivial.
Qed.

(* ============================================= *)
          

Lemma lt_U_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (U b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t1).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (U (bsize t1))).
apply bbal_size_l.
assert ((U b) <BN (U (bsize t1))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Theorem rightE: forall (a:A) (t1 t2:BTree), bbal(N a t1 t2) -> t2 = E -> (t1 = E \/ exists (aa:A), t1 = (N aa E E)).
Proof.
intros.
inversion H.
destruct (bbalCond_eqs (bsize t1) (bsize t2)).
trivial.
trivial.
rewrite H0 in H8.
simpl in H8.
apply bsize_Z in H8.
intuition.
rewrite H0 in H8.
right.
destruct t1.
simpl in H8.
inversion H8.
simpl in H8.
replace (U Z) with (sucBN Z) in H8.
apply SucBNinj in H8.
apply plusBN_Z_Z in H8.
destruct H8.
apply bsize_Z in H8.
apply bsize_Z in H9.
exists a1.
rewrite H8.
rewrite H9.
trivial.
intuition.
Qed.


Lemma lt_D_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (D b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t2).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (D (bsize t2))).
apply bbal_size_r2.
assert ((D b) <BN (D (bsize t2))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Lemma bbal_leaf: forall (a:A), bbal (N a E E).
Proof.
intro a.
constructor.
constructor.
constructor.
apply lteqBN_refl. 
apply lteqs.
Qed.



Theorem leftE_leaf: forall (t1 t2:BTree) (a:A), bbal (N a t1 t2) -> t1 = E -> t2 = E.
Proof.
intros t1 t2 c HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
apply bsize_Z in H9.
trivial.
inversion H7.
Qed.



Lemma bbal_inv: forall (t:BTree), t <> E ->  
                          (exists (z:A), t = N z E E)  \/ 
                           exists (z:A) (r1 r2:BTree), bbal r1 /\ bbal r2 /\ r1 <> E /\ t = N z r1 r2.
Proof.
intros.
assert (bbal t).
+ apply allBal.
+ induction t.
  - contradiction.
  - destruct t1, t2.
    * left; exists a; trivial.
    * inversion H0.
      inversion H6.
      ** assert (Z <> sucBN (bsize t2_1 ⊞ bsize t2_2)).
         ++ apply ZnotSucBN.
         ++ rewrite H10 in H9; contradiction.
      ** inversion H8.
    * right.
      exists a; exists (N a0 t1_1 t1_2); exists E.
      split.
      ** assert (N a0 t1_1 t1_2 <> E).
         ++ discriminate.
         ++ apply IHt1 in H1.
            -- destruct H1.
               +++ destruct H1.
                   rewrite H1.
                   do 2 constructor.
                   simpl.
                   constructor.
               +++ constructor.
                   *** destruct H1.
                       do 2 destruct H1.
                       destruct H1.
                       destruct H2.
                       destruct H3.
                       inversion H4.
                       trivial.
                   *** destruct H1.
                       do 2 destruct H1.
                       destruct H1.
                       destruct H2.
                       destruct H3.
                       inversion H4.
                       trivial.
                   *** inversion H0.
                       inversion H5.
                       trivial.
                   *** inversion H0.
                       inversion H5.
                       trivial.
            -- inversion H0.
               trivial.
      ** split.
         ++ constructor.
         ++ split.
            -- discriminate.
            -- trivial.
    * right; exists a.
      exists (N a0 t1_1 t1_2); exists (N a1 t2_1 t2_2).
      split.
      ** inversion H0.
         trivial.
      ** split.
         ++ inversion H0.
            trivial.
         ++ split.
            -- discriminate.
            -- trivial.
Qed.


Lemma lkp_upd_BN: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
(*Induction on t*)
induction t.
- (*Base case t = E *)
intuition.
- (*Induction step t = N a t1 t2*)
intros.
(*cases on BNat number b*)
destruct b.
+ (*1. b=Z*)
reflexivity.
+ (*2. b = U b*)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
* (*i) t1=E A*)
assert (t2 = E).
-- apply (leftE_leaf t1 t2 a).
   ++ eexact H.
   ++ assumption.
-- (*t1=E  and t2=E *)
   subst.
   simpl in H1.
   inversion H1.
   inversion H4.
* (*ii) t1<>E A*)
simpl. 
apply IHt1.
-- inversion H.
   assumption.
-- assumption.
-- eapply lt_U_bsize.
   exact H1.
+ (*3. b = D b*)
  destruct (eq_btree_dec t2 E).
  * destruct (rightE a t1 t2).
    -- assumption.
    -- assumption.
    -- simpl.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
    -- destruct H2.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
* simpl. 
  apply IHt2.
  -- inversion H.
     assumption.
  -- assumption.
  -- eapply lt_D_bsize.
     exact H1.
Qed.




Lemma lkp_upd_BNindbal: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
induction H.
- intuition.
- intros.
  destruct b.
  + reflexivity.
  + simpl.
    destruct (eq_btree_dec s E).
    * destruct (eq_btree_dec t E).
      -- subst.
         simpl in H4.
         apply lt_U in H4.
         inversion H4.
      -- subst.
         simpl in H1.
         inversion H1. 
         ++ subst.
            apply bsize_nonZ in n.
            contradiction n.  
         ++ inversion H5.
    * apply IHbbal1.
      -- assumption.
      -- apply lt_U.
         eapply lt_lteqBN_trans.
         ++ exact H4.
         ++ apply bbal_size_l.
  + destruct (eq_btree_dec t E).
    * destruct (eq_btree_dec s E). 
       -- subst.
          simpl in H4.
          inversion H4.
          inversion H7.
       -- subst.
          simpl in H2.
          inversion H2.
          ++ simpl in H4.
             rewrite H7 in H4.
             simpl in H4. 
             inversion H4.
             inversion H9.
          ++ subst.
             inversion H5.
             ** contradict n.
             apply bsize_Z.
             intuition. 
             ** inversion H8.
             ** inversion H8.
    *  simpl.
       apply IHbbal2.
       -- assumption.
       -- apply lt_D.
          eapply lt_lteqBN_trans.
          ++ exact H4.
          ++ apply bbal_size_r2.  
Qed.       
       
          
Lemma elmnt_lkp_upd : forall (t:BTree) (i j:BN), 
                        i <BN (bsize t) -> j <BN (bsize t) -> 
                        i <> j -> 
                        forall (x:A), 
                          lookup_bn (update t i x) j = lookup_bn t j.
Proof.
intros t.
induction t.
(* t = E*)
- intros.
simpl in H0.
inversion H0.
- (* t = N a t1 t2 *)
intros.
assert (tBal:=allBal (N a t1 t2)).
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ (* exists z : A, N a t1 t2 = N z E E *)
destruct H2.
inversion H2.
subst.
simpl in H.
inversion H.
* subst.
  simpl in H0.
  inversion H0.
  -- subst. intuition.
  -- reflexivity.
  -- reflexivity. 
* destruct j.
  -- reflexivity.
  -- inversion H5.
  -- inversion H5.
* inversion H5.
+ (*  exists (z : A) (r1 r2 : BTree),
         bbal r1 /\ bbal r2 /\ r1 <> E /\ N a t1 t2 = N z r1 r2 *)
do 4 (destruct H2).
destruct H3.
destruct H4.
destruct H5.
destruct i.
* destruct j. 
  -- intuition.
  -- reflexivity.
  -- reflexivity.
* destruct j.
  -- reflexivity.
  -- simpl.
     apply IHt1. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_l. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_l.
     ++ contradict H1.
        subst;reflexivity.
   -- reflexivity.
  * destruct j.
    -- reflexivity.
    -- reflexivity.
    -- simpl. 
       apply IHt2. 
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_r2.
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_r2.
     ++ contradict H1.
        subst;reflexivity.
Qed.


Lemma bsize_upd: forall (t:BTree) (x:A) (b:BN), 
                  b <BN bsize t -> bsize t = bsize (update t b x).
Proof.
intro t.
induction t.
- (* Base case *)
intuition.
inversion H.
- (* Inductive step *)
intros.
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ destruct H0.
  rewrite H0 in H.
  simpl in H.
  inversion H.
  * (* b = Z *)
   reflexivity.
  * (* U a0 = b, a < Z *)
    inversion H3.
  * (* D a0 = b, a < Z *)
    inversion H3.
+ do 4 (destruct H0).
  destruct H1.
  destruct H2.
  inversion H3.
  subst.
  destruct b.
  * (* Z *)
    reflexivity.
  * (* U b*)
   simpl.
   rewrite (IHt1 x b).
   -- reflexivity.
   -- apply (lt_U_bsize b x0 x1 x2).
      assumption. 
  * (* b = D b *)
    simpl.
    rewrite (IHt2 x b).
    -- reflexivity.
    -- apply (lt_D_bsize b x0 x1 x2).
       assumption.
Qed.


Lemma bsize_le: forall (t:BTree) (x:A), bsize (le x t) = sucBN (bsize t).
Proof.
intro.
assert (HBal := allBal t).  
induction HBal.
- reflexivity.
- intro.
  simpl.
  rewrite IHHBal2.
  rewrite <- plusSuc.
  rewrite plusComm.
  reflexivity.
Qed.



Lemma bal_le: forall (t:BTree), bbal t -> 
                 forall (x:A), bbal (le x t).
Proof.
intros t HtBal.
induction HtBal.
- simpl.
  apply bbal_leaf.
- intros.
  simpl.
  constructor.
  + apply IHHtBal2.
  + assumption.
  + rewrite bsize_le.
    assumption.
  + rewrite bsize_le.
    apply lteqBN_suc.
    assumption.
Qed.

Lemma le_head: forall (t: BTree) (x:A),  lookup_bn (le x t) Z = x.
Proof.
intros.
destruct t.
- intuition.
- intuition.
Qed.


Lemma le_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (le x t) (sucBN j) = lookup_bn t j.
Proof.
intros t B.
induction B.
- intros.
  simpl in H.
  inversion H.
- intros.
  clear IHB1.
  destruct j.
  + simpl.
    apply le_head.
  + reflexivity.
  + simpl.
    apply IHB2.
    apply (lt_D_bsize j a s t).
    assumption.
Qed.


(*High Extension*)

Lemma bsize_he: forall (t:BTree) (x:A), 
                    bsize (he x t) = sucBN (bsize t).
Proof.
intro.
induction t.
- intuition.
- intros.
  destruct (bbal_size_r a t1 t2).
  + simpl in H.
    simpl.     
    rewrite H.
    simpl.
    rewrite IHt1.
    rewrite <- plusSuc.
    rewrite H. 
    intuition.
  + simpl in H.
    simpl.
    rewrite H.
    simpl.
    rewrite IHt2.
    rewrite <- plusSuc_2.
    rewrite H.
    intuition.
Qed.



Lemma bal_he: forall (t:BTree), bbal t -> 
                forall (x:A), bbal (he x t).
Proof.
intros t Ht.
induction t.
- simpl.
  apply bbal_leaf.
- intros.
  inversion Ht.
  subst.
  destruct (bbal_size_r a t1 t2).
  + assert(H6:=H).
    apply size_caseU in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor.
    * apply IHt1.
      assumption.
    * assumption.
    * rewrite bsize_he.
      inversion H4.
      -- intuition.
      -- constructor; apply (ltBN_trans (bsize t2) (bsize t1) (sucBN (bsize t1))).
         ++ trivial.
         ++ apply lts.
    * rewrite bsize_he.
      rewrite H.
      intuition.
  + assert(H6:=H).
    apply size_caseD in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor.
    * trivial.
    * apply IHt2.
      trivial.
    * destruct t2.
      -- simpl in H.
         rewrite H.
         constructor.
      -- rewrite bsize_he.
         rewrite H; constructor.
    * rewrite bsize_he.
      inversion H5.
      -- constructor; apply lts.
      -- constructor.
         apply (ltBN_trans (bsize t1) (sucBN (bsize t2)) (sucBN (sucBN (bsize t2)))).
         ++ trivial.
         ++ apply lts.
Qed.

(* Propiedad auxiliar: Si un árbol tiene ambos subárboles de tamaño
   U x1 y U x2, entonces x1 = x2. *)
Lemma bbal_u: forall (t1 t2: BTree) (x: A) (x1 x2: BN), bbal (N x t1 t2) -> bsize t1 = U x1 -> bsize t2 = U x2 -> x1 = x2.
Proof.
induction t1.
+ intros.
  simpl in H0.
  discriminate H0.
+ intros.
  inversion H.
  rewrite H1 in H8.
  rewrite H0 in H8.
  simpl in H8.
  rewrite H1, H0 in H7.
  inversion H7; inversion H8.
  - trivial.
  - inversion H9; inversion H12.
    * trivial.
    * apply ltBN_asym in H17.
      contradiction.
Qed.

Lemma he_last: forall (t: BTree) (x:A), lookup_bn (he x t) (bsize t) = x.
Proof.
induction t.
+ intro.
  simpl.
  trivial.
+ assert (bbal (N a t1 t2)).
  - apply allBal.
  - intro.
    destruct (bsize t1) eqn:det1; destruct (bsize t2) eqn:det2.
    * simpl.
      rewrite det1, det2.
      simpl.
      apply IHt1.
    * assert (~(bbal (N a t1 t2))).
      ++ intro.
         inversion H.
         rewrite det2 in H6; rewrite det1 in H6.
         inversion H6.
         apply z_not_gt in H8.
         trivial.
      ++ contradiction.
    * assert (~(bbal (N a t1 t2))).
      ++ intro.
         inversion H.
         rewrite det2 in H6; rewrite det1 in H6.
         inversion H6.
         apply z_not_gt in H8.
         trivial.
      ++ contradiction.
    * simpl.
      rewrite det1; rewrite det2; simpl.
      inversion H.
      rewrite det1 in H6; rewrite det2 in H6.
      inversion H6.
      ++ apply IHt2.
      ++ inversion H7.
         apply z_not_gt in H12.
         contradiction.
    * simpl.
      rewrite det1, det2.
      simpl.
      inversion H.
      assert (b = b0).
      ++ apply (bbal_u t1 t2 a); trivial.
      ++ rewrite <- H7.
         rewrite plus_U.
         apply IHt1.
    * simpl.
      rewrite det1, det2.
      simpl.
      Admitted.

Lemma he_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (he x t) j = lookup_bn t j.
Admitted. (* Tarea moral *)

(***********************************************
************************************************
************************************************
            EJERCICIOS DE LA TAREA 
************************************************
************************************************
************************************************)

(* Si el árbol izquierdo es E, el derecho también 
   Solo la usamos para árboles balanceados.      *)
Lemma lefte_impl_righte: forall (t t2: BTree) (a:A), bbal t -> t = N a E t2 -> t2 = E.
Proof.
intros.
rewrite H0 in H.
inversion H.
inversion H6.
- apply bsize_Z.
  trivial.
- simpl in H8; apply z_not_gt in H8; contradiction.
Qed.
      
(* EJERCICIO 2 *)
Theorem bsize_lr_pred: forall (t:BTree), t <> E -> bsize (lr t) = predBN (bsize t).
Proof.
intros.
induction t.
+ contradiction.
+ assert (bal:= allBal (N a t1 t2)).
  simpl.
  destruct t1 eqn:quien.
  * assert (t2 = E).
    - apply (lefte_impl_righte (N a E t2) t2 a); trivial.
    - rewrite H0; simpl.
      trivial.
  * rewrite <- quien.
    rewrite <- quien in IHt1.
    simpl.
    destruct (eq_btree_dec t1 E).
    - rewrite e in quien.
      inversion quien.
    - replace (bsize (lr t1)) with (predBN (bsize t1)).
      ++ replace (bsize t2 ⊞ predBN (bsize t1)) with (predBN (bsize t1) ⊞ bsize t2).
         -- replace (sucBN (predBN (bsize t1) ⊞ bsize t2)) with (sucBN (predBN (bsize t1))⊞ bsize t2).
            ** replace (sucBN (predBN (bsize t1))) with (bsize t1).
               +++ replace (predBN (sucBN (bsize t1 ⊞ bsize t2))) with (bsize t1 ⊞ bsize t2).
                   *** trivial.
                   *** rewrite predsucBNinv.
                       trivial.
               +++ rewrite sucpredBNinv.
                   *** trivial.
                   *** apply bsize_nonZ.
                       trivial. 
            ** rewrite plusSuc.
               trivial.
         -- rewrite plusComm; trivial.
      ++ rewrite IHt1.
         -- trivial.
         -- trivial.
Qed.

(* EJERCICIO 3 *)
Theorem bbal_lr: forall (t: BTree), t <> E -> bbal t -> bbal (lr t).
Proof.
induction t.
+ intro; contradiction.
+ intros.
  simpl.
  destruct t1 eqn:quien.
  - constructor.
  - constructor.
    * inversion H0.
      trivial.
    * apply IHt1.
      -- discriminate.
      -- inversion H0; trivial.
    * rewrite bsize_lr_pred.
      -- inversion H0.
         inversion H7.
         ** replace (bsize t2) with (bsize b1 ⊞ bsize b2).
            ++ simpl.
               inversion H10.
               simpl.
               rewrite predsucBNinv.
               constructor.
            ++ apply SucBNinj; trivial.
         ** simpl.
            constructor.
            simpl in H8.
            rewrite predsucBNinv.
            apply suc_lt in H8.
            trivial.
      -- discriminate.
    * rewrite bsize_lr_pred.
      -- rewrite sucpredBNinv.
         ** inversion H0.
            trivial.
         ** apply bsize_nonZ.
            discriminate.
      -- discriminate.
Qed.

(* Lema auxiliar: buscar en el lr un U es lo mismo que buscar en el subárbol derecho. *)
Lemma lookup_lr_right: forall t1 t2 a x, lookup_bn (lr (N a t1 t2)) (U x) = lookup_bn t2 x.
Proof.
intros.
destruct t1, t2.
* simpl; trivial.
* assert (balc := allBal (N a E (N a0 t2_1 t2_2))).
  assert (N a0 t2_1 t2_2 = E).
  - apply (lefte_impl_righte (N a E (N a0 t2_1 t2_2)) (N a0 t2_1 t2_2) a).
    + trivial.
    + trivial.
  - discriminate H.
* simpl.
  trivial.
* simpl.
  trivial.
Qed.

(* Lema auxiliar: buscar en el lr un D es lo mismo que buscar en el lr del izquierdo. *)
Lemma lookup_lr_left: forall t1 t2 a x, t1 <> E -> lookup_bn (lr (N a t1 t2)) (D x) = lookup_bn (lr t1) x.
Proof.
intros.
destruct t1, t2.
+ contradiction.
+ contradiction.
+ simpl.
  trivial.
+ simpl.
  trivial.
Qed.

(* EJERCICIO 4 *)
Theorem lookup_lr: forall t j, t <> E -> lookup_bn (lr t) j = lookup_bn t (sucBN j).
Proof.
induction t.
+ intro; contradiction.
+ intros.
  destruct j eqn:Jota.
  * simpl.
    destruct t1 eqn:T1.
    - trivial.
    - simpl; trivial.
  * simpl sucBN.
    destruct t1 eqn:T1.
    - simpl.
      assert (t2 = E).
      ** apply (lefte_impl_righte (N a E t2) t2 a).
         -- apply allBal.
         -- trivial.
      ** rewrite H0; trivial.
    - simpl.
      trivial.
  * simpl sucBN.
    destruct t1 eqn:T1.
    - simpl.
      trivial.
    - rewrite lookup_lr_left.
      ** rewrite IHt1.
         -- simpl.
            trivial.
         -- discriminate.
      ** discriminate.
Qed.

(* EJERCICIO 5 *)
Theorem lr_le: forall t x, lr (le x t) = t.
Proof.
induction t.
+ intro; reflexivity.
+ intro.
  simpl.
  destruct (le a t2) eqn:Low.
  - destruct t2 eqn:T2.
    * simpl in Low.
      discriminate Low.
    * simpl in Low.
      discriminate Low.
  - rewrite <- Low.
    rewrite IHt2.
    replace a0 with a.
    * trivial.
    * destruct t2 eqn:T2.
      -- simpl in Low.
         inversion Low.
         trivial.
      -- simpl in Low.
         inversion Low; trivial.
Qed.


(* EJERCICIO 6 *)
Theorem le_z_lr: forall t, t <> E -> le (lookup_bn t Z) (lr t) = t.
Proof.
induction t.
+ intro; contradiction.
+ intro.
  simpl lookup_bn.
  simpl.
  destruct t1 eqn:T1.
  - simpl.
    assert (t2 = E).
    * apply (lefte_impl_righte (N a E t2) t2 a).
      -- apply allBal.
      -- trivial. 
    * rewrite H0; trivial.
  - rewrite <- T1.
    simpl le.
    assert (le a0 (lr t1) = t1).
    * assert (lookup_bn (N a0 b1 b2) Z = a0).
      -- reflexivity.
      -- rewrite H0 in IHt1.
         rewrite <- T1 in IHt1.  
         apply IHt1.
         rewrite T1.
         discriminate.
    * rewrite H0; trivial.
Qed.

(* EJERCICIO 7 *)
Theorem bsize_hr_t: forall t, t <> E -> bsize (hr t) = predBN (bsize t).
Proof.
induction t.
+ intro; contradiction.
+ intro.
  destruct t1 eqn:T1.
  * simpl.
    rewrite predsucBNinv.
    assert (t2 = E).
    - apply (lefte_impl_righte (N a E t2) t2 a).
      ** apply allBal.
      ** trivial.
    - rewrite H0; reflexivity.
  * destruct t2 eqn:T2.
    - assert (b1 = E).
      ** assert (Bal := allBal (N a (N a0 b1 b2) E)).
         inversion Bal.
         simpl in H6.
         inversion H6.
         -- replace (U Z) with (sucBN Z) in H9.
            ++ apply SucBNinj in H9.
               apply plusBN_Z_Z in H9.
               destruct H9.
               apply bsize_Z in H8.
               trivial.
            ++ reflexivity.
         -- replace (U Z) with (sucBN Z) in H7.
            ++ apply suc_lt in H7.
               apply z_not_gt in H7.
               contradiction.
            ++ reflexivity.
      ** assert (b2 = E).
         -- apply (lefte_impl_righte (N a0 b1 b2) b2 a0).
            ++ apply allBal.
            ++ rewrite H0.
               trivial.
         -- rewrite H0, H1.
            simpl.
            trivial.
    - rewrite <- T1; rewrite <- T2.
      simpl hr.
      rewrite T1.
      rewrite <- T1.
      destruct (sucBN (bsize t1 ⊞ bsize t2)) eqn:Size.
      ** apply suc_not_z in Size; contradiction.
      ** rewrite <- T1 in IHt1; rewrite <- T2 in IHt2.
         simpl.
         rewrite IHt2.
         -- rewrite predsucBNinv.
            rewrite plusComm.
            rewrite plusSuc.
            rewrite sucpredBNinv.
            ++ rewrite plusComm.
               trivial.
            ++ rewrite T2.
               simpl. 
               apply suc_not_z.
         -- rewrite T2; discriminate.
      ** rewrite <- T1 in IHt1.
         simpl.
         rewrite IHt1.
         -- rewrite plusSuc.
            rewrite sucpredBNinv.
            ++ rewrite predsucBNinv.
               trivial.
            ++ rewrite T1; simpl; apply suc_not_z.
         -- rewrite T1; discriminate.
Qed.

(* EJERCICIO 8 *)
Theorem bbal_hr: forall t, t <> E -> bbal t -> bbal (hr t).
Proof.
induction t.
+ intro; contradiction.
+ intros.
  destruct t1 eqn:T1; destruct t2 eqn:T2.
  - simpl.
    constructor.
  - simpl.
    constructor.
  - assert ((b1 = E) /\ (b2 = E)).
    * inversion H0.
      simpl in H7.
      inversion H7.
      ++ replace (U Z) with (sucBN Z) in H10.
         -- apply SucBNinj in H10.
            apply plusBN_Z_Z in H10.
            destruct H10.
            apply bsize_Z in H9; apply bsize_Z in H10.
            intuition.
         -- reflexivity.
      ++ inversion H8.
         -- apply ZnotSucBN in H12.
            contradiction.
         -- apply z_not_gt in H13.
            contradiction.
         -- apply z_not_gt in H13; contradiction.
   * destruct H1.
     rewrite H1, H2.
     simpl. 
     constructor.
     ++ constructor.
     ++ constructor.
     ++ constructor.
     ++ constructor.
        apply lts.
  - rewrite <- T2.
    destruct (bsize (N a t1 t2)) eqn:Size.
    * simpl in Size.
      apply suc_not_z in Size; contradiction.
    * rewrite <- T1.
      simpl.
      rewrite T1.
      rewrite <- T1.  
      replace (sucBN (bsize t1 ⊞ bsize t2)) with (bsize (N a t1 t2)).
      ++ rewrite Size.
         apply prop_0_U in Size.
         -- rewrite <- T2 in IHt2.
            rewrite <- T1 in H0; rewrite <- T2 in H0; inversion H0.
            constructor.
            ** trivial.
            ** apply IHt2; trivial.
               rewrite T2; discriminate.
            ** rewrite bsize_hr_t.
               +++ inversion H6.
                   *** constructor; apply ltpred.
                       rewrite T2; simpl.
                       apply suc_not_z.
                   *** constructor.
                       apply (ltBN_trans (predBN (bsize t2)) (bsize t2) (bsize t1)).
                       --- apply ltpred.
                           rewrite T2.
                           simpl; apply suc_not_z.
                       --- trivial.
               +++ rewrite T2; discriminate.
            ** rewrite bsize_hr_t.
               +++ rewrite sucpredBNinv.
                   *** destruct Size.
                       rewrite H8, H9; constructor.
                   *** rewrite T2; apply suc_not_z.
               +++ rewrite T2; discriminate.
         -- rewrite T1, T2; trivial.
      ++ simpl.
         trivial.
    * rewrite <- T1.
      simpl.
      rewrite T1.
      rewrite <- T1.
      replace (sucBN (bsize t1 ⊞ bsize t2)) with (bsize (N a t1 t2)).
      ++ rewrite <- T1 in H0; rewrite <- T2 in H0; inversion H0.
         rewrite Size.
         apply prop_0_D in Size.
         -- destruct Size.
            constructor.
            ** rewrite <- T1 in IHt1; apply IHt1.
               +++ rewrite T1; discriminate.
               +++ trivial.
            ** trivial.
            ** rewrite bsize_hr_t. 
               +++ rewrite H8, H9.
                   rewrite predsucBNinv.
                   constructor.
               +++ trivial.
                   rewrite T1; discriminate.
            ** rewrite bsize_hr_t.
               +++ rewrite H8, H9.
                   rewrite predsucBNinv.
                   constructor.
                   apply lts.
               +++ rewrite T1; discriminate.
         -- trivial.
      ++ simpl.
         trivial.
Qed.

(* Lema auxiliar *)
Lemma bal_right_e: forall a b t1 t2, bbal (N a (N b t1 t2) E) -> t1 = E /\ t2 = E.
Proof.
intros.
inversion H.
simpl in H6.
inversion H6.
* destruct t1, t2.
  + intuition.
  + split; trivial.
    simpl in H9.
    replace (U Z) with (sucBN Z) in H9.
    - apply SucBNinj in H9.
      apply suc_not_z in H9; contradiction.
    - reflexivity.
  + split; trivial.
    replace (U Z) with (sucBN Z) in H9.
    - apply SucBNinj in H9.
      simpl in H9.
      rewrite plus_neutro in H9.
      apply suc_not_z in H9; contradiction.
    - reflexivity.
  + replace (U Z) with (sucBN Z) in H9.
    - apply SucBNinj in H9.
      simpl in H9.
      rewrite <- plusSuc in H9.
      apply suc_not_z in H9; contradiction.
    - reflexivity.
* inversion H7.
  + apply ZnotSucBN in H11; contradiction.
  + apply z_not_gt in H12; contradiction.
  + apply z_not_gt in H12; contradiction.
Qed.
    

(* Otro lema auxiliar *)
Lemma d_lt_bal: forall t1 t2 j a, bbal (N a t1 t2) -> D j <BN bsize t1 ⊞ bsize t2 -> j <BN bsize t1 /\ j <BN bsize t2.
Proof.
intros.
inversion H.
inversion H0.
+ destruct (bsize (N a t1 t2)) eqn:Size.
  - simpl in Size.
    apply suc_not_z in Size; contradiction.
  - simpl in Size.
    rewrite <- H9 in Size.
    simpl in Size.
    discriminate Size.
  - destruct (size_case_comb a t1 t2).
    * trivial.
    * rewrite H11 in H9.
      assert (sucBN (U b) = sucBN (bsize t2 ⊞ bsize t2)).
      ++ rewrite H9; trivial.
      ++ rewrite plus_U in H12.
         simpl in H12.
         discriminate H12.
    * rewrite H11 in H9.
      rewrite <- plusSuc in H9.
      rewrite plus_U in H9.
      inversion H9. 
      split.
      ++ rewrite H13 in H10.
         apply (ltBN_trans j (bsize t2) (bsize t1)).
         ** trivial.
         ** rewrite H11.
            apply lts.
      ++ rewrite H13 in H10; trivial.
+ destruct (bsize (N a t1 t2)) eqn:Size.
  * simpl in Size; apply suc_not_z in Size; contradiction.
  * apply size_caseU in Size.
    rewrite Size in H9.
    assert (sucBN (sucBN (bsize t2) ⊞ bsize t2) = D (bsize t2)).
    - apply plus_D.
    - rewrite <- plusSuc in H11.
      rewrite <- H9 in H11.
      simpl in H11.
      inversion H11.
      split.
      ++ rewrite Size; rewrite <- H13.
         apply (ltBN_trans j b (sucBN b)).
         -- trivial.
         -- apply lts.
      ++ apply (ltBN_trans j b (sucBN b)); trivial.
         apply lts.
  * apply size_caseD in Size.
    rewrite Size in H9.
    rewrite <- plusSuc in H9.
    rewrite plus_U in H9.
    inversion H9.
Qed.

(* EJERCICIO 9 *)
Theorem lookup_hr: forall t j, t <> E -> j <> (predBN (bsize t)) -> lookup_bn (hr t) j = lookup_bn t j.
Proof.
induction t.
+ intros.
  contradiction.
+ intros.
  assert (Bal := allBal (N a t1 t2)).
  destruct (bsize (N a t1 t2)) eqn:Size.
  - simpl in Size.
    apply suc_not_z in Size; contradiction.
  - simpl in Size.
    simpl.
    rewrite Size.
    destruct t1 eqn:T1.
    * assert (t2 = E).
      ++ apply (lefte_impl_righte (N a E t2) t2 a).
         -- trivial.
         -- trivial. 
      ++ rewrite H1 in Size.
         simpl in Size.
         inversion Size.
         destruct j eqn:J.
         -- rewrite <- H3 in H0.
            simpl in H0.
            contradiction.
         -- reflexivity.
         -- rewrite H1.
            reflexivity.
    * simpl.
      destruct j eqn:J; trivial.
      apply IHt2.
      destruct t2 eqn:T2.
      ++ rewrite plus_neutro in Size.
         apply bal_right_e in Bal.
         destruct Bal.
         rewrite H1, H2 in Size.
         simpl in Size.
         inversion Size.
      ++ discriminate.
      ++ assert ((bsize t1) = b /\ (bsize t2) = b).
         -- apply (prop_0_U a t1 t2 b).
            rewrite T1.
            trivial.
            rewrite T1; simpl.
            trivial.
         -- destruct H1.
            rewrite H2.
            intro.
            rewrite H3 in H0.
            simpl in H0.
            destruct b eqn:B.
            ** rewrite T1 in H1.
               simpl in H1.
               apply suc_not_z in H1; trivial.
            ** simpl in H0.
               contradiction.
            ** contradiction.
  - simpl.
    destruct t1 eqn:T1.
    ++ assert (t2 = E).
       -- apply (lefte_impl_righte (N a E t2) t2 a).
          ** trivial.
          ** trivial.
       -- rewrite H1 in Size.
          simpl in Size.
          inversion Size.
    ++ simpl in Size.
       destruct (sucBN (bsize t1 ⊞ bsize t2)) eqn:Tamano.
       -- apply suc_not_z in Tamano; contradiction.
       -- rewrite T1 in Tamano.
          simpl in Tamano.
          rewrite Tamano in Size.
          inversion Size.
       -- rewrite T1 in Tamano; rewrite Tamano.
          destruct j eqn:J.
          ** simpl.
             trivial.
          ** replace (lookup_bn (N a (hr (N a0 b0_1 b0_2)) t2) (U b1)) with (lookup_bn (hr (N a0 b0_1 b0_2)) b1).
             *** apply IHt1.
                 --- discriminate.
                 --- simpl in H0.
                     simpl.
                     rewrite predsucBNinv.
                     intro.
                     rewrite <- H1 in Size.
                     assert (bsize t2 = b1).
                     +++ replace (sucBN (sucBN b1 ⊞ bsize t2)) with (bsize (N a t1 t2)) in Size.
                         **** apply size_caseD in Size.
                              rewrite T1 in Size.
                              simpl in Size.
                              rewrite <- H1 in Size.
                              apply SucBNinj.
                              intuition.
                         **** rewrite T1.
                              simpl.
                              rewrite H1; trivial.
                     +++ rewrite H2 in Size.
                         rewrite plus_D in Size.
                         inversion Size.
                         rewrite H4 in H0; contradiction.
             *** reflexivity.
          ** reflexivity.
Qed.

(* EJERCICIO 10 *)
Theorem hr_he: forall t x, hr (he x t) = t.
Proof.
induction t.
+ reflexivity.
+ intro.
  destruct (bsize (N a t1 t2)) eqn:Size.
  - simpl in Size.
    apply suc_not_z in Size; contradiction.
  - simpl in Size.
    simpl.
    rewrite Size.
    simpl.
    destruct (he x t1) eqn:He.
    * assert (HeS := bsize_he t1 x).
      rewrite He in HeS.
      simpl in HeS.
      apply ZnotSucBN in HeS.
      contradiction.
    * rewrite <- He.
      rewrite bsize_he.
      rewrite <- plusSuc.
      rewrite Size.
      simpl.
      rewrite IHt1.
      trivial.
  - simpl in Size.
    simpl.
    rewrite Size.
    simpl.
    assert (Bal := allBal (N a t1 t2)).
    destruct t1 eqn:T1.
    * simpl in Size.
      assert (t2 = E).
      ** apply (lefte_impl_righte (N a E t2) t2 a).
         -- trivial.
         -- trivial.
      ** rewrite H in Size.
         simpl in Size; discriminate Size.
    * rewrite bsize_he.
      rewrite <- plusComm.
      rewrite <- plusSuc.
      rewrite plusComm.
      rewrite Size.
      simpl.
      rewrite IHt2.
      trivial.
Qed.

(* EJERCICIO 11 *)  
Theorem he_lookup_hr: forall t, t <> E -> he (lookup_bn t (predBN (bsize t))) (hr t) = t.
Proof.
induction t.
+ intro; contradiction.
+ intro.
  destruct (bsize (N a t1 t2)) eqn:Size.
  * simpl in Size; apply suc_not_z in Size; contradiction.
  * simpl.
    simpl in Size.
    rewrite Size.
    destruct b eqn:B.
    - replace (U Z) with (sucBN Z) in Size.
      -- apply SucBNinj in Size.
         assert (t1 = E).
         ** apply plusBN_Z_Z in Size.
            destruct Size.
            apply bsize_Z; trivial.
         ** rewrite H0.
            simpl.
            assert (Bal := allBal (N a t1 t2)).
            rewrite H0 in Bal.
            assert (t2 = E).
            ++ apply (lefte_impl_righte (N a E t2) t2 a).
               --- trivial.
               --- trivial.
            ++ rewrite H1; trivial.
      -- reflexivity.
    - destruct t1 eqn:T1.
      -- assert (t2 = E).
            ++ apply (lefte_impl_righte (N a E t2) t2 a).
               --- apply allBal.
               --- trivial.
            ++ rewrite H0 in Size.
               simpl in Size.
               inversion Size.
      -- replace (sucBN (bsize (N a0 b1_1 b1_2) ⊞ bsize t2)) with (bsize (N a t1 t2)) in Size.
         ** assert (Size2:= Size).         
            apply size_caseU in Size.
            simpl in Size2.
            rewrite Size in Size2.
            rewrite plus_U in Size2.
            inversion Size2.
            rewrite <- T1.
            simpl he.
            destruct (sucBN (bsize t1 ⊞ bsize (hr t2))) eqn:UmasD.
            ++ apply suc_not_z in UmasD; contradiction.
            ++ rewrite Size in UmasD.
               --- rewrite bsize_hr_t in UmasD.
                   +++ rewrite H1 in UmasD.
                       assert (exists y, sucBN (U b0 ⊞ predBN (U b0)) = D y).
                       *** apply u_plus_sucu.
                       *** destruct H0.
                           rewrite H0 in UmasD; inversion UmasD.
                   +++ intro.
                       rewrite H0 in H1; simpl in H1; inversion H1.
            ++ rewrite IHt2.
               --- trivial.
               --- intro co; rewrite co in H1; simpl in H1; inversion H1.
         ** rewrite <- T1.
            simpl.
            trivial.
    - destruct t1 eqn:T1.
      -- assert (t2 = E). 
         ** apply (lefte_impl_righte (N a E t2) t2 a);trivial.
            apply allBal.
         ** rewrite H0 in Size; simpl in Size.
            inversion Size.
      -- rewrite <- T1.
         simpl.
         rewrite bsize_hr_t.
         ** assert (bsize t1 = bsize t2).
            --- apply (size_caseU a _ _ (D b0)).
                rewrite T1.
                simpl.
                trivial.
            --- rewrite H0.
                assert (exists x, sucBN (bsize t2 ⊞ predBN (bsize t2)) = D x).
                *** assert (bsize t2 = (D b0)).
                    +++ rewrite <- T1 in Size; rewrite H0 in Size.
                        rewrite plus_U in Size.
                        inversion Size.
                        trivial.
                    +++ rewrite H1.
                        apply d_plus_sucd.
                *** destruct H1.
                    rewrite H1.
                    rewrite <- T1 in Size; rewrite H0 in Size.
                    rewrite plus_U in Size.
                    inversion Size.
                    rewrite H3 in IHt2.
                    simpl in IHt2.
                    rewrite IHt2.
                    ---- trivial.
                    ---- intro C.
                         rewrite C in H3; simpl in H3; inversion H3.
         ** intro C.
            assert (bsize t1 = bsize t2).
            --- apply (size_caseU a _ _ (D b0)).
                rewrite T1; simpl.
                simpl in Size.
                trivial.
            --- rewrite <- T1 in Size.
                rewrite H0 in Size.
                rewrite C in Size; simpl in Size.
                inversion Size.
  * simpl.
    destruct t1 eqn:T1.
    - assert (t2 = E).
      ** apply (lefte_impl_righte (N a E t2) t2 a); trivial.
         apply allBal.
      ** rewrite H0 in Size; simpl in Size; inversion Size.
    - simpl in Size.
      replace (bsize (N a0 b0_1 b0_2)) with (sucBN (bsize b0_1 ⊞ bsize b0_2)).  
      ** rewrite Size.
         rewrite <- T1.
         simpl.
         rewrite bsize_hr_t.
         -- assert (bsize t1 = sucBN (bsize t2)).
            ++ apply (size_caseD a _ _ b).
               rewrite T1.
               simpl.
               trivial.
            ++ rewrite H0.
               rewrite predsucBNinv.
               rewrite plus_U.
               rewrite <- T1 in IHt1.
               replace (he (lookup_bn t1 b) (hr t1)) with t1.
               *** trivial.
               *** replace b with (predBN (bsize t1)).
                   --- rewrite IHt1; trivial.
                       +++ intro C.
                           rewrite C in H0; simpl in H0.
                           apply ZnotSucBN in H0.
                           trivial.
                   --- replace (sucBN (bsize b0_1 ⊞ bsize b0_2)) with (bsize t1) in Size.
                       +++ rewrite H0 in Size.
                           rewrite plus_D in Size.
                           inversion Size.
                           rewrite H2 in H0.
                           rewrite H0.
                           rewrite predsucBNinv.
                           intuition.
                        +++ rewrite T1; simpl.
                            trivial.
         -- rewrite T1; discriminate.
      ** reflexivity.
Qed. 
