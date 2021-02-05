(* Importando definiciones. *)
From Tarea3VF Require Export Defs_BN.

(* Imports del profe. *)
Require Import Arith.
(*Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import ArithRing.
Require Import Setoid.
Require Import Omega.*)


Lemma UInj: forall (a b:BN), U a = U b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma DInj: forall (a b:BN), D a = D b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.


Lemma ZnotU: forall (a:BN), Z <> U a.
Proof.
intros.
discriminate.
Qed.

Lemma ZnotD: forall (a:BN), Z <> U a.
Proof.
intros.
discriminate.
Qed.

  (* Lemma UnotD: forall (a:BN), U a <> D a. La cambié por la siguiente. C.V. 29/nov/2016 *)
Lemma UnotD: forall (a b:BN), U a <> D b.
Proof.
intros.
discriminate.
Qed.

Lemma DnotU: forall (a b:BN), D a <> U b. (* La agregué. C.V. 29/nov/2016 *)
Proof.
intros.
discriminate.
Qed.

Lemma bnotU : forall (a:BN), U a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
(*a=D a*)
intuition.
inversion H.
Qed.

Lemma bnotD : forall (a:BN), D a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
(*a=D a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
Qed.

Theorem dec_eq_BN: forall (a b:BN), {a = b} + {a <> b}.
Proof. (* This can be done fully automatic with decide equality *)
intro.
induction a.
+ intro.
  destruct b.
  * left.
    trivial.
  * right; discriminate.
  * right; discriminate.
+ intro.
  destruct b.
  * right; discriminate.
  * destruct (IHa b).
    - rewrite e; left; trivial.
    - right.
      intro c.
      inversion c.
      contradiction.
  * right; discriminate.
+ intro; destruct b.
  * right; discriminate.
  * right; discriminate.
  * destruct (IHa b).
    - rewrite e; left; trivial.
    - right; intro c; inversion c; contradiction.
Qed.

Lemma ZnotSucBN: forall (a:BN), Z <> sucBN a.
Proof.
intros.
induction a.
simpl.
discriminate.
simpl.
discriminate.
simpl.
discriminate.
Qed.

(* Conmutación del lema anterior. *)
Lemma suc_not_z: forall (a:BN), sucBN a <> Z.
Proof.
intro.
intro.
assert (Z <> sucBN a).
+ apply (ZnotSucBN).
+ rewrite H in H0.
  contradiction.
Qed.

Lemma notSucBN : forall (a:BN), a <> sucBN a.
Proof.
intros.
destruct a.
simpl; discriminate.
simpl; discriminate.
simpl; discriminate.
Qed.


Lemma bnNonZ: forall (b:BN), b <> Z -> exists (c:BN), b = U c \/ b = D c.
Proof.
intros.
destruct b.
intuition.
exists b;left;trivial.
exists b;right;trivial.
Qed.

Lemma 
predBNUD: forall (a:BN), a <> Z -> predBN (U a) = D (predBN a).
Proof.
intros.
destruct a.
contradict H.
trivial.
reflexivity.
reflexivity.
Qed.

Lemma U_not: forall (i j :BN), U i <> U j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma D_not: forall (i j :BN), D i <> D j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma predsucBNinv: forall (a:BN), predBN (sucBN a) = a.
Proof.
induction a.
+ reflexivity.
+ reflexivity.
+ simpl.
  destruct (sucBN a) eqn:con.
  * assert (Z <> sucBN a).
    - apply ZnotSucBN.
    - rewrite con in H.
      contradiction.
  * rewrite IHa; reflexivity.
  * rewrite IHa; reflexivity.
Qed.

Lemma sucpredBNinv: forall (a:BN), a <> Z -> sucBN (predBN a) = a.
Proof.
induction a.
+ intro.
  contradiction.
+ intro.
  simpl.
  destruct a.
  - simpl.
    trivial.
  - simpl in IHa.
    simpl.
    rewrite IHa.
    trivial.
    discriminate.
  - reflexivity.
+ intro.
  reflexivity.
Qed.

Lemma toN_sucBN : forall (b : BN), toN(sucBN b) = S(toN b).
Proof.
induction b.
simpl.
trivial.
simpl.
ring.
simpl.
rewrite IHb.
ring.
Qed.

Lemma sucBN_toBN : forall (n : nat), sucBN (toBN n) = toBN (S n).
Proof.
destruct n.
simpl.
trivial.
simpl.
trivial.
Qed.

Lemma inverse_op : forall (n : nat), toN(toBN n) = n.
Proof.
induction n.
simpl.
trivial.
simpl.
rewrite toN_sucBN.
rewrite IHn.
trivial.
Qed.


Lemma SucBNinj: forall (a b : BN), sucBN a = sucBN b -> a = b.
Proof.
induction a.
+ intros.
  destruct b.
  - reflexivity.
  - inversion H.
  - inversion H.
    apply ZnotSucBN in H1.
    exfalso; trivial.
+ intros.
  destruct b.
  - simpl in H.
    inversion H.
  - simpl in H.
    inversion H.
    trivial.
  - simpl in H.
    inversion H.
+ intros.
  destruct b.
  - simpl in H.
    inversion H.
    assert (Z <> sucBN a).
    * apply ZnotSucBN.
    * rewrite H1 in H0.
      contradiction.
  - simpl in H.
    inversion H.
  - simpl in H.
    inversion H.
    apply IHa in H1.
    rewrite H1; trivial.
Qed.

Lemma plusBN_toN : forall (a b : BN), toN(a ⊞ b) = toN a + toN b.
Proof.
intro.
induction a.
simpl.
trivial.
intros.
destruct b.
simpl.
ring.
simpl.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
destruct b.
simpl.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
Qed.



Lemma plus_neutro: forall (b:BN), b ⊞ Z = b.
Proof.
intros.
destruct b.
simpl;trivial.
simpl;trivial.
simpl;trivial.
Qed.

Lemma plus_U: forall (b : BN),  sucBN (b ⊞ b) = U b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite IHb.
trivial.
simpl.
rewrite IHb.
simpl.
trivial.
Qed.



Lemma plus_D: forall (b : BN),  sucBN (sucBN b ⊞ b) = D b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite plus_U.
trivial.
simpl.
rewrite IHb.
trivial.
Qed.


Lemma plusSuc : forall (b c: BN), sucBN (b ⊞ c) = sucBN b ⊞ c.
Proof.
induction b.
+ intro.
  simpl.
  destruct c; reflexivity.
+ intro; destruct c; reflexivity.
+ intro; destruct c.
  * reflexivity.
  * simpl.
    rewrite IHb.
    reflexivity.
  * simpl.
    rewrite IHb.
    reflexivity.
Qed.

Lemma plus_toBN:  forall (n m: nat), toBN(n + m) = toBN n ⊞ toBN m.
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite IHn.
rewrite <- plusSuc.
trivial.
Qed.

(* El sucesor de un número es ese número mas 1 *)
Lemma suc_plus_one_BN: forall (b:BN), sucBN b = b ⊞ U Z.
Proof.
destruct b.
+ reflexivity.
+ simpl.
  rewrite plus_neutro.
  trivial.
+ simpl.
  rewrite plus_neutro.
  reflexivity.
Qed.

Lemma inverse_op_2 : forall (b:BN), toBN(toN b) = b.
Proof.
induction b.
+ reflexivity.
+ simpl.
  rewrite plus_toBN.
  rewrite plus_toBN.
  assert (toN b + 0 = toN b).
  - ring.
  - rewrite H.
    rewrite IHb.
    simpl.
    rewrite <- suc_plus_one_BN.
    apply plus_U.
+ simpl.
  rewrite plus_toBN.
  rewrite plus_toBN.
  assert (toN b + 0 = toN b).
  - ring.
  - rewrite H.
    simpl.
    rewrite IHb.
    destruct b.
    * reflexivity.
    * simpl.
      rewrite plus_neutro.
      rewrite plus_U.
      trivial.
    * simpl.
      rewrite plus_neutro.
      rewrite plus_U.
      reflexivity.
Qed.

Lemma plusComm: forall (a b:BN), (a ⊞ b) = (b ⊞ a).
Proof.
induction a.
+ intro.
  simpl.
  rewrite plus_neutro.
  trivial.
+ intro.
  simpl.
  destruct b eqn:quien.
  * reflexivity.
  * simpl.
    rewrite IHa.
    trivial.
  * simpl.
    rewrite IHa; trivial.
+ intro.
  simpl.
  destruct b; simpl.
  * trivial.
  * rewrite IHa; trivial.
  * rewrite IHa; trivial.
Qed. 

Lemma plusSuc_2 : forall (b c: BN), sucBN (b ⊞ c) = b ⊞ sucBN c.
Proof.
induction b.
+ intro.
  reflexivity.
+ intro.
  simpl.
  destruct c eqn:who.
  * simpl.
    rewrite plus_neutro.
    trivial.
  * reflexivity.
  * simpl.
    rewrite IHb.
    trivial.
+ intro.
  simpl.
  destruct c eqn:who.
  * simpl.
    rewrite plus_neutro.
    trivial.
  * reflexivity.
  * simpl.
    rewrite IHb.
    trivial.
Qed.

Lemma plusBN_Z_Z: forall (x y:BN), x ⊞ y = Z -> x = Z /\ y = Z.
Proof.
intros.
destruct x, y.
+ split;trivial.
+ simpl in H.
  inversion H.
+ simpl in H.
  inversion H.
+ rewrite plus_neutro in H; inversion H.
+ simpl in H; inversion H.
+ simpl in H; inversion H.
+ rewrite plus_neutro in H; inversion H.
+ simpl in H; inversion H.
+ simpl in H; inversion H.
Qed.

Lemma UDCase: forall (x:BN), x <> Z -> exists (b:BN), x = U b \/ x = D b.
Proof.
intros.
destruct x.
intuition.
exists x;left;trivial.
exists x;right;trivial.
Qed.

Lemma suc_not_zero: forall (x:BN), sucBN x <> Z.
Proof.
intros.
destruct x.
simpl;discriminate.
simpl;discriminate.
simpl;discriminate.
Qed.

Lemma addition_a_a : forall (a b:BN), a ⊞ a = b ⊞ b -> a = b.
Proof.
intros.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

Lemma addition_SucBNa_a : forall (a b:BN), sucBN a ⊞ a = sucBN b ⊞ b -> a = b.
Proof.
intros.
rewrite <- plusSuc in H.
rewrite <- plusSuc in H.
apply SucBNinj in H.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

Lemma ltBN_arefl: forall (a:BN), ~ a <BN a.
Proof.
intros.
induction a.
unfold not.
intros.
inversion H.
contradict IHa.
inversion IHa.
trivial.
contradict IHa.
inversion IHa.
trivial.
Qed.

Create HintDb PNatDb.

Hint Resolve ltBN_arefl: PNatDb.

Lemma ltBN_asym: forall (a b:BN), a <BN b -> ~ b <BN a.
Proof.
intros.
induction H.
unfold not;intros.
inversion H.
unfold not;intros.
inversion H.
contradict IHltBN.
inversion IHltBN.
trivial.
unfold not;intros.
inversion H.
apply (ltBN_arefl a).
trivial.
unfold not;intros.
inversion H0.
intuition.
contradict IHltBN.
inversion IHltBN.
rewrite H2 in H.
trivial.
trivial.
contradict IHltBN.
inversion IHltBN.
trivial.
Qed.

Hint Resolve ltBN_asym: PNatDb.

(* Z no es mayor que nadie *)
Lemma z_not_gt: forall (b: BN), ~ b <BN Z.
Proof.
intro.
intro.
inversion H.
Qed.

(* a < D a /\ a < U a *)
Lemma lt_D_U: forall (a: BN), a <BN D a /\ a <BN U a.
Proof.
induction a.
+ split;constructor.
+ split.
  - constructor.
    apply IHa.
  - constructor.
    apply IHa.
+ split.
  - constructor.
    apply IHa.
  - constructor.
    apply IHa.
Qed.

(* a < c -> a < U c /\ a < D c*)
Lemma lt_U_D: forall (a c: BN), a <BN c -> a <BN U c /\ a <BN D c.
Proof.
induction a.
+ intros.
  split; constructor.
+ intros.
  split.
  - inversion H.
    * constructor.
      apply IHa in H1.
      intuition.
    * constructor.
      apply lt_D_U.
    * constructor.
      apply IHa in H1.
      intuition.
  - inversion H.
    * constructor.
      apply IHa in H1.
      intuition.
    * constructor.
      apply lt_D_U.
    * constructor.
      apply IHa in H1.
      intuition.
+ intros.
  split.
  - constructor.
    inversion H.
    * apply IHa in H1.
      intuition.
    * apply IHa in H1.
      intuition.
  - constructor; inversion H.
    * apply IHa in H1; intuition.
    * apply IHa in H1; intuition.
Qed.

(* U a < c -> a < c *)
Lemma u_lt: forall (a c : BN), U a <BN c -> a <BN c.
Proof.
intros.
destruct c.
+ inversion H.
+ inversion H.
  apply lt_U_D.
  assumption.
+ inversion H.
  * apply lt_D_U.
  * apply lt_U_D.
    assumption.
Qed.

Lemma ltBN_tr: forall (b c:BN), b <BN c -> forall (a:BN), a <BN b -> a <BN c.
Proof.
do 3 intro.
induction H.
+ intros.
  inversion H.
+ intros.
  inversion H.
+ intros.
  destruct a0.
  - constructor.
  - constructor.
    inversion H0.
    apply IHltBN.
    assumption.
  - inversion H0.
    constructor.
    apply IHltBN.
    assumption.
+ intros.
  destruct a0.
  - constructor.
  - inversion H; constructor; assumption.
  - inversion H; constructor; assumption.
+ intros.
  destruct a0.
  - constructor.
  - constructor.
    inversion H0.
    apply IHltBN.
    assumption.
  - constructor; inversion H0; apply IHltBN; assumption.
+ intros.
  destruct a0.
  - constructor.
  - constructor; inversion H0.
    * assumption.
    * apply IHltBN.
      assumption.
  - constructor; inversion H0.
    apply IHltBN.
    assumption.
+ intros.
  destruct a0; constructor; inversion H0.
  - assumption.
  - apply IHltBN.
    assumption.
  - apply IHltBN.
    assumption.
Qed.

Hint Resolve ltBN_tr: PNatDb.


Lemma ltBN_trans: forall (a b c:BN), a <BN b -> b <BN c -> a <BN c.
Proof.
intros.
eapply ltBN_tr.
eexact H0.
trivial.
Qed.

Hint Resolve ltBN_trans: PNatDb.

Lemma lt_lteqBN_trans: forall (a b c:BN), a <BN b -> b ≤BN c -> a <BN c.
Proof.
intros.
inversion H0.
rewrite H2 in H.
trivial.
eapply ltBN_trans.
eexact H.
trivial.
Qed.

Hint Resolve lt_lteqBN_trans: PNatDb.

Lemma lteqBN_trans: forall (a b c:BN), a ≤BN b -> b ≤BN c -> a ≤BN c.
Proof.
intros.
inversion H.
trivial.
inversion H0.
rewrite H5 in H.
trivial.
constructor.
eapply ltBN_trans.
eexact H1.
trivial.
Qed.

Hint Resolve lteqBN_trans: PNatDb.

Lemma ltDs: forall (a:BN), (D a) <BN (U (sucBN a)).
Proof.
intros.
induction a.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve ltDs: PNatDb.

Lemma lts: forall (a:BN), a <BN (sucBN a).
Proof.
intros.
induction a.
constructor.
simpl.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve lts: PNatDb.

Lemma lteqs: forall (a:BN), a ≤BN (sucBN a).
Proof.
intros.
induction a.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
inversion IHa.
contradict H0.
apply notSucBN.
trivial.
Qed.

Hint Resolve lteqs: PNatDb.

Lemma ltpred : forall (a:BN), a <> Z -> (predBN a) <BN a.
Proof.
intros.
induction a.
+ contradiction.
+ simpl.
  destruct a.
  * constructor.
  * constructor.
    apply IHa.
    intro.
    inversion H0.
  * constructor.
    apply IHa.
    intro; inversion H0.
+ simpl.
  constructor.
Qed.

Hint Resolve ltpred: PNatDb.

Lemma lte_U_D: forall (a b: BN), a ≤BN b -> U a <BN D b.
Proof.
intros.
induction H.
* constructor.
* constructor.
  assumption.
Qed.

(* Lema auxiliar *)
Lemma U_D_lte: forall (a b: BN), U a <BN D b -> a ≤BN b.
Proof.
destruct a.
+ intros.
  destruct b.
  * constructor.
  * do 2 constructor.
  * do 2 constructor.
+ intros.
  inversion H.
  * constructor.
  * constructor; assumption.
+ intros.
  inversion H.
  * constructor.
  * constructor; assumption.
Qed.

(* Zero <= todos *)
Lemma lte_z: forall (x: BN), Z ≤BN x.
Proof.
intro.
destruct x.
+ constructor.
+ constructor; constructor.
+ constructor; constructor.
Qed.

(* Lema auxiliar *)
Lemma d_lte: forall (a b: BN), D a ≤BN D b -> a ≤BN b.
Proof.
destruct a.
+ intros.
  apply lte_z.
+ intros.
  inversion H.
  * constructor.
  * inversion H0.
    constructor.
    assumption.
+ intros.
  inversion H.
  * constructor.
  * inversion H0.
    constructor; assumption.
Qed.

(* Otro lema auxiliar *)
Lemma lte_d: forall (a b:BN), a ≤BN b -> D a ≤BN D b.
Proof.
induction a.
+ intros.
  destruct b.
  * constructor.
  * do 3 constructor.
  * do 3 constructor.
+ intros.
  inversion H.
  * constructor.
  * do 2 constructor; assumption.
+ intros.
  inversion H.
  * constructor.
  * do 2 constructor; assumption.
Qed. 

Lemma lt1: forall (b a:BN), a <BN (sucBN b) -> a ≤BN b.
Proof.
induction b.
+ intros.
  inversion H.
  - constructor.
  - inversion H2.
  - inversion H2.
+ intros.
  inversion H.
  - apply lte_z.
  - constructor.
  - constructor.
    constructor.
    assumption.
  - constructor.
    constructor.
    assumption.
+ intros.
  inversion H.
  - apply lte_z.
  - constructor.
    apply lte_U_D.
    apply IHb.
    assumption.
  - apply lte_d.
    apply IHb.
    assumption.
Qed.

Hint Resolve lt1: PNatDb.

Lemma lt2: forall (b a:BN), a ≤BN b -> a <BN (sucBN b).
Proof.
induction b.
+ intros.
  destruct a.
  * simpl; constructor.
  * inversion H.
    inversion H0.
  * inversion H.
    inversion H0.
+ intros.
  simpl.
  inversion H.
  * constructor.
  * apply (ltBN_trans a (U b) (D b)).
    - assumption.
    - constructor.
+ intros.
  simpl.
  inversion H.
  * constructor.
    apply lts.
  * destruct a.
    - constructor.
    - constructor.
      apply IHb.
      apply U_D_lte.
      assumption.
    - constructor.
      apply IHb.
      constructor.
      inversion H0.
      assumption.
Qed.

Hint Resolve lt2: PNatDb.

Lemma lteqBN_suc_pred : forall (a b:BN), a <> Z -> a ≤BN (sucBN b) -> (predBN a) ≤BN b.
Proof.
intros.
assert ((predBN a) <BN a).
apply ltpred.
trivial.
assert (predBN a <BN sucBN b).
eapply lt_lteqBN_trans.
eexact H1.
trivial.
apply lt1.
trivial.
Qed.

Hint Resolve lteqBN_suc_pred: PNatDb.

Lemma ltaux1: forall (j:BN), Z ≤BN (D j) -> Z ≤BN j.
Proof.
intros.
apply lte_z.
Qed.

Lemma lteqBN_refl : forall (b:BN), b ≤BN b.
Proof.
intros.
constructor.
Qed.

Lemma lteqBN_Z : forall (b:BN), Z ≤BN b.
Proof.
intros.
destruct b.
constructor.
constructor;constructor.
constructor;constructor.
Qed.

Theorem not_lt_suc: forall (a:BN), ~ exists (b:BN), a <BN b /\ b <BN (sucBN a).
Proof.
induction a.
+ intro.
  destruct H.
  destruct H; destruct x.
  * inversion H.
  * simpl in H0.
    inversion H0.
    destruct x; inversion H3.
  * simpl in H0; inversion H0.
    destruct x; inversion H3.
+ intro.
  destruct H.
  destruct H.
  simpl in H0.
  destruct IHa.
  destruct x.
  * inversion H.
  * inversion H.
    exists x.
    split.
    - assumption.
    - inversion H0.
      ** apply lts.
      ** apply (ltBN_trans x a (sucBN a)).
         ++ assumption.
         ++ apply lts.
  * apply U_D_lte in H.
    inversion H.
    - rewrite H2 in H0.
      apply ltBN_arefl in H0.
      exfalso; assumption.
    - exists x.
      split.
      ** assumption.
      ** inversion H0.
         apply (ltBN_trans x a (sucBN a)).
         ++ assumption.
         ++ apply lts.
+ intro.
  contradict IHa.
  destruct H.
  destruct H.
  * destruct x.
    - inversion H.
    - inversion H.
      exists x.
      split.
      ** assumption.
      ** inversion H0.
         assumption.
   - inversion H.
     exists x.
     split.
     ** assumption.
     ** inversion H0.
        assumption.
Qed.

Lemma trichotomy: forall (a b:BN), a <BN b \/ a=b \/ b <BN a.
Proof.
induction a.
+ intro.
  destruct b.
  - right; left; trivial.
  - left; constructor.
  - left; constructor.
+ intro.
  destruct b.
  - right; right; constructor.
  - destruct (IHa b).
    * left; constructor; trivial.
    * destruct H.
      ++ right; left; rewrite H; trivial.
      ++ right; right; constructor; trivial.
  - destruct (IHa b).
    * left; constructor; trivial.
    * destruct H.
      ++ left; rewrite H; constructor.
      ++ right; right; constructor; trivial.
+ intro.
  destruct b.
  - right; right; constructor.
  - destruct (IHa b).
    * left; constructor; trivial.
    * destruct H.
      ++ right; right; rewrite H; constructor.
      ++ right; right; constructor; trivial.
  - destruct (IHa b).
    * left; constructor; trivial.
    * destruct H.
      ++ right; left; rewrite H; trivial.
      ++ right; right; constructor; trivial.
Qed.

Lemma u_impl_notu: forall(a b: BN), U a ≤BN U b -> a ≤BN b.
Proof.
intros.
inversion H.
+ constructor.
+ constructor.
  inversion H0.
  trivial.
Qed.

Lemma not_lt: forall (a b:BN), b ≤BN a -> ~ a <BN b.
Proof.
induction a.
+ intros.
  destruct b; inversion H.
  - intro.
    inversion H1.
  - intro.
    inversion H3.
  - inversion H0.
  - inversion H0.
+ intros.
  intro.
  destruct b; inversion H0.
  - inversion H.
    * apply u_impl_notu in H.
      apply IHa in H.
      contradiction.
    * apply (ltBN_asym (U a) (U b)).
      ++ trivial.
      ++ trivial.
  - inversion H.
    apply (ltBN_asym (D b) (U a)); trivial.
  - inversion H.
    apply (ltBN_asym (D b) (U a)); trivial.
+ intros.
  intro.
  inversion H.
  * rewrite H2 in H0.
    apply (ltBN_arefl (D a)); trivial.
  * apply (ltBN_asym (D a) b); trivial.
Qed.

Lemma sucBN_lt: forall (a b:BN), sucBN a <> b -> a <BN b -> (sucBN a) <BN b.
Proof.
induction a.
+ intros.
  destruct b.
  - exfalso; apply (ltBN_arefl Z); trivial.
  - simpl.
    constructor.
    destruct b.
    * simpl in H; contradiction.
    * constructor.
    * constructor.
  - simpl.
    apply lte_U_D.
    apply lte_z.
+ intros.
  simpl.
  destruct b.
  - inversion H0.
  - inversion H0.
    constructor.
    trivial.
  - inversion H0.
    * rewrite H3 in H.
      simpl in H.
      contradiction.
    * constructor; trivial.
+ intros.
  simpl.
  destruct b.
  - inversion H0.
  - inversion H0.
    constructor.
    simpl in H.
    assert (sucBN a <> b).
    * intro.
      rewrite H4 in H.
      contradiction.
    * apply IHa.
      -- trivial.
      -- trivial.
  - destruct (dec_eq_BN (sucBN a) b).
    * rewrite e.
      constructor.
    * constructor.
      apply IHa; trivial.
      inversion H0; trivial.
Qed.

Lemma leq_impl_u: forall (a b: BN), a ≤BN b -> U a ≤BN U b.
Proof.
destruct a.
+ intros.
  inversion H.
  - do 2 constructor.
  - do 2 constructor; trivial.
+ intros.
  inversion H; do 2 constructor.
  trivial.
+ intros.
  inversion H; trivial.
  - constructor.
  - do 2 constructor; trivial.
Qed.

Lemma leq_impl_u_d: forall (a b: BN), a ≤BN b -> U a ≤BN D b.
Proof.
destruct a.
+ intros.
  inversion H.
  - do 2 constructor.
  - do 2 constructor; trivial.
+ intros.
  inversion H; do 2 constructor.
  trivial.
+ intros.
  inversion H; trivial.
  - constructor.
    constructor.
  - constructor.
    constructor; trivial.
Qed.

Lemma lt_suc_lteq: forall (a b:BN), a <BN b -> (sucBN a) ≤BN b.
Proof.
induction a.
+ intros.
  simpl.
  destruct b.
  * inversion H.
  * destruct b.
    - constructor.
    - do 3 constructor.
    - do 3 constructor.
  * destruct b.
    - do 2 constructor.
    - do 3 constructor.
    - do 3 constructor.
+ intros.
  simpl.
  destruct b.
  * inversion H.
  * inversion H; do 2 constructor; trivial.
  * inversion H; do 2 constructor; trivial.
+ intros.
  simpl.
  destruct b.
  * inversion H.
  * inversion H.
    apply leq_impl_u.
    apply IHa.
    apply H2.
  * apply leq_impl_u_d.
    apply IHa.
    inversion H; trivial.
Qed. 

Lemma lteqBN_suc: forall (a b:BN), a ≤BN b -> (sucBN a) ≤BN (sucBN b). 
Proof.
intros.
inversion H.
constructor.
apply lt_suc_lteq.
apply lt2.
trivial.
Qed.

(* Next lemmas are used for Okasaki's size *)

Lemma lteqBN_U_U:forall (a b:BN), (U a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_D_D : forall (a b : BN), (D a) ≤BN (D b)-> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_U_D:forall (a b:BN), (U a) ≤BN (D b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
constructor.
trivial.
Qed.

Lemma lteqBN_D_U:forall (a b:BN), (D a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
trivial.
Qed.

Lemma bbalCond_eqs: forall (s t:BN), t ≤BN s -> s ≤BN sucBN t -> s = t \/ s = sucBN t.  (* nov-2016, C.V. *)
Proof.
intros.
inversion H.
intuition.
inversion H0.
intuition.
exfalso.
eapply not_lt_suc.
exists s.
split.
exact H1.
assumption.
Qed.

Lemma lt_U: forall (a b:BN), a <BN b <-> (U a) <BN U b.
Proof.
intros.
split.
+ intro.
  constructor; trivial.
+ intro.
  inversion H; trivial.
Qed.

Lemma lt_D: forall (a b:BN), a <BN b <-> (D a) <BN D b.
Proof.
intros.
split.
+ intro.
  constructor; trivial.
+ intro.
  inversion H; trivial.
Qed.

(* a < suc b -> U a < D b *)
Lemma lt_suc_u_d: forall (a b: BN), a <BN sucBN b -> U a <BN D b.
Proof.
intros.
apply lte_U_D.
apply lt1; trivial.
Qed.

(* Sucesores menores implica menores. *)
Lemma suc_lt: forall (a b: BN), sucBN a <BN sucBN b -> a <BN b.
Proof.
induction a.
+ intros.
  destruct b; simpl in H.
  * inversion H.
    apply z_not_gt in H2.
    contradiction.
  * constructor.
  * constructor.
+ intros.
  destruct b.
  * inversion H.
    apply z_not_gt in H2.
    contradiction.
  * constructor.
    inversion H.
    trivial.
  * inversion H.
    apply lt_suc_u_d.
    trivial.
+ intros.
  destruct b.
  * inversion H.
    apply z_not_gt in H2; contradiction.
  * inversion H.
    - constructor.
      apply lts.
    - constructor.
      apply (ltBN_trans a (sucBN a) b).
      ++ apply lts.
      ++ trivial.
  * inversion H.
    constructor.
    apply IHa.
    trivial.
Qed.

(* Z < S quien sea *)
Lemma z_lt_suc: forall a, Z <BN sucBN a.
Proof.
destruct a.
+ simpl; constructor.
+ simpl; constructor.
+ simpl; constructor.
Qed.

(* 2k+2 < 2k+3 *)
Lemma lt_D_suc: forall a, D a <BN U (sucBN a).
Proof.
induction a.
+ simpl.
  constructor.
  constructor.
+ simpl.
  constructor.
  constructor.
+ simpl.
  constructor.
  apply IHa.
Qed.

(* D a < U b -> suc a < b *)
Lemma D_lt: forall a b, D a <BN U b -> sucBN a ≤BN b.
Proof.
induction a.
+ intros.
  simpl.
  destruct b eqn:B.
  - inversion H.
    inversion H2.
  - destruct b0 eqn:B0.
    * constructor.
    * do 3 constructor.
    * do 3 constructor.
  - destruct b0 eqn:B0.
    * do 2 constructor.
    * do 3 constructor.
    * do 3 constructor.
+ intros.
  simpl.
  destruct b eqn:B.
  - inversion H.
    inversion H2.
  - inversion H.
    constructor.
    constructor.
    inversion H2.
    trivial. 
  - inversion H.
    destruct b0 eqn:B0.
    * inversion H2.
      ++ constructor.
      ++ do 2 constructor; trivial.
    * inversion H2.
      ++ constructor.
      ++ do 2 constructor; trivial.
    * replace (D a) with (sucBN (U a)).
      ++ apply lt_suc_lteq.
         trivial.
      ++ reflexivity.
+ intros.
  destruct b eqn:B.
  - inversion H.
    inversion H2.
  - inversion H.
    simpl.
    apply leq_impl_u.
    apply IHa.
    trivial.
  - inversion H.
    simpl. 
    apply leq_impl_u_d.
    apply IHa.
    constructor.
    inversion H2.
    trivial.
Qed.
 
(* Lema auxiliar, sucesor conserva desigualdad. *)
Lemma suc_le: forall a b, a <BN b -> sucBN a <BN sucBN b.
Proof.
induction a.
+ intros.
  simpl.
  destruct b eqn:B.
  - inversion H.
  - simpl.
    apply lte_U_D.
    destruct b0 eqn:B0; constructor.
    * constructor.
    * constructor.
  - simpl.
    constructor.
    apply z_lt_suc.
+ intros.
  destruct b eqn:B.
  - inversion H.
  - inversion H.
    simpl.
    constructor.
    trivial.
  - simpl.
    inversion H.
    apply U_D_lte in H.
    * inversion H.
      -- constructor.
         apply lts.
      -- apply lt_D_suc.
    * constructor.
      apply (ltBN_trans a b0 (sucBN b0)).
      -- trivial.
      -- apply lts.
+ intros.
  destruct b eqn:B.
  - apply z_not_gt in H; contradiction.
  - simpl.
    apply D_lt in H.
    inversion H.
    * constructor.
    * constructor; trivial.
  - simpl.
    constructor.
    apply IHa.
    inversion H.
    trivial.
Qed.

(* Lema auxiliar *)
Lemma u_plus_sucu: forall b, exists x, sucBN ((U b) ⊞ predBN (U b)) = D x.
Proof.
destruct b.
+ exists Z.
  reflexivity.
+ rewrite predBNUD.
  - simpl.
    exists ((sucBN
       match match b with
             | Z => Z
             | _ => D (predBN b)
             end with
       | Z => U b
       | U y => D (b ⊞ y)
       | D y => U (sucBN (b ⊞ y))
       end)).
    trivial.
  - discriminate.
+ simpl.
  exists (D (sucBN (b ⊞ b))).
  trivial.
Qed.

(* Lema auxiliar *)
Lemma d_plus_sucd: forall b, exists x, sucBN ((D b) ⊞ predBN (D b)) = D x.
Proof.
destruct b.
+ exists (U Z).
  reflexivity.
+ simpl.
  exists (U (sucBN (b ⊞ b))).
  trivial.
+ simpl.
  exists (U (sucBN (sucBN (b ⊞ b)))).
  trivial.
Qed.