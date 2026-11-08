(* ConstructiveWorld-Main - the finite-sum machinery of the finite Euler
   product node: range sums, divisibility tests, reindexing. *)
(** * GaC2_03_a: the finite-sum base leaf of node C2.03.
    Mission.  The finite-sum machinery of the finite Euler product
      node: the generic complex range sum [cxsum] (sum of g d for
      1 <= d <= B), the divisibility test [dvdb] and the
      divisor-indicator sum [dsumCx], with the extension,
      pointwise-extensionality, single-point and
      multiplication-reindexing faces consumed by the node stem's
      main identity.
    Dependencies.  Stdlib [Arith.Arith], [List] (+ [ListNotations]),
      [Bool], [Lia].  Requires [S01_BaseRing] (selective [NatLe]
      import), [S02_CauchyComplete], [S03_QExp], [CxRealPairCore],
      [CxRealPairExpLog], and [GaC2_01_DirichletPartialSum] of this
      development.
    References.  Finite-sum carrier shape aligned with the tree
      precedent abl_Pr_euler_prod.v pze_sumf / pze_lsum faces
      (statement-face alignment only, zero proof-body transplant,
      absorption coeff 0.35).
    Constructivity.  Every named construction is carried by [Set]; the
      Cx equality face [c_eq] and the bool tests are Set-sorted; no
      new Prop statements; every proof closes under the global
      context; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_a.v] compiles cleanly (exit 0), wrapped by
      [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce
      0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import abl_Pr_core_01.
Require Import GaC2_01_DirichletPartialSum.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ==== Section 1. The generic complex range sum ==== *)

(* cxsum g B = sum of g d over d = 1 .. B (empty at B = 0). *)
Fixpoint cxsum (g : nat -> Cx) (B : nat) : Cx :=
  match B with
  | O => c_zero
  | S B' => c_plus (g (S B')) (cxsum g B')
  end.

(* Definitional head equation (pure conversion, usable by c_eq_refl). *)
Lemma cxsum_S : forall (g : nat -> Cx) (B : nat),
  c_eq (cxsum g (S B)) (c_plus (g (S B)) (cxsum g B)).
Proof. intros g B. apply c_eq_refl. Qed.

(* Pointwise extensionality on the summed range. *)
Lemma cxsum_ext : forall (g h : nat -> Cx) (B : nat),
  (forall d : nat, (1 <= d)%nat -> (d <= B)%nat -> c_eq (g d) (h d)) ->
  c_eq (cxsum g B) (cxsum h B).
Proof.
  intros g h B. induction B as [|B' IH]; intros Hag.
  - apply c_eq_refl.
  - apply (c_eq_trans _ (c_plus (g (S B')) (cxsum g B'))).
    + apply c_eq_refl.
    + apply c_plus_congr.
      * apply Hag. lia. lia.
      * apply IH. intros d Hd1 Hd2. apply Hag; lia.
Qed.

(* Right-distributing one scalar across the range (left factor fixed). *)
Lemma cxsum_scalar_l : forall (u : Cx) (g : nat -> Cx) (B : nat),
  c_eq (cxsum (fun d => c_mult u (g d)) B) (c_mult u (cxsum g B)).
Proof.
  intros u g B. induction B as [|B' IH].
  - cbn [cxsum]. apply (c_eq_trans _ (c_mult c_zero u)).
    + apply c_eq_sym. apply c_mult_zero.
    + apply c_mult_comm.
  - apply (c_eq_trans _ (c_plus (c_mult u (g (S B'))) (c_mult u (cxsum g B')))).
    + apply c_plus_congr; [ apply c_eq_refl | exact IH ].
    + apply c_eq_sym. apply c_distrib.
Qed.

(* Right-distributing one scalar on the right of each term. *)
Lemma cxsum_scalar_r : forall (u : Cx) (g : nat -> Cx) (B : nat),
  c_eq (cxsum (fun d => c_mult (g d) u) B) (c_mult (cxsum g B) u).
Proof.
  intros u g B. induction B as [|B' IH].
  - cbn [cxsum]. apply c_eq_sym. apply c_mult_zero.
  - apply (c_eq_trans _ (c_plus (c_mult (g (S B')) u)
                                (cxsum (fun d => c_mult (g d) u) B'))).
    + apply c_eq_refl.
    + apply (c_eq_trans _ (c_plus (c_mult (g (S B')) u) (c_mult (cxsum g B') u))).
      * apply c_plus_congr; [ apply c_eq_refl | exact IH ].
      * apply (c_eq_trans _ (c_mult u (c_plus (g (S B')) (cxsum g B')))).
        -- apply (c_eq_trans _ (c_plus (c_mult u (g (S B'))) (c_mult u (cxsum g B')))).
           ++ apply c_plus_congr; apply c_mult_comm.
           ++ apply c_eq_sym. apply (c_distrib u (g (S B')) (cxsum g B')).
        -- apply (c_mult_comm u (cxsum g (S B'))).
Qed.

(* A sum whose summand is pointwise c_zero collapses to c_zero. *)
Lemma cxsum_range_zero : forall (T : nat -> Cx) (B : nat),
  (forall d : nat, (d <= B)%nat -> c_eq (T d) c_zero) ->
  c_eq (cxsum T B) c_zero.
Proof.
  intros T B HT. induction B as [|B' IH].
  - apply c_eq_refl.
  - apply (c_eq_trans _ (c_plus c_zero c_zero)).
    + apply c_plus_congr.
      * apply HT. lia.
      * apply IH. intros d Hd. apply HT. lia.
    + apply (c_plus_zero c_zero).
Qed.

(* Middle-swap: x + (y + z) = y + (x + z). *)
Lemma c_plus_swap : forall x y z : Cx,
  c_eq (c_plus x (c_plus y z)) (c_plus y (c_plus x z)).
Proof.
  intros x y z.
  apply (c_eq_trans _ (c_plus (c_plus x y) z)).
  - apply c_plus_assoc.
  - apply (c_eq_trans _ (c_plus (c_plus y x) z)).
    + apply c_plus_congr; [ apply c_plus_comm | apply c_eq_refl ].
    + apply c_eq_sym. apply (c_plus_assoc y x z).
Qed.

(* Extending the range by D: cxsum g (B + D) splits into the base part over
   1..B and the zero-extended block over B < d <= B + D. *)
Lemma cxsum_range_ext : forall (g : nat -> Cx) (B D : nat),
  c_eq (cxsum g (B + D))
       (c_plus (cxsum g B)
               (cxsum (fun d => if Nat.ltb B d then g d else c_zero) (B + D))).
Proof.
  intros g B D. induction D as [|D' IH].
  - rewrite Nat.add_0_r.
    assert (Htz : c_eq (cxsum (fun d => if Nat.ltb B d then g d else c_zero) B)
                       c_zero).
    { apply cxsum_range_zero. intros d Hd.
      destruct (Nat.ltb B d) eqn:E.
      - apply Nat.ltb_lt in E. lia.
      - apply c_eq_refl. }
    apply (c_eq_trans _ (c_plus (cxsum g B) c_zero)).
    + apply (c_eq_trans _ (c_plus c_zero (cxsum g B))).
      * apply c_eq_sym. apply (c_plus_zero (cxsum g B)).
      * apply (c_plus_comm c_zero (cxsum g B)).
    + apply c_plus_congr; [ apply c_eq_refl | apply c_eq_sym; exact Htz ].
  - rewrite Nat.add_succ_r.
    set (T := fun d => if Nat.ltb B d then g d else c_zero).
    apply (c_eq_trans _ (c_plus (cxsum g B)
                                (c_plus (if Nat.ltb B (S (B + D'))
                                                then g (S (B + D')) else c_zero)
                                        (cxsum T (B + D'))))).
    + apply (c_eq_trans _ (c_plus (g (S (B + D'))) (cxsum g (B + D')))).
      * apply c_eq_refl.
      * apply (c_eq_trans _ (c_plus (g (S (B + D')))
                                    (c_plus (cxsum g B) (cxsum T (B + D'))))).
        -- apply c_plus_congr; [ apply c_eq_refl | exact IH ].
        -- apply (c_eq_trans _ (c_plus (cxsum g B)
                       (c_plus (g (S (B + D'))) (cxsum T (B + D'))))).
           ++ apply (c_plus_swap (g (S (B + D'))) (cxsum g B) (cxsum T (B + D'))).
           ++ apply c_plus_congr; [ apply c_eq_refl | apply c_eq_sym ].
              ** rewrite (proj2 (Nat.ltb_lt B (S (B + D')))
                                (proj2 (Nat.lt_succ_r B (B + D')) (Nat.le_add_r B D'))).
                 apply c_eq_refl.
    + apply c_eq_refl.
Qed.

(* A sum whose only contributing point is n (with 1 <= n <= B inside the
   range) collapses to the value at n. *)
Lemma cxsum_at : forall (u : Cx) (n B : nat),
  (1 <= n)%nat -> (n <= B)%nat ->
  c_eq (cxsum (fun d => if Nat.eqb d n then u else c_zero) B) u.
Proof.
  intros u n B Hn1 HnB. induction B as [|B' IH].
  - lia.
  - destruct (Nat.eq_dec n (S B')) as [Heq|Hne].
    + subst n.
      apply (c_eq_trans _ (c_plus u c_zero)).
      * apply c_plus_congr.
        -- rewrite Nat.eqb_refl. apply c_eq_refl.
        -- apply cxsum_range_zero. intros d Hd.
           destruct (Nat.eqb d (S B')) eqn:E.
           ++ apply Nat.eqb_eq in E. subst d. lia.
           ++ apply c_eq_refl.
      * apply (c_eq_trans _ (c_plus c_zero u)).
        -- apply c_plus_comm.
        -- apply (c_plus_zero u).
    + assert (HnB' : n <= B') by lia.
      destruct (Nat.eqb (S B') n) eqn:E.
      * apply Nat.eqb_eq in E. lia.
      * apply (c_eq_trans _ (c_plus c_zero u)).
        -- apply c_plus_congr;
           [ rewrite E; apply c_eq_refl | exact (IH HnB') ].
        -- apply (c_plus_zero u).
Qed.

(* Shift face: adding a multiple of q does not change the residue. *)
Lemma mod_shift_mul : forall q m t : nat, (q * m + t) mod q = t mod q.
Proof.
  intros q m t.
  rewrite (Nat.mul_comm q m).
  rewrite <- Nat.Div0.add_mod_idemp_l.
  rewrite Nat.Div0.mod_mul, Nat.add_0_l.
  reflexivity.
Qed.

(* ==== Section 2. Divisibility test and divisor-indicator sum ==== *)

(* Boolean divisibility test dvdb d N (false at d = 0; the sum indices are
   always at least 1, so the zero branch is inert). *)
Definition dvdb (d N : nat) : bool :=
  match d with
  | O => false
  | S d' => Nat.eqb (N mod d) 0
  end.

(* Spec: for d >= 1, dvdb d N = true iff d divides N. *)
Lemma dvdb_spec_true : forall d N : nat, (1 <= d)%nat ->
  dvdb d N = true -> Nat.divide d N.
Proof.
  intros d N Hd Hdvd. destruct d as [|d']; [ lia | ].
  unfold dvdb in Hdvd. apply Nat.eqb_eq in Hdvd.
  apply (pr_mod0_dvd (S d') N); [ exact Hd | exact Hdvd ].
Qed.

Lemma dvdb_spec_false : forall d N : nat, (1 <= d)%nat ->
  dvdb d N = false -> (Nat.divide d N -> False).
Proof.
  intros d N Hd Hdvd Hdiv. destruct d as [|d']; [ lia | ].
  unfold dvdb in Hdvd.
  assert (Hmod : N mod S d' = 0)
    by (apply (pr_dvd_mod0 (S d') N); [ exact Hd | exact Hdiv ]).
  rewrite Hmod in Hdvd. discriminate Hdvd.
Qed.

Lemma dvdb_of_divide : forall d N : nat, (1 <= d)%nat ->
  Nat.divide d N -> dvdb d N = true.
Proof.
  intros d N Hd Hdiv. destruct d as [|d']; [ lia | ].
  unfold dvdb. apply Nat.eqb_eq.
  apply (pr_dvd_mod0 (S d') N); [ exact Hd | exact Hdiv ].
Qed.

(* The divisor-indicator sum: sum of f d over the divisors d of N with
   1 <= d <= N. *)
Definition dsumCx (f : nat -> Cx) (N : nat) : Cx :=
  cxsum (fun d => if dvdb d N then f d else c_zero) N.

(* A divisor beyond N does not exist, hence contributes nothing: the
   divisor sum is unchanged when the range is extended beyond N. *)
Lemma dsumCx_range : forall (f : nat -> Cx) (N E : nat),
  (1 <= N)%nat -> (N <= E)%nat ->
  c_eq (dsumCx f N) (cxsum (fun d => if dvdb d N then f d else c_zero) E).
Proof.
  intros f N E HN1 HNE. unfold dsumCx.
  assert (HE : (N + (E - N) = E)%nat) by lia.
  rewrite <- HE.
  apply c_eq_sym.
  apply (c_eq_trans _ (c_plus (cxsum (fun d => if dvdb d N then f d else c_zero) N)
                              (cxsum (fun d => if N <? d then
                                             (if dvdb d N then f d else c_zero)
                                             else c_zero)
                                     (N + (E - N))))).
  - apply (cxsum_range_ext (fun d => if dvdb d N then f d else c_zero) N (E - N)).
  - apply (c_eq_trans _ (c_plus (cxsum (fun d => if dvdb d N then f d else c_zero) N) c_zero)).
    + apply c_plus_congr;
       [ apply c_eq_refl | apply cxsum_range_zero; intros d Hd ].
      destruct (dvdb d N) eqn:Ed.
      * destruct d as [|d'].
        -- discriminate Ed.
        -- assert (H1d : (1 <= S d')%nat) by lia.
           assert (Hmod : N mod S d' = 0).
           { unfold dvdb in Ed. apply Nat.eqb_eq in Ed. exact Ed. }
           pose proof (Nat.Div0.div_mod N (S d')) as Hdm.
           rewrite Hmod, Nat.add_0_r in Hdm.
           assert (Hq1 : (1 <= N / S d')%nat).
           { destruct (N / S d') as [|q'] eqn:Eq.
             - rewrite Nat.mul_0_r in Hdm. lia.
             - lia. }
           pose proof (Nat.mul_le_mono_r 1 (N / S d') (S d') Hq1) as HSd2.
           rewrite Nat.mul_1_l in HSd2.
           destruct (Nat.ltb N (S d')) eqn:El.
           ++ apply Nat.ltb_lt in El. lia.
           ++ apply c_eq_refl.
      * destruct (Nat.ltb N d) eqn:El.
        ++ apply c_eq_refl.
        ++ apply c_eq_refl.
    + apply (c_eq_trans _ (c_plus c_zero (cxsum (fun d => if dvdb d N then f d else c_zero) N))).
      * apply c_plus_comm.
      * apply (c_plus_zero (cxsum (fun d => if dvdb d N then f d else c_zero) N)).
Qed.

(* ==== Section 3. Multiplication reindexing ==== *)

(* Reindexing face: summing g (d / q) over the q-multiples inside
   1 .. q*M equals the plain range sum of g over 1 .. M. *)
Lemma cxsum_reindex_mul : forall (q M : nat) (g : nat -> Cx),
  (1 <= q)%nat ->
  c_eq (cxsum (fun d => if Nat.eqb (d mod q) 0 then g (d / q) else c_zero)
              (q * M))
       (cxsum g M).
Proof.
  intros q M g Hq1. induction M as [|M' IH].
  - rewrite Nat.mul_0_r. apply c_eq_refl.
  - rewrite Nat.mul_succ_r.
    apply (c_eq_trans _ (c_plus (cxsum (fun d => if Nat.eqb (d mod q) 0 then g (d / q) else c_zero) (q * M'))
                                (cxsum (fun d => if Nat.ltb (q * M') d then (if Nat.eqb (d mod q) 0 then g (d / q) else c_zero) else c_zero) (q * M' + q)))).
    + apply cxsum_range_ext.
    + apply (c_eq_trans _ (c_plus (cxsum g M') (g (S M')))).
      * apply c_plus_congr.
        -- exact IH.
        -- apply (c_eq_trans _ (cxsum (fun d => if Nat.eqb d (q * S M') then g (S M') else c_zero) (q * M' + q))).
           ++ apply cxsum_ext. intros d Hd1 Hd2.
              destruct (Nat.ltb (q * M') d) eqn:E1.
              ** apply Nat.ltb_lt in E1.
                 assert (Htrng : (1 <= d - q * M')%nat /\ (d - q * M' <= q)%nat) by lia.
                 destruct (Nat.eqb (d mod q) 0) eqn:E2.
                 --- apply Nat.eqb_eq in E2.
                     assert (Hsplit : d = q * M' + (d - q * M')) by lia.
                     rewrite Hsplit in E2.
                     rewrite mod_shift_mul in E2.
                     destruct (Nat.eq_dec (d - q * M') q) as [Ht|Ht].
                     { assert (Hd : d = q * S M').
                       { rewrite Ht in Hsplit.
                         rewrite Nat.mul_succ_r. lia. }
                       rewrite Hd.
                       replace ((q * S M') mod q)%nat with 0%nat
                         by (rewrite (Nat.mul_comm q (S M')); symmetry;
                             apply Nat.Div0.mod_mul).
                       replace ((q * S M') / q)%nat with (S M')%nat
                         by (rewrite (Nat.mul_comm q (S M')); symmetry;
                             apply Nat.div_mul; lia).
                       rewrite Nat.eqb_refl.
                       apply c_eq_refl. }
                     { exfalso.
                       destruct Htrng as [Ht1 Ht2].
                       assert (Hltq : (d - q * M' < q)%nat) by lia.
                       rewrite Nat.mod_small in E2 by exact Hltq.
                       lia. }
                 --- destruct (Nat.eqb d (q * S M')) eqn:E3.
                     { apply Nat.eqb_eq in E3. subst d.
                       rewrite (Nat.mul_comm q (S M')) in E2.
                       rewrite Nat.Div0.mod_mul in E2.
                       rewrite Nat.eqb_refl in E2. discriminate E2. }
                     { apply c_eq_refl. }
              ** apply Nat.ltb_ge in E1.
                 destruct (Nat.eqb d (q * S M')) eqn:E3.
                 { apply Nat.eqb_eq in E3. rewrite Nat.mul_succ_r in E3. lia. }
                 { apply c_eq_refl. }
           ++ apply cxsum_at; lia.
      * apply (c_eq_trans _ (c_plus (g (S M')) (cxsum g M'))).
        -- apply c_plus_comm.
        -- apply c_eq_sym. apply (cxsum_S g M').
Qed.
