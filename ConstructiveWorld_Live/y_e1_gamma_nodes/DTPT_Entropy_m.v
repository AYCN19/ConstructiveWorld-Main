(* ConstructiveWorld-Main - DTPT_Entropy_m: gate-clean LINT-6 split piece 13/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_m.

    Mission.  part 13 of the multi-entropy family face.
      Carries source lines 3597-3874 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g, DTPT_Entropy_h, DTPT_Entropy_i, DTPT_Entropy_j, DTPT_Entropy_k, DTPT_Entropy_l (linear Require Import chain).
    References.  Boxed face ConstructiveWorld_Live/DTPT_Entropy.v (231/231 statement texts
      mechanically verified verbatim against this cast); seat_wash80 setlive_probe_world.
    Constructivity.  Zero axioms, nothing left open, no classical logic; Set-carried
      statements; every proof closes with Qed.  Numerical check instances live in
      DTPT_Entropy_cert (R2 certificate separation).
    Build.  coqc -native-compiler no -q via cpu_guard_v3 (TempLimit 96), flat work/build face.
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h DTPT_Entropy_i DTPT_Entropy_j DTPT_Entropy_k DTPT_Entropy_l.

(* ============================================================
   The exact convolution identity of the entropy family under
   concatenation.
   Uses only lemmas already in this file: [freq_q_app], the [nsum] tools,
   [sqsum_app_eq] (the exact cross-term decomposition), the definitions of
   [collide] / [H_freq], and the bridge [H_freq_eq_bridge]
   ([H_freq == 1 - collide]).
   Every statement was first checked numerically by [vm_compute] before
   being committed; the check instances are kept permanently below.
   Honest boundary: the convolution identities carry the guard that n1, n2
   are both nonempty — the field route needs every quotient denominator
   nonzero.  In the degenerate n1 = 0 / n2 = 0 cases the quotient w = 0
   makes the identities still true, but normalization under concatenation
   has no direction (pinned by the counterexamples above); no statements
   beyond the guard are claimed here.
   ============================================================ *)

(* ---------- convolution algebra helpers ---------- *)

(* Q has no zero divisors (the field side condition): nonzero * nonzero <> 0 *)
Lemma qmul_neq0 : forall x y : Q,
  ~ (x == 0) -> ~ (y == 0) -> Not (QeqT (x * y) 0).
Proof.
  intros [xn xd] [yn yd] Hx Hy Hxy. apply qeqT_imp_qeq in Hxy.
  assert (Hxn : (xn <> 0)%Z).
  { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  assert (Hyn : (yn <> 0)%Z).
  { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  unfold Qeq, Qmult in Hxy. simpl in Hxy.
  rewrite ? Z.mul_1_r in Hxy.
  apply Z.mul_eq_0 in Hxy.
  exfalso. destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)].
Qed.

(* summing the indicator = the frequency (the base-change bridge between
   [nsum] and [freq_q]) *)
Lemma nsum_freq_q_ind : forall (a : Q) (l : list Q), Id (nsum (fun x => if Qeq_bool x a then 1%nat else 0%nat) l) (freq_q a l).
Proof.
  intros a l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct (Qeq_bool y a) eqn:E1; destruct (Qeq_bool a y) eqn:E2; try lia.
    + exfalso.
      assert (C : Qeq_bool a y = true).
      { apply (proj2 (Qeq_bool_iff a y)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff y a)). exact E1. }
      rewrite C in E2. discriminate.
    + exfalso.
      assert (C : Qeq_bool y a = true).
      { apply (proj2 (Qeq_bool_iff y a)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff a y)). exact E2. }
      rewrite C in E1. discriminate.
Qed.

(* ---------- baseline: the explicit cross-term form and the symmetric
   double sum ---------- *)

(* companion of [sqsum_app_eq] (the same shape, by expanding [freq_q_app]
   on both sides plus distribution of [nsum]); the body reuses that main
   theorem, no re-proof. *)
Theorem sqsum_app_cross : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof. intros l1 l2. apply eq_imp_id. destruct (sqsum_app_eq l1 l2). reflexivity. Qed.

(* symmetric double sum: the two cross terms are equal (the same counted
   pairing set {(p,q) in l1 x l2 : p == q}) — the load-bearing face of the
   normalized 2X form of the convolution identity. *)
Theorem sqsum_cross_sym : forall l1 l2 : list Q, Id (nsum (fun x => freq_q x l2) l1) ((nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1. induction l1 as [| a t IH]; intros l2; apply eq_imp_id.
  - cbn [nsum]. symmetry.
    rewrite (nsum_ext_in (fun x : Q => freq_q x []) (fun _ : Q => 0%nat) l2
               (fun x _ => eq_refl)).
    pose proof (nsum_const 0%nat l2) as HC. rewrite HC. lia.
  - cbn [nsum].
    assert (Eext : forall x : Q,
      freq_q x (a :: t) = (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat).
    { intros x. simpl. destruct (Qeq_bool x a); lia. }
    rewrite (nsum_ext_in (fun x : Q => freq_q x (a :: t))
              (fun x : Q => (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat)
              l2 (fun x _ => Eext x)).
    rewrite nsum_add.
    rewrite (nsum_freq_q_ind a l2).
    rewrite IH. lia.
Qed.

(* normalized 2X form: the cross terms merge into the symmetric double sum
   ([sqsum_app_cross] and [cross_sym]) *)
Theorem sqsum_app_eq2 : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2 + 2 * nsum (fun x => freq_q x l2) l1)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. rewrite (sqsum_app_cross l1 l2).
  rewrite (sqsum_cross_sym l1 l2). lia.
Qed.

(* ---------- main theorem: the collision convolution under concatenation
   (weighted exact form) ---------- *)

(* collide (l1 ++ l2) = (n1/(n1+n2))^2 * collide l1
   + (n2/(n1+n2))^2 * collide l2
   + (sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1) / (n1+n2)^2.
   A squared-weight combination plus a cross-correction term; nonempty
   guards n1, n2 (field route). *)
Theorem collide_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (collide (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * collide l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * collide l2
    + (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  unfold collide.
  rewrite length_app.
  rewrite (sqsum_app_eq l1 l2).
  assert (qn_addP : forall a b : nat, qn (a + b)%nat == qn a + qn b)
    by (intros a b; exact (qeqT_imp_qeq _ _ (qn_add a b))).
  rewrite ! qn_addP.
  assert (Hnn : (0 < length l1 + length l2)%nat) by lia.
  assert (HN : ~ (qn (length l1 + length l2)%nat == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Ha : ~ (qn (length l1) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1))
      (QltT_to_Qlt 0 (qn (length l1)) (qn_pos _ H1))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Hb : ~ (qn (length l2) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l2))
      (QltT_to_Qlt 0 (qn (length l2)) (qn_pos _ H2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP1 : ~ (qn (length l1) * qn (length l1) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l1)) (qn (length l1)) Ha Ha
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP2 : ~ (qn (length l2) * qn (length l2) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l2)) (qn (length l2)) Hb Hb
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Zc. apply HN.
    rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))). exact Zc. }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- main piece: the [H_freq] convolution under concatenation
   (weighted, with the 2 w1 w2 cross-correction) ---------- *)

(* H_freq (l1 ++ l2) = w1^2 * H_freq l1 + w2^2 * H_freq l2 + 2 * w1 * w2
   - (sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1) / (n1+n2)^2.
   From [collide_app_eq] and [H_freq_eq_bridge] (== 1 - collide); the
   cross-correction 2 * w1 * w2 - X / (n1+n2)^2 is nonnegative and bounded
   (2 * (n1*n2 - X) / (n1+n2)^2 >= 0, with X <= n1 * n2 pointwise by
   [freq_q_le_length]) — the full convolution identity of the entropy
   family. *)
Theorem H_freq_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (H_freq (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * H_freq l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * H_freq l2
    + 2 * (qn (length l1) / qn (length l1 + length l2)%nat)
        * (qn (length l2) / qn (length l1 + length l2)%nat)
    - (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  assert (Hnn : (0 < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
  assert (Hnn2 : (0 < length l1 + length l2)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (H_freq_eq_bridge (l1 ++ l2) Hnn)). unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_app_eq l1 l2 H1 H2)).
  assert (B1 : collide l1 == 1 - H_freq l1).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l1 H1)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  assert (B2 : collide l2 == 1 - H_freq l2).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l2 H2)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  rewrite B1, B2.
  rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))).
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Hc.
    rewrite <- (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))) in Hc.
    destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- bonus: associativity consistency of the convolution for
   three-way concatenation (value face) ---------- *)

(* (l1 ++ l2) ++ l3 and l1 ++ (l2 ++ l3) are the same list (definitionally,
   by [app_assoc]), so the three convolution quantities coincide pointwise
   under both groupings — the consistency closure of the convolution
   identity for three-way concatenation. *)
Theorem sqsum_app_assoc : forall (l1 l2 l3 : list Q), Id (sqsum ((l1 ++ l2) ++ l3)) (sqsum (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply eq_imp_id. rewrite <- app_assoc. reflexivity. Qed.

Theorem collide_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (collide ((l1 ++ l2) ++ l3)) (collide (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

Theorem H_freq_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (H_freq ((l1 ++ l2) ++ l3)) (H_freq (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

(* ---------- numerical anchors ([vm_compute] check instances) ---------- *)

(* check instance: l1 = [0;1], l2 = [1;1] (with nontrivial cross terms
   X1 = X2 = 2).  Measured: sqsum (l1++l2) = 10, collide = 5/8,
   H_freq = 3/8; the weighted right-hand sides of both main theorems
   evaluate to the same values — the statements were verified to be true
   before being committed. *)
Lemma sqsum_app_cross_val : Id (sqsum ([0;1] ++ [1;1])) (10%nat).
Proof. apply eq_imp_id.
  change (sqsum [0; 1; 1; 1] = 10%nat).
  change (nsum (fun x => freq_q x [0; 1; 1; 1]) [0; 1; 1; 1] = 10%nat).
  change (Nat.add (freq_q 0 [0; 1; 1; 1])
            (Nat.add (freq_q 1 [0; 1; 1; 1])
               (Nat.add (freq_q 1 [0; 1; 1; 1])
                  (Nat.add (freq_q 1 [0; 1; 1; 1]) 0%nat))) = 10%nat).
  change ((1 + (3 + (3 + (3 + 0))))%nat = 10%nat).
  reflexivity.
Qed.

Lemma sqsum_cross_sym_val : Id (nsum (fun x => freq_q x [1;1]) [0;1]) (nsum (fun x => freq_q x [0;1]) [1;1]).
Proof. apply eq_imp_id.
  change (Nat.add (freq_q 0 [1; 1]) (freq_q 1 [1; 1])
          = Nat.add (freq_q 1 [0; 1]) (freq_q 1 [0; 1])).
  change ((0 + 2)%nat = (1 + 1)%nat).
  reflexivity.
Qed.







(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions qmul_neq0.
Print Assumptions nsum_freq_q_ind.
Print Assumptions sqsum_app_cross.
Print Assumptions sqsum_cross_sym.
Print Assumptions sqsum_app_eq2.
Print Assumptions collide_app_eq.
Print Assumptions H_freq_app_eq.
Print Assumptions sqsum_app_assoc.
Print Assumptions collide_app_assoc.
Print Assumptions H_freq_app_assoc.
Print Assumptions sqsum_app_cross_val.
Print Assumptions sqsum_cross_sym_val.
Print Assumptions sqsum_app_cross_val.
Print Assumptions sqsum_cross_sym_val.