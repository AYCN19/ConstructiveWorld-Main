(* ConstructiveWorld-Main - the self-audit-and-measure-bridge stem of the DTPT base library *)

(** * DTPT_m: the self-audit-and-measure-bridge stem of the DTPT base library (stem M of fourteen).

    Mission.  the zero-assumed-constant self-audit of the M2 merged family (section J, nine main theorems) and results segment F2: the cozero-ideal and empirical-measure bridge (section 15, the mu_fiber faces over the Measure x CoZero composition).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g], [DTPT_h], [DTPT_i], [DTPT_j], [DTPT_k], [DTPT_l]

    References.  the DTPT base library of the constructive development (the judged-code truth-predicate line); statements conserved verbatim from the boxed original piece; consumed by the later stems of this node.

    Constructivity.  All carriers [Set]; conclusions in Set-valued order
    predicates and equality forms; zero assumed constants; zero admissions;
    every proof closes by Qed.

    Build.  [coqc -q -native-compiler no] under the acceptance build
    faces, [cpu_guard v3] wrapped. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.
Require Import DTPT_a.
Require Import DTPT_b.
Require Import DTPT_c.
Require Import DTPT_d.
Require Import DTPT_e.
Require Import DTPT_f.
Require Import DTPT_g.
Require Import DTPT_h.
Require Import DTPT_i.
Require Import DTPT_j.
Require Import DTPT_k.
Require Import DTPT_l.
(* ========== section J, the zero-assumed-constant self-audit (the 9 main theorems of the M2 merged family, concentrated at the file tail:
   the PmidEnd face, 3 pieces + the OrgDiff face, 6 pieces) ========== *)
Print Assumptions Pmid_len_endpoint.
Print Assumptions Pmid_len_perm.
Print Assumptions Pmid_len_spectrum.
Print Assumptions P0_absorbs_Pmid_len.
Print Assumptions OrgDiff_eq.
Print Assumptions OrgDiff_nonneg.
Print Assumptions OrgDiff_nonneg_dec.
Print Assumptions OrgDiff_Pmid_len_zero.
Print Assumptions OrgDiff_Pmid_general_nonzero.

(* ============================================================
   section 15, results segment F2: the F5 cozero-ideal and empirical-measure bridge
   composition of the on-disc active pieces (zero fabrication): section-12 Measure (the freq/mu/sumf/dedup/qsum
   faces) x section-13 CoZero (fiber = the zero-tested filter sublist).
   bridge theorems:
   - mu_fiber_pos (floor piece 1, the measure positivity of zero-tested membership): a member of the zero fiber has
     strictly positive mass under the world measure - a direct push of the In x w component of fiber_in times the member frequency >= 1;
   - mu_fiber_mass_lb (floor piece 2, the main bridge, the empirical-frequency lower bound of the fiber mass):
     the w-measure mass over the fiber support is >= the zero empirical frequency |fiber|/|w| - pointwise
     frequencies do not increase along filter sublists + sum_freq_dedup mass conservation, closed by order-preserving multiplication with the same Q denominator;
     closing in the order-preserving direction;
   - mu_fiber_mass_eq (bonus, the explicit mass-conservation form): equality when phi is Qeq-extensional along the support -
     the empirical frequency of P_phi(0) is exactly the w-measure mass of the fiber
     (the zero-weighted generalization of mu_total_mass; at f := the constant zero it degenerates to the original piece).
   honest note: a general phi is non-extensional (the section-13 section-2 header counterexample: phi reads the low bits of the Qnum),
   so the main bridge guarantees only >=, not =; the equality face needs an extensionality guard, not a forced splice.
   dependencies: everything goes through the active pieces of sections 12/13 + stdlib Q order lemmas (the registered names
   Qmult_le_compat_r/Qmult_lt_0_compat/Qinv_lt_0_compat etc.).
   ============================================================ *)

(* ---------- section 15.0, load-bearing piece: member frequency positivity ---------- *)

(* a member of the world list implies at least one vote (the positive dual of freq_zero_of_notQmem) *)
Lemma freq_pos_of_in : forall (l : list Q) (x : Q),
  In x l -> (1 <= freq l x)%nat.
Proof.
  intros l x. induction l as [| a t IH]; intros Hin.
  - destruct Hin.
  - simpl. destruct (Qeq_bool a x) eqn:Eax.
    + lia.
    + destruct Hin as [Ha | Hin].
      * exfalso.
        assert (Ht : Qeq_bool a x = true).
        { rewrite Ha. apply (proj2 (Qeq_bool_iff x x)). apply Qeq_refl. }
        rewrite Ht in Eax. discriminate.
      * specialize (IH Hin). lia.
Qed.

(* ---------- section 15.1, load-bearing piece: pointwise frequencies do not increase along filter sublists ---------- *)

Lemma freq_filter_le : forall (g : Q -> bool) (l : list Q) (x : Q),
  (freq (filter g l) x <= freq l x)%nat.
Proof.
  intros g l x. induction l as [| a t IH].
  - simpl. lia.
  - simpl. destruct (g a); simpl.
    + destruct (Qeq_bool a x); lia.
    + destruct (Qeq_bool a x); lia.
Qed.

(* ---------- section 15.2, load-bearing piece: sumf is pointwise monotone on the right ---------- *)

Lemma sumf_mono_r : forall (m l1 l2 : list Q),
  (forall y : Q, (freq l1 y <= freq l2 y)%nat) ->
  (sumf m l1 <= sumf m l2)%nat.
Proof.
  intros m l1 l2 H. induction m as [| a t IH]; simpl.
  - lia.
  - specialize (H a). lia.
Qed.

(* ---------- section 15.3, load-bearing piece: the w-measure sum over the fiber support (the Q-side carrying) ---------- *)

(* the de-mass-one-ified skeleton of mu_total_mass: the w-measure sum over an arbitrary index list m
   = the sumf quotient (no Qnodup guard; shared by the two main-bridge pieces) *)
Lemma qsum_map_mu_w : forall (w m : list Q),
  qsum (map (mu w) m)
  == (Z.of_nat (sumf m w) # 1)%Q / (Z.of_nat (length w) # 1)%Q.
Proof.
  intros w m.
  assert (Hfun : forall y : Q,
           mu w y = ((Z.of_nat (freq w y) # 1) / (Z.of_nat (length w) # 1))%Q)
    by (intros y; reflexivity).
  rewrite (map_ext (mu w)
             (fun y => ((Z.of_nat (freq w y) # 1) / (Z.of_nat (length w) # 1))%Q)
             Hfun).
  rewrite (qsum_map_div (Z.of_nat (length w) # 1)%Q
                        (fun y => (Z.of_nat (freq w y) # 1)%Q)).
  rewrite (qsum_freq_map w m).
  reflexivity.
Qed.

(* ---------- section 15.4, floor piece 1: the measure positivity of zero-tested membership ---------- *)

(* x lands in the zero fiber implies x lands in the world implies at least one vote implies the uniform measure is strictly positive
   - the shortest composition face of 'fiber is filter, mu is freq over length' *)
Theorem mu_fiber_pos : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> 0 < mu w x.
Proof.
  intros f w x Hin.
  apply fiber_in in Hin. destruct Hin as [Hin _].
  assert (Hf : (1 <= freq w x)%nat) by (apply freq_pos_of_in; exact Hin).
  assert (Hn : (1 <= length w)%nat).
  { destruct w as [| a t].
    - destruct Hin.
    - simpl. lia. }
  assert (Hnum : 0 < (Z.of_nat (freq w x) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_lt 0 (freq w x))). lia. }
  assert (Hden : 0 < (Z.of_nat (length w) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_lt 0 (length w))). lia. }
  unfold Qdiv. apply Qmult_lt_0_compat.
  - exact Hnum.
  - apply (Qinv_lt_0_compat (Z.of_nat (length w) # 1)%Q). exact Hden.
Qed.

(* ---------- section 15.5, floor piece 2 (the main bridge): the empirical-frequency lower bound of the fiber mass ---------- *)

(* the sum of the world-measure masses over the fiber support is >= |fiber|/|w| = the empirical frequency of P_phi(0):
   each zero vote is charged at least once under the w-measure (a non-extensional phi only adds, never omits) *)
Theorem mu_fiber_mass_lb : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  ((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q
  <= qsum (map (mu w) (dedup (fiber f w))).
Proof.
  intros f w Hne.
  assert (Hpos : (1 <= Z.of_nat (length w))%Z).
  { apply (proj1 (Znat.Nat2Z.inj_le 1 (length w))).
    destruct w as [| a t]; [exfalso; apply Hne; reflexivity | simpl; lia]. }
  assert (HDne : ~ ((Z.of_nat (length w) # 1)%Q == 0%Q)).
  { intros Hc. unfold Qeq in Hc. simpl in Hc. lia. }
  assert (HDpos : 0 < (Z.of_nat (length w) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r. lia. }
  assert (Hnat : (length (fiber f w)
                  <= sumf (dedup (fiber f w)) w)%nat).
  { assert (H1 : (sumf (dedup (fiber f w)) (fiber f w)
                  <= sumf (dedup (fiber f w)) w)%nat).
    { apply sumf_mono_r. intros y. unfold fiber. apply freq_filter_le. }
    pose proof (sum_freq_dedup (fiber f w)) as H2.
    unfold Sigma_freq in H2. lia. }
  assert (HQ : ((Z.of_nat (length (fiber f w)) # 1)
                <= (Z.of_nat (sumf (dedup (fiber f w)) w) # 1))%Q).
  { unfold Qle. rewrite !Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_le (length (fiber f w))
                                    (sumf (dedup (fiber f w)) w))).
    exact Hnat. }
  rewrite (qsum_map_mu_w w (dedup (fiber f w))).
  unfold Qdiv. apply Qmult_le_compat_r.
  - exact HQ.
  - apply (Qlt_le_weak 0 (/ (Z.of_nat (length w) # 1)%Q)).
    apply (Qinv_lt_0_compat (Z.of_nat (length w) # 1)%Q). exact HDpos.
Qed.

(* ---------- section 15.6, load-bearing piece: the record-level membership preservation of dedup ---------- *)

Lemma dedup_aux_In_l : forall (x : Q) (l : list Q) (y : Q),
  In y (dedup_aux x l) -> In y l.
Proof.
  intros x l y. induction l as [| a t IH]; simpl; intros Hc.
  - destruct Hc.
  - destruct (Qeq_bool x a).
    + right. apply IH. exact Hc.
    + destruct Hc as [Heq | Hc].
      * left. exact Heq.
      * right. apply IH. exact Hc.
Qed.

Lemma dedup_In_l : forall (l : list Q) (y : Q),
  In y (dedup l) -> In y l.
Proof.
  intros l y. induction l as [| a t IH]; simpl; intros Hc.
  - destruct Hc.
  - destruct Hc as [Heq | Hc].
    + left. exact Heq.
    + right. apply dedup_aux_In_l in Hc. apply IH. exact Hc.
Qed.

(* ---------- section 15.7, load-bearing piece: filter preserves frequencies for extensional phi ---------- *)

(* general form: if the zero-tester opens true on every Qeq-twin of y, the vote count of y is unchanged across filter *)
Lemma freq_filter_eq_all : forall (g : Q -> bool) (l : list Q) (y : Q),
  (forall a : Q, In a l -> a == y -> g a = true) ->
  freq (filter g l) y = freq l y.
Proof.
  intros g l y. induction l as [| a t IH]; intros Hall.
  - reflexivity.
  - simpl. destruct (g a) eqn:Ega.
    + simpl. rewrite (IH (fun a0 Ha0 => Hall a0 (or_intror Ha0))).
      destruct (Qeq_bool a y); reflexivity.
    + destruct (Qeq_bool a y) eqn:Eay2.
      * exfalso.
        assert (Ht : g a = true).
        { apply (Hall a (or_introl eq_refl)).
          exact (proj1 (Qeq_bool_iff a y) Eay2). }
        rewrite Ht in Ega. discriminate.
      * rewrite (IH (fun a0 Ha0 => Hall a0 (or_intror Ha0))). reflexivity.
Qed.

(* the extensional-phi instance: the zero fiber keeps every vote of each zero y *)
Lemma freq_w_fiber_eq : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (w : list Q) (y : Q), Qeq_bool (f y) 0 = true ->
  freq (fiber f w) y = freq w y.
Proof.
  intros f Hf w y Hy. unfold fiber.
  apply (freq_filter_eq_all (fun x => Qeq_bool (f x) 0) w y).
  intros a _ Ha. apply Qeqb_true_of.
  apply (Qeq_trans (f a) (f y) 0).
  - apply Hf. exact Ha.
  - apply (proj1 (Qeq_bool_iff (f y) 0)). exact Hy.
Qed.

(* the pointwise-equality transport of sumf on the right *)
Lemma sumf_ext : forall (m l1 l2 : list Q),
  (forall y : Q, In y m -> freq l1 y = freq l2 y) ->
  sumf m l1 = sumf m l2.
Proof.
  intros m l1 l2. induction m as [| a t IH]; intros H; simpl.
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* ---------- section 15.8, bonus piece: the explicit mass-conservation form of the fiber mass ---------- *)

(* equality when phi is extensional along the support: the empirical frequency |fiber phi w|/|w| of P_phi(0)
   is exactly the w-measure mass over the fiber support - not a single zero vote is left uncharged to the fiber.
   at f := the constant zero, fiber = w, degenerating to the section-12 mu_total_mass (the consistency cross-check). *)
Theorem mu_fiber_mass_eq : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  (forall x y : Q, x == y -> f x == f y) ->
  qsum (map (mu w) (dedup (fiber f w)))
  == ((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q.
Proof.
  intros f w Hne Hf.
  assert (Hsum : sumf (dedup (fiber f w)) w = length (fiber f w)).
  { rewrite (sumf_ext (dedup (fiber f w)) w (fiber f w)).
    - rewrite <- (sum_freq_dedup (fiber f w)). reflexivity.
    - intros y Hy. apply eq_sym.
      apply freq_w_fiber_eq; [exact Hf |].
      destruct (proj1 (fiber_in f w y) (dedup_In_l (fiber f w) y Hy))
        as [_ Hb].
      exact Hb. }
  rewrite (qsum_map_mu_w w (dedup (fiber f w))).
  rewrite Hsum. reflexivity.
Qed.

(* ---------- section 15.9, final audit: Print Assumptions (the G4 gate) ---------- *)

Print Assumptions mu_fiber_pos.
Print Assumptions mu_fiber_mass_lb.
Print Assumptions mu_fiber_mass_eq.

