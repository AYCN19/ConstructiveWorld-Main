(* ConstructiveWorld-Main - the Real-level transport kit from rational
   precision statements to arbitrary carriers. *)

(** * UpReqPadeTailPos_e: Q-to-Real embedding bridges, series
      bridges, and the Real-level Pade lower-bound transport.

    Mission.  The Q-level small combinators ([qtr_qlt_sub],
      [qtr_div2_lt], [qtr_div2_ltT], [qtr_div_cancel]); the
      embedding order bridges ([qtr_embed_mono], [qtr_embed_le]):
      rational order carries into the Real embedding with the
      half-gap witness; the series bridges ([qtr_partial_gap],
      [qtr_exp_gt_partial], [qtr_exp_ge_partial]): the exponential
      exceeds every partial sum by more than half the next term;
      the left congruence of real_mult over real_eq; and the
      transport statements [qtr_pade_lower_real], its sigT
      extraction form [qtr_pade_lower_extract] (eps = y^5/720,
      N = 6), and the weak companion [qtr_pade_lower_real_le].
    Dependencies.  S01_BaseRing through S15_TailFEPUp, UpReqPadeExp,
      UpReqQExpTail, UpReqPadeLower (the library edition of the
      strict lower bound); Stdlib QArith, Qabs, Arith, Lia, Setoid,
      Morphisms.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos (its fourth section).
    Constructivity.  Pure Set-level content; the real_lt statements
      are sigT witness forms with explicit rational witnesses; no
      classical principles, no axioms; every audited name is Closed
      under the global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, temperature guard wrapped.
*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeLower.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia Setoid.
From Stdlib Require Import Setoid Morphisms.

Local Open Scope Q_scope.

(* ===== B0 bridges: small Q-level combinators ===== *)

(* a < b implies 0 < b - a (QltT face).  Route: Qplus_lt_r with
   z := -a plus setoid reshaping through Qplus_opp_r and Qplus_comm;
   Qminus b a is definitionally b + (-a). *)
Lemma qtr_qlt_sub : forall a b : Q, QltT a b -> QltT 0 (b - a).
Proof.
  intros a b H.
  assert (Hlt : Qlt a b) by (apply QltT_to_Qlt; exact H).
  assert (H1 : Qlt (- a + a) (- a + b)).
  { exact (proj2 (Qplus_lt_r a b (- a)) Hlt). }
  apply Qlt_to_QltT.
  setoid_rewrite (Qplus_comm (- a) a) in H1.
  setoid_rewrite (Qplus_opp_r a) in H1.
  setoid_rewrite (Qplus_comm (- a) b) in H1.
  exact H1.
Qed.

(* 0 < x implies x/2 < x (strict half contraction). *)
Lemma qtr_div2_lt : forall x : Q, Qlt 0 x -> Qlt (x / 2) x.
Proof.
  intro x. unfold Qlt in *.
  destruct x as [nx dx]. simpl in *. lia.
Qed.

Lemma qtr_div2_ltT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply Qlt_to_QltT. apply qtr_div2_lt.
  apply QltT_to_Qlt. exact H.
Qed.

(* Cancellation certificate: m /= 0 implies (a/m)*m == a. *)
Lemma qtr_div_cancel : forall a m : Q, ~ (m == 0) -> a / m * m == a.
Proof.
  intros a m Hm. unfold Qdiv.
  rewrite <- (Qmult_assoc a (/ m) m).
  rewrite (Qmult_comm (/ m) m).
  rewrite (Qmult_inv_r m Hm).
  apply Qmult_1_r.
Qed.

(* ===== G1 embedding order bridges: rational order into the Real
   embedding ===== *)

(* Strict form: a < b implies real_const a < real_const b.
   Witness eps := (b-a)/2 > 0 and N := 0 (constant sequences agree
   pointwise). *)
Theorem qtr_embed_mono : forall a b : Q, QltT a b ->
  real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (Hsub : QltT 0 (b - a)) by (apply qtr_qlt_sub; exact Hab).
  assert (Hhalf : QltT ((b - a) / 2) (b - a)) by (apply qtr_div2_ltT; exact Hsub).
  unfold real_lt.
  exists ((b - a) / 2)%Q. split.
  - apply qltT_div_pos.
    + exact Hsub.
    + exact qltT_0_2.
  - exists 0%nat. intros n _.
    assert (Hraw : projT1 (real_const b) n - projT1 (real_const a) n
                   == b - a).
    { apply Qminus_comp; apply real_const_proj. }
    apply qltT_eq_compat_r with (a' := (b - a)%Q).
    + exact Hraw.
    + exact Hhalf.
Qed.

(* Weak form: a <= b implies real_const a <= real_const b (the strict
   branch through the embedding bridge; the Id-equal branch through
   the Qabs zero congruence). *)
Theorem qtr_embed_le : forall a b : Q, QleT a b ->
  real_le (real_const a) (real_const b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | H0].
  - left. apply qtr_embed_mono. exact Hlt.
  - right. intros eps Heps. exists 0%nat. intros n _.
    assert (Hab0 : a - b == 0).
    { destruct H0. ring. }
    assert (Habs0 : Qabs (projT1 (real_const a) n
                          - projT1 (real_const b) n) == 0).
    { apply Qeq_trans with (y := Qabs (a - b)).
      - apply Qabs_wd. apply Qminus_comp; apply real_const_proj.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. exact Hab0.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ===== G1 series pier: the Q-level tail-gap lower bound ===== *)

(* First omitted term bounds the tail gap: 0 <= y and d >= 0 imply
   y^(n+1)/(n+1)! <= E_{n+1+d}(y) - E_n(y).  Induction: each step
   appends a nonnegative term y^k/k!. *)
Lemma qtr_partial_gap : forall (y : Q) (n d : nat), QleT 0 y ->
  Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
      (exp_partial (Datatypes.S n + d) y - exp_partial n y).
Proof.
  intros y n d Hy. revert d.
  assert (Hy0 : Qle 0 y) by (apply qtail_QleT_to_Qle; exact Hy).
  induction d as [| d IH].
  - replace (Datatypes.S n + 0)%nat with (Datatypes.S n)%nat by lia.
    change (exp_partial (Datatypes.S n) y) with
      (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    (* atomize the quotient: ring treats the Qdiv atom *)
    set (T := q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    apply qeq_imp_qle. ring.
  - replace (Datatypes.S n + Datatypes.S d)%nat
      with (Datatypes.S (Datatypes.S n + d))%nat by lia.
    change (exp_partial (Datatypes.S (Datatypes.S n + d)) y) with
      (exp_partial (Datatypes.S n + d) y
       + q_pow y (Datatypes.S (Datatypes.S n + d))
         / q_fact (Datatypes.S (Datatypes.S n + d))).
    set (T2 := q_pow y (Datatypes.S (Datatypes.S n + d))
                 / q_fact (Datatypes.S (Datatypes.S n + d))).
    apply (Qle_trans _
             ((exp_partial (Datatypes.S n + d) y - exp_partial n y) + T2)%Q _).
    + (* first term <= old gap <= old gap plus the new nonnegative term *)
      apply (Qle_trans _ (exp_partial (Datatypes.S n + d) y - exp_partial n y) _).
      * exact IH.
      * apply qtail_le_plus_r.
        unfold T2. apply q_pow_fact_nonneg. exact Hy0.
    + (* reshaping: (E - F) + T2 == E + T2 - F (quotient atomized for ring) *)
      apply qeq_imp_qle. ring.
Qed.

(* ===== G1 series bridge: the Real-level exp y >= nth partial sum ===== *)

(* Strict form: y > 0 implies real_const(E_n(y)) < e^y.
   Witness eps := (y^(n+1)/(n+1)!)/2 and N := n+1; the pointwise gap
   E_m(y) - E_n(y) is at least y^(n+1)/(n+1)!, hence above eps. *)
Theorem qtr_exp_gt_partial : forall (y : Q) (n : nat), QltT 0 y ->
  real_lt (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy.
  assert (Hterm : QltT 0 (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
  { apply qltT_div_pos.
    - apply Qlt_to_QltT. apply (cpl_qpow_pos y (Datatypes.S n)).
      apply QltT_to_Qlt. exact Hy.
    - apply Qlt_to_QltT. apply q_fact_pos. }
  unfold real_lt.
  exists (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)%Q.
  split.
  - apply qltT_div_pos.
    + exact Hterm.
    + exact qltT_0_2.
  - exists (Datatypes.S n). intros m Hm.
    assert (Hle : (Datatypes.S n <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hraw : projT1 (cauchy_real_exp (real_const y)) m
                   - projT1 (real_const (exp_partial n y)) m
                   == exp_partial m y - exp_partial n y).
    { apply Qminus_comp.
      - apply exp_const_proj.
      - apply real_const_proj. }
    assert (Hgap : Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
                       (exp_partial m y - exp_partial n y)).
    { replace m with (Datatypes.S n + (m - Datatypes.S n))%nat by lia.
      apply qtr_partial_gap.
      left. exact Hy. }
    assert (HgapT : QltT (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)
                         (exp_partial m y - exp_partial n y)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      - apply qtr_div2_lt. apply QltT_to_Qlt. exact Hterm.
      - exact Hgap. }
    apply qltT_eq_compat_r with (a' := (exp_partial m y - exp_partial n y)%Q).
    + exact Hraw.
    + exact HgapT.
Qed.

(* Weak form: y >= 0 implies real_const(E_n(y)) <= e^y (the strict
   branch through the series bridge; the y == 0 branch through the
   all-ones partial sum congruence). *)
Theorem qtr_exp_ge_partial : forall (y : Q) (n : nat), QleT 0 y ->
  real_le (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy. destruct Hy as [Hlt | H0].
  - left. apply qtr_exp_gt_partial. exact Hlt.
  - assert (H0q : 0 == y) by (destruct H0; apply Qeq_refl).
    assert (Hn1 : exp_partial n y == 1%Q).
    { apply Qeq_trans with (y := exp_partial n 0).
      - apply Qeq_sym. apply (cpl_ep_ext n 0 y H0q).
      - apply exp_partial_zero. }
    assert (Hk1 : forall k : nat, exp_partial k y == 1%Q).
    { intro k. apply Qeq_trans with (y := exp_partial k 0).
      - apply Qeq_sym. apply (cpl_ep_ext k 0 y H0q).
      - apply exp_partial_zero. }
    right. intros eps Heps. exists 0%nat. intros k _.
    assert (Habs0 : Qabs (projT1 (real_const (exp_partial n y)) k
                          - projT1 (cauchy_real_exp (real_const y)) k) == 0).
    { apply Qeq_trans with (y := Qabs (1%Q - 1%Q)).
      - apply Qabs_wd.
        apply Qminus_comp.
        + apply Qeq_trans with (y := exp_partial n y).
          * apply real_const_proj.
          * exact Hn1.
        + apply Qeq_trans with (y := exp_partial k y).
          * apply exp_const_proj.
          * apply Hk1.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. ring.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ===== G2 core: left congruence of real_mult over real_eq ===== *)

(* With the cancellation certificate: x = z implies x*v = z*v
   (real_eq face).  Route: the boundedness of v, the half-eps
   relaxation eps/2/Mv', and the product bound closed by the
   cancellation certificate. *)
Lemma qtr_mult_eq_compat_l : forall x z v : Real,
  real_eq x z -> real_eq (real_mult x v) (real_mult z v).
Proof.
  intros [u Hu] [z Hz] [w Hw] Heq eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) w Hw))
    as [Mv [HMvT HMv]].
  set (Mv' := (Qabs Mv + 1)%Q).
  assert (HMv'0 : Qlt 0 Mv').
  { unfold Mv'. setoid_rewrite <- (Qplus_comm 1%Q (Qabs Mv)).
    apply (Qlt_le_trans 0%Q 1%Q).
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (HMv'posT : QltT 0 Mv') by (apply Qlt_to_QltT; exact HMv'0).
  (* half-eps scaling: feed eps/2 into the equality, restore strictness by eps/2 < eps *)
  destruct (Heq (eps / 2 / Mv')
    (qltT_div_pos (eps / 2) Mv'
       (qltT_div_pos eps 2%Q Heps qltT_0_2) HMv'posT)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* HN : QltT |u_n − z_n| (eps/2/Mv') *)
  assert (Hwn : Qle (Qabs (w n)) Mv').
  { apply (Qle_trans _ Mv _).
    - apply (QleT'_to_Qle _ _ (HMv n)).
    - apply (Qle_trans _ (Qabs Mv) _).
      + apply Qle_Qabs.
      + apply Qle_plus_nonneg_r.
        (* 0 <= 1: Qle expansion then lia (trivial at the Z level) *)
        unfold Qle. simpl. lia. }
  assert (Hle2 : Qle (Qabs (u n - z n) * Qabs (w n))
                     ((eps / 2 / Mv') * Mv')).
  { apply (Qmult_le_compat_nonneg (Qabs (u n - z n))
             (eps / 2 / Mv')%Q (Qabs (w n)) Mv').
    - split.
      + apply Qabs_nonneg.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact HN.
    - split.
      + apply Qabs_nonneg.
      + exact Hwn. }
  assert (Hab : Qabs (u n * w n - z n * w n)
                == Qabs (u n - z n) * Qabs (w n)).
  { apply Qeq_trans with (y := Qabs ((u n - z n) * w n)).
    - apply Qabs_wd. ring.
    - apply Qabs_Qmult. }
  assert (Hchain : QltT (Qabs (u n - z n) * Qabs (w n)) eps).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (eps / 2) eps).
    - apply (Qle_trans _ ((eps / 2 / Mv') * Mv')).
      + exact Hle2.
      + apply qeq_imp_qle.
        apply qtr_div_cancel. apply qtail_neq0. exact HMv'0.
    - apply qtr_div2_lt.
      apply QltT_to_Qlt. exact Heps. }
  apply qltT_eq_compat_l with (a := Qabs (u n - z n) * Qabs (w n)).
  - apply Qeq_sym. exact Hab.
  - exact Hchain.
Qed.

(* ===== G2 main statement: the Real-level Pade lower bound over an
   arbitrary carrier ===== *)

(* y > 0 and w = e^y (any real_eq carrier) imply P2(y) < w * Q2(y)
   (multiplied, division-free form). *)
Theorem qtr_pade_lower_real : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw.
  apply (real_lt_eq_lt _ _ _ (cpl_lower_even y Hy)).
  apply qtr_mult_eq_compat_l.
  apply real_eq_sym. exact Hw.
Qed.

(* ===== G2b reverse bridge: real_lt certificates into explicit
   pointwise QltT faces (N/eps pass through) ===== *)

Theorem qtr_pade_lower_extract : forall y : Q, QltT 0 y ->
  sigT (fun N : nat => sigT (fun eps : Q => And (QltT 0 eps)
    (forall m : nat, NatLe N m ->
      QltT eps (exp_partial m y * pade_den 2%nat y
                - pade_num 2%nat y)%Q))).
Proof.
  intros y Hy.
  destruct (cpl_lower_even y Hy) as [eps [Heps [N HN]]].
  exists N. exists eps. split.
  - exact Heps.
  - intros m Hm.
    specialize (HN m Hm).
    assert (Hmult : projT1 (real_mult (cauchy_real_exp (real_const y))
                                      (real_const (pade_den 2%nat y))) m
                    == exp_partial m y * pade_den 2%nat y).
    { apply Qeq_trans with
        (y := projT1 (cauchy_real_exp (real_const y)) m
              * projT1 (real_const (pade_den 2%nat y)) m).
      - apply real_mult_proj.
      - apply Qmult_comp.
        + apply exp_const_proj.
        + apply real_const_proj. }
    assert (Hconst : projT1 (real_const (pade_num 2%nat y)) m
                     == pade_num 2%nat y).
    { apply real_const_proj. }
    assert (Hraw : projT1 (real_mult (cauchy_real_exp (real_const y))
                                     (real_const (pade_den 2%nat y))) m
                   - projT1 (real_const (pade_num 2%nat y)) m
                   == exp_partial m y * pade_den 2%nat y
                      - pade_num 2%nat y).
    { apply Qminus_comp.
      - exact Hmult.
      - exact Hconst. }
    exact (qltT_eq_compat_r _ _ _ (Qeq_sym _ _ Hraw) HN).
Qed.

(* weak companion: y > 0 and w = e^y imply P2(y) <= w * Q2(y). *)
Theorem qtr_pade_lower_real_le : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_le (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw. left.
  apply (qtr_pade_lower_real y w Hy Hw).
Qed.

Print Assumptions qtr_embed_mono.
Print Assumptions qtr_embed_le.
Print Assumptions qtr_partial_gap.
Print Assumptions qtr_exp_gt_partial.
Print Assumptions qtr_exp_ge_partial.
Print Assumptions qtr_mult_eq_compat_l.
Print Assumptions qtr_pade_lower_real.
Print Assumptions qtr_pade_lower_extract.
Print Assumptions qtr_pade_lower_real_le.
