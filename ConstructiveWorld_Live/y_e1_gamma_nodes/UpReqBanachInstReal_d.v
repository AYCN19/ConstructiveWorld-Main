(* ConstructiveWorld-Main - the completeness and audit stem of the
   Real instantiation of the Banach-algebra pre-class. *)

(** * UpReqBanachInstReal_d: completeness dividend and extraction
      audit (stem four of four).

    Mission.  Conserved statement-for-statement from the boxed piece
    UpReqBanachInstReal: the norm-difference conversion, the
    first-term-column Cauchy dividend, the limit-element
    construction, the honest convergence-note carrier, the
    conditional assembly bridge with its smoke lemma, the Separate
    Extraction check, and the assumption-face self-audit exits
    (all Closed under the global context).

    Dependencies.  Stdlib [QArith], [Qabs], [ZArith], [Lia],
    [Extraction]; [S01_BaseRing], [S02_CauchyComplete],
    [S03_QExp], [UpReqBanachExp_dep], [UpReqBanachInstB_dep],
    [UpReqBanachInst_dep], sibling stems _a/_b/_c.

    References.  The Banach-algebra instantiation line of the
    constructive development; the boxed original piece.

    Constructivity.  All carriers [Set]; conclusions in
    [Id]/[QeqT]/[QleT'] forms; zero assumed constants; every proof
    closes by Qed; the extraction-inherent magic of existT/record
    forms is an extractor trait, not a statement debt.

    Build.  [coqc -q -native-compiler no] under the acceptance
    build faces, [cpu_guard v3] wrapped. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp_dep.
Require Import UpReqBanachInstB_dep.
Require Import UpReqBanachInst_dep.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.
Require Import UpReqBanachInstReal_a.
Require Import UpReqBanachInstReal_b.
Require Import UpReqBanachInstReal_c.
(* ============================================================ *)
(* S5: half-acquisition of the completeness dividend (the bcauchy preferred-consumer position) + an honest note              *)
(* ============================================================ *)

(* Norm-difference conversion: the Qeq value of bnorm(u m -u n) equals the absolute value of the first-term column difference *)
Lemma bxra_norm_diff_head : forall (u : nat -> Real) (m n : nat),
  QeqT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n))))
       (Qabs (bxra_head (u m) - bxra_head (u n))%Q).
Proof.
  intros u m n. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus (u m) (bxra_bopp_f (u n))).
  rewrite (bxra_head_bopp (u n)).
  rewrite (bxib_qnorm_fix_id (bxra_head (u m)
            + bxib_qnorm (- bxra_head (u n))%Q)%Q).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (bxib_qnorm
        (bxra_head (u m) - bxra_head (u n))%Q))).
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_qeqT_of_qeqT.
    apply bxib_qeqT_cong_plus.
    + apply bxib_qeqT_refl.
    + apply bxib_qnorm_fix.
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
Qed.

(* Dividend acquisition (1): the first-term column of a Pre-Cauchy sequence is itself a Q-Cauchy sequence in the S02 sense *)
Lemma bxra_head_col_cauchy : forall u : nat -> Real,
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps)) ->
  cauchy (fun k => bxra_head (u k)).
Proof.
  intros u Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply (bxra_qltT_wd (bxra_bnorm_f
        (bxra_bplus_f (u m) (bxra_bopp_f (u n))))).
  - apply bxra_norm_diff_head.
  - apply HN; assumption.
Qed.

(* Dividend acquisition (2): the limit [element] is constructible on the Real carrier                *)
(* (the measured form of the carrier's built-in completeness dividend: the Cauchy witness is supplied *)
(*   by the first-term column itself; existT packaging yields a genuine Real element - zero gaps on the carrier side.)               *)
Definition bxra_cauchy_limit_elem (u : nat -> Real)
  (Hu : forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps))
  : Real :=
  existT (fun s : Qseq => cauchy s)
         (fun k => bxra_head (u k)) (bxra_head_col_cauchy u Hu).

(* Honest note: the convergence statement (the inner layer of bxin_pre_complete) - the norm reads term 0, *)
(* and term 0 of the limit element would have to be the (constructively unnameable) limit value of the first-term column,        *)
(* = the Q-sequence completeness wall (the INST3 proven conclusion stands, zero forcing; residual items are listed in the delivery report).    *)
Definition bxra_pre_complete_real : Set :=
  bxin_pre_complete bxra_real_pre.

(* Assembly bridge connection (conditional form: with the completeness input in place one obtains the full BanachAlg) *)
Definition bxra_BanachAlg_of_real
  (Hc : bxin_pre_complete bxra_real_pre) : BanachAlg :=
  bxin_BanachAlg_of_pre bxra_real_pre Hc.

Lemma bxra_bridge_smoke : forall Hc : bxin_pre_complete bxra_real_pre,
  @bae (bxra_BanachAlg_of_real Hc)
       (@bcoef (bxra_BanachAlg_of_real Hc) 1%Q)
       (@bone (bxra_BanachAlg_of_real Hc)).
Proof. intro Hc. apply bxin_bone_is_one. Qed.

(* ============================================================ *)
(* S6: extraction check + assumption-face self-audit (the G3 face)                              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
(* Extraction check (the INST5 discipline: scalar/lemma-level pieces; carrier-dependent items are not extracted -   *)
(*   the inherent Obj.magic of existT/record extraction is an extractor trait, not a statement debt; *)
(*   the dependent pieces bxra_cauchy_limit_elem/bxra_BanachAlg_of_real carry the assumption-face *)
(*   self-audit through their Print Assumptions Closed exits).                   *)
Separate Extraction bxra_qabs_opp_norm bxra_norm_wd_qeqt bxra_norm_coef_qeqt
  bxra_f_norm_opp bxra_f_plus_opp bxra_f_norm_mult bxra_raw_pin_wall
  bxra_qabs_mult bxra_qleT_zero_abs_qn bxra_qltT_wd bxra_norm_diff_head.

Print Assumptions bxra_qabs_opp_norm.
Print Assumptions bxra_norm_wd_qeqt.
Print Assumptions bxra_norm_coef_qeqt.
Print Assumptions bxra_f_norm_opp.
Print Assumptions bxra_f_plus_assoc.
Print Assumptions bxra_f_plus_opp.
Print Assumptions bxra_f_norm_mult.
Print Assumptions bxra_cauchy_limit_elem.
Print Assumptions bxra_real_pre.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_bridge_smoke.

(* - assumption-face self-audit of the replaced pieces (slice three; all should be Closed under the global context) - *)
Print Assumptions bxra_head_cR.
Print Assumptions bxra_head_bplus.
Print Assumptions bxra_head_bmult.
Print Assumptions bxra_head_bopp.
Print Assumptions bxra_f_coef_zero.
Print Assumptions bxra_f_coef_one.
Print Assumptions bxra_f_norm_zero.
Print Assumptions bxra_f_norm_one.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_inst_smoke_norm_coef.
Print Assumptions bxra_inst_smoke_norm_wd.
