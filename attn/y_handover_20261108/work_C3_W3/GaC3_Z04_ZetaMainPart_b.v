(* ===================================================================== *)
(* GaC3_Z04_ZetaMainPart_b.v                                              *)
(* Mission. Node C3-Z04 (segment C3), second slice: the strip section of  *)
(*   the zeta main-part expansion.  At the rational strip point (a, b)    *)
(*   with the window premises QleT' (1/2) a, QleT' a 2 (the in_strip      *)
(*   shadow), the off-pole slot QltT 0 d and the truncation N, the three  *)
(*   draft faces are cast as squared-modulus slot theorems in the Bishop  *)
(*   eps form: [z04_main_part] |zeta_part - mp|^2 <= B^2 + eps,           *)
(*   [z04_deriv_main_part] |zeta'_part + mp2|^2 <= B2^2 + eps and         *)
(*   [z04_logderiv_main_part] |logderiv_part - mp|^2 <= B2'^2 + eps, with *)
(*   the continuation carriers [zeta1] / [zeta1d] / [zls], the truncation *)
(*   carriers on the C2.01 zeta partial sums, the Z01 von Mangoldt        *)
(*   partial sums and the log-weight partial sums, and the per-face bound *)
(*   halves as explicit named Section premises (the GAPASUME slot family  *)
(*   L-Z04-A..F; the slots discharge at End, so every named item reads    *)
(*   Closed under the global context).  The shared engine is the split    *)
(*   [z04_split_gen], the V03 modulus dilute face and the constant-fold   *)
(*   bookkeeping; each difference carrier subtracts exactly 1/(s-1) (or   *)
(*   adds 1/(s-1)^2): the card main-part-difference shape.                *)
(* Dependencies. [GaC3_Z04_ZetaMainPart] (the pole carrier algebra:      *)
(*   [z04_mp], [z04_mp2], [z04_split_gen], [z04_fold_eps],                *)
(*   [z04_norm_sq_comm], [z04_const_le]), [GaC2_Iface_DS] ([c_zeta_part], *)
(*   [zeta_part_add_R_N_stem]), [GaC2_02_AbsConvTailBound_a]              *)
(*   ([nat_real_pos], [c_norm_sq_wd]), [GaC3_Z01_LogDerivSeries]          *)
(*   ([z01_ln], [z01_manpart]), [GaC3_V03_VinoZeta]                       *)
(*   ([v03_norm_sq_dilute], [v03_H2le]), [S01_BaseRing], [S02_Cauchy-     *)
(*   Complete], [S07_RealSetoidExpLog], [CxRealPairCore/ExpLog]; Stdlib   *)
(*   [QArith].  The Z03 casting is the GREEN precondition of this node    *)
(*   (supply-route registration, no compile-time consumption position).   *)
(* References. drafts_C3.md C3-Z04 card (statement skeleton and slot      *)
(*   discipline); ZZ theory (AFP PNT_with_Remainder) zeta_bound family    *)
(*   :197-268 (the explicit strip-constant discipline); tree precedent    *)
(*   [GaC3_V03_VinoZeta] (squared-face re-carrier, slot family shape).    *)
(* Constructivity. Set-carried statements (real_le / real_lt / QleT' /    *)
(*   QltT are Set-sorted); no global assumption commands, no proof        *)
(*   abandonment, no classical principles; the eps form is the Bishop     *)
(*   interface of the non-decidable order face; no computation tokens in  *)
(*   this slice.                                                          *)
(* Build. coqc -native-compiler no -q -Q . "" -Q ../boot_src "" from the  *)
(*   work directory, single compile lane under the thermal guard wrapper. *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Require Import GaC2_03_a.
Require Import HansonLcm.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_P05_CauchyFormula.
Require Import GaC3_V03_VinoZeta.
Require Import GaC3_Z04_ZetaMainPart.

Local Open Scope Q_scope.

(* ==== Part 2. The strip section: carriers, slots, and the three faces. ==== *)

Section Z04_Main.

(* The rational shadow of the strip point s = (a, b) and the strip window *)
(* premises (the draft in_strip face at the rational shadow). *)
Variable a b : Q.
Hypothesis Ha12 : QleT' (1 # 2) a.
Hypothesis Ha2 : QleT' a 2.
(* The off-pole slot: the pole distance stays positive (s <> 1 at the     *)
(* rational shadow; the Set carrier of the draft Re s <> 1 face). *)
Hypothesis Hd : QltT 0 (z04_dd a b).

(* The truncation of the partial-sum carriers. *)
Variable N : nat.

(* The draft constants B, B2, B2': explicit, premise-carried (the values *)
(* are audited downstream; the certificate slice folds the quarter books). *)
Variables B B2 B2' : Q.

(* The strip point and the three truncated carriers: the C2.01 zeta face, *)
(* the Z01 von Mangoldt face (the log-derivative carrier) and the log-    *)
(* weighted derivative face. *)
Definition z04_sP : Cx := (real_const a, real_const b).
Definition z04_mpP : Cx := z04_mp a b.
Definition z04_mp2P : Cx := z04_mp2 a b.
Definition z04_zpartP : Cx := c_zeta_part nat_real_pos N z04_sP.
Definition z04_manP : Cx := z01_manpart nat_real_pos N z04_sP.

Fixpoint z04_lsum (M : nat) : Cx :=
  match M with
  | O => c_zero
  | Datatypes.S m => c_plus (z04_lsum m)
       (c_scale (z01_ln nat_real_pos (Datatypes.S m) (NatLe_one_S m))
                (c_powq nat_real_pos (Datatypes.S m) (NatLe_one_S m) z04_sP))
  end.

(* The truncated derivative carrier: -sum_{n<=N} ln(n) n^{-s}. *)
Definition z04_dpartP : Cx := c_opp (z04_lsum N).

(* The continuation carriers: zeta(s), zeta'(s) and -zeta'/zeta(s) as     *)
(* section-level data (supplied by the continuation machinery; the slot   *)
(* premises below pin the partial sums to them). *)
Variable zeta1 zeta1d zls : Cx.

(* GAPASUME slot L-Z04-A: |zeta(s) - 1/(s-1)|^2 <= B^2/4 at the strip     *)
(* point (the main half of the zeta face). *)
Hypothesis Hz_main : real_le (c_norm_sq (c_plus zeta1 (c_opp z04_mpP)))
                             (real_const (B * B * (1 # 4))).

(* GAPASUME slot L-Z04-B: |zeta(s) - sum_{n<=N} n^{-s}|^2 <= B^2/4 (the   *)
(* tail half; supply route: the C2.04 divisor-sum split [z04_dsum_split]  *)
(* with the smooth remainder bounded, or the continuation truncation).   *)
Hypothesis Hz_tail : real_le (c_norm_sq (c_plus zeta1 (c_opp z04_zpartP)))
                             (real_const (B * B * (1 # 4))).

(* GAPASUME slot L-Z04-C: |zeta'(s) + 1/(s-1)^2|^2 <= B2^2/4. *)
Hypothesis Hzd_main : real_le (c_norm_sq (c_plus zeta1d z04_mp2P))
                              (real_const (B2 * B2 * (1 # 4))).

(* GAPASUME slot L-Z04-D: |zeta'(s) - dpart_N|^2 <= B2^2/4. *)
Hypothesis Hzd_tail : real_le (c_norm_sq (c_plus zeta1d (c_opp z04_dpartP)))
                              (real_const (B2 * B2 * (1 # 4))).

(* GAPASUME slot L-Z04-E: |-zeta'/zeta(s) - 1/(s-1)|^2 <= B2'^2/4 (the    *)
(* residue-one main part of the log-derivative carrier). *)
Hypothesis Hzl_main : real_le (c_norm_sq (c_plus zls (c_opp z04_mpP)))
                              (real_const (B2' * B2' * (1 # 4))).

(* GAPASUME slot L-Z04-F: |-zeta'/zeta(s) - manpart_N|^2 <= B2'^2/4. *)
Hypothesis Hzl_tail : real_le (c_norm_sq (c_plus zls (c_opp z04_manP)))
                              (real_const (B2' * B2' * (1 # 4))).

(* The tail-slot direction bridges: the slots bound the carrier minus    *)
(* the truncation; the dilute argument reads the reversed difference, so *)
(* each tail bound is transported through the norm commutation once.     *)
Lemma z04_tailB_le :
  real_le (c_norm_sq (c_plus z04_zpartP (c_opp zeta1)))
          (real_const (B * B * (1 # 4))).
Proof.
  apply (RealSetoid.real_le_compat (c_norm_sq (c_plus zeta1 (c_opp z04_zpartP)))
         (c_norm_sq (c_plus z04_zpartP (c_opp zeta1)))
         (real_const (B * B * (1 # 4))) (real_const (B * B * (1 # 4)))
         (z04_norm_sq_comm zeta1 z04_zpartP) (real_eq_refl _)
         Hz_tail).
Qed.

Lemma z04_dtailB_le :
  real_le (c_norm_sq (c_plus z04_dpartP (c_opp zeta1d)))
          (real_const (B2 * B2 * (1 # 4))).
Proof.
  apply (RealSetoid.real_le_compat (c_norm_sq (c_plus zeta1d (c_opp z04_dpartP)))
         (c_norm_sq (c_plus z04_dpartP (c_opp zeta1d)))
         (real_const (B2 * B2 * (1 # 4))) (real_const (B2 * B2 * (1 # 4)))
         (z04_norm_sq_comm zeta1d z04_dpartP) (real_eq_refl _)
         Hzd_tail).
Qed.

Lemma z04_ltailB_le :
  real_le (c_norm_sq (c_plus z04_manP (c_opp zls)))
          (real_const (B2' * B2' * (1 # 4))).
Proof.
  apply (RealSetoid.real_le_compat (c_norm_sq (c_plus zls (c_opp z04_manP)))
         (c_norm_sq (c_plus z04_manP (c_opp zls)))
         (real_const (B2' * B2' * (1 # 4))) (real_const (B2' * B2' * (1 # 4)))
         (z04_norm_sq_comm zls z04_manP) (real_eq_refl _)
         Hzl_tail).
Qed.

(* ---- Main face 1: the zeta main-part difference. ---- *)
(* |sum_{n<=N} n^{-s} - 1/(s-1)|^2 <= B^2 + eps: the squared reading of   *)
(* the draft |zeta(s) - 1/(s-1)| <= B in the strip. *)
Theorem z04_main_part : forall eps : Real, real_lt real_zero eps ->
  real_le (c_norm_sq (c_plus z04_zpartP (c_opp z04_mpP)))
          (real_plus (real_const (B * B)) eps).
Proof.
  intros eps Heps.
  apply (real_le_trans _
    (real_plus (real_plus (real_mult (c_norm_sq (c_plus zeta1 (c_opp z04_mpP))) (real_const 2))
                          (real_mult (c_norm_sq (c_plus z04_zpartP (c_opp zeta1))) (real_const 2)))
               eps) _).
  - apply (real_le_trans _
             (c_norm_sq (c_plus (c_plus zeta1 (c_opp z04_mpP))
                                (c_plus z04_zpartP (c_opp zeta1)))) _).
    + apply (RealSetoid.real_eq_le _ _). apply c_norm_sq_wd.
      exact (z04_split_gen zeta1 (c_opp z04_mpP) z04_zpartP).
    + exact (v03_norm_sq_dilute (c_plus zeta1 (c_opp z04_mpP))
                                (c_plus z04_zpartP (c_opp zeta1)) eps Heps).
  - apply (real_le_trans _
             (real_plus (real_plus (real_mult (real_const (B * B * (1 # 4))) (real_const 2))
                                   (real_mult (real_const (B * B * (1 # 4))) (real_const 2)))
                        eps) _).
    + apply real_le_plus_compat.
      * apply real_le_plus_compat.
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus zeta1 (c_opp z04_mpP)))
                   (real_const (B * B * (1 # 4))) (real_const 2) v03_H2le Hz_main).
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus z04_zpartP (c_opp zeta1)))
                   (real_const (B * B * (1 # 4))) (real_const 2) v03_H2le z04_tailB_le).
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le _ _). exact (z04_fold_eps (B * B) eps).
Qed.

(* ---- Main face 2: the derivative main-part difference. ---- *)
(* |-sum_{n<=N} ln(n) n^{-s} + 1/(s-1)^2|^2 <= B2^2 + eps: the squared    *)
(* reading of the draft |zeta'(s) + 1/(s-1)^2| <= B2. *)
Theorem z04_deriv_main_part : forall eps : Real, real_lt real_zero eps ->
  real_le (c_norm_sq (c_plus z04_dpartP z04_mp2P))
          (real_plus (real_const (B2 * B2)) eps).
Proof.
  intros eps Heps.
  apply (real_le_trans _
    (real_plus (real_plus (real_mult (c_norm_sq (c_plus zeta1d z04_mp2P)) (real_const 2))
                          (real_mult (c_norm_sq (c_plus z04_dpartP (c_opp zeta1d))) (real_const 2)))
               eps) _).
  - apply (real_le_trans _
             (c_norm_sq (c_plus (c_plus zeta1d z04_mp2P)
                                (c_plus z04_dpartP (c_opp zeta1d)))) _).
    + apply (RealSetoid.real_eq_le _ _). apply c_norm_sq_wd.
      exact (z04_split_gen zeta1d z04_mp2P z04_dpartP).
    + exact (v03_norm_sq_dilute (c_plus zeta1d z04_mp2P)
                                (c_plus z04_dpartP (c_opp zeta1d)) eps Heps).
  - apply (real_le_trans _
             (real_plus (real_plus (real_mult (real_const (B2 * B2 * (1 # 4))) (real_const 2))
                                   (real_mult (real_const (B2 * B2 * (1 # 4))) (real_const 2)))
                        eps) _).
    + apply real_le_plus_compat.
      * apply real_le_plus_compat.
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus zeta1d z04_mp2P))
                   (real_const (B2 * B2 * (1 # 4))) (real_const 2) v03_H2le Hzd_main).
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus z04_dpartP (c_opp zeta1d)))
                   (real_const (B2 * B2 * (1 # 4))) (real_const 2) v03_H2le z04_dtailB_le).
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le _ _). exact (z04_fold_eps (B2 * B2) eps).
Qed.

(* ---- Main face 3: the log-derivative main-part difference. ---- *)
(* |manpart_N - 1/(s-1)|^2 <= B2'^2 + eps: the squared reading of the     *)
(* draft |-zeta'/zeta(s) - 1/(s-1)| <= B2' (the residue-one face; the    *)
(* consumption shape of the residue certificate node). *)
Theorem z04_logderiv_main_part : forall eps : Real, real_lt real_zero eps ->
  real_le (c_norm_sq (c_plus z04_manP (c_opp z04_mpP)))
          (real_plus (real_const (B2' * B2')) eps).
Proof.
  intros eps Heps.
  apply (real_le_trans _
    (real_plus (real_plus (real_mult (c_norm_sq (c_plus zls (c_opp z04_mpP))) (real_const 2))
                          (real_mult (c_norm_sq (c_plus z04_manP (c_opp zls))) (real_const 2)))
               eps) _).
  - apply (real_le_trans _
             (c_norm_sq (c_plus (c_plus zls (c_opp z04_mpP))
                                (c_plus z04_manP (c_opp zls)))) _).
    + apply (RealSetoid.real_eq_le _ _). apply c_norm_sq_wd.
      exact (z04_split_gen zls (c_opp z04_mpP) z04_manP).
    + exact (v03_norm_sq_dilute (c_plus zls (c_opp z04_mpP))
                                (c_plus z04_manP (c_opp zls)) eps Heps).
  - apply (real_le_trans _
             (real_plus (real_plus (real_mult (real_const (B2' * B2' * (1 # 4))) (real_const 2))
                                   (real_mult (real_const (B2' * B2' * (1 # 4))) (real_const 2)))
                        eps) _).
    + apply real_le_plus_compat.
      * apply real_le_plus_compat.
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus zls (c_opp z04_mpP)))
                   (real_const (B2' * B2' * (1 # 4))) (real_const 2) v03_H2le Hzl_main).
        -- exact (real_le_mult_compat_weak (c_norm_sq (c_plus z04_manP (c_opp zls)))
                   (real_const (B2' * B2' * (1 # 4))) (real_const 2) v03_H2le z04_ltailB_le).
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le _ _). exact (z04_fold_eps (B2' * B2') eps).
Qed.

(* The strip reading of the window: the rational shadow premises give the *)
(* real-level lower and upper faces on the real part (the in_strip       *)
(* reading of the draft statement shape). *)
Theorem z04_strip_read :
  And (real_le (real_const (1 # 2)) (cRe z04_sP)) (real_le (cRe z04_sP) (real_const 2)).
Proof.
  split.
  - apply z04_const_le. exact Ha12.
  - apply z04_const_le. exact Ha2.
Qed.

End Z04_Main.

(* ==== Supply-face audit tail ==== *)

(* Named-item census of this slice (acceptance counting): 8 section       *)
(* Definitions/Fixpoint (z04_sP, z04_mpP, z04_mp2P, z04_zpartP, z04_manP, *)
(* z04_lsum, z04_dpartP and the strip reading face) + 3 section Lemmas    *)
(* (the tail-direction bridges z04_tailB_le, z04_dtailB_le,               *)
(* z04_ltailB_le) + 4 section Theorems (the three slot theorems           *)
(* z04_main_part, z04_deriv_main_part, z04_logderiv_main_part and the     *)
(* strip reading z04_strip_read).  The section carries the six premise    *)
(* slots L-Z04-A..F and the three window slots; they discharge as         *)
(* explicit arguments at End.  Zero assumption commands, zero proof       *)
(* abandonment, zero classical principles, zero computation tokens in     *)
(* this slice.                                                            *)
