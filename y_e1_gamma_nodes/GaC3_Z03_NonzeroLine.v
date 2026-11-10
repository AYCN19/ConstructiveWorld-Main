(* ConstructiveWorld-Main - the three-cosine nonvanishing line engine. *)
(** * GaC3_Z03_NonzeroLine: the three-cosine racing engine for the
    nonvanishing line Re s = 1 (the core face).

    Mission.  Node C3-Z03 (segment C3): the constructive core of the
    three-cosine nonvanishing argument.  This stem casts the real-part
    bridge of the complex three-point carrier ([z03_cre_powq]: the
    real part of the exponential term at the point (sg, t) is the
    polar face exp(-sg*ln n) * cos(-t*ln n); [z03_cre_plus] /
    [z03_cre_scale]: the real part distributes over the complex sum
    and the scaling), the real-line mirror of the Z01 von Mangoldt
    partial sum ([z03_resum], [z03_cre_manpart]), the combined Cx
    carrier assembled with the 3-4-1 weights ([z03_comb], the ZZ
    logderiv_zeta_ineq assembly face), its square-form mirror
    ([z03_sqsum], the per-term square form of the Z02 identity weighted
    by the Lambda weight and the exponential factor), the per-term
    bridge ([z03_cre_tri]), and the equality face Theorem
    [z03_comb_sqsum_eq] (the combined carrier's real part equals the
    square-form sum).  Piece layout: the rational transport kit and the
    Q-level cosine congruence kit live in leaf a
    [GaC3_Z03_NonzeroLine_a]; the term carriers and the relax-order
    kit live in leaf b [GaC3_Z03_NonzeroLine_b]; the discharge and
    racing faces (the weight nonnegativity, the asymptotic
    nonnegativity of the square-form sum and of the combined real
    part, and the explicit-radius slot contradiction
    [z03_racing_contra] under Section Z03_Race) live in
    [GaC3_Z03_NonzeroLine_race]; the literal radius certificates live
    in [GaC3_Z03_NonzeroLine_cert].  The literal zeta-carrier
    statement of the card (drafts_C3.md C3-Z03:
    [zeta_nonzero_line] / [zeta_nonzero_line_quant]) awaits the
    eta-continuation supply face (GaC2_10_EtaContinuation, not yet in
    the tree); the slot form is the registered consumption shape of
    the certified V03 pattern.  The cross-segment supply line
    [GaC2_Iface_Eta] is held now (the interface slice is cast and
    accepted, accept/C2.IfaceEta.json verdict PASS), so the eta-side
    discharge lands on this line when the continuation faces arrive.

    Dependencies.  Leaf a [GaC3_Z03_NonzeroLine_a] (transitively via
    leaf b), leaf b [GaC3_Z03_NonzeroLine_b] ([z03npos],
    [z03_lnreal], [z03_eterm], [z03_coterm], [z03_cos_peq],
    [z03_exp_peq]), [S01_BaseRing] ([NatLe], selective import),
    [S02_CauchyComplete] (order faces), [S03_QExp], 
    [S07_RealSetoidExpLog] (RealSetoid compat faces),
    [S10_KVQuantTrig] ([cauchy_real_cos]), [CxRealPairCore] +
    [CxRealPairExpLog] (base pair), [GaC2_Iface_DS] ([c_powq],
    [nat_real_pos], [NatLe_one_S] via the leaf import),
    [GaC2_Iface_Eta] (the eta-block cross-segment trans-supply slice;
    registered consumer line of drafts_C3.md C3-Z03),
    [GaC3_Z01_LogDerivSeries] ([z01_lam], [z01_manpart]),
    [GaC3_Z02_ThreeCosine] ([GaC3_Z02_three_cosine_sq]); Stdlib
    [QArith] (with [Qring]), [Setoid], [Morphisms], [Arith], [Lia].

    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163 (the three-cosine weighted inequality); drafts_C3.md C3-Z03
    (racing skeleton, explicit-radius obligation, cross-segment line
    GaC2_Iface_Eta); cards_C3 C3-Z03 (multiplicity main part).  The
    four-term main-part slot is the registered open supply face (zero
    factorization route).

    Constructivity.  Every named construction is carried by [Set]; the
    nonnegativity face is carried by [real_ge_relax] (the asymptotic
    order, per the Z02 precedent on the equality-versus-positivity
    obstruction).  Zero assumed constants, zero abandoned proofs, zero
    classical choice; Print Assumptions of every named item reads
    Closed under the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_Z03_NonzeroLine.v] from the work directory through the
    dependency-closure build (50_toolkit/build_deposit.py); acceptance
    runs use 50_toolkit/accept_node.py and write accept/<node>.json,
    single compile lane under the thermal guard configuration. *)

Require S01_BaseRing.
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_Iface_Eta.
Require Import GaC3_Z03_NonzeroLine_a.
Require Import GaC3_Z03_NonzeroLine_b.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_Z02_ThreeCosine.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* The shared pointwise normalisation: expand the real-level sums and   *)
(* products down to the rational approximations, then close by ring.    *)
Ltac z03_pt :=
  repeat (first [rewrite real_mult_proj | rewrite real_plus_proj
                | rewrite real_opp_proj]);
  repeat match goal with
         | [ |- context[projT1 real_one ?n] ] => progress (rewrite (real_one_pt n))
         | [ |- context[projT1 real_zero ?n] ] => progress (rewrite (real_zero_pt n))
         | [ |- context[projT1 (real_const ?c) ?n] ] =>
             progress (rewrite (real_const_proj c n))
         end;
  ring.

(* ===================================================================== *)
(* Part 1. The three-point Lambda-weighted carrier and its nonnegativity *)
(* face (assumption-free): the real-part bridge and the equality face.   *)
(* ===================================================================== *)

(* The real part of the exponential term at the point (sg, t): the      *)
(* polar face exp(-sg*ln n) * cos(-t*ln n).  The bridge splits into the *)
(* conversion face (the c_powq components reduce to the literal form)   *)
(* and the pointwise argument-cleaning face. *)
Lemma z03_cre_powq : forall (n : nat) (Hn : NatLe 1 n) (sg t : Real),
  real_eq (cRe (c_powq z03npos n Hn (sg, t)))
          (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)).
Proof.
  intros n Hn sg t.
  apply (real_eq_trans _
    (real_mult (cauchy_real_exp (real_mult (real_opp real_one)
                   (real_plus (real_mult sg (z03_lnreal n Hn))
                              (real_opp (real_mult t real_zero)))))
               (cauchy_real_cos (real_mult (real_opp real_one)
                   (real_plus (real_mult sg real_zero)
                              (real_mult t (z03_lnreal n Hn))))))).
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_mult_compat.
    + apply z03_exp_peq. intro k. z03_pt.
    + apply z03_cos_peq. intro k. z03_pt.
Qed.

(* The real part distributes over the complex sum. *)
Lemma z03_cre_plus : forall z w : Cx,
  real_eq (cRe (c_plus z w)) (real_plus (cRe z) (cRe w)).
Proof.
  intros z w. apply real_eq_of_zero_diff. intro k.
  rewrite (cRe_plus_pt z w k), (real_plus_proj (cRe z) (cRe w) k). ring.
Qed.

(* The real part of a scaled complex number is the scaled real part     *)
(* (conversion face). *)
Lemma z03_cre_scale : forall (a : Real) (z : Cx),
  real_eq (cRe (c_scale a z)) (real_mult a (cRe z)).
Proof. intros a z. apply real_eq_refl. Qed.

(* The real part of the Z01 von Mangoldt partial sum, mirrored on the   *)
(* real line. *)
Fixpoint z03_resum (N : nat) (s : Cx) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S m => real_plus (z03_resum m s)
             (real_mult (z01_lam (Datatypes.S m))
                        (cRe (c_powq z03npos (Datatypes.S m) (NatLe_one_S m) s)))
  end.

Lemma z03_cre_manpart : forall (N : nat) (s : Cx),
  real_eq (cRe (z01_manpart z03npos N s)) (z03_resum N s).
Proof.
  intro N. induction N as [| N IH]; intro s.
  - cbn [z01_manpart z03_resum]. apply real_eq_refl.
  - cbn [z01_manpart z03_resum].
    apply (real_eq_trans _ (real_plus (cRe (z01_manpart z03npos N s))
             (cRe (c_scale (z01_lam (Datatypes.S N))
                      (c_powq z03npos (Datatypes.S N) (NatLe_one_S N) s))))).
    + apply z03_cre_plus.
    + apply RealSetoid.real_eq_plus_compat.
      * exact (IH s).
      * apply z03_cre_scale.
Qed.

(* The combined Cx carrier: the Z01 partial sums at the three racing    *)
(* points, assembled with the 3-4-1 weights (the ZZ logderiv_zeta_ineq  *)
(* assembly face). *)
Definition z03_comb (N : nat) (sg t : Real) : Cx :=
  c_plus (c_scale (real_const 3) (z01_manpart z03npos N (sg, real_zero)))
         (c_plus (c_scale (real_const 4) (z01_manpart z03npos N (sg, t)))
                 (z01_manpart z03npos N (sg, real_plus t t))).

(* The real-line mirror of the combined carrier: the per-term square    *)
(* form of the Z02 identity weighted by the Lambda weight and the       *)
(* exponential factor. *)
Fixpoint z03_sqsum (N : nat) (sg t : Real) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S m => real_plus (z03_sqsum m sg t)
             (real_mult (real_mult (z01_lam (Datatypes.S m))
                                   (z03_eterm (Datatypes.S m) (NatLe_one_S m) sg))
                        (real_mult (real_const 2)
                           (real_mult (real_plus real_one
                                        (z03_coterm (Datatypes.S m) (NatLe_one_S m) t))
                                      (real_plus real_one
                                        (z03_coterm (Datatypes.S m) (NatLe_one_S m) t)))))
  end.

(* The per-term core: the weighted three-point real part is the weight  *)
(* times the square form at the ordinate argument. *)
Lemma z03_cre_tri : forall (n : nat) (Hn : NatLe 1 n) (sg t : Real),
  real_eq (real_mult (z01_lam n)
            (real_plus (real_mult (real_const 3)
                         (cRe (c_powq z03npos n Hn (sg, real_zero))))
                       (real_plus (real_mult (real_const 4)
                                    (cRe (c_powq z03npos n Hn (sg, t))))
                                  (cRe (c_powq z03npos n Hn (sg, real_plus t t))))))
          (real_mult (real_mult (z01_lam n) (z03_eterm n Hn sg))
                     (real_mult (real_const 2)
                        (real_mult (real_plus real_one (z03_coterm n Hn t))
                                   (real_plus real_one (z03_coterm n Hn t))))).
Proof.
  intros n Hn sg t.
  apply (real_eq_trans _
    (real_mult (z01_lam n)
       (real_plus (real_mult (real_const 3)
                    (real_mult (z03_eterm n Hn sg)
                       (cauchy_real_cos
                          (real_mult (real_opp real_zero) (z03_lnreal n Hn)))))
                  (real_plus (real_mult (real_const 4)
                               (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)))
                             (real_mult (z03_eterm n Hn sg)
                                (cauchy_real_cos
                                   (real_mult (real_opp (real_plus t t))
                                              (z03_lnreal n Hn)))))))).
  - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
    apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat;
        [apply real_eq_refl | exact (z03_cre_powq n Hn sg real_zero)].
    + apply RealSetoid.real_eq_plus_compat.
      * apply RealSetoid.real_eq_mult_compat;
          [apply real_eq_refl | exact (z03_cre_powq n Hn sg t)].
      * exact (z03_cre_powq n Hn sg (real_plus t t)).
  - apply (real_eq_trans _
      (real_mult (z01_lam n)
         (real_mult (z03_eterm n Hn sg)
                    (real_plus (real_const 3)
                               (real_plus (real_mult (real_const 4)
                                            (z03_coterm n Hn t))
                                          (cauchy_real_cos
                                             (real_plus
                                                (real_mult (real_opp t)
                                                           (z03_lnreal n Hn))
                                                (real_mult (real_opp t)
                                                           (z03_lnreal n Hn))))))))).
    + (* the zero-ordinate cosine is 1 and the doubled-ordinate cosine   *)
      (* is the doubled argument; then the ring form factors out       *)
      apply (real_eq_trans _
        (real_mult (z01_lam n)
           (real_plus (real_mult (real_const 3)
                        (real_mult (z03_eterm n Hn sg) real_one))
                      (real_plus (real_mult (real_const 4)
                                   (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)))
                                 (real_mult (z03_eterm n Hn sg)
                                    (cauchy_real_cos
                                       (real_plus (real_mult (real_opp t)
                                                          (z03_lnreal n Hn))
                                                  (real_mult (real_opp t)
                                                             (z03_lnreal n Hn))))))))).
      { apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        apply RealSetoid.real_eq_plus_compat.
        - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
          apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
          apply (real_eq_trans _ (cauchy_real_cos real_zero)).
          * apply z03_cos_peq. intro k. z03_pt.
          * exact real_cos_one.
        - apply RealSetoid.real_eq_plus_compat.
          + apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply z03_cos_peq. intro k. z03_pt.
          + apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply z03_cos_peq. intro k. z03_pt. }
      { apply real_eq_of_zero_diff. intro k. z03_pt. }
    + (* the Z02 identity at the ordinate argument, then the weight     *)
      (* association *)
      apply (real_eq_trans _
        (real_mult (z01_lam n)
           (real_mult (z03_eterm n Hn sg)
                      (real_mult (real_const 2)
                         (real_mult (real_plus real_one (z03_coterm n Hn t))
                                    (real_plus real_one (z03_coterm n Hn t))))))).
      * apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        exact (GaC3_Z02_three_cosine_sq
                 (real_mult (real_opp t) (z03_lnreal n Hn))).
      * apply real_eq_of_zero_diff. intro k. z03_pt.
Qed.

(* The combined carrier's real part equals the square-form sum. *)
Theorem z03_comb_sqsum_eq : forall (N : nat) (sg t : Real),
  real_eq (cRe (z03_comb N sg t)) (z03_sqsum N sg t).
Proof.
  intro N. induction N as [| N IH]; intros sg t.
  - cbn [z03_sqsum]. apply real_eq_of_zero_diff. intro k.
    cbn [z03_comb z01_manpart c_plus c_scale cRe cIm fst snd c_zero]. z03_pt.
  - cbn [z03_sqsum].
    apply (real_eq_trans _
      (real_plus
        (real_plus (real_mult (real_const 3)
                     (cRe (z01_manpart z03npos N (sg, real_zero))))
                   (real_plus (real_mult (real_const 4)
                                (cRe (z01_manpart z03npos N (sg, t))))
                              (cRe (z01_manpart z03npos N (sg, real_plus t t)))))
        (real_mult (z01_lam (Datatypes.S N))
                   (real_plus (real_mult (real_const 3)
                                (cRe (c_powq z03npos (Datatypes.S N)
                                        (NatLe_one_S N) (sg, real_zero))))
                              (real_plus (real_mult (real_const 4)
                                           (cRe (c_powq z03npos (Datatypes.S N)
                                                   (NatLe_one_S N) (sg, t))))
                                         (cRe (c_powq z03npos (Datatypes.S N)
                                                 (NatLe_one_S N)
                                                 (sg, real_plus t t)))))))).
    + (* the regrouping of the unfolded step (same atom families) *)
      apply real_eq_of_zero_diff. intro k.
      cbn [z03_comb z01_manpart c_plus c_scale cRe cIm fst snd]. z03_pt.
    + apply RealSetoid.real_eq_plus_compat.
      * (* the N-level three-sum: the assembly face composed with the IH *)
        assert (Hsmall : real_eq
                   (real_plus (real_mult (real_const 3)
                                (cRe (z01_manpart z03npos N (sg, real_zero))))
                              (real_plus (real_mult (real_const 4)
                                           (cRe (z01_manpart z03npos N (sg, t))))
                                         (cRe (z01_manpart z03npos N
                                                 (sg, real_plus t t)))))
                   (cRe (z03_comb N sg t))).
        { apply real_eq_of_zero_diff. intro k.
          cbn [z03_comb c_plus c_scale cRe cIm fst snd]. z03_pt. }
        exact (real_eq_trans _ _ _ Hsmall (IH sg t)).
      * exact (z03_cre_tri (Datatypes.S N) (NatLe_one_S N) sg t).
Qed.
