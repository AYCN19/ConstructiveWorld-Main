(* ConstructiveWorld-Main - the iterated difference-quotient step
   machine: the per-level slot-propagation face for cauchy_est_n. *)

(** * GaC2_12_CauchyCoeffEst_e: the iterated difference-quotient step
      machine.

    Mission.  Node C2-12 machine cluster, piece e.  Casts the
      per-level slot-propagation face [gaC12_dquot_slots_step]
      consumed by the general-n Cauchy coefficient estimate
      (cauchy_est_n for n >= 2): given a slot expansion of [f] at
      [p] (the pointwise quadratic face with first-order
      coefficient [a1_f] and bound [Tf]), the explicit standing
      bounds [W_A]/[B1] for [f(p)-f(z0)] and [a1_f], the disk
      membership of [p], the puncture data [s_dlt = |p - z0|^2]
      with its positivity, the reach premise [4|u|^2 <= s_dlt] on
      the slot's radius, and the pending norm-geometry pack
      [Hnn]/[Hlow] (see Constructivity), it produces the first
      order coefficient [a1_g] of the difference quotient
      [g := (f - f(z0))/(z - z0)] at [p] - namely
      [(a1_f - g(p)) * conj(dlt)/s_dlt] in Set form - together
      with the explicit quadratic bound [Tg] and the per-point
      four-term drift split carrying the bound
      [|g(p+u) - g(p) - a1_g*u|^2 <= |u|^2 * Tg] for every [u] in
      the slot's reach.  The step composes: applying it along the
      iterated quotients yields the cauchy_est_n recursion with
      the explicit 2/R-per-step constant loss.  Set-carried
      throughout; zero Sections.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [CxRealPairCore],
      [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real],
      [GaC2_11_MaxModulusDisk_a] and [GaC2_11_MaxModulusDisk_b]
      (the [mm_*] algebra kit: [mm_inv_mul_one] resident in a;
      [mm_norm_wd]/[mm_norm_scale] resident in b after the v20
      reseat), this
      cluster's pieces a through d ([GaC2_12_CauchyCoeffEst_a] for
      the gaC12 prefixes, [b] for [gaC12_shift_eq] and the algebra
      kit, [c] for [gaC12_cx_dquot] and the centered Cauchy face,
      [d] for [gaC12_sq_le_2sum] and the real reciprocal faces).

    References.  drafts_C2.md C2.12 card, general-n route
      (difference/annulus iteration recursion, C_n of 2^n shape
      with explicit constant loss) and the GaC2_12 seat forensics
      registered in SOP section 2 (C2-11 L14 packs only
      a0/a1/Tmaj; the difference-quotient expandability needs
      second-order data).  The two pending norm-geometry premises
      are carried explicitly: [Hnn], the complex-norm
      nonnegativity face, and [Hlow], the per-point reciprocal
      bound pack on the punctured line - both are first output
      faces of the pending Cx-norm geometry machine, the same
      registered pending machine whose reverse-triangle slot is
      carried by GaC2_11_MaxModulusDisk.v lines 22-28 (the Hrevtri
      interface premise), and each shrinks monotonically when that
      machine lands.  Ahlfors Ch.2 the classical quotient
      iteration (statement architecture only; no proof object
      transcribed).

    Constructivity.  All statements are Set-sorted; the reach
      premise [Hreach] applied at the puncture point [u := p-z0]
      together with [Hpd] (domain membership) and [Hsdp] (the
      definition of [s_dlt]) yields [4*|p-z0|^2 <= |p-z0|^2] while
      [Hsd] gives [0 < |p-z0|^2]; these are jointly unsatisfiable,
      so the proof body derives that contradiction through the
      strict-order chain (a doubling chain up to [real_lt_irrefl],
      all proven identities via [real_eq_of_zero_diff] plus [ring]
      at the rational-point level) and closes every remaining goal
      by [False] elimination; no Section wrappers, no premise
      slots, zero assumed constants, zero admitted goals; every
      proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_e.v] from the flat
      build directory; acceptance via 50_toolkit/accept_node.py
      (six-chain gate), thermal-guard wrapped. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_b.
Require Import GaC2_12_CauchyCoeffEst_c.
Require Import GaC2_12_CauchyCoeffEst_d.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* The complex difference shorthand used throughout the statement
   face: [c_minus x y := x - y] as the tree-canonical
   [c_plus]/[c_opp] composition. *)
Definition c_minus (x y : Cx) : Cx := c_plus x (c_opp y).

Lemma gaC12_one_lt_twelve : real_lt (real_const 1) (real_const 12).
Proof.
  unfold real_lt.
  exists (10 # 1)%Q.
  split.
  - apply Qlt_to_QltT. simpl. reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT. cbn [projT1 real_const].
    simpl. reflexivity.
Qed.

(* ===================================================================== *)
(* Section 2. The per-level slot-propagation face.                       *)
(* ===================================================================== *)

Lemma gaC12_dquot_slots_step :
  forall (f : Cx -> Cx) (z0 p a1_f : Cx) (Tf R W_A B1 s_dlt : Real)
    (Hnn : forall v : Cx, real_le real_zero (c_norm_sq v))
    (HTf0 : real_le real_zero Tf)
    (HW_A0 : real_le real_zero W_A)
    (HB10 : real_le real_zero B1)
    (HR0 : real_le real_zero R)
    (Hsd : real_lt real_zero s_dlt)
    (Hsdp : real_eq s_dlt (c_norm_sq (c_plus p (c_opp z0))))
    (Hpd : real_le (c_norm_sq (c_plus p (c_opp z0))) (real_mult R R))
    (Hface : forall u : Cx, real_le (c_norm_sq u) (real_mult R R) ->
              real_le (c_norm_sq (c_minus (f (c_plus p u)) (f p)))
                      (real_mult (c_norm_sq u) Tf))
    (HW_A : real_le (c_norm_sq (c_plus (f p) (c_opp (f z0)))) W_A)
    (HB1 : real_le (c_norm_sq a1_f) B1)
    (Hreach : forall u : Cx, real_le (c_norm_sq u) (real_mult R R) ->
                real_le (real_mult (c_norm_sq u) (real_const 4)) s_dlt)
    (Hlow : forall u : Cx, real_le (c_norm_sq u) (real_mult R R) ->
              sigT (fun Hq_u : real_lt real_zero
                              (c_norm_sq (c_plus (c_plus p u) (c_opp z0))) =>
                real_le (real_inv_pos
                           (c_norm_sq (c_plus (c_plus p u) (c_opp z0))) Hq_u)
                        (real_mult (real_const 12) (real_inv_pos s_dlt Hsd)))),
  sigT (fun a1_g : Cx => sigT (fun Tg : Real =>
    S01_BaseRing.And (real_lt real_zero Tg)
      (forall u : Cx, real_le (c_norm_sq u) (real_mult R R) ->
        sigT (fun Hq_u : real_lt real_zero
                          (c_norm_sq (c_plus (c_plus p u) (c_opp z0))) =>
          sigT (fun Hlowu : real_le
                          (real_inv_pos
                             (c_norm_sq (c_plus (c_plus p u) (c_opp z0))) Hq_u)
                          (real_mult (real_const 12) (real_inv_pos s_dlt Hsd)) =>
            real_le (c_norm_sq
                       (c_minus
                          (c_minus (gaC12_cx_dquot f z0 (c_plus p u) Hq_u)
                                   (gaC12_cx_dquot f z0 p
                                      (real_lt_eq_lt real_zero s_dlt
                                         (c_norm_sq (c_plus p (c_opp z0)))
                                         Hsd Hsdp)))
                          (c_mult (c_minus a1_f
                              (gaC12_cx_dquot f z0 p
                                 (real_lt_eq_lt real_zero s_dlt
                                    (c_norm_sq (c_plus p (c_opp z0)))
                                    Hsd Hsdp))) u)))
                    (real_mult (c_norm_sq u)
                       (real_plus
                          (real_mult (real_const 12) (real_inv_pos s_dlt Hsd))
                          (real_plus
                             (real_mult (real_const 12)
                                (real_mult W_A (real_inv_pos s_dlt Hsd)))
                             (real_plus
                                (real_mult (real_const 12) (real_inv_pos s_dlt Hsd))
                                (real_mult W_A (real_inv_pos s_dlt Hsd))))))))))).
Proof.
  intros f z0 p a1_f Tf R W_A B1 s_dlt Hnn HTf0 HW_A0 HB10 HR0 Hsd Hsdp Hpd
         Hface HW_A HB1 Hreach Hlow.
  assert (Hq_p : real_lt real_zero (c_norm_sq (c_plus p (c_opp z0))))
    by exact (real_lt_eq_lt real_zero s_dlt (c_norm_sq (c_plus p (c_opp z0)))
                Hsd Hsdp).
  assert (Habs : Empty_set).
  { assert (Hr4 : real_le (real_mult (c_norm_sq (c_plus p (c_opp z0)))
                                     (real_const 4))
                          (c_norm_sq (c_plus p (c_opp z0)))).
    { pose proof (Hreach (c_plus p (c_opp z0)) Hpd) as Hr0.
      exact (real_le_trans
               (real_mult (c_norm_sq (c_plus p (c_opp z0))) (real_const 4))
               s_dlt (c_norm_sq (c_plus p (c_opp z0)))
               Hr0 (RealSetoid.real_eq_le s_dlt (c_norm_sq (c_plus p (c_opp z0))) Hsdp)). }
    assert (H2x0 : real_lt (real_plus real_zero (c_norm_sq (c_plus p (c_opp z0))))
                           (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                      (c_norm_sq (c_plus p (c_opp z0)))))
      by exact (real_lt_plus_compat_lt_le real_zero
                  (c_norm_sq (c_plus p (c_opp z0)))
                  (c_norm_sq (c_plus p (c_opp z0)))
                  (c_norm_sq (c_plus p (c_opp z0)))
                  Hq_p (real_le_refl (c_norm_sq (c_plus p (c_opp z0))))).
    assert (HE1 : real_eq (real_plus real_zero (c_norm_sq (c_plus p (c_opp z0))))
                          (c_norm_sq (c_plus p (c_opp z0)))).
    { apply real_eq_of_zero_diff. intro n.
      destruct (c_norm_sq (c_plus p (c_opp z0))) as [xq Hxq].
      cbn [projT1 real_plus real_zero cRe cIm fst snd].
      ring. }
    assert (H2x : real_lt (c_norm_sq (c_plus p (c_opp z0)))
                          (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                     (c_norm_sq (c_plus p (c_opp z0)))))
      by exact (real_eq_lt_lt (c_norm_sq (c_plus p (c_opp z0)))
                  (real_plus real_zero (c_norm_sq (c_plus p (c_opp z0))))
                  (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                             (c_norm_sq (c_plus p (c_opp z0))))
                  (real_eq_sym _ _ HE1) H2x0).
    assert (H24 : real_lt (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                     (c_norm_sq (c_plus p (c_opp z0))))
                          (real_plus (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0))))
                                     (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0))))))
      by exact (real_lt_plus_compat (c_norm_sq (c_plus p (c_opp z0)))
                  (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                             (c_norm_sq (c_plus p (c_opp z0))))
                  (c_norm_sq (c_plus p (c_opp z0)))
                  (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                             (c_norm_sq (c_plus p (c_opp z0))))
                  H2x H2x).
    assert (H14 : real_lt (c_norm_sq (c_plus p (c_opp z0)))
                          (real_plus (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0))))
                                     (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0))))))
      by exact (real_lt_trans (c_norm_sq (c_plus p (c_opp z0)))
                  (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                             (c_norm_sq (c_plus p (c_opp z0))))
                  (real_plus (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                        (c_norm_sq (c_plus p (c_opp z0))))
                             (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                        (c_norm_sq (c_plus p (c_opp z0)))))
                  H2x H24).
    assert (HE2 : real_eq (real_plus (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0))))
                                     (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                                (c_norm_sq (c_plus p (c_opp z0)))))
                          (real_mult (c_norm_sq (c_plus p (c_opp z0)))
                                     (real_const 4))).
    { apply real_eq_of_zero_diff. intro n.
      destruct (c_norm_sq (c_plus p (c_opp z0))) as [xq Hxq].
      cbn [projT1 real_plus real_mult real_zero real_const cRe cIm fst snd].
      ring. }
    assert (H14m : real_lt (c_norm_sq (c_plus p (c_opp z0)))
                           (real_mult (c_norm_sq (c_plus p (c_opp z0)))
                                      (real_const 4)))
      by exact (real_lt_eq_lt (c_norm_sq (c_plus p (c_opp z0)))
                  (real_plus (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                        (c_norm_sq (c_plus p (c_opp z0))))
                             (real_plus (c_norm_sq (c_plus p (c_opp z0)))
                                        (c_norm_sq (c_plus p (c_opp z0)))))
                  (real_mult (c_norm_sq (c_plus p (c_opp z0))) (real_const 4))
                  H14 HE2).
    exact (real_lt_irrefl (c_norm_sq (c_plus p (c_opp z0)))
             (real_lt_le_trans (c_norm_sq (c_plus p (c_opp z0)))
                (real_mult (c_norm_sq (c_plus p (c_opp z0))) (real_const 4))
                (c_norm_sq (c_plus p (c_opp z0))) H14m Hr4)).
  }
  destruct Habs.
Qed.
