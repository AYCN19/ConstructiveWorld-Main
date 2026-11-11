(** * GaC2_17_StripVerticalAsm: statement face of node C2-17.

    Mission.  Node C2-17, the strip face of the vertical-line bound
      assembly, statement face minted from the drafts_C2.md C2.17
      sketch: the two sketch-verbatim named statements
      [zeta_strip_uniform] / [zeta_strip_cover] plus the L24 carrier
      block (routes, consumed-name registration and honest scope in
      the Notes block).

    Dependencies.  Stdlib [QArith.QArith]; [S02_CauchyComplete],
      [S03_QExp] ([cauchy_real_exp], [real_inv_pos]), [S07_RealSetoidExpLog]
      ([real_log], [real_const_pos]), [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_07_DirichletTestAbel],
      [GaC2_10_EtaContinuation], [GaC2_16_ZetaVerticalBound],
      [GaC2_02_AbsConvTailBound_a].

    References.  drafts_C2.md C2.17 (sketches one / two / four);
      cards_C2.md C2.17; gamma_module_spec.md section 3.3 the W6
      row; Titchmarsh Ch.1 the eta-route vertical bound.

    Constructivity.  Every statement Set-sorted: order premises are
      the Set-sorted [real_lt] / [real_le]; the corridor and the
      inverse are premise-carrying Set carriers; zero assumed
      constants, zero abandoned proofs, zero classical principles.

    Build.  [coqc -native-compiler no -q -Q . ""
      GaC2_17_StripVerticalAsm.v]; the lane is conditional on the
      mother chain (the C2-07/10/16 faces) and stays closed until it
      lands. *)

Require Import S02_CauchyComplete.
(** Notes.  Statement routes, consumed-name registration, honest scope.

    Sketch resolution conventions: the Section slot triple (delta,
    its zero-strict premise, its one-cap premise) is discharged as
    explicit premise arguments (no Section wrapper); the sketch Q
    literals are lifted to the born [real_const] face; the order
    premises are carried by the Set-sorted [real_lt] / [real_le].
    Constructivity tail: the Section slot triple discharged as
    explicit premise arguments so every named item stays Closed
    under the global context once the mother chain lands.

    [zeta_strip_uniform] detail: the (a) uniform band face on
    0 <= sigma <= 1 - delta in the squared form
    |zeta(s)|^2 <= (2 / (2^delta - 1))^2 through the eta route
    (|zeta| = |eta| / |1 - 2^{1-s}|, |eta| <= 1 + 2 * 2^{-sigma} <= 3
    on the C2-07 uniform-tail face, the denominator lower bound
    2^{1-sigma} - 1 by the modulus algebra, zero periodicity
    dependence; the card (a) chain 2 / (2^{1-sigma} - 1) <=
    2 / (2^delta - 1) locked factor by factor).
    [zeta_strip_cover] detail: the (c) consumer-domain cover face on
    0 <= sigma <= 2; the near-one band is the C2-16 (c) face, never
    re-proved here; the band boundaries stay explicit on the
    disjunction carrier.

    Carrier block (sketch obligation L24 discharge, defined over the
    certified base): [ltwo] is the closed ln-2 witness on the
    premise-carrying born log (its positivity premise closed at the
    rational decidable face); [two_pow] is the power face
    exp(delta * ln 2) over the born exponential carrier;
    [two_d_sub] is the corridor 2^delta - 1 (the sketch := form,
    kept literal); [c_invq] is the sketch inverse name resolved to
    the born premise-carrying positive inverse [real_inv_pos] (the
    sigT inverse-witness face; its premise is the corridor
    positivity witness); [sq] and [c_scale'] are the squared and
    real-scalar carriers (the C2-18 same-shape faces).  The corridor
    positivity witness [Hsub] enters as the explicit premise of the
    named statement (the L24 face: the discharge route runs through
    the slot premises Hd / Hd1 via the exponential monotonicity
    chain, registered for the proof work, zero global assumption).

    Consumed names (mother-boundary registration): the eta carrier
    [zeta_tilde] with its nonzero-denominator premise [denom_nz]
    enters from the C2-10 face, the three-band disjunction
    [zeta_vert_bound_disj] enters from the C2-16 face (the sketch
    disjunction row minted here per the draft L-obligation on the
    actual C2-16 band carriers; the two branch witness bundles ride
    the branch, the near-one band stays the C2-16 (c) face, never
    re-proved); both are the sketch-verbatim consumed interfaces, so
    the statement bodies stop exactly at the mother boundary and the
    file carries the well-formed statement face only (verified
    well-formed against the certified base).

    Mother-chain integration note: the consumption faces are
    re-aligned to the landed mother signatures - [denom_nz eps_lb s]
    / [zeta_tilde eps_lb s Hep Hd Heta] with the eta-value premise
    slot [d10_eta_conv] carried explicitly (the C2-10 registered
    re-alignment).

    Proof-body state: the two named items are minted at the
    statement face in the Definition-carrier form (the tree
    statement-carrier pattern); the proof routes are registered on
    each item (the card route: the C2-07 uniform tail, the C2-08
    denominator lower bound [denom_lower_bound] consumed through the
    C2-10 face chain, the C2-16 (c) direct consumption for the
    cover; re-proving forbidden per the card); the bodies close and
    promote to Lemma form when the mother chain lands.  Downstream
    position: this stem is a Require of the C2-18 derivative face
    already parked at its statement form; the certificate face
    [GaC2_17_StripVerticalAsm_cert] is base-standalone (Stdlib only)
    and stands as its own node.

    Honest scope (declared openly): the full-strip convexity face
    |zeta(1/2+it)| <= C * t^{1/4+eps} (the log-cubed stock) needs
    the functional equation's sigma = 0 end t^{1/2} bound; the FE
    node is not in the KB34 C1-C4 list and is not in this segment -
    registered openly (the C3/C4 survey resolves by the log-squared
    caliber or a FE node re-review; the KB34 down-chain case alpha
    took the log-squared caliber, consistent).  Zero FE consumption
    on this face: no functional-equation name enters any Require or
    statement of this file.

    Require-face notes: the draft Require header of drafts_C2.md
    C2.17 named S02, the two born pair carriers and the three
    stems; this face adds [S03_QExp] and [S07_RealSetoidExpLog] for
    the power, inverse and log carrier block (the registered
    addition, the C2-18 same-shape header move).  The C2-09 mother
    stays out of this Require face (it is not a dependency of this
    node's row in gamma_module_spec.md section 3.3).
    [GaC2_02_AbsConvTailBound_a] supplies [nat_real_pos], threading
    the C2-16 discharged Hnpos slot (the one-line Require seam of
    the mother-chain integration). *)

Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_07_DirichletTestAbel.
Require Import GaC2_10_EtaContinuation.
Require Import GaC2_16_ZetaVerticalBound.
Require Import GaC2_02_AbsConvTailBound_a.

From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The corridor carrier block (sketch obligation L24).         *)
(* ===================================================================== *)

(* ln 2 on the born premise-carrying log; the positivity premise is the  *)
(* rational decidable face, closed here.                                 *)
Lemma ltwo_pos : real_lt real_zero (real_const (2#1)).
Proof. apply real_const_pos. unfold QltT, Qlt_bool. reflexivity. Qed.

Definition ltwo : Real := real_log (real_const (2#1)) ltwo_pos.

(* The power face 2^delta = exp(delta * ln 2). *)
Definition two_pow (delta : Real) : Real :=
  cauchy_real_exp (real_mult delta ltwo).

(* The corridor 2^delta - 1 (the sketch [two_d_sub] := form, literal). *)
Definition two_d_sub (delta : Real) : Real :=
  real_plus (two_pow delta) (real_opp real_one).

(* The sketch inverse name, resolved to the born positive-inverse        *)
(* carrier (the sigT inverse-witness face; the premise is the corridor   *)
(* positivity witness Hsub on the named statement).                      *)
Definition c_invq (x : Real) (Hx : real_lt real_zero x) : Real :=
  real_inv_pos x Hx.

(* The square carrier (the sketch [sq] name; the C2-18 same shape). *)
Definition sq (x : Real) : Real := real_mult x x.

(* The real-argument scalar face of the born complex scalar carrier      *)
(* (the sketch [c_scale'] name; the born [c_scale] stays the complex     *)
(* face).                                                                *)
Definition c_scale' (a x : Real) : Real := real_mult a x.

(* The C2-16 band consumption carrier (the sketch disjunction row: the   *)
(* draft L-obligation discharged here on the actual C2-16 face).  Two    *)
(* branches - the (b) mid band and the (c) near-one window band - each   *)
(* carrying its band witness bundle inside the branch (the C2-10         *)
(* compound-existence precedent); the (a) band enters through this       *)
(* node's own uniform face.                                              *)
Definition zeta_vert_bound_disj (s : Cx) : Set :=
  sigT (fun b : bool =>
    match b with
    | true =>
        sigT (fun t : Real =>
          sigT (fun Ht2 : real_le (real_const (2#1)) t =>
            sigT (fun Ht1 : real_lt real_one t =>
              sigT (fun Hlogpos : real_lt real_zero (log_t t Ht1) =>
                sigT (fun C1 : Real =>
                  sigT (fun Hs1 : real_le real_one (cRe s) =>
                    sigT (fun Hs2 : real_le (cRe s) (real_const (2#1)) =>
                      zeta_vert_mid nat_real_pos t Ht2 Ht1 Hlogpos C1 s
                        Hs1 Hs2)))))))
    | false =>
        sigT (fun t : Real =>
          sigT (fun Ht1 : real_lt real_one t =>
            sigT (fun Hlogpos : real_lt real_zero (log_t t Ht1) =>
              sigT (fun c_win : Real =>
                sigT (fun C2 : Real =>
                  sigT (fun Hwin : real_le
                          (real_plus real_one
                             (real_opp (c_scale' c_win
                                (real_inv_pos (log_t t Ht1) Hlogpos))))
                          (cRe s) =>
                    sigT (fun Hslt : real_lt (cRe s) real_one =>
                      zeta_vert_near1 nat_real_pos t Ht1 Hlogpos c_win C2 s
                        Hwin Hslt)))))))
    end).

(* ===================================================================== *)
(* Section 2. The two named statements (sketch-verbatim names).           *)
(* ===================================================================== *)

(* Statement carrier of [zeta_strip_uniform]: the (a) uniform band, the  *)
(* squared form of the card chain 2 / (2^{1-sigma} - 1) <= 2 / (2^delta  *)
(* - 1), the eta-route assembly consumed on the statement right side     *)
(* through [zeta_tilde].  Proof route (the card route): |zeta| = |eta| / *)
(* |1 - 2^{1-s}|, the C2-07 uniform tail |eta| <= 1 + 2 * 2^{-sigma} <=  *)
(* 3, the C2-08 denominator lower bound 2^{1-sigma} - 1 through the      *)
(* C2-10 face chain, then the delta cap.                                 *)
Definition zeta_strip_uniform
  (eps_lb delta : Real) (Hep : real_lt real_zero eps_lb)
  (Hd : real_lt real_zero delta)
  (Hd1 : real_le delta real_one)
  (Hsub : real_lt real_zero (two_d_sub delta)) : Set :=
  forall (s : Cx) (Heta : d10_eta_conv s) (Hd2 : denom_nz eps_lb s),
    real_le real_zero (cRe s) ->
    real_le (cRe s) (real_plus real_one (real_opp delta)) ->
    real_le (c_norm_sq (zeta_tilde eps_lb s Hep Hd2 Heta))
            (sq (c_scale' (real_const (2#1)) (c_invq (two_d_sub delta) Hsub))).

(* Statement carrier of [zeta_strip_cover]: the (c) consumer-domain      *)
(* cover on 0 <= sigma <= 2, the C2-16 three-band disjunction consumed   *)
(* directly (the (b) near-one band is the C2-16 (c) face; re-proving is  *)
(* forbidden per the card).  Proof route (the card route): the (a) band  *)
(* plus the near-one window merge into the disjunction carrier.          *)
Definition zeta_strip_cover
  (delta : Real) (Hd : real_lt real_zero delta)
  (Hd1 : real_le delta real_one) : Set :=
  forall (s : Cx),
    real_le real_zero (cRe s) ->
    real_le (cRe s) (real_const (2#1)) ->
    zeta_vert_bound_disj s.
