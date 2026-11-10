(* ConstructiveWorld-Main - statement face of the zeta derivative         *)
(* log-squared bound on the consumer domain (segment-tail node).          *)

(** * GaC2_18_ZetaDerivBound: statement face of node C2-18.

    Mission.  Node C2-18 (segment C2, slot W7, the closing node of the
    segment), statement face minted from the drafts_C2.md C2.18 sketch,
    the sketch form resolved per the module spec conventions: the
    Section slot pair discharged as explicit premise arguments, the
    existence conclusion carried by the nested sigT witness form (no
    bare Prop statements), the modulus comparison carried by
    [c_norm_sq] with zero square-root dependence.  Two named
    statements, kept verbatim from the sketch:
    - [r_pos_lower]: on the consumer domain every point [s0] carries a
      disk radius [r] with the triple witness (r positive; the
      zero-set distance lower-bound face [dist_lb_ok s0 r], the half
      of the zero-set distance registration; and the explicit ball
      geometry [disk_in_consumer T c s0 r]).
    - [zeta_deriv_bound]: the derivative bound on the consumer domain,
      the squared form |zeta'(s0)|^2 <= (C3 * (log cap)^2)^2, the
      zeta-prime carrier [nth_coeff 1 (local_exp zeta_tilde s0)] (the
      C2-12 same-source first-coefficient form; zero global
      differentiable/deriv theory consumed).
    Carrier face (the sketch obligation L25 discharge, defined here
    over the certified base): [consumer_domain] is the explicit
    two-sided carrier sigma >= 1 - c / log(cap) and -cap <= t <= cap
    (the inverse taken on the positive-inverse carrier [real_inv_pos],
    the two-sided bound as a sigT pair, zero absolute-value face); the
    cap carrier [t_cap] is the identity-on-cap discharge, re-aligned
    when the vertical-bound faces land their own cap carrier; [log_t]
    is the premise-carrying log wrapper; [sq] is the square carrier;
    [c_scale'] is the real-argument scalar face of the born [c_scale].
    The sketch obligation L26 ([dist_lb_ok], the zero-set distance
    consumption interface) stays a consumed name aligned to the C2-09
    output form: its defining module is the C2-09 final form, so the
    name enters this face as the sketch-verbatim consumed interface.
    The sketch obligation L25 block ([consumer_domain],
    [disk_in_consumer]) is discharged here.  Numeric face: C3 enters
    as the explicit constant argument of the statement (the sketch
    free constant resolved per the GAPASUME form: constants enter as
    explicit arguments, zero global assumptions); its explicit value
    corridor (the C3 = 4 * C2 / c binding with the vertical-bound
    constant C2 and the consumer-domain constant c) lives in the
    certificate face [GaC2_18_ZetaDerivBound_cert] and binds when the
    mother chain closes.
    Honest scope (fail-loud): the (b) face of the card, the
    higher-order derivative bounds deeper than 1 - c / log(cap) (the
    VK-layer consumption form of segment C3), is NOT in this node's
    closed domain; registered for the C3 survey re-check (high-n on
    the same machine, constant accumulation accounting to C4.3).
    Proof-body state (fail-loud): the two named items are minted at
    the statement face in the Definition-carrier form (the tree
    statement-carrier pattern), so the statements are well-formed and
    their bodies stop exactly at the mother boundary: the four
    consumed names [dist_lb_ok] / [nth_coeff] / [local_exp] /
    [zeta_tilde] and the five segment stems.  The proof routes are
    registered on each item (the card route: C2-10 local expansion of
    zeta-tilde on the disk, C2-16/17 vertical bound |zeta| <= C2 log,
    C2-12 n=1 coefficient form giving |zeta'| <= 2 M / r, C2-09
    zero-set membership giving the radius face); the bodies close and
    promote to Lemma form when the mother chain lands, per the work
    order (compile lane conditional, not burned while the chain is
    open).  Segment-tail position: this node feeds the segment
    interface file GaC2_Iface_VL (the eight-node block, produced at
    the wave-end joint certification, never earlier).

    Dependencies.  Stdlib [QArith.QArith].  Requires [S02_CauchyComplete]
    ([Real], [real_zero], [real_one], [real_const], [real_plus],
    [real_mult], [real_opp], [real_lt_trans], [real_lt_zero_one],
    [real_log_one], [real_log_lt_mono], the order algebra), the
    positive-inverse carrier via [S03_QExp] ([real_inv_pos]), the log
    wrapper base via [S07_RealSetoidExpLog] ([real_log]), [CxRealPairCore]
    ([Cx], [cRe], [cIm], [c_plus], [c_opp], [c_norm_sq]),
    [CxRealPairExpLog], the segment dependency stems [GaC2_09_DenomZeroSet]
    (the zero-set distance consumption interface, the L26 alignment
    target), [GaC2_10_EtaContinuation], [GaC2_12_CauchyCoeffEst],
    [GaC2_16_ZetaVerticalBound], [GaC2_17_StripVerticalAsm].

    References.  drafts_C2.md C2.18 (sketch one study card, sketch two
    statement face, sketch four acceptance: the base five plus the
    node specials - the squared-carrier registration, the five-stem
    consumption census at five positions or more, the honest-scope
    line, the interface-file position); cards_C2.md C2.18 card (the
    attainable grading: all-chain consumption assembly, zero new
    method pieces); gamma_module_spec.md section 3.3 the W7 row
    (C2-18 over C2.09/10/12/16/17); Titchmarsh section 3.9 the
    derivative-bound consumption form.

    Constructivity.  Every statement Set-sorted: the order predicates
    are the Set-sorted [real_lt] / [real_le], the existence face is
    the nested [sigT] witness form, the two-sided bound is the sigT
    pair, zero assumed constants, zero abandoned proofs, zero
    classical principles, the Section slot pair discharged as explicit
    premise arguments so every named item stays Closed under the
    global context.

    Build.  [coqc -native-compiler no -q -Q . ""
    GaC2_18_ZetaDerivBound.v] from the flat build directory; the lane
    is conditional on the mother chain (the C2-09 final form and the
    C2-10/12/16/17 faces) and stays closed until it lands; the static
    track of the toolkit accept script passed for this file pair in
    the static mode. *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_09_DenomZeroSet.
Require Import GaC2_10_EtaContinuation.
Require Import GaC2_12_CauchyCoeffEst.
Require Import GaC2_16_ZetaVerticalBound.
Require Import GaC2_17_StripVerticalAsm.

From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The consumer-domain carrier block (sketch obligation L25).  *)
(* ===================================================================== *)

(* The cap carrier: the identity-on-cap discharge of the sketch cap      *)
(* projection; re-aligned when the vertical-bound faces land their own   *)
(* cap carrier.                                                          *)
Definition t_cap (T : Real) : Real := T.

(* The log wrapper on the cap, premise-carrying: the tree log needs the  *)
(* positivity premise, discharged from the one-strict premise through    *)
(* the order chain (zero < one < cap).                                   *)
Definition log_t (T : Real) (HT1 : real_lt real_one (t_cap T)) : Real :=
  real_log (t_cap T)
    (real_lt_trans real_zero real_one (t_cap T) real_lt_zero_one HT1).

(* The square carrier (the sketch [sq] name). *)
Definition sq (x : Real) : Real := real_mult x x.

(* The real-argument scalar face of the born complex scalar carrier      *)
(* (the sketch [c_scale'] name; the born [c_scale] stays the complex     *)
(* face).                                                                *)
Definition c_scale' (a x : Real) : Real := real_mult a x.

(* The consumer domain (sketch obligation L25): sigma >= 1 - c / log(cap *)
(* ) and the two-sided imaginary bound -cap <= t <= cap, all Set-sorted, *)
(* the inverse on the positive-inverse carrier, zero absolute-value      *)
(* face, zero division carrier.                                          *)
Definition consumer_domain
  (T c : Real) (HT1 : real_lt real_one (t_cap T))
  (Hlogpos : real_lt real_zero (log_t T HT1)) (s0 : Cx) : Set :=
  sigT
    (fun Hsigma :
       real_le
         (real_plus real_one
            (real_opp (c_scale' c (real_inv_pos (log_t T HT1) Hlogpos))))
         (cRe s0) =>
     sigT (fun _ : real_le (real_opp (t_cap T)) (cIm s0) =>
       real_le (cIm s0) (t_cap T))).

(* The explicit ball geometry (sketch obligation L25): the disk of       *)
(* radius [r] around [s0] sits inside the consumer domain, carried on    *)
(* the squared distance (zero square-root dependence).                   *)
Definition disk_in_consumer
  (T c : Real) (HT1 : real_lt real_one (t_cap T))
  (Hlogpos : real_lt real_zero (log_t T HT1)) (s0 : Cx) (r : Real) : Set :=
  forall z : Cx,
    real_le (c_norm_sq (c_plus z (c_opp s0))) (sq r) ->
    consumer_domain T c HT1 Hlogpos z.

(* ===================================================================== *)
(* Section 2. The two named statements (sketch-verbatim names).           *)
(* ===================================================================== *)

(* Statement carrier of [r_pos_lower]: the local disk radius face with   *)
(* the triple sigT witness.  Sketch Section slot pair (T, HT) discharged *)
(* as the explicit premise block; the sketch bare [log_t T] form gains   *)
(* its premise pair (the derivability from the two-bound premise HT      *)
(* through one-strict-cap then log-positive is registered for the proof  *)
(* body via the strict-weak order chain and the log monotonicity).       *)
(* Proof route (the card route): the C2-09 zero-set membership - the     *)
(* zero set sits on the unit-vertical line - plus the consumer-domain    *)
(* distance algebra give the radius witness as half the zero-set         *)
(* distance with the explicit lower bound; the ball geometry then        *)
(* replays the consumer-domain algebra along the disk.                   *)
Definition r_pos_lower
  (T c : Real) (HT : real_le (real_const 2#1) (t_cap T))
  (HT1 : real_lt real_one (t_cap T))
  (Hlogpos : real_lt real_zero (log_t T HT1))
  (s0 : Cx) (Hdom : consumer_domain T c HT1 Hlogpos s0) : Set :=
  sigT (fun r : Real =>
    sigT (fun _ : real_lt real_zero r =>
      sigT (fun _ : dist_lb_ok s0 r =>
        disk_in_consumer T c HT1 Hlogpos s0 r))).

(* Statement carrier of [zeta_deriv_bound]: the derivative bound on the  *)
(* consumer domain in the squared form, the zeta-prime carrier the       *)
(* C2-12 same-source first-coefficient form.  C3 enters as the explicit  *)
(* constant argument (the sketch free constant; the explicit value       *)
(* corridor lives in the certificate face and binds at mother-chain      *)
(* integration).                                                         *)
(* Proof route (the card route): zeta-tilde expands locally on the disk  *)
(* (C2-10), the vertical bound |zeta| <= C2 log on the disk (C2-16/17),  *)
(* the C2-12 n=1 coefficient form gives |zeta'| <= 2 M / r, and with     *)
(* r >= c / (2 log(cap)) on the consumer domain the constant closes at   *)
(* C3 = 4 C2 / c, explicit.                                              *)
Definition zeta_deriv_bound
  (T c : Real) (HT : real_le (real_const 2#1) (t_cap T))
  (HT1 : real_lt real_one (t_cap T))
  (Hlogpos : real_lt real_zero (log_t T HT1))
  (C3 : Real)
  (s0 : Cx) (Hdom : consumer_domain T c HT1 Hlogpos s0) : Set :=
  real_le (c_norm_sq (nth_coeff 1 (local_exp zeta_tilde s0)))
          (sq (c_scale' C3 (sq (log_t T HT1)))).
