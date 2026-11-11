(* ConstructiveWorld-Main - statement face of the eta quotient continuation. *)
(** * GaC2_10_EtaContinuation: the eta quotient continuation face of node C2-10.
    Mission.  Node C2-10 (slot W4): the eta-continuation node of the C2.18 closing
    chain - zeta-tilde on the denominator nonzero domain.  Sketch names kept:
    [denom_nz], [zeta_tilde], [zeta_tilde_agree] (the (a) face),
    [zeta_tilde_analytic] (the (b) face), [zeta_tilde_unif_bound] (the (c) face,
    weight faces [w_one] / [w_sq]); the machine cluster closes now.  Statement
    faces, carrier state, honest boundary (card row (d)), the GAPASUME discharge
    and the registered adaptations: the Notes block after the requires (fail-loud).

    Dependencies.  Stdlib [QArith.QArith].  Requires [S01_BaseRing] (selective [NatLe] import),
    [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog],
    [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_01_DirichletPartialSum], [GaC2_02_AbsConvTailBound_a],
    [GaC2_09_DenomZeroSet_b]; zero cross-segment requires (consumed names: the Notes block).

    References.  drafts_C2.md C2.10 statement sketch; cards_C2.md C2.10 (the (a)-(d)
    proposition rows, the certificate row sigma0 in {1/2, 1}); the F7 precedent
    mapping rows (statement shape only, the mathlib Hurwitz route not absorbed);
    Titchmarsh Ch.2 the eta continuation quotient (statement architecture only).

    Constructivity.  Every named construction is carried by [Set]; the order predicates
    are the Set-sorted [real_lt] / [real_le]; no Section, no Hypothesis, no assumed
    constant, no global assumption; the machine cluster proofs close under the global
    context; the statement carriers are Set-typed with the proof routes registered.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> "" -Q <build dir> "" GaC2_10_EtaContinuation.v]
    (flat build directory, thermal guard wrapper); acceptance runs [50_toolkit/accept_node.py --node C2.10]
    with the certificate face [GaC2_10_EtaContinuation_cert] (base-standalone, Stdlib QArith only). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_09_DenomZeroSet_b.
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(** Notes.  Named-item statement faces.  [denom_nz]: the sketch body verbatim,
    [real_lt eps_lb (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s))))]; the
    sketch free constant [eps_lb] discharged as the explicit leading argument
    (the GAPASUME rule: constants enter as explicit arguments, zero global
    assumptions); this is the L13 local-constant slot, the disk dependent lower
    bound, sampled on the certificate face.  [zeta_tilde]: the quotient carrier
    eta / (1 - 2^(1-s)); the sketch product form [c_mult eta_s (c_inv_wit
    (nz_wit Hd))] realized division-free as the conjugate-pair scale [c_scale
    (c_inv_wit |d|^2 wit) (c_mult eta_s (c_conj d))] with [d] the denominator
    (the witness inverse [c_inv_wit] is Real-typed, so the complex quotient runs
    through the conjugate pair and the squared-modulus witness - the house
    squared carrier form); [nz_wit] realized by the machine lemma [denom_sq_pos]
    deriving the positivity witness from the [denom_nz] premise.
    [zeta_tilde_agree]: the sketch conclusion [c_eq (zeta_tilde s Hd) zeta_s]
    with [zeta_s] realized as the premised zeta value carrier [projT1 Hz], where
    [d10_zeta_conv] is the explicit-tail zeta value interface (the C2.02
    condensation + C2.08 limit identity consumption slot, discharged at
    mother-chain integration).  [zeta_tilde_analytic]: the sketch sigT
    coefficient form realized as the nested carrier - a positive radius, the
    coefficient sequence [c_n : nat -> Cx], the denominator bounded below on the
    closed disk (the L13 local face), the series value agreed with [zeta_tilde]
    on the disk, and the uniform rational-margin Cauchy tails of the partial sums
    (the C1-15 same-shape series Cauchy form, the R3 wave-end cross-check row of
    GaC2_Iface_Eta).  [zeta_tilde_unif_bound]: the sketch conclusion [real_le
    (c_norm_sq (zeta_tilde s Hd)) (w_sq sig0 ...)] with the minted weight faces
    [w_one] / [w_sq] (the |eta| corridor 1 + 2 * 2^{-sigma0}, the two-power face
    read off the C2-09 carrier at the real point 1 + sigma0) times the witness
    inverse of the squared denominator modulus (the |1 - 2^(1-s)|^{-1} weighting,
    the lower bound routed through the C2-09 zero-set faces).

    Statement-carrier state (fail-loud): the three named statements are minted
    in the Definition-carrier form (the tree statement-carrier pattern, the
    GaC2_18 precedent): their bodies are the well-formed Set statement types,
    their proof routes stop at the mother boundary because the draft routes
    consume rows not yet in the tree - the (a) route consumes the C2.08 eta-zeta
    limit identity, the (b) route is the Weierstrass double series constructive
    land (the card breakthrough terrain, zero in-tree precedent), the (c) route
    consumes the C2.07 uniform eta tail; the C2.07 [GaC2_07_DirichletTestAbel]
    and C2.08 [GaC2_08_EtaZetaRelation] rows have no module in the tree at cast
    time (the GaC2_Iface_Eta whitelist rows are open), so the eta value enters
    through the explicit premise carrier [d10_eta_conv] (the alternating-tail
    modulus interface, the C2.07 consumption slot) and the discharge lands when
    those rows cast.  The machine cluster closes now: [denom_sq_pos],
    [d10_denom_is_d09], [d10_eta_sgn_one], [d10_eta_part_zero], [d10_cpow_zero].

    Honest boundary (the card (d) face): the removable singularity row at the
    nonzero lattice points s_k (k nonzero) is NOT in this node's closed domain;
    registered for the C3 consumption-face survey (the review condition hangs on
    C3; the dVp chain avoids the window by the sigma >= 1 - c/L corridor).

    Downstream alignment note: the C2-18 cast consumes the name [zeta_tilde]
    inside its expansion carrier shape; the premise family carried here
    ([eps_lb], [Hep], [Hd], [Heta]) re-aligns there at mother-chain integration
    when the disk witness carries the family (the same registered re-alignment
    language as the C2-18 cap carrier row).

    Registered adaptations over the drafts_C2.md C2.10 sketch: (i) [eta_s]
    carried as the premised value interface [d10_eta_conv] (the C2.07 row
    absent); (ii) [zeta_s] carried as the premised value interface
    [d10_zeta_conv] (the C2.02/08 rows discharge downstream); (iii) the quotient
    realized division-free through the conjugate pair; (iv) the sketch's
    unresolved [cIm] slot in the (c) row dropped - the card statement carries no
    imaginary constraint on the sigma band; (v) the (b) row's point-eta premise
    widened to the disk family [Hetad] inside the carrier (the local-uniform
    shape demands the eta value at every disk point; the slot is part of the
    compound existence face and its witnesses are provided by the C2.07
    discharge downstream).

    Dependencies consumed names: [S02] the real carrier and the
    [real_eq_of_zero_diff] ring route; [S03_QExp] [cauchy_real_exp];
    [S07] [real_lt_trans] (the strict order transit), [real_const_pos];
    [CxRealPairCore] [Cx], [cRe], [cIm], [c_eq], [c_eq_refl], [c_zero], [c_one],
    [c_plus], [c_opp], [c_mult], [c_conj], [c_norm_sq]; [CxRealPairExpLog]
    [c_exp], [c_scale]; [GaC2_01_DirichletPartialSum] [c_of_real], [nat_real],
    [NatLe_one_S], the n^{-s} carrier [c_powq] (discharged signature
    [c_powq Hnpos n Hn s]), the zeta partial sum [c_zeta_part Hnpos N s], the
    witness inverse [c_inv_wit] + [c_inv_wit_correct];
    [GaC2_02_AbsConvTailBound_a] the closed positivity witness [nat_real_pos]
    baking the [Hnpos] slot (consumed as [d10_npos], zero premise threading);
    [GaC2_09_DenomZeroSet_b] (the C2-09 landed leaf) [two_pow_1ms], [d09_denom],
    [d09_ln2] - the consolidating stem [GaC2_09_DenomZeroSet] is in flight at
    cast time, so the leaf is consumed directly and the row moves to the stem
    when it lands. *)


(* ===================================================================== *)
(* Section 1. The machine cluster: sign, eta partial sums, powers.       *)
(* ===================================================================== *)

(* The baked positivity witness of the embedded naturals (the C2.02-a   *)
(* closed face; zero premise threading downstream).                     *)
Definition d10_npos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n) :=
  nat_real_pos.

(* The alternating sign carrier: +1 on odd indices, -1 on even indices  *)
(* (the placeholder slot at index 0 is the double-opp fixed point).     *)
Fixpoint d10_eta_sgn (n : nat) : Cx :=
  match n with
  | O => c_opp c_one
  | S O => c_one
  | S (S m) => c_opp (c_opp (d10_eta_sgn m))
  end.

(* The eta partial sum column: sum_{n<=N} (-1)^(n-1) * n^{-s}.          *)
Fixpoint d10_eta_part (N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (d10_eta_part m s)
             (c_mult (d10_eta_sgn (S m)) (c_powq d10_npos (S m) (NatLe_one_S m) s))
  end.

(* The monomial carrier w^k of the local power series (the (b) face).   *)
Fixpoint d10_cpow (z : Cx) (k : nat) : Cx :=
  match k with
  | O => c_one
  | S m => c_mult (d10_cpow z m) z
  end.

(* The power series partial sum sum_{k<=N} c_k * w^k (the (b) face).    *)
Fixpoint d10_psum (c_n : nat -> Cx) (w : Cx) (N : nat) : Cx :=
  match N with
  | O => c_n O
  | S m => c_plus (d10_psum c_n w m) (c_mult (c_n (S m)) (d10_cpow w (S m)))
  end.

(* The closed disk of radius R around c, squared-modulus form (the L14  *)
(* disk shape; minted here because the C2-11 stem is not consumable at  *)
(* cast time - the wave-end cross-check binds the carriers).            *)
Definition d10_closed_disk (z c : Cx) (R : Real) : Set :=
  real_le (c_norm_sq (c_plus z (c_opp c))) (real_mult R R).

Lemma d10_eta_sgn_one : c_eq (d10_eta_sgn 1) c_one.
Proof. apply c_eq_refl. Qed.

Lemma d10_eta_part_zero : forall s : Cx, c_eq (d10_eta_part 0 s) c_zero.
Proof. intro s. apply c_eq_refl. Qed.

Lemma d10_cpow_zero : forall z : Cx, c_eq (d10_cpow z 0) c_one.
Proof. intro z. apply c_eq_refl. Qed.

(* ===================================================================== *)
(* Section 2. The eta and zeta value premise carriers (the open rows).   *)
(* ===================================================================== *)

(* The eta value interface: a value with the explicit alternating-tail  *)
(* modulus, the bound twice the first omitted term (self-contained;     *)
(* the C2.07 consumption slot - discharged when that row casts).        *)
Definition d10_eta_conv (s : Cx) : Set :=
  sigT (fun v : Cx =>
    forall N : nat,
      real_lt (c_norm_sq (c_plus v (c_opp (d10_eta_part N s))))
        (real_mult (real_const (2#1))
           (c_norm_sq (c_powq d10_npos (S N) (NatLe_one_S N) s)))).

(* The eta value carrier (the sketch consumed name [eta_s]).            *)
Definition eta_s (s : Cx) (Heta : d10_eta_conv s) : Cx := projT1 Heta.

(* The zeta value interface: a value with an explicit positive uniform  *)
(* tail bound beyond an explicit threshold (the C2.02 condensation +    *)
(* C2.08 limit identity consumption slot; the sketch name [zeta_s]).    *)
Definition d10_zeta_conv (s : Cx) : Set :=
  sigT (fun v : Cx =>
    sigT (fun M0 : nat =>
      sigT (fun B : Real =>
        sigT (fun _ : real_lt real_zero B =>
          forall N : nat, NatLe M0 N ->
            real_lt (c_norm_sq (c_plus v (c_opp (c_zeta_part d10_npos N s))))
                    B)))).

(* ===================================================================== *)
(* Section 3. The denominator face (the sketch row verbatim).            *)
(* ===================================================================== *)

(* The denominator nonzero domain: the sketch body verbatim, [eps_lb]   *)
(* the L13 local-constant slot discharged as the leading argument.      *)
Definition denom_nz (eps_lb : Real) (s : Cx) : Set :=
  real_lt eps_lb (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))).

(* The nz_wit realization: the positivity witness of the squared        *)
(* denominator modulus, derived from the local constant premise.        *)
Lemma denom_sq_pos : forall (eps_lb : Real) (s : Cx),
  real_lt real_zero eps_lb -> denom_nz eps_lb s ->
  real_lt real_zero (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))).
Proof.
  intros eps_lb s Hep Hd. unfold denom_nz in Hd.
  exact (real_lt_trans real_zero eps_lb
           (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))) Hep Hd).
Qed.

(* The bridge to the C2-09 landed carrier: the sketch denominator body  *)
(* IS the C2-09 [d09_denom] (name-reality bond, zero delta).            *)
Lemma d10_denom_is_d09 : forall s : Cx,
  c_eq (c_plus c_one (c_opp (two_pow_1ms s))) (d09_denom s).
Proof. intro s. apply c_eq_refl. Qed.

(* ===================================================================== *)
(* Section 4. The quotient carrier and the three named statements.       *)
(* ===================================================================== *)

(* The quotient carrier (the sketch name [zeta_tilde]): eta times the   *)
(* witness inverse of the squared denominator modulus times the         *)
(* conjugate denominator - the division-free quotient.                  *)
Definition zeta_tilde (eps_lb : Real) (s : Cx) (Hep : real_lt real_zero eps_lb)
  (Hd : denom_nz eps_lb s) (Heta : d10_eta_conv s) : Cx :=
  c_scale
    (c_inv_wit (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s))))
       (denom_sq_pos eps_lb s Hep Hd))
    (c_mult (eta_s s Heta)
       (c_conj (c_plus c_one (c_opp (two_pow_1ms s))))).

(* The weight faces of the (c) row: the eta corridor 1 + 2 * 2^{-sig0}  *)
(* (the two-power face read off the C2-09 carrier at the real point     *)
(* 1 + sig0, where the imaginary part is the zero face).                *)
Definition w_one (sig0 : Real) : Real :=
  real_plus real_one
    (real_mult (real_const (2#1))
       (cRe (two_pow_1ms (c_of_real (real_plus real_one sig0))))).
Definition w_sq (sig0 : Real) : Real := real_mult (w_one sig0) (w_one sig0).

(* (a) The agreement face: zeta-tilde equals the zeta value on          *)
(* sigma > 1.  Proof route (the card route): the C2.08 eta-zeta limit   *)
(* identity consumed directly; the body closes at mother-chain          *)
(* integration when the C2.08 row casts.                                *)
Definition zeta_tilde_agree
  (eps_lb : Real) (Hep : real_lt real_zero eps_lb) (s : Cx)
  (Hs1 : real_lt real_one (cRe s))
  (Hd : denom_nz eps_lb s) (Heta : d10_eta_conv s)
  (Hz : d10_zeta_conv s) : Set :=
  c_eq (zeta_tilde eps_lb s Hep Hd Heta) (projT1 Hz).

(* (b) The local power series face: radius, coefficients, the L13 nz    *)
(* band on the disk, the value agreement, and the uniform rational-     *)
(* margin Cauchy tails (the C1-15 same-shape form).  The sketch's       *)
(* point-eta premise is widened to the disk family [Hetad] (the local-  *)
(* uniform shape demands the eta value at every disk point).  Proof     *)
(* route (the card route): the Weierstrass double series constructive   *)
(* land - the breakthrough terrain, zero in-tree precedent; the body    *)
(* closes at mother-chain integration.                                  *)
Definition zeta_tilde_analytic
  (eps_lb : Real) (Hep : real_lt real_zero eps_lb) (s : Cx)
  (Hd : denom_nz eps_lb s) : Set :=
  sigT (fun R : Real =>
    sigT (fun _ : real_lt real_zero R =>
      sigT (fun Hetad : forall z : Cx, d10_closed_disk z s R -> d10_eta_conv z =>
        sigT (fun c_n : nat -> Cx =>
          sigT
            (fun Hnz : forall z : Cx,
                 d10_closed_disk z s R -> denom_nz eps_lb z =>
          sigT
            (fun Hval : forall z : Cx, d10_closed_disk z s R -> Cx =>
          And
            (forall (z : Cx) (Hzd : d10_closed_disk z s R),
               c_eq (Hval z Hzd)
                    (zeta_tilde eps_lb z Hep (Hnz z Hzd) (Hetad z Hzd)))
            (forall (w : Cx) (Hw : d10_closed_disk w s R),
              forall d : Q, QltT 0 d ->
                sigT (fun M0 : nat =>
                  forall N M : nat, NatLe M0 M -> NatLe M N ->
                    real_lt (c_norm_sq
                               (c_plus (d10_psum c_n (c_plus w (c_opp s)) N)
                                       (c_opp (d10_psum c_n (c_plus w (c_opp s)) M))))
                            (real_const d))))))))).

(* (c) The uniform modulus face: the squared bound weighted by the      *)
(* witness inverse of the squared denominator modulus.  Proof route     *)
(* (the card route): the C2.07 uniform eta tail |eta| <= 1 + 2 2^{-s0}  *)
(* consumed directly, the weighting through the nz premise; the body    *)
(* closes when the C2.07 row casts.                                     *)
Definition zeta_tilde_unif_bound
  (sig0 eps_lb : Real) (Hs0 : real_lt real_zero sig0)
  (Hep : real_lt real_zero eps_lb) (s : Cx) (Hs : real_lt sig0 (cRe s))
  (Hd : denom_nz eps_lb s) (Heta : d10_eta_conv s) : Set :=
  real_le (c_norm_sq (zeta_tilde eps_lb s Hep Hd Heta))
    (real_mult (w_sq sig0)
       (c_inv_wit (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s))))
                  (denom_sq_pos eps_lb s Hep Hd))).
