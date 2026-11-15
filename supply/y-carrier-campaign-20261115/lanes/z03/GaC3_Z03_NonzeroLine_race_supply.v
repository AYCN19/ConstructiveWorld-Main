(** * GaC3_Z03_NonzeroLine_race_supply: supply and registration face of Section Z03_Race (node C3-Z03).

    Mission.  The racing contradiction [z03_racing_contra] consumes four premise
    slots; each is supplied as far as the tree allows, the remainder registered.
    (1) Hd (a positive racing offset d : Q): the concrete instance at the radius
    literal [z03_radius_lit] = 1/64 with margin m0 = 32, plus [z03_m0_pos] at the
    radius; the universal "for all d, 0 < d" is false (d := 0), claimed nowhere.
    (2) Hsig3 / Htwo (upper-bound datum slots, bounds B3 B2 : Real): the weakest
    witness - the bound datum is the bounded quantity itself ([real_le_refl]);
    the load sits in the window condition 3*B3 + B2 < 4*m0.  (3) Hmain4 (the
    fixed main part -1/(2d)): registered open, not supplied (route: the
    eta-continuation supply line).
    Statement faces (8): z03s_Hd_radius_lit, z03s_m0_radius_value, z03s_m0_pos_radius,
    z03s_Hsig3_selfbound, z03s_Htwo_selfbound, z03s_racing_radius_assembled,
    z03s_Hmain4_shape, z03s_radius_window_face.

    Dependencies.  [S02_CauchyComplete], [S07_RealSetoidExpLog], [CxRealPairCore],
    [GaC3_Z03_NonzeroLine_b], [GaC3_Z01_LogDerivSeries], [GaC3_Z03_NonzeroLine_cert],
    [GaC3_Z03_NonzeroLine_race]; Stdlib [QArith.QArith].

    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]:136-163;
    drafts_C3.md C3-Z03 and cards_C3 C3-Z03; the honest-scope note of GaC3_Z03_NonzeroLine_cert
    (the eta-continuation open rows); the rLPO-family precedent abl_W9_slice57_10.

    Constructivity.  Every proved item is [Set]-carried; the two registered
    definitional faces are statement carriers marked NOT claimed; zero assumed
    constants, zero abandoned proofs; every Print Assumptions reads Closed.

    Build.  coqc -native-compiler no -q -Q . "" GaC3_Z03_NonzeroLine_race_supply.v
    (dependency-closure build directory). *)

Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import GaC3_Z03_NonzeroLine_b.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_Z03_NonzeroLine_cert.
Require Import GaC3_Z03_NonzeroLine_race.
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 1. The Hd slot: the radius instance and the margin faces.         *)
(* ===================================================================== *)

(* The Hd slot at the registered radius literal: the concrete positive   *)
(* racing offset d = 1/64.  Compute-face re-derivation, independent of   *)
(* the certificate band proof term. *)
Lemma z03s_Hd_radius_lit : QltT 0 z03_radius_lit.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.

(* The racing margin constant at the radius literal: 1/(2*(1/64)) = 32,  *)
(* so the window constant 4 * m0 is the certified 128 of the radius band.*)
Lemma z03s_m0_radius_value : QeqT (Qinv (2 * z03_radius_lit)) (Qmake 32 1)%Q.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.

(* The in-tree consumption face of the Hd slot ([z03_m0_pos], discharged *)
(* as forall d, QltT 0 d -> real_lt real_zero (z03_m0 d)) instantiated at *)
(* the radius literal with the radius certificate. *)
Lemma z03s_m0_pos_radius : real_lt real_zero (z03_m0 z03_radius_lit).
Proof. exact (z03_m0_pos z03_radius_lit z03_radius_pos). Qed.

(* ===================================================================== *)
(* Part 2. The two upper-bound datum slots: the weakest witness.          *)
(* ===================================================================== *)

(* The Hsig3 slot is inhabited by the canonical weakest witness: the     *)
(* bound datum taken to be the bounded quantity itself.  The datum slot  *)
(* alone carries no gap; the window condition carries the load. *)
Lemma z03s_Hsig3_selfbound : forall (d : Q) (Nrace : nat),
  real_le (cRe (z01_manpart z03npos Nrace (z03_p0 d)))
          (cRe (z01_manpart z03npos Nrace (z03_p0 d))).
Proof. intros d Nrace. apply real_le_refl. Qed.

(* The Htwo slot at the doubled-ordinate point, same weakest witness. *)
Lemma z03s_Htwo_selfbound : forall (t : Real) (d : Q) (Nrace : nat),
  real_le (cRe (z01_manpart z03npos Nrace (z03_p2 t d)))
          (cRe (z01_manpart z03npos Nrace (z03_p2 t d))).
Proof. intros t d Nrace. apply real_le_refl. Qed.

(* ===================================================================== *)
(* Part 3. The assembled consumption form at the radius literal.          *)
(* ===================================================================== *)

(* The racing contradiction at the radius literal with the Hd slot and   *)
(* both datum slots discharged by the supplies of this file: what        *)
(* remains are exactly the two open faces, the main-part slot premise    *)
(* and the window premise. *)
Theorem z03s_racing_radius_assembled :
  forall (t : Real) (Nrace : nat),
  real_le (cRe (z01_manpart z03npos Nrace (z03_p1 t z03_radius_lit)))
          (real_opp (real_const (Qinv (2 * z03_radius_lit)))) ->
  real_lt (real_plus (real_mult (real_const 3)
                        (cRe (z01_manpart z03npos Nrace (z03_p0 z03_radius_lit))))
                     (cRe (z01_manpart z03npos Nrace (z03_p2 t z03_radius_lit))))
          (real_mult (real_const 4) (z03_m0 z03_radius_lit)) ->
  False.
Proof.
  intros t Nrace Hmain4 Hwin.
  exact (z03_racing_contra t z03_radius_lit Nrace
           (cRe (z01_manpart z03npos Nrace (z03_p0 z03_radius_lit)))
           (cRe (z01_manpart z03npos Nrace (z03_p2 t z03_radius_lit)))
           Hmain4
           (z03s_Hsig3_selfbound z03_radius_lit Nrace)
           (z03s_Htwo_selfbound t z03_radius_lit Nrace)
           Hwin).
Qed.

(* ===================================================================== *)
(* Part 4. The main-part slot and the window face: statement carriers.    *)
(* ===================================================================== *)

(* The Hmain4 slot shape, replicated faithfully from Section Z03_Race    *)
(* (the real part of the partial sum at sigma + i*t stays below the      *)
(* fixed multiplicity main part -1/(2d)).  NOT claimed: this is the      *)
(* registered open supply face (the zero factorization route, awaiting   *)
(* the eta-continuation supply line). *)
Definition z03s_Hmain4_shape (t : Real) (d : Q) (Nrace : nat) : Set :=
  real_le (cRe (z01_manpart z03npos Nrace (z03_p1 t d)))
          (real_opp (real_const (Qinv (2 * d)))).

(* The window obligation under the weakest-witness bound choice at the   *)
(* radius literal: the sum 3*Re(M(s0)) + Re(M(s2)) below 4*m0.  NOT      *)
(* claimed: the proof body needs an explicit upper-bound assembly for    *)
(* the two partial sums (the application-layer supply, registered open). *)
Definition z03s_radius_window_face (t : Real) (Nrace : nat) : Set :=
  real_lt (real_plus (real_mult (real_const 3)
                        (cRe (z01_manpart z03npos Nrace (z03_p0 z03_radius_lit))))
                     (cRe (z01_manpart z03npos Nrace (z03_p2 t z03_radius_lit))))
          (real_mult (real_const 4) (z03_m0 z03_radius_lit)).
