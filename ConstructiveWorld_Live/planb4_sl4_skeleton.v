(* ========================================================================= *)
(* planb4_sl4_skeleton.v - SL4 statement faces: the Delta_n <> 0 witness-    *)
(* newness supply line (born statements, honestly unproven; nothing claimed).*)
(* Mission      : the Delta_n <> 0 supply line of planb4_l4_hesc_slot        *)
(*                (fourslots:101-109) needs a constructive carrier of strict *)
(*                linear-form decay x reduced-denominator growth (survey     *)
(*                volume SL4, sections 2 and 5).  Statement faces and the    *)
(*                pending-debt ledger ONLY: the determinant face on the     *)
(*                ab_def carrier, the born forall-n nonzero body, two        *)
(*                growth-account targets (B-side bits, gcd bound), the       *)
(*                ZZ2020 proportionality half, and the twin Delta-slot       *)
(*                premise faces.  Every proof-shaped debt is registered,     *)
(*                none claimed.  The n = 1..3 machine-false note in          *)
(* u5_carrier_align (:279-280) is a planb4_pdiv defect, NOT a refutation of Delta *)
(* Dependencies : Stdlib ZArith, QArith; planb3_g1_calib (frozen tables;     *)
(*                fallback 0, calib:79/:261); planb4_g1_ab_def (carrier      *)
(*                A/B : nat -> Z, ab_def:72/:74 - only legal carrier for     *)
(*                forall-n faces: frozen tables read 0 above n = 40 while    *)
(*                planb_b_nlo q > 40 for q >= 2^79, survey ss.1.2); window   *)
(*                picker = generic function argument (planb1:215-217).       *)
(* References   : hesc18:111-163/:1587-1643 (dodge chain; swap target);      *)
(*                rs_channel:44-54; laur_extract:144-189 (n = 1..6 only);    *)
(*                u5_carrier_align:58-65/:127-129; g2_design:170-180;        *)
(*                ZZ2020 MJCT 9 (2020) 407-419 (the |I_n| face lives on the  *)
(*                SL2 joint carrier fourslots:112-116, outside this file).   *)
(* Constructivity: no assumption commands, no proof surrender, no weakened   *)
(* closed definitions planb4_sl4_delta and planb4_sl4_denom_reduced are transpare *)
(* tree names; pins 6 (per-step bits) and (5n-1)/2 (survey M1:329) are table-extr *)
(* Build        : coqc -q -native-compiler no -Q <dir> planb4_sl4_skeleton.v *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.

(* ================================================================== *)
(* Section 1. The named determinant face (closed definition; the      *)
(*            carrier is the TOTAL ab_def pair, per survey 1.2-1).    *)
(* ================================================================== *)

(* Delta n is the dodge determinant of the consecutive witness pair:  *)
(* A n * B (S n) - A (S n) * B n, the verbatim shape consumed by the  *)
(* dodge chain (hesc18:109/:1592/:1625-1627), now named and bound to  *)
(* the total carrier planb4_g1_A/planb4_g1_B instead of the frozen    *)
(* n = 1..40 table.  A definition, not a claim.                       *)
Definition planb4_sl4_delta (n : nat) : Z :=
  (planb4_g1_A n * planb4_g1_B (S n)
   - planb4_g1_A (S n) * planb4_g1_B n)%Z.

(* ================================================================== *)
(* Section 2. The born forall-n nonzero body (the SL4 breakthrough    *)
(*            target; born statement, honestly unproven / NOT         *)
(*            claimed).                                               *)
(* ================================================================== *)

(* Survey section 5, the breakthrough row: the missing piece is one   *)
(* constructive Rocq carrier of strict linear-form decay x reduced-  *)
(* denominator growth.  This statement is its landing shape.         *)
Definition planb4_sl4_delta_nz : Prop :=
  forall n : nat, planb4_sl4_delta n <> 0%Z.

(* ================================================================== *)
(* Section 3. Route B, half 1: the B-side growth account (born        *)
(*            statement, honestly unproven / NOT claimed).            *)
(* ================================================================== *)

(* Machine survey (survey section 3, exact Z over the frozen table):  *)
(* |B| monotone with zero violations on n = 1..39, per-step bit       *)
(* growth min 6 max 32, |B_1| at 13 bits.  The constant 6 below is    *)
(* the conservative table-extrapolated pin; the forall-n face is the  *)
(* debt (Laurent product structure, general-n face = P6 debt).        *)
Definition planb4_sl4_bgrowth : Prop :=
  forall n : nat, (1 <= n)%nat ->
    (2 ^ Z.of_nat ((6 * (n - 1))%nat) <= Z.abs (planb4_g1_B n))%Z.

(* ================================================================== *)
(* Section 4. Route B, half 2: the reduced-denominator gcd bound      *)
(*            (born statement, honestly unproven / NOT claimed).      *)
(* ================================================================== *)

(* d_n := |B n| / gcd(|A n|, |B n|) - the reduced denominator of the  *)
(* witness fraction.  Survey section 3: the criterion holds on        *)
(* n = 1..40 with huge margin (n = 40: d_n at 632 bits vs threshold   *)
(* 100 bits).  Threshold form 2^((5n-1)/2) = 2^(ceil(5n/2)-1), the    *)
(* M1:329 criterion (i) pin (survey section 2, skeleton C).  The      *)
(* forall-n face is the N2c-chain debt (g2_design:170-180).           *)
Definition planb4_sl4_denom_reduced (n : nat) : Z :=
  (Z.abs (planb4_g1_B n)
   / Z.gcd (Z.abs (planb4_g1_A n)) (Z.abs (planb4_g1_B n)))%Z.

Definition planb4_sl4_denom_bound : Prop :=
  forall n : nat, (1 <= n)%nat ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) <= planb4_sl4_denom_reduced n)%Z.

(* ================================================================== *)
(* Section 5. Route ZZ, algebraic half: proportionality on zero       *)
(*            determinant (born statement, honestly unproven / NOT    *)
(*            claimed).                                               *)
(* ================================================================== *)

(* ZZ2020 nonzeroness-automatic-since-I_n-to-0 recast (survey       *)
(* section 2, skeleton A): if Delta n = 0 the two coefficient pairs   *)
(* are proportional over Q, so I_(S n) = lambda * I_n with            *)
(* |lambda| = |B (S n)| / |B n| >= 1 under monotone growth - blocking *)
(* any strict decay.  THIS statement is the pure-Z/Q algebraic half   *)
(* (rank-1 proportionality of a 2x2 pair with zero determinant over   *)
(* the fraction field); the decay half needs the |I_n| carrier l2_dv  *)
(* and is NOT stated in this file - it is debt D-SL4-6, owned by the  *)
(* SL12 joint seat on the hcage-slot carrier (fourslots:112-116).     *)
Definition planb4_sl4_proportional_on_zero : Prop :=
  forall n : nat, planb4_sl4_delta n = 0%Z ->
    exists l : Q,
      Qeq (inject_Z (planb4_g1_A (S n)))
          (Qmult l (inject_Z (planb4_g1_A n))) /\
      Qeq (inject_Z (planb4_g1_B (S n)))
          (Qmult l (inject_Z (planb4_g1_B n))).

(* ================================================================== *)
(* Section 6. The twin Delta-slot premise faces (consumption shapes;  *)
(*            born statements, honestly unproven / NOT claimed).      *)
(* ================================================================== *)

(* The current consumption premise of window_route/global is stated   *)
(* at the FROZEN carrier, verbatim hesc18:1592-1594/:1625-1627, with  *)
(* the concrete picker planb_b_nlo (planb1:215-217).  The picker      *)
(* enters here as a generic function argument (postulate-free: no    *)
(* Parameter); a dispatching seat instantiates it at planb_b_nlo or   *)
(* at a repaired picker.                                              *)

(* The frozen-carrier face - the carrier the tree consumes today.     *)
(* Domain honesty: this premise is literally false for q >= 2^79      *)
(* (the picker lands above the table, both slots read 0, the          *)
(* subtracted determinant is 0), which is exactly why the swap debt   *)
(* D-SL4-2 exists (survey section 1.2; calib:79/:261).                *)
Definition planb4_sl4_window_slot_frozen (nlo : nat -> nat) : Prop :=
  forall q : nat, (1 <= q)%nat ->
    (planb3_g1_A (nlo q) * planb3_g1_B (S (nlo q))
     - planb3_g1_A (S (nlo q)) * planb3_g1_B (nlo q) <> 0)%Z.

(* The ab_def-carrier twin - the swap target; identical shape, total  *)
(* carrier.  Literally the instance planb4_sl4_delta (nlo q) <> 0.    *)
Definition planb4_sl4_window_slot_abdef (nlo : nat -> nat) : Prop :=
  forall q : nat, (1 <= q)%nat -> planb4_sl4_delta (nlo q) <> 0%Z.

(* ================================================================== *)
(* Section 7. Pending-debt ledger (comments only; mirror of the       *)
(*            appended survey-volume section; each row independently  *)
(*            dispatchable; estimates are EXTRAPOLATED, UNCALIBRATED; *)
(*            nothing in this ledger is claimed, proven, or priced    *)
(*            beyond the survey volume's own no-pricing-before-       *)
(*            survey law).                                            *)
(* ================================================================== *)

(* D-SL4-1  table-domain anchor blank. *)
(*   target statement : planb4_sl4_delta (Section 1) + vm_compute      *)
(*     anchors n = 1..39, 39/39 true (the delta_survey.py readings,    *)
(*     survey section 3, recast as born Examples in a build file).     *)
(*   dependencies     : planb4_g1_ab_def (in tree); survey section 3.  *)
(*   estimate         : about 0.5-1 seat-hours (extrapolated,          *)
(*     uncalibrated; the survey slice S-1 share).                      *)
(*   review condition : any carrier or table change re-anchors.        *)

(* D-SL4-2  carrier swap above the forced band. *)
(*   target statement : planb4_sl4_window_slot_abdef (Section 6)       *)
(*     assembled as the twin of window_route/global for q >= 2^79      *)
(*     addresses; the frozen face (Section 6) stays as the in-domain   *)
(*     twin; signature of hesc18 untouched (stability law).            *)
(*   dependencies     : D-SL4-1; hesc18:1587-1643 consumption faces.   *)
(*   estimate         : about 1-3 seat-hours (extrapolated,            *)
(*     uncalibrated; the survey slice S-2 share; S-1 + S-2 within the  *)
(*     survey's 2-4 total).                                            *)
(*   review condition : any hesc18 signature change re-prices.         *)

(* D-SL4-3  B-side growth account (breakthrough half 1). *)
(*   target statement : planb4_sl4_bgrowth (Section 3).                *)
(*   dependencies     : Laurent product structure general-n; the       *)
(*     poleA well-definedness face is the P6 debt (M1:437); r/s        *)
(*     channel table-certified n = 1..6 only (laur_extract:144-189,    *)
(*     rs_channel:59-88); survey section 3 readings.                   *)
(*   estimate         : about 4-10 seat-hours (extrapolated,           *)
(*     uncalibrated).                                                  *)
(*   review condition : P6 progress, N2c landing, or SL2 slotting      *)
(*     forces re-estimate (M1:319(a) reverse-isomorphic gate).         *)

(* D-SL4-4  reduced-denominator gcd bound (breakthrough half 2). *)
(*   target statement : planb4_sl4_denom_bound (Section 4).            *)
(*   dependencies     : D-SL4-3; the G4/N2c chain                      *)
(*     (g2_design:170-180 registration; M1:329 upstream list).         *)
(*   estimate         : about 4-10 seat-hours (extrapolated,           *)
(*     uncalibrated).                                                  *)
(*   review condition : any gcd upper-bound lemma landing in tree      *)
(*     forces re-estimate.                                             *)

(* D-SL4-5  proportionality half, ZZ algebraic limb. *)
(*   target statement : planb4_sl4_proportional_on_zero (Section 5).   *)
(*   dependencies     : none upstream - pure Z/Q algebra over the      *)
(*     Section 1 face; the smallest startable piece of the ledger.     *)
(*   estimate         : about 1-2 seat-hours (extrapolated,            *)
(*     uncalibrated; classical rank-1 fact, constructive Prop          *)
(*     carrier).                                                       *)
(*   review condition : none external; lands and waits for the         *)
(*     decay half to consume it.                                       *)

(* D-SL4-6  decay half, SL2 joint face (NOT stated in this file). *)
(*   target statement : strict decay of |l2_dv (A n) (B n)| forall n   *)
(*     on the hcage-slot carrier (fourslots:112-116); to be minted by  *)
(*     the SL12 joint seat, not by this skeleton.                      *)
(*   dependencies     : SL2 slotting; ZZ2020 v2 source verbatim        *)
(*     survey (G3 disk src_v2/pimeas_v2.tex, 34,929 B, unread per      *)
(*     survey section 8); S02/LW1PiMeasure dependency closure.         *)
(*   estimate         : about 6-12 seat-hours (extrapolated,           *)
(*     uncalibrated).                                                  *)
(*   review condition : any SL2 |I_n| certificate forces immediate     *)
(*     re-estimate (survey section 5, review condition 3).             *)

(* D-SL4-7  forall-n body confluence and consumption wiring. *)
(*   target statement : planb4_sl4_delta_nz (Section 2) + the          *)
(*   instance planb4_sl4_window_slot_abdef planb_b_nlo feeding the     *)
(*   q >= 2^79 band of the escape face.                                *)
(*   dependencies     : (D-SL4-3 AND D-SL4-4 AND D-SL4-5, by the       *)
(*   growth-route contradiction) OR (D-SL4-5 AND D-SL4-6, by the       *)
(*   ZZ-route contradiction); D-SL4-2 for wiring.                      *)
(*   estimate         : about 2-5 seat-hours (extrapolated,            *)
(*   uncalibrated; confluence only - the mathematical content lives    *)
(*   upstream).                                                        *)
(*   review condition : any upstream limb landing forces re-estimate.  *)

(* D-SL4-8  depth-warning remainder (review-driven only). *)
(*   target statement : witness pdiv retirement note face; Laurent     *)
(*   multi-sum bite advanced past n = 2 (u5:58-65 OOM register).       *)
(*   dependencies     : u5_carrier_align:127-129/:279-280;             *)
(*   piu_zz_kernel_sum.                                                *)
(*   estimate         : about 2-6 seat-hours (extrapolated,            *)
(*   uncalibrated).                                                    *)
(*   review condition : dispatched only if skeleton D (recurrence)     *)
(*   is re-priced; it is the sole re-evaluation channel of the         *)
(*   pure-algebraic route (rs_channel:44-54, no recurrence face).      *)

(* ================= end of statement faces and ledger ============== *)
