(* ================================================================= *)
(* piu_zz_n2c_sigma_assembly.v — gammaP1 N2c node, assembly-surface    *)
(*   constants unit (crude_size_sharp integration at 2^{17n}).         *)
(* ================================================================= *)
(* Mission.: N2c assembly-surface constants unit per workorder GEDAN-  *)
(*   gammaP1 sec.2 N2c ("integrate crude_size_sharp at 2^{17n}") and   *)
(*   the KB41c pre-acceptance table 4-3 (P1-P6, verdict GO):           *)
(*     P1  A-face all-j le17  -> sharp obligation face + finite flags  *)
(*        n=1..3 (all j) in exact Q form;                              *)
(*     P2/P3 L1 face le17/le16.94 -> non-binding observation face, no  *)
(*        tree carrier (zz_lsum_abs true-gap, N2b b3 record) - only    *)
(*        comments, NOT in acceptance (P6);                            *)
(*     P4/P5 control-band asymptote 16.9358 / extrapolation slack ->   *)
(*        machine-outside fit values, banned from the statement        *)
(*        surface (comments only);                                     *)
(*     P6  acceptance object = the A coefficient-value face            *)
(*        (Qabs (piu_zz_Aj n j), e_carrier :627-630 load semantics),   *)
(*        NOT the pre-collapse l1 face.                                *)
(*   The unit also relays the sigma_ZZ assembly pin (KB41b C5 EXACT,   *)
(*   paper-exact 16.7553, slack 0.2447 = 17 - 16.7553 machine-outside; *)
(*   judgment power carried by the C5 EXACT certificate in N2a), pins  *)
(*   the mu_ZZ name mapping, and lands the KB41k numeric-bank v2       *)
(*   anchors (kappa / c0 / N0 / pin order / C(1)).                     *)
(* Dependencies.: S02_CauchyComplete.v (QltT :48, QleT' :99,           *)
(*   Qle_to_QleT' :115, QeqT :303); piu_zz_kernel_sum.v - calibration  *)
(*   table definition source, consumed INDIRECTLY via Require          *)
(*   (qleT :73, zz6 :280, zz_Tnat :282, zz_Mj :328, piu_zz_Aj :632,    *)
(*   piu_zz_crude_size :987; KB85 mutual-verification corrected map:   *)
(*   no local re-definition of the calibration table); born first-wave *)
(*   units piu_zz_cage_constants.v (N2a: C5 EXACT certificate, C*      *)
(*   constant), piu_zz_sigma_decay.v (N2b: b0 qleT->QleT' bridge :56,  *)
(*   b2 A-face all-j consumption face :94), piu_zz_n1_linform.v (N1:   *)
(*   zz_seq_in); piu_zz_constants.v (piu_zzc_mu_zz_lower :123);        *)
(*   trust cache ConstructiveWorld_vo (deps .vo-present).              *)
(* References.: receipt-KB41c (tables 4-1/4-2/4-3, P1-P6 GO, flags     *)
(*   erratum 5-5); receipt-KB41b (C5 EXACT, table 3-1); receipt-KB41e  *)
(*   (corrected power-form flagger kb41e_flagsfix.py, md5 0b6dce99);   *)
(*   receipt-KB41k (numeric bank v2, 81 checks; bank anchors = kappa / *)
(*   c0 / N0 / pin order / C(1); A(1,1)=6880 is a KB41n sample, NOT a  *)
(*   bank anchor); receipt-KB41o (N2a/N2b statement-face drafts and    *)
(*   the N2c consumption note); receipt-KB72 (first-wave born state);  *)
(*   workorder GEDAN-gammaP1 sec.2 N2c row.                            *)
(* Constructivity.: statement faces Set-carried (QleT'/QltT/QeqT over  *)
(*   Id/bool); zero new Prop surface (red-line v2.4 path A); no open   *)
(*   leaves, no abandoned proofs, no axiom declarations;               *)
(*   machine-outside values (16.7553, 0.2447,                          *)
(*   16.9358, 0.0642, sup_j fits) stay in comments - none is a         *)
(*   theorem; flags in the corrected exact form: integer thresholds    *)
(*   judged by direct exact Q comparison, fractional thresholds by the *)
(*   corrected power form |A|^q <= 2^(tq n) (the KB41b flags_abs       *)
(*   missing-square erratum is on record: kb41b_calib.py:150-157       *)
(*   certified sigma <= 2t+4, not sigma <= t; all le17/le16.94         *)
(*   conclusions re-verified TRUE under the corrected form, KB41c      *)
(*   5-5; stored kb41b JSON not rewritten, territory discipline);      *)
(*   mu_ZZ is a comment-semantic name only - the true tree name is     *)
(*   piu_zzc_mu_zz_lower (constants.v:123); no identifier "mu_ZZ" is   *)
(*   created here. lia unused.                                         *)
(* Build.: rocq c -native-compiler no -q -time -Q . "" -Q              *)
(*   kb45_work_20261028 "" -Q kb72_work_20261030/born3 "" -Q           *)
(*   ConstructiveWorld-Main/ConstructiveWorld_vo ""                    *)
(*   piu_zz_n2c_sigma_assembly.v, cpu_guard v3 TL98 three-gate         *)
(*   (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce 0), sandbox      *)
(*   kb86_work_20261031. REPL rehearsal before born (this unit).       *)
(* ================================================================= *)

From Stdlib Require Import QArith ZArith Arith Lia.
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qabs.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_constants.
Require Import piu_zz_cage_constants.
Require Import piu_zz_sigma_decay.
Require Import piu_zz_n1_linform.

(* ================================================================= *)
(* Section 1. consumption relay: the 2^(37n) crude bound enters the    *)
(* QleT' world (b0 bridge + piu_zz_crude_size). The tree bound is      *)
(* stated with the literal (2 ^ (37*n) # 1) Q form; the sharp face of  *)
(* Section 2 is stated in the Qpower form fixed by the N2b b2          *)
(* consumption face. A concrete-n QeqT form check witnesses the two    *)
(* notations (symbolic-n conversion is not claimed and not needed).    *)
(* ================================================================= *)

Lemma piu_zz_n2c_crude_relay_37 :
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      ((Z.of_nat (2 ^ (37 * n)) # 1)%Q).
Proof.
  intros n j Hj.
  apply piu_zz_n2b_qleT_to_QleT'.
  apply piu_zz_crude_size.
  exact Hj.
Qed.

(* form witness at n=1: Qpower 2 37 == (2^37 # 1) as Q values.         *)
(* (numerator in Z scope: a unary-nat 2^37 is not computable — the     *)
(* kb41n S1-d trap "2^36 unary nat not computable" applies a fortiori  *)
(* at 2^37; Z.pow is binary and immediate.)                            *)
Lemma piu_zz_n2c_pow_form_check_n1 :
  S02_CauchyComplete.QeqT (Qpower (inject_Z 2) (Z.of_nat 37))
    ((2 ^ 37)%Z # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Section 2. P1 sharp face (the N2c acceptance object, A-face         *)
(* semantics per P6) + finite machine certificates in corrected exact  *)
(* flag form + the corrected power-form witness.                       *)
(* ================================================================= *)

(* The sharp face: forall n j (j <= 3n), |A_{n,j}| <= 2^(17n). This    *)
(* is exactly the N2b b2 consumption face piu_zz_n2b_A_allj_le17_face  *)
(* (agreement lemma below); its universal proof consumes the N2a GF    *)
(* bound (workorder N2c quantity-1 body; the finite n<=2 domain is     *)
(* machine-certified below, the n>=3 domain stays on the obligation    *)
(* face with the 2^(19n) fallback margin tier retained, KB41b 7).      *)
Definition piu_zz_n2c_crude_size_sharp : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).

(* interface bite: the N2c sharp face IS the N2b b2 face. *)
Lemma piu_zz_n2c_sharp_face_agrees_b2 :
  piu_zz_n2c_crude_size_sharp = piu_zz_n2b_A_allj_le17_face.
Proof. reflexivity. Qed.

(* finite flag (exact Q comparison; integer threshold 17 needs no      *)
(* power form - the direct comparison IS the corrected exact flag).    *)
Definition piu_zz_n2c_finite_le17_flag (n : nat) : bool :=
  forallb (fun j => Qle_bool (Qabs (piu_zz_Aj n j))
                             (Qpower (inject_Z 2) (Z.of_nat (17 * n))))
          (zz_seq (3 * n + 1)).

(* spec: a true finite flag discharges the sharp face on 0..3n. *)
Lemma piu_zz_n2c_finite_le17_spec :
  forall n j : nat, (j <= 3 * n)%nat ->
    piu_zz_n2c_finite_le17_flag n = true ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).
Proof.
  intros n j Hj H. unfold piu_zz_n2c_finite_le17_flag in H.
  rewrite forallb_forall in H.
  assert (Hlt : (j < 3 * n + 1)%nat) by lia.
  destruct (zz_seq_in_BidT (3 * n + 1) j Hlt) as [Hin].
  specialize (H j Hin).
  unfold S02_CauchyComplete.QleT'.
  rewrite H. reflexivity.
Qed.

(* P1 machine certificates, n = 1..2 all j (KB41c table 4-1 rows 1-2;  *)
(* kb45 F11 budgets: the deepest box-certified Aj face is n=2 — this   *)
(* unit's own rehearsal confirmed it: the n=3 flag vm_compute does NOT *)
(* terminate (isolated 150s probe, no progress; zz_Tnat unary-nat      *)
(* products reach ~1e8-1e9 scale at n=3, the kb41n S1-d unary trap     *)
(* family). Larger n stay Python-verified (KB41c n=1..16 all TRUE) and *)
(* on the obligation face. *)
Lemma piu_zz_n2c_finite_le17_n1 : piu_zz_n2c_finite_le17_flag 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_finite_le17_n2 : piu_zz_n2c_finite_le17_flag 2 = true.
Proof. vm_compute. reflexivity. Qed.

(* corrected power-form witness (the 16.94-pin shape, fractional       *)
(* threshold 847/50: |A|^50 <= 2^847; A-face form; cf. the acc-face    *)
(* conversion 847 + 4*50 = 1047, N2b F7): |A_{1,1}|^50 <= 2^847.       *)
(* A(1,1)=6880 is a KB41n sample value, NOT a KB41k bank anchor.       *)
Lemma piu_zz_n2c_power_flag_n1_j1 :
  S02_CauchyComplete.QleT'
    (Qpower (Qabs (piu_zz_Aj 1 1)) 50%Z)
    (Qpower (inject_Z 2) 847%Z).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Section 3. sigma_ZZ assembly pin relay (KB41b C5 EXACT).            *)
(* N3^2 * e^(2(4-c)) <= 2^39 iff sigma_ZZ <= 17; paper-exact assembly  *)
(* value sigma_ZZ = 16.7553 (KB41c table 4-2) and slack 0.2447 =       *)
(* 17 - 16.7553 are machine-outside display values (KB41o discipline:  *)
(* no statement surface); judgment power = the C5 EXACT certificate.   *)
(* ================================================================= *)

Definition piu_zz_n2c_sigmaZZ_cover : Set :=
  S02_CauchyComplete.QleT'
    (inject_Z 21852 * inject_Z 21852 * piu_zz_c5_E_up)%Q
    (Qpower (2 # 1)%Q 39%Z).

Lemma piu_zz_n2c_sigmaZZ_cover_relay : piu_zz_n2c_sigmaZZ_cover.
Proof. exact piu_zz_c5_21852_sq_Eup_le_2pow39. Qed.

(* ================================================================= *)
(* Section 4. mu_ZZ name mapping pin. mu_ZZ is the comment-semantic    *)
(* name (KB85 corrected interface map); the true tree constant is      *)
(* piu_zzc_mu_zz_lower (piu_zz_constants.v:123). This unit value-pins  *)
(* the constant; the separation 7 < mu_ZZ is owned by piu_zz_nail_mu.  *)
(* ================================================================= *)

Lemma piu_zz_n2c_mu_zz_const_value :
  S02_CauchyComplete.QeqT piu_zzc_mu_zz_lower
    (7103205334137 # 1000000000000)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Section 5. KB41k numeric-bank v2 anchors (five true anchor          *)
(* families; A(1,1)=6880 excluded by the anchor charter). All values   *)
(* re-derived here by vm_compute (born-side measured anchors, not      *)
(* alias relays) for the post-born Fraction cross-check.               *)
(* ================================================================= *)

(* anchor 1 (bank R4): kappa = 35831808 = 2^14 * 3^7. *)
Lemma piu_zz_n2c_bank_kappa :
  S02_CauchyComplete.QeqT (inject_Z 35831808)%Q
    (inject_Z (2 ^ 14 * 3 ^ 7))%Q.
Proof. vm_compute. reflexivity. Qed.

(* anchor 2 (bank R4): c0 = 1/(2*kappa) = 1/71663616; 2*kappa*c0 = 1.  *)
Lemma piu_zz_n2c_bank_c0 :
  S02_CauchyComplete.QeqT
    ((2 # 1)%Q * (35831808 # 1)%Q * (1 # 71663616)%Q)%Q
    (1 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* anchor 3 (bank R8, beta=1): N0 = 1348, last-violation+1 type:       *)
(* 375^1347 < 1347*373^1347 (violation at 1347) and                    *)
(* 1348*373^1348 <= 375^1348 (holds at 1348).                          *)
Lemma piu_zz_n2c_bank_N0_violation_1347 :
  S02_CauchyComplete.QltT (Qpower (375 # 1)%Q 1347%Z)
    (inject_Z 1347 * Qpower (373 # 1)%Q 1347%Z)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_N0_hold_1348 :
  S02_CauchyComplete.QleT'
    (inject_Z 1348 * Qpower (373 # 1)%Q 1348%Z)%Q
    (Qpower (375 # 1)%Q 1348%Z).
Proof. vm_compute. reflexivity. Qed.

(* anchor 4 (bank R5/H5): pin order 13/400 < 373/2500 < 3/20 < 1/2     *)
(* (rho dead < rho tight < rho main < 1/2).                            *)
Lemma piu_zz_n2c_bank_pin_dead_tight :
  S02_CauchyComplete.QltT (13 # 400)%Q (373 # 2500)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_pin_tight_main :
  S02_CauchyComplete.QltT (373 # 2500)%Q (3 # 20)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_pin_main_half :
  S02_CauchyComplete.QleT' (3 # 20)%Q (1 # 2)%Q.
Proof. vm_compute. reflexivity. Qed.

(* anchor 4 supplement (bank R5): tau closure (1,2) - 2^1*3=6 <= 20,   *)
(* 2^2*3=12 <= 20, 2^3*3=24 > 20 (tau>=3 dead).                        *)
Lemma piu_zz_n2c_bank_tau1_alive :
  S02_CauchyComplete.QleT' (6 # 1)%Q (20 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_tau2_alive :
  S02_CauchyComplete.QleT' (12 # 1)%Q (20 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_tau3_dead :
  S02_CauchyComplete.QltT (20 # 1)%Q (24 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* anchor 5 (bank R1): C(1) = 375^187/(187*373^187), the beta=1 head   *)
(* judgment constant (N4 countersign C-star); simple-fraction brackets *)
(* both sides (KB41g; OFFSYS display 0.0145363011...).                 *)
Definition piu_zz_n2c_bank_C1 : Q :=
  (Qpower (inject_Z 375) 187%Z
    / (inject_Z 187 * Qpower (inject_Z 373) 187%Z))%Q.

Lemma piu_zz_n2c_bank_C1_bracket_lo :
  S02_CauchyComplete.QltT (1489765 # 102485838)%Q piu_zz_n2c_bank_C1.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2c_bank_C1_bracket_hi :
  S02_CauchyComplete.QltT piu_zz_n2c_bank_C1 (6855632 # 471621491)%Q.
Proof. vm_compute. reflexivity. Qed.

(* C* definitional alias check: the bank C(1) face value is the N2a    *)
(* C7 countersign constant (interface bite, KB41g 4-3(c)).             *)
Lemma piu_zz_n2c_bank_C1_is_N2a_Cstar :
  piu_zz_n2c_bank_C1 = piu_zz_c7_Casm_bound_v187.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* downstream notes: N4/N5/N6'-b consume the sharp face (Definition    *)
(* piu_zz_n2c_crude_size_sharp) together with the N2b b1 slot faces    *)
(* and the N2a C5/C7 certificates; the L1 observation face stays out   *)
(* of acceptance (P6, thin band 0.0642 not conceded, KB41c P4/P5       *)
(* machine-outside). The 2^(19n) fallback margin tier stays retained   *)
(* (KB41b 7) until the universal GF supply lands.                      *)
(* ================================================================= *)

Print Assumptions piu_zz_n2c_crude_relay_37.
Print Assumptions piu_zz_n2c_pow_form_check_n1.
Print Assumptions piu_zz_n2c_sharp_face_agrees_b2.
Print Assumptions piu_zz_n2c_finite_le17_spec.
Print Assumptions piu_zz_n2c_finite_le17_n1.
Print Assumptions piu_zz_n2c_finite_le17_n2.
Print Assumptions piu_zz_n2c_power_flag_n1_j1.
Print Assumptions piu_zz_n2c_sigmaZZ_cover_relay.
Print Assumptions piu_zz_n2c_mu_zz_const_value.
Print Assumptions piu_zz_n2c_bank_kappa.
Print Assumptions piu_zz_n2c_bank_c0.
Print Assumptions piu_zz_n2c_bank_N0_violation_1347.
Print Assumptions piu_zz_n2c_bank_N0_hold_1348.
Print Assumptions piu_zz_n2c_bank_pin_dead_tight.
Print Assumptions piu_zz_n2c_bank_pin_tight_main.
Print Assumptions piu_zz_n2c_bank_pin_main_half.
Print Assumptions piu_zz_n2c_bank_tau1_alive.
Print Assumptions piu_zz_n2c_bank_tau2_alive.
Print Assumptions piu_zz_n2c_bank_tau3_dead.
Print Assumptions piu_zz_n2c_bank_C1_bracket_lo.
Print Assumptions piu_zz_n2c_bank_C1_bracket_hi.
Print Assumptions piu_zz_n2c_bank_C1_is_N2a_Cstar.
