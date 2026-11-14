(* sl12_constants.v - verified Gantumur constants for the SL12 slots.
   Ticket: SL12 ticket 1a first cut (constant pinning, serial-first).
   Mission: pin the 22 confirmed citation entries of arXiv:2512.02466v2
   (T. Gantumur, An expository review of the Chebyshev-Sylvester method
   in prime number theory, v2) as Q-form definitions, one anchor Example
   each, feeding the SL12 supply faces of the slot draft. Statement
   inventory: 103 Definitions of Q data (8 delta-certificate indicator
   functions nat -> Q under Kronecker semantics plus 95 rational pins)
   and 103 anchor Examples closed by vm_compute + reflexivity.
   Dependencies: the SL12 slot draft section 0 block verbatim (Stdlib
   QArith.QArith, QArith.Qabs, ZArith, Arith.Arith, Lia, Qpower; base
   S02_CauchyComplete, piu_mu_criterion, piu_zz_e_carrier,
   planb4_g1_witness, planb4_l2_dv_cast, planb3_g1_g2_design,
   planb1_hcage_zerotouch_prescription, planb3_g1_calib).
   References (source routing): values transcribed verbatim from the
   confirmed extraction volume of the dispatch package, re-verified
   digit by digit against the official LaTeXML math text in the packet
   snapshot; A(nu-star) is stated twice in the source (5-dp at eq (34),
   4-dp at eq (43)), both truncations pinned verbatim, not unified; the
   provenance ledger is kept with the seat receipt, not in this file.
   NOT claimed: no optimality, tightness, truth, or fitness claim is
   made here; each pinned constant is a born anchor of its citation.
   Constructivity: postulate-free - zero global assumptions, zero proof
   surrender, zero check weakening, zero choice principles, zero solver
   closers; all named data is Set-carried; anchors are proof-bridge
   props (Qed kept: numeric content lives in the transparent Definitions,
   anchors are extraction-erased pins).
   Build: coqc -native-compiler no -q -Q <root> "" <file>, E952
   script form, order per Require topology; registrations: the sl12_
   namespace is the slot-draft sandbox earmark. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_e_carrier.
(* piu_zz_e_carrier: the ec_sigma/ec_tau names; canonical premise   *)
(* shapes :615-650 of that module.                                   *)
Require Import planb4_g1_witness.
(* planb4_g1_witness: planb4_lcm_upto/:46-47, planb4_L/:49-50,       *)
(* planb4_Pn_list/:200-201, planb4_Phi/:204-205, planb4_LZn/:208-209.*)
Require Import planb4_l2_dv_cast.
(* planb4_l2_dv_cast: l2_dv and the two closed limbs.                *)
Require Import planb3_g1_g2_design.
(* planb3_g1_g2_design: planb3_dv_anchor/:119-120, the G2 DO faces   *)
(* :122-152.                                                          *)
Require Import planb1_hcage_zerotouch_prescription.
(* planb1: planb_b_hval_direct/:386-389, planb_b_sigma/:58.          *)
Require Import planb3_g1_calib.
(* planb3_g1_calib: the frozen A/B tables n=1..40 (head anchors).    *)

(* ==== Section 1: the Chebyshev certificate nu-star, eq (24) ==== *)

(* Chebyshev certificate: delta_1 - delta_2 - delta_3 - delta_5 + delta_30
  (eq 24); Kronecker delta semantics. *)
Definition sl12_nu_star (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 30 then (1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu_star :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu_star 1 + (1 # 2) * sl12_nu_star 2 + (1 # 3) *
  sl12_nu_star 3 + (1 # 5) * sl12_nu_star 5 + (1 # 30) * sl12_nu_star 30)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 2: the Chebyshev V(x) selection pattern, eq (23) ==== *)

(* Chebyshev original V(x) = T(x) - T(x/2) - T(x/3) - T(x/5) + T(x/30) (eq
  23); the T-shift coefficient pattern. *)
Definition sl12_v_chebyshev_shape (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 30 then (1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_v_chebyshev_shape :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_v_chebyshev_shape 1 + (1 # 2) * sl12_v_chebyshev_shape
  2 + (1 # 3) * sl12_v_chebyshev_shape 3 + (1 # 5) * sl12_v_chebyshev_shape 5
  + (1 # 30) * sl12_v_chebyshev_shape 30)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 3: the A(nu) functional, eq (27)-(28) ==== *)
(* eq (27) defines A(nu) = -sum nu(n) ln n / n and eq (28) the       *)
(* frame psi(x) <= N/(N-1) A(nu) x + O(ln^2 x); neither states a      *)
(* rational constant, so this section pins nothing; the numeric       *)
(* shadows of the functional live in Sections 4, 10, 11, 12.          *)

(* ==== Section 4: the Chebyshev closed form A-star and N, eq (34) ==== *)

(* Chebyshev closed form A* = ln2/2 + ln3/3 + ln5/5 - ln30/30 = 0.92129...
  (eq 34), five decimals as stated. *)
Definition sl12_A_star : Q := (92129 # 100000)%Q.
Example sl12_anchor_A_star :
  Qeq (92129 # 100000) sl12_A_star.
Proof. vm_compute. reflexivity. Qed.

(* N = 6 for nu-star: E(x) = 1 for 1 <= x < 6 (companion of eq 34). *)
Definition sl12_N_nu_star : Q := (6 # 1)%Q.
Example sl12_anchor_N_nu_star :
  Qeq (6 # 1) sl12_N_nu_star.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 5: Sylvester-Hammond nu1/nu2/nu3, eq (39)-(40) ==== *)

(* Sylvester-Hammond certificate nu1 = delta_1 - 2 delta_2 (eq 39). *)
Definition sl12_nu1 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-2 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu1 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu1 1 + (1 # 2) * sl12_nu1 2)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Sylvester-Hammond certificate nu2 = delta_1 - delta_2 - 2 delta_3 +
  delta_6 (eq 39). *)
Definition sl12_nu2 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-2 # 1) else (0 # 1)) +
   (if Nat.eqb n 6 then (1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu2 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu2 1 + (1 # 2) * sl12_nu2 2 + (1 # 3) * sl12_nu2 3 +
  (1 # 6) * sl12_nu2 6)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Sylvester-Hammond certificate nu3 = delta_1 - delta_2 - delta_3 - delta_4
  + delta_12 (eq 39). *)
Definition sl12_nu3 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 4 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 12 then (1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu3 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu3 1 + (1 # 2) * sl12_nu3 2 + (1 # 3) * sl12_nu3 3 +
  (1 # 4) * sl12_nu3 4 + (1 # 12) * sl12_nu3 12)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 6: Sylvester extension nu4/nu5/nu6, eq (44)-(45) ==== *)

(* Sylvester extension certificate nu4 = delta_1 - delta_2 - delta_3 -
  delta_6 (eq 44). *)
Definition sl12_nu4 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 6 then (-1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu4 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu4 1 + (1 # 2) * sl12_nu4 2 + (1 # 3) * sl12_nu4 3 +
  (1 # 6) * sl12_nu4 6)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Sylvester extension certificate nu5 = delta_1 + delta_15 - delta_2 -
  delta_3 - delta_5 - delta_30 (eq 44). *)
Definition sl12_nu5 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 15 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 30 then (-1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu5 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu5 1 + (1 # 15) * sl12_nu5 15 + (1 # 2) * sl12_nu5 2 +
  (1 # 3) * sl12_nu5 3 + (1 # 5) * sl12_nu5 5 + (1 # 30) * sl12_nu5 30)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Sylvester extension certificate nu6 = delta_1 + delta_6 + delta_70 -
  delta_2 - delta_3 - delta_5 - delta_7 - delta_210 (eq 44). *)
Definition sl12_nu6 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 6 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 70 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 7 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 210 then (-1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu6 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu6 1 + (1 # 6) * sl12_nu6 6 + (1 # 70) * sl12_nu6 70 +
  (1 # 2) * sl12_nu6 2 + (1 # 3) * sl12_nu6 3 + (1 # 5) * sl12_nu6 5 + (1 #
  7) * sl12_nu6 7 + (1 # 210) * sl12_nu6 210)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Period of E(x) is 6 for nu4 (companion of eq 44). *)
Definition sl12_period_nu4 : Q := (6 # 1)%Q.
Example sl12_anchor_period_nu4 :
  Qeq (6 # 1) sl12_period_nu4.
Proof. vm_compute. reflexivity. Qed.

(* Period of E(x) is 30 for nu5 (companion of eq 44). *)
Definition sl12_period_nu5 : Q := (30 # 1)%Q.
Example sl12_anchor_period_nu5 :
  Qeq (30 # 1) sl12_period_nu5.
Proof. vm_compute. reflexivity. Qed.

(* Period of E(x) is 210 for nu6 (companion of eq 44). *)
Definition sl12_period_nu6 : Q := (210 # 1)%Q.
Example sl12_anchor_period_nu6 :
  Qeq (210 # 1) sl12_period_nu6.
Proof. vm_compute. reflexivity. Qed.

(* N = 6 for nu4: E(x) = 1 on 1 <= x < 5. *)
Definition sl12_N_nu4 : Q := (6 # 1)%Q.
Example sl12_anchor_N_nu4 :
  Qeq (6 # 1) sl12_N_nu4.
Proof. vm_compute. reflexivity. Qed.

(* N = 6 for nu5: E(x) = 1 on 1 <= x < 6. *)
Definition sl12_N_nu5 : Q := (6 # 1)%Q.
Example sl12_anchor_N_nu5 :
  Qeq (6 # 1) sl12_N_nu5.
Proof. vm_compute. reflexivity. Qed.

(* N = 10 for nu6: E(x) = 1 on 1 <= x < 10. *)
Definition sl12_N_nu6 : Q := (10 # 1)%Q.
Example sl12_anchor_N_nu6 :
  Qeq (10 # 1) sl12_N_nu6.
Proof. vm_compute. reflexivity. Qed.

(* E(x) = 1 holds up to x < 5 for nu4. *)
Definition sl12_E1_x_lt_nu4 : Q := (5 # 1)%Q.
Example sl12_anchor_E1_x_lt_nu4 :
  Qeq (5 # 1) sl12_E1_x_lt_nu4.
Proof. vm_compute. reflexivity. Qed.

(* E(x) = 1 holds up to x < 6 for nu5. *)
Definition sl12_E1_x_lt_nu5 : Q := (6 # 1)%Q.
Example sl12_anchor_E1_x_lt_nu5 :
  Qeq (6 # 1) sl12_E1_x_lt_nu5.
Proof. vm_compute. reflexivity. Qed.

(* E(x) = 1 holds up to x < 10 for nu6. *)
Definition sl12_E1_x_lt_nu6 : Q := (10 # 1)%Q.
Example sl12_anchor_E1_x_lt_nu6 :
  Qeq (10 # 1) sl12_E1_x_lt_nu6.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 7: gigantic schemes nu7/nu8, eq (90) ==== *)

(* Gigantic scheme nu7 = [1, 6, 10, 210, 231, 1155; 2, 3, 5, 7, 11, 105] (eq
  90): plus part on the upper list, minus part on the lower list. *)
Definition sl12_nu7 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 6 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 10 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 210 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 231 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 1155 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 7 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 11 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 105 then (-1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu7 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu7 1 + (1 # 6) * sl12_nu7 6 + (1 # 10) * sl12_nu7 10 +
  (1 # 210) * sl12_nu7 210 + (1 # 231) * sl12_nu7 231 + (1 # 1155) * sl12_nu7
  1155 + (1 # 2) * sl12_nu7 2 + (1 # 3) * sl12_nu7 3 + (1 # 5) * sl12_nu7 5 +
  (1 # 7) * sl12_nu7 7 + (1 # 11) * sl12_nu7 11 + (1 # 105) * sl12_nu7 105)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Gigantic scheme nu8 = [1, 6, 10, 14, 105; 2, 3, 5, 7, 11, 13, 385, 1001]
  (eq 90). *)
Definition sl12_nu8 (n : nat) : Q :=
  ((if Nat.eqb n 1 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 6 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 10 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 14 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 105 then (1 # 1) else (0 # 1)) +
   (if Nat.eqb n 2 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 3 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 5 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 7 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 11 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 13 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 385 then (-1 # 1) else (0 # 1)) +
   (if Nat.eqb n 1001 then (-1 # 1) else (0 # 1)))%Q.
Example sl12_anchor_nu8 :
  Qeq (0 # 1)
     ( (1 # 1) * sl12_nu8 1 + (1 # 6) * sl12_nu8 6 + (1 # 10) * sl12_nu8 10 +
  (1 # 14) * sl12_nu8 14 + (1 # 105) * sl12_nu8 105 + (1 # 2) * sl12_nu8 2 +
  (1 # 3) * sl12_nu8 3 + (1 # 5) * sl12_nu8 5 + (1 # 7) * sl12_nu8 7 + (1 #
  11) * sl12_nu8 11 + (1 # 13) * sl12_nu8 13 + (1 # 385) * sl12_nu8 385 + (1
  # 1001) * sl12_nu8 1001)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Period of E(x) is 2310 for nu7 (companion of eq 90). *)
Definition sl12_period_nu7 : Q := (2310 # 1)%Q.
Example sl12_anchor_period_nu7 :
  Qeq (2310 # 1) sl12_period_nu7.
Proof. vm_compute. reflexivity. Qed.

(* Period of E(x) is 30030 for nu8 (companion of eq 90). *)
Definition sl12_period_nu8 : Q := (30030 # 1)%Q.
Example sl12_anchor_period_nu8 :
  Qeq (30030 # 1) sl12_period_nu8.
Proof. vm_compute. reflexivity. Qed.

(* Lower envelope bound -2 <= E(x) for nu7 (companion of eq 90). *)
Definition sl12_E_lo_nu7 : Q := (-2 # 1)%Q.
Example sl12_anchor_E_lo_nu7 :
  Qeq (-2 # 1) sl12_E_lo_nu7.
Proof. vm_compute. reflexivity. Qed.

(* Upper envelope bound E(x) <= 2 for nu7 (companion of eq 90). *)
Definition sl12_E_hi_nu7 : Q := (2 # 1)%Q.
Example sl12_anchor_E_hi_nu7 :
  Qeq (2 # 1) sl12_E_hi_nu7.
Proof. vm_compute. reflexivity. Qed.

(* First occurrence of E(x) = -2 for nu7 is at x = 616 (companion of eq 90). *)
Definition sl12_E_first_nu7 : Q := (616 # 1)%Q.
Example sl12_anchor_E_first_nu7 :
  Qeq (616 # 1) sl12_E_first_nu7.
Proof. vm_compute. reflexivity. Qed.

(* Lower envelope bound -1 <= E(x) for nu8 (companion of eq 90). *)
Definition sl12_E_lo_nu8 : Q := (-1 # 1)%Q.
Example sl12_anchor_E_lo_nu8 :
  Qeq (-1 # 1) sl12_E_lo_nu8.
Proof. vm_compute. reflexivity. Qed.

(* Upper envelope bound E(x) <= 4 for nu8 (companion of eq 90). *)
Definition sl12_E_hi_nu8 : Q := (4 # 1)%Q.
Example sl12_anchor_E_hi_nu8 :
  Qeq (4 # 1) sl12_E_hi_nu8.
Proof. vm_compute. reflexivity. Qed.

(* First occurrence of E(x) = 4 for nu8 is at x = 1891 (companion of eq 90). *)
Definition sl12_E_first_nu8 : Q := (1891 # 1)%Q.
Example sl12_anchor_E_first_nu8 :
  Qeq (1891 # 1) sl12_E_first_nu8.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 8: the nu4 recurrence eq (62), eigenvalues eq (71) ==== *)

(* nu4 iteration recurrence (eq 62): coefficient a_i/6 in the lower step. *)
Definition sl12_nu4_step_a : Q := (1 # 6)%Q.
Example sl12_anchor_nu4_step_a :
  Qeq (1 # 6) sl12_nu4_step_a.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration recurrence (eq 62): coefficient b_i/11 in the lower step. *)
Definition sl12_nu4_step_b11 : Q := (1 # 11)%Q.
Example sl12_anchor_nu4_step_b11 :
  Qeq (1 # 11) sl12_nu4_step_b11.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration recurrence (eq 62): coefficient b_i/5 in the lower step. *)
Definition sl12_nu4_step_b5 : Q := (1 # 5)%Q.
Example sl12_anchor_nu4_step_b5 :
  Qeq (1 # 5) sl12_nu4_step_b5.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration recurrence (eq 62): outer factor 6/5 of the upper step. *)
Definition sl12_nu4_step_bfact : Q := (6 # 5)%Q.
Example sl12_anchor_nu4_step_bfact :
  Qeq (6 # 5) sl12_nu4_step_bfact.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration recurrence (eq 62): coefficient a_i/7 inside the upper step.
  *)
Definition sl12_nu4_step_a7 : Q := (1 # 7)%Q.
Example sl12_anchor_nu4_step_a7 :
  Qeq (1 # 7) sl12_nu4_step_a7.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration recurrence (eq 62): coefficient b_i/12 inside the upper
  step. *)
Definition sl12_nu4_step_b12 : Q := (1 # 12)%Q.
Example sl12_anchor_nu4_step_b12 :
  Qeq (1 # 12) sl12_nu4_step_b12.
Proof. vm_compute. reflexivity. Qed.

(* Perturbation eigenvalue lambda_1 = -0.0924... of the nu4 recurrence matrix
  (eq 71). *)
Definition sl12_nu4_lambda1 : Q := (-924 # 10000)%Q.
Example sl12_anchor_nu4_lambda1 :
  Qeq (-924 # 10000) sl12_nu4_lambda1.
Proof. vm_compute. reflexivity. Qed.

(* Perturbation eigenvalue lambda_2 = 0.3591... of the nu4 recurrence matrix
  (eq 71). *)
Definition sl12_nu4_lambda2 : Q := (3591 # 10000)%Q.
Example sl12_anchor_nu4_lambda2 :
  Qeq (3591 # 10000) sl12_nu4_lambda2.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 9: rho-rule selection values, source section 6 ==== *)

(* rho-rule value for nu4: rho = 1.5 (section 6 computational optimization). *)
Definition sl12_rho_nu4 : Q := (15 # 10)%Q.
Example sl12_anchor_rho_nu4 :
  Qeq (15 # 10) sl12_rho_nu4.
Proof. vm_compute. reflexivity. Qed.

(* rho-rule value for the Chebyshev certificate nu-star: rho = 1.2. *)
Definition sl12_rho_nu_star : Q := (12 # 10)%Q.
Example sl12_anchor_rho_nu_star :
  Qeq (12 # 10) sl12_rho_nu_star.
Proof. vm_compute. reflexivity. Qed.

(* rho-rule value for nu5: rho = 1.2. *)
Definition sl12_rho_nu5 : Q := (12 # 10)%Q.
Example sl12_anchor_rho_nu5 :
  Qeq (12 # 10) sl12_rho_nu5.
Proof. vm_compute. reflexivity. Qed.

(* rho-rule value for nu6: rho = 1.105. *)
Definition sl12_rho_nu6 : Q := (1105 # 1000)%Q.
Example sl12_anchor_rho_nu6 :
  Qeq (1105 # 1000) sl12_rho_nu6.
Proof. vm_compute. reflexivity. Qed.

(* rho-rule value for nu7: rho = 1.113. *)
Definition sl12_rho_nu7 : Q := (1113 # 1000)%Q.
Example sl12_anchor_rho_nu7 :
  Qeq (1113 # 1000) sl12_rho_nu7.
Proof. vm_compute. reflexivity. Qed.

(* rho-rule value for nu8: rho = 1.09. *)
Definition sl12_rho_nu8 : Q := (109 # 100)%Q.
Example sl12_anchor_rho_nu8 :
  Qeq (109 # 100) sl12_rho_nu8.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 10: static pairs for nu1/nu2/nu3, eq (42) ==== *)

(* A(nu1) = 0.6931... (eq 42). *)
Definition sl12_A_nu1 : Q := (6931 # 10000)%Q.
Example sl12_anchor_A_nu1 :
  Qeq (6931 # 10000) sl12_A_nu1.
Proof. vm_compute. reflexivity. Qed.

(* B(nu1) = 2 A(nu1) (eq 42): the stated factor. *)
Definition sl12_B_factor_nu1 : Q := (2 # 1)%Q.
Example sl12_anchor_B_factor_nu1 :
  Qeq (2 # 1) sl12_B_factor_nu1.
Proof. vm_compute. reflexivity. Qed.

(* B(nu1) = 1.3862... (eq 42); anchor checks the stated identity 2 * A(nu1)
  on the pinned decimals. *)
Definition sl12_B_nu1 : Q := (13862 # 10000)%Q.
Example sl12_anchor_B_nu1 :
  Qeq sl12_B_nu1 (sl12_B_factor_nu1 * sl12_A_nu1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* A(nu2) = 0.7803... (eq 42). *)
Definition sl12_A_nu2 : Q := (7803 # 10000)%Q.
Example sl12_anchor_A_nu2 :
  Qeq (7803 # 10000) sl12_A_nu2.
Proof. vm_compute. reflexivity. Qed.

(* B(nu2) = (3/2) A(nu2) (eq 42): the stated factor. *)
Definition sl12_B_factor_nu2 : Q := (3 # 2)%Q.
Example sl12_anchor_B_factor_nu2 :
  Qeq (3 # 2) sl12_B_factor_nu2.
Proof. vm_compute. reflexivity. Qed.

(* B(nu2) = 1.1705... (eq 42). *)
Definition sl12_B_nu2 : Q := (11705 # 10000)%Q.
Example sl12_anchor_B_nu2 :
  Qeq (11705 # 10000) sl12_B_nu2.
Proof. vm_compute. reflexivity. Qed.

(* A(nu3) = 0.8522... (eq 42). *)
Definition sl12_A_nu3 : Q := (8522 # 10000)%Q.
Example sl12_anchor_A_nu3 :
  Qeq (8522 # 10000) sl12_A_nu3.
Proof. vm_compute. reflexivity. Qed.

(* B(nu3) = (4/3) A(nu3) (eq 42): the stated factor. *)
Definition sl12_B_factor_nu3 : Q := (4 # 3)%Q.
Example sl12_anchor_B_factor_nu3 :
  Qeq (4 # 3) sl12_B_factor_nu3.
Proof. vm_compute. reflexivity. Qed.

(* B(nu3) = 1.1363... (eq 42). *)
Definition sl12_B_nu3 : Q := (11363 # 10000)%Q.
Example sl12_anchor_B_nu3 :
  Qeq (11363 # 10000) sl12_B_nu3.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 11: the Chebyshev static pair, eq (43) ==== *)

(* A(nu-star) = 0.9212... (eq 43); anchor checks it is the 4-decimal
  truncation of the eq (34) pin. *)
Definition sl12_A_nu_star_4dp : Q := (9212 # 10000)%Q.
Example sl12_anchor_A_nu_star_4dp : 9212%Z = Z.div (Qnum sl12_A_star) 10%Z.
Proof. vm_compute. reflexivity. Qed.

(* B(nu-star) = (6/5) A(nu-star) = 1.1055... (eq 43); anchor checks floor-4dp
  of (6/5) times the eq (34) pin. *)
Definition sl12_B_nu_star : Q := (11055 # 10000)%Q.
Example sl12_anchor_B_nu_star :
  11055%Z =
    Z.div (Qnum ((6 # 5) * sl12_A_star) * 10000)
           (Z.pos (Qden ((6 # 5) * sl12_A_star))).
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 12: A values for nu4/nu5/nu6, eq (48) ==== *)

(* A(nu4) = 1.0114... (eq 48). *)
Definition sl12_A_nu4 : Q := (10114 # 10000)%Q.
Example sl12_anchor_A_nu4 :
  Qeq (10114 # 10000) sl12_A_nu4.
Proof. vm_compute. reflexivity. Qed.

(* A(nu5) = 0.9675... (eq 48). *)
Definition sl12_A_nu5 : Q := (9675 # 10000)%Q.
Example sl12_anchor_A_nu5 :
  Qeq (9675 # 10000) sl12_A_nu5.
Proof. vm_compute. reflexivity. Qed.

(* A(nu6) = 0.9787... (eq 48). *)
Definition sl12_A_nu6 : Q := (9787 # 10000)%Q.
Example sl12_anchor_A_nu6 :
  Qeq (9787 # 10000) sl12_A_nu6.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 13: the M values of eq (49) ==== *)

(* M = 5 for nu4 (eq 49 companion, Example 4.2). *)
Definition sl12_M_nu4 : Q := (5 # 1)%Q.
Example sl12_anchor_M_nu4 :
  Qeq (5 # 1) sl12_M_nu4.
Proof. vm_compute. reflexivity. Qed.

(* M = 17 for nu5 (eq 49 companion, Example 4.2). *)
Definition sl12_M_nu5 : Q := (17 # 1)%Q.
Example sl12_anchor_M_nu5 :
  Qeq (17 # 1) sl12_M_nu5.
Proof. vm_compute. reflexivity. Qed.

(* M = 13 for nu6 (eq 49 companion, Example 4.2). *)
Definition sl12_M_nu6 : Q := (13 # 1)%Q.
Example sl12_anchor_M_nu6 :
  Qeq (13 # 1) sl12_M_nu6.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 14: corrected static values, eq (55) ==== *)

(* A'(nu4) = (19/25) A(nu4) (eq 55); anchor checks the eq (49) form 1 -
  N/(M(N-1)) with the pinned N = 6, M = 5. *)
Definition sl12_red_nu4 : Q := (19 # 25)%Q.
Example sl12_anchor_red_nu4 :
  Qeq sl12_red_nu4
      ((1 # 1) -
       (sl12_N_nu4 / (sl12_M_nu4 * (sl12_N_nu4 - (1 # 1)))))%Q.
Proof. vm_compute. reflexivity. Qed.

(* A'(nu4) = 0.7686... (eq 55); anchor checks floor-4dp of (19/25) times the
  pinned A(nu4). *)
Definition sl12_Ap_nu4 : Q := (7686 # 10000)%Q.
Example sl12_anchor_Ap_nu4 :
  7686%Z =
    Z.div (Qnum (sl12_red_nu4 * sl12_A_nu4) * 10000)
           (Z.pos (Qden (sl12_red_nu4 * sl12_A_nu4))).
Proof. vm_compute. reflexivity. Qed.

(* B(nu4) = (6/5) A(nu4) (eq 55); anchor checks N/(N-1) with the pinned N =
  6. *)
Definition sl12_Bup_nu4 : Q := (6 # 5)%Q.
Example sl12_anchor_Bup_nu4 :
  Qeq sl12_Bup_nu4 (sl12_N_nu4 / (sl12_N_nu4 - (1 # 1)))%Q.
Proof. vm_compute. reflexivity. Qed.

(* B(nu4) = 1.2136... (eq 55); anchor checks floor-4dp of (6/5) times the
  pinned A(nu4). *)
Definition sl12_B_nu4 : Q := (12136 # 10000)%Q.
Example sl12_anchor_B_nu4 :
  12136%Z =
    Z.div (Qnum (sl12_Bup_nu4 * sl12_A_nu4) * 10000)
           (Z.pos (Qden (sl12_Bup_nu4 * sl12_A_nu4))).
Proof. vm_compute. reflexivity. Qed.

(* A'(nu5) = (79/85) A(nu5) (eq 55); anchor checks the eq (49) form with the
  pinned N = 6, M = 17. *)
Definition sl12_red_nu5 : Q := (79 # 85)%Q.
Example sl12_anchor_red_nu5 :
  Qeq sl12_red_nu5
      ((1 # 1) -
       (sl12_N_nu5 / (sl12_M_nu5 * (sl12_N_nu5 - (1 # 1)))))%Q.
Proof. vm_compute. reflexivity. Qed.

(* A'(nu5) = 0.8992... (eq 55); anchor checks floor-4dp of (79/85) times the
  pinned A(nu5). *)
Definition sl12_Ap_nu5 : Q := (8992 # 10000)%Q.
Example sl12_anchor_Ap_nu5 :
  8992%Z =
    Z.div (Qnum (sl12_red_nu5 * sl12_A_nu5) * 10000)
           (Z.pos (Qden (sl12_red_nu5 * sl12_A_nu5))).
Proof. vm_compute. reflexivity. Qed.

(* B(nu5) = (6/5) A(nu5) (eq 55); anchor checks N/(N-1) with the pinned N =
  6. *)
Definition sl12_Bup_nu5 : Q := (6 # 5)%Q.
Example sl12_anchor_Bup_nu5 :
  Qeq sl12_Bup_nu5 (sl12_N_nu5 / (sl12_N_nu5 - (1 # 1)))%Q.
Proof. vm_compute. reflexivity. Qed.

(* B(nu5) = 1.1610... (eq 55); anchor checks floor-4dp of (6/5) times the
  pinned A(nu5). *)
Definition sl12_B_nu5 : Q := (11610 # 10000)%Q.
Example sl12_anchor_B_nu5 :
  11610%Z =
    Z.div (Qnum (sl12_Bup_nu5 * sl12_A_nu5) * 10000)
           (Z.pos (Qden (sl12_Bup_nu5 * sl12_A_nu5))).
Proof. vm_compute. reflexivity. Qed.

(* A'(nu6) = (107/117) A(nu6) (eq 55); anchor checks the eq (49) form with
  the pinned N = 10, M = 13. *)
Definition sl12_red_nu6 : Q := (107 # 117)%Q.
Example sl12_anchor_red_nu6 :
  Qeq sl12_red_nu6
      ((1 # 1) -
       (sl12_N_nu6 / (sl12_M_nu6 * (sl12_N_nu6 - (1 # 1)))))%Q.
Proof. vm_compute. reflexivity. Qed.

(* A'(nu6) = 0.8951... (eq 55). The floor route from the 4-dp A(nu6) pin
  disagrees with this digit (both source routes agree with the true-value
  route), so the literal pin stands alone. *)
Definition sl12_Ap_nu6 : Q := (8951 # 10000)%Q.
Example sl12_anchor_Ap_nu6 :
  Qeq (8951 # 10000) sl12_Ap_nu6.
Proof. vm_compute. reflexivity. Qed.

(* B(nu6) = (10/9) A(nu6) (eq 55); anchor checks N/(N-1) with the pinned N =
  10. *)
Definition sl12_Bup_nu6 : Q := (10 # 9)%Q.
Example sl12_anchor_Bup_nu6 :
  Qeq sl12_Bup_nu6 (sl12_N_nu6 / (sl12_N_nu6 - (1 # 1)))%Q.
Proof. vm_compute. reflexivity. Qed.

(* B(nu6) = 1.0875... (eq 55). The floor route from the 4-dp A(nu6) pin
  disagrees with this digit (both source routes agree with the true-value
  route), so the literal pin stands alone. *)
Definition sl12_B_nu6 : Q := (10875 # 10000)%Q.
Example sl12_anchor_B_nu6 :
  Qeq (10875 # 10000) sl12_B_nu6.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 15: the nu4 iteration fixed points, eq (65)-(66) ==== *)

(* nu4 iteration fixed point alpha = 4242/5391 (eq 65); anchor checks the
  stated decimal 0.7868 as the 4-dp floor of the fraction. *)
Definition sl12_alpha_nu4 : Q := (4242 # 5391)%Q.
Example sl12_anchor_alpha_nu4 :
  7868%Z = Z.div (Qnum sl12_alpha_nu4 * 10000) (Z.pos (Qden sl12_alpha_nu4)).
Proof. vm_compute. reflexivity. Qed.

(* alpha = 0.7868... (eq 65), four decimals as stated. *)
Definition sl12_alpha_nu4_4dp : Q := (7868 # 10000)%Q.
Example sl12_anchor_alpha_nu4_4dp :
  Qeq (7868 # 10000) sl12_alpha_nu4_4dp.
Proof. vm_compute. reflexivity. Qed.

(* nu4 iteration fixed point beta = 6380/5391 (eq 65); anchor checks the
  stated decimal 1.18345 as the 5-dp floor of the fraction. *)
Definition sl12_beta_nu4 : Q := (6380 # 5391)%Q.
Example sl12_anchor_beta_nu4 :
  118345%Z = Z.div (Qnum sl12_beta_nu4 * 100000) (Z.pos (Qden sl12_beta_nu4)).
Proof. vm_compute. reflexivity. Qed.

(* beta = 1.18345... (eq 65), five decimals as stated. *)
Definition sl12_beta_nu4_5dp : Q := (118345 # 100000)%Q.
Example sl12_anchor_beta_nu4_5dp :
  Qeq (118345 # 100000) sl12_beta_nu4_5dp.
Proof. vm_compute. reflexivity. Qed.

(* a = alpha A = 0.7958... (eq 66); anchor checks floor-4dp of alpha times
  the pinned A(nu4). *)
Definition sl12_a_nu4_iter : Q := (7958 # 10000)%Q.
Example sl12_anchor_a_nu4_iter :
  7958%Z =
    Z.div (Qnum (sl12_alpha_nu4 * sl12_A_nu4) * 10000)
           (Z.pos (Qden (sl12_alpha_nu4 * sl12_A_nu4))).
Proof. vm_compute. reflexivity. Qed.

(* b = beta A = 1.1969... (eq 66); anchor checks floor-4dp of beta times the
  pinned A(nu4). *)
Definition sl12_b_nu4_iter : Q := (11969 # 10000)%Q.
Example sl12_anchor_b_nu4_iter :
  11969%Z =
    Z.div (Qnum (sl12_beta_nu4 * sl12_A_nu4) * 10000)
           (Z.pos (Qden (sl12_beta_nu4 * sl12_A_nu4))).
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 16: the Chebyshev iteration, eq (84)-(88) ==== *)

(* Chebyshev iteration eigenvalue lambda_1 = -0.0054... (eq 84). *)
Definition sl12_lambda1_cheb : Q := (-54 # 10000)%Q.
Example sl12_anchor_lambda1_cheb :
  Qeq (-54 # 10000) sl12_lambda1_cheb.
Proof. vm_compute. reflexivity. Qed.

(* Chebyshev iteration eigenvalue lambda_2 = 0.1671... (eq 84). *)
Definition sl12_lambda2_cheb : Q := (1671 # 10000)%Q.
Example sl12_anchor_lambda2_cheb :
  Qeq (1671 # 10000) sl12_lambda2_cheb.
Proof. vm_compute. reflexivity. Qed.

(* Chebyshev iteration fixed point alpha = 51072/50999 (eq 86). *)
Definition sl12_alpha_cheb : Q := (51072 # 50999)%Q.
Example sl12_anchor_alpha_cheb :
  Qeq (51072 # 50999) sl12_alpha_cheb.
Proof. vm_compute. reflexivity. Qed.

(* Chebyshev iteration fixed point beta = 59595/50999 (eq 86). *)
Definition sl12_beta_cheb : Q := (59595 # 50999)%Q.
Example sl12_anchor_beta_cheb :
  Qeq (59595 # 50999) sl12_beta_cheb.
Proof. vm_compute. reflexivity. Qed.

(* a = alpha A = 0.9226... (eq 88); anchor checks floor-4dp of alpha times
  the eq (34) pin. *)
Definition sl12_a_cheb_iter : Q := (9226 # 10000)%Q.
Example sl12_anchor_a_cheb_iter :
  9226%Z =
    Z.div (Qnum (sl12_alpha_cheb * sl12_A_star) * 10000)
           (Z.pos (Qden (sl12_alpha_cheb * sl12_A_star))).
Proof. vm_compute. reflexivity. Qed.

(* b = beta A = 1.0765... (eq 88); anchor checks floor-4dp of beta times the
  eq (34) pin. *)
Definition sl12_b_cheb_iter : Q := (10765 # 10000)%Q.
Example sl12_anchor_b_cheb_iter :
  10765%Z =
    Z.div (Qnum (sl12_beta_cheb * sl12_A_star) * 10000)
           (Z.pos (Qden (sl12_beta_cheb * sl12_A_star))).
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 17: the nu5 iteration limit, eq (93) ==== *)

(* nu5 iteration limit a = 0.9119... (eq 93). *)
Definition sl12_a_nu5_iter : Q := (9119 # 10000)%Q.
Example sl12_anchor_a_nu5_iter :
  Qeq (9119 # 10000) sl12_a_nu5_iter.
Proof. vm_compute. reflexivity. Qed.

(* nu5 iteration limit b = 1.0909... (eq 93). *)
Definition sl12_b_nu5_iter : Q := (10909 # 10000)%Q.
Example sl12_anchor_b_nu5_iter :
  Qeq (10909 # 10000) sl12_b_nu5_iter.
Proof. vm_compute. reflexivity. Qed.

(* nu5 iteration ratio b/a = 1.1963... (companion of eq 93). The floor route
  from the pinned decimal pair disagrees with this digit (the true-value
  route agrees), so the literal pin stands alone. *)
Definition sl12_ratio_nu5_iter : Q := (11963 # 10000)%Q.
Example sl12_anchor_ratio_nu5_iter :
  Qeq (11963 # 10000) sl12_ratio_nu5_iter.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 18: the nu6 triples, eq (95)-(97) ==== *)

(* nu6 static pair (eq 95): a = 0.941854... *)
Definition sl12_a_nu6_eq95 : Q := (941854 # 1000000)%Q.
Example sl12_anchor_a_nu6_eq95 :
  Qeq (941854 # 1000000) sl12_a_nu6_eq95.
Proof. vm_compute. reflexivity. Qed.

(* nu6 static pair (eq 95): b = 1.056726... *)
Definition sl12_b_nu6_eq95 : Q := (1056726 # 1000000)%Q.
Example sl12_anchor_b_nu6_eq95 :
  Qeq (1056726 # 1000000) sl12_b_nu6_eq95.
Proof. vm_compute. reflexivity. Qed.

(* nu6 pair with the omitted terms included (eq 96): a = 0.941806... *)
Definition sl12_a_nu6_eq96 : Q := (941806 # 1000000)%Q.
Example sl12_anchor_a_nu6_eq96 :
  Qeq (941806 # 1000000) sl12_a_nu6_eq96.
Proof. vm_compute. reflexivity. Qed.

(* nu6 pair with the omitted terms included (eq 96): b = 1.056825... *)
Definition sl12_b_nu6_eq96 : Q := (1056825 # 1000000)%Q.
Example sl12_anchor_b_nu6_eq96 :
  Qeq (1056825 # 1000000) sl12_b_nu6_eq96.
Proof. vm_compute. reflexivity. Qed.

(* nu6 pair at rho = 1.105 (eq 97): a = 0.944462... *)
Definition sl12_a_nu6_eq97 : Q := (944462 # 1000000)%Q.
Example sl12_anchor_a_nu6_eq97 :
  Qeq (944462 # 1000000) sl12_a_nu6_eq97.
Proof. vm_compute. reflexivity. Qed.

(* nu6 pair at rho = 1.105 (eq 97): b = 1.055800... *)
Definition sl12_b_nu6_eq97 : Q := (1055800 # 1000000)%Q.
Example sl12_anchor_b_nu6_eq97 :
  Qeq (1055800 # 1000000) sl12_b_nu6_eq97.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 19: the nu7 triples, eq (98)-(100) ==== *)

(* nu7 mixed pair (eq 98): a = 0.946197... *)
Definition sl12_a_nu7_eq98 : Q := (946197 # 1000000)%Q.
Example sl12_anchor_a_nu7_eq98 :
  Qeq (946197 # 1000000) sl12_a_nu7_eq98.
Proof. vm_compute. reflexivity. Qed.

(* nu7 mixed pair (eq 98): b = 1.055185... *)
Definition sl12_b_nu7_eq98 : Q := (1055185 # 1000000)%Q.
Example sl12_anchor_b_nu7_eq98 :
  Qeq (1055185 # 1000000) sl12_b_nu7_eq98.
Proof. vm_compute. reflexivity. Qed.

(* nu7 lower bound with terms up to psi(x/616) (eq 99): b = 1.054239... *)
Definition sl12_b_nu7_eq99 : Q := (1054239 # 1000000)%Q.
Example sl12_anchor_b_nu7_eq99 :
  Qeq (1054239 # 1000000) sl12_b_nu7_eq99.
Proof. vm_compute. reflexivity. Qed.

(* nu7 pair at rho = 1.113 (eq 100): a = 0.946585... *)
Definition sl12_a_nu7_eq100 : Q := (946585 # 1000000)%Q.
Example sl12_anchor_a_nu7_eq100 :
  Qeq (946585 # 1000000) sl12_a_nu7_eq100.
Proof. vm_compute. reflexivity. Qed.

(* nu7 pair at rho = 1.113 (eq 100): b = 1.054309... *)
Definition sl12_b_nu7_eq100 : Q := (1054309 # 1000000)%Q.
Example sl12_anchor_b_nu7_eq100 :
  Qeq (1054309 # 1000000) sl12_b_nu7_eq100.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 20: the nu8 records, eq (101)-(102) ==== *)

(* nu8 champion upper record (eq 101): a = 0.95695... *)
Definition sl12_a_nu8_eq101 : Q := (95695 # 100000)%Q.
Example sl12_anchor_a_nu8_eq101 :
  Qeq (95695 # 100000) sl12_a_nu8_eq101.
Proof. vm_compute. reflexivity. Qed.

(* nu8 champion lower record (eq 101): b = 1.04423... *)
Definition sl12_b_nu8_eq101 : Q := (104423 # 100000)%Q.
Example sl12_anchor_b_nu8_eq101 :
  Qeq (104423 # 100000) sl12_b_nu8_eq101.
Proof. vm_compute. reflexivity. Qed.

(* nu8 pair at rho = 1.09 (eq 102): a = 0.957600... *)
Definition sl12_a_nu8_eq102 : Q := (957600 # 1000000)%Q.
Example sl12_anchor_a_nu8_eq102 :
  Qeq (957600 # 1000000) sl12_a_nu8_eq102.
Proof. vm_compute. reflexivity. Qed.

(* nu8 pair at rho = 1.09 (eq 102): b = 1.043521... *)
Definition sl12_b_nu8_eq102 : Q := (1043521 # 1000000)%Q.
Example sl12_anchor_b_nu8_eq102 :
  Qeq (1043521 # 1000000) sl12_b_nu8_eq102.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 21: the upper-frame factor for N = 6, eq (33)-(35) ==== *)

(* Upper-frame factor for N = 6: psi(x) <= (6/5) A*x (eq 35), the
  geometric-sum factor N/(N-1) of eq (33). *)
Definition sl12_frame_upper_factor_n6 : Q := (6 # 5)%Q.
Example sl12_anchor_frame_upper_factor_n6 :
  Qeq sl12_frame_upper_factor_n6
      (sl12_N_nu_star / (sl12_N_nu_star - (1 # 1)))%Q.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 22: the computational oracle pointer ==== *)
(* The source performs all computations in a public Python notebook   *)
(* repository (its reference [11]); a repository pointer carries no   *)
(* rational constant, so this section pins nothing.                   *)

(* End of file: 103 pinned constants, 103 anchors, all vm_compute      *)
(* pins over verbatim citation values; NOT claimed beyond citation.    *)
