(* ================================================================= *)
(* Mission.: gammaP1 N2a node, cage constant face (formal statement    *)
(*   unit): the KB41b C1-C7 EXACT certificate chain as Set-carried Coq *)
(*   statements for the v2-r2 workorder N6'-a face — piece one = C1-C4 *)
(*   (rho pin-face calibration), piece two = C5+C7 (sigma assembly     *)
(*   coverage + N0 poly absorption); C6 lives in piu_zz_sigma_decay.v  *)
(*   b4. The 65 kb41o_samples.py machine samples are lifted to         *)
(*   vm_compute Qed lemmas; proof-open faces stay as Set-typed         *)
(*   obligations: no Prop surface, admission-free, axiom-free.         *)
(* Dependencies.: S02_CauchyComplete.v (QltT :48, QleT' :99,           *)
(*   Qle_to_QleT' :115, QeqT :303, real_lt :468, real_const :859);     *)
(*   S03_QExp.v cauchy_real_exp :1203 (C5 bridge face);                *)
(*   S10_KVQuantTrig.v real_pi_geom :8543 (C1 gap faces, prec :9355);  *)
(*   trust cache ConstructiveWorld_vo (12/12 deps .vo-present).        *)
(* References.: receipt-KB41b (C1-C7 table 3-1); receipt-KB41e (N3     *)
(*   1e-8 bracket); receipt-KB41g 3-3.4/4-2/4-3/4-4 (four-piece        *)
(*   method, U-shape endpoint rule, C_asm sheet); receipt-KB41o        *)
(*   (statement-face drafts, tier table, 65 machine samples);          *)
(*   workorder GEDAN-gammaP1 sec.2 N6'-a/N6'-b, sec.5 pin sheet,       *)
(*   sec.6 red lines 1-8.                                              *)
(* Constructivity.: statement faces Set-carried (QleT'/QeqT/QltT/      *)
(*   real_lt/real_le over sigT); transcendental endpoints stay gap     *)
(*   faces (C1 = Machin machine increment; C5 bridge = S03 consumer    *)
(*   face); the draft's top-level assumed constant becomes the         *)
(*   Casm-indexed faces (F1); lia/nia only in declared closed-form     *)
(*   auxiliary steps: C7 U-shape pair (KB41g 4-2(a)), C3 P' (RL3).     *)
(* Build.: coqc -native-compiler no -q -Q ConstructiveWorld_vo ""      *)
(*   piu_zz_cage_constants.v | cpu_guard v3 wrapped ASCII cmd relay,   *)
(*   sandbox kb45_work_20261028; sample oracle kb41o_samples.py.       *)
(* ================================================================= *)

From Stdlib Require Import QArith ZArith Arith Lia.
From Stdlib Require Import QArith.Qabs.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

(* Fail-loud log (this seat, build log carries the full account):
   F1 draft's top-level assumed constant piu_zz_ec_Casm -> Casm-indexed
      faces (keeps this unit axiom-free);
   F2 draft qexp_sum lacked Qred (denominator blowup) -> Qred per step
      (judgments cross-multiply, so Qred changes size only);
   F3 draft qexp_sum index term (Z.of_nat N + 1)%Q ill-scooped ->
      (inject_Z (Z.of_nat (S N'))) form;
   F4 C5 E_up geometric tail added per the sample oracle qexp_ub (the
      draft deferred it as a pending item);
   F5 draft-side Z.abs on Q values -> Qabs (N2b unit);
   F6 draft Abort'd lemmas re-landed as Set-typed obligation faces. *)

(* ---------- shared Q-series proxies (Set, fully computable) ------- *)

(* exact rational k! (Qred per step keeps denominators exact-math size) *)
Fixpoint piu_zz_qfact (k : nat) : Q :=
  match k with
  | O => (1 # 1)%Q
  | S k' => Qred ((inject_Z (Z.of_nat (S k')) * piu_zz_qfact k')%Q)
  end.

(* exact rational x^k *)
Fixpoint piu_zz_qpow_nat (k : nat) (x : Q) : Q :=
  match k with
  | O => (1 # 1)%Q
  | S k' => Qred ((piu_zz_qpow_nat k' x * x)%Q)
  end.

(* x^k / k! *)
Definition piu_zz_qexp_term (k : nat) (x : Q) : Q :=
  Qred ((piu_zz_qpow_nat k x / piu_zz_qfact k)%Q).

(* e^x partial sum S_N = sum_{k<=N} x^k/k! (all-positive series;
   partial sum = lower-bound proxy). Qred per step (F2). *)
Fixpoint piu_zz_qexp_sum (N : nat) (x : Q) {struct N} : Q :=
  match N with
  | O => (1 # 1)%Q
  | S N' => Qred ((piu_zz_qexp_sum N' x + piu_zz_qexp_term (S N') x)%Q)
  end.

(* geometric tail bound: e^x <= S_N + (x^{N+1}/(N+1)!)*(N+2)/(N+2-x),
   valid for N+2 > x (kb41o_samples.py qexp_ub verbatim math; F4) *)
Definition piu_zz_qexp_tail (N : nat) (x : Q) : Q :=
  Qred ((piu_zz_qexp_term (S N) x
         * (inject_Z (Z.of_nat (N + 2))
            / (inject_Z (Z.of_nat (N + 2)) - x))%Q)%Q).

(* P(N) = 108N^3 - 2359989N^2 + 138304N - 2048 (ZZ2020 eq (18)) *)
Definition piu_zz_q_eval_P (N : Q) : Q :=
  ((108 # 1) * (N * N * N) - (2359989 # 1) * (N * N)
    + (138304 # 1) * N - (2048 # 1))%Q.

(* P'(N) = 324N^2 - 4719978N + 138304 *)
Definition piu_zz_q_eval_P' (N : Q) : Q :=
  ((324 # 1) * (N * N) - (4719978 # 1) * N + (138304 # 1))%Q.

(* Z-carried mirror of P' + bridge (fail-loud F10: symbolic Q-layer
   reduction trips the binary-literal match expansion of Z.mul and
   blinds micromega; the bridge restates P' at the inject_Z image so
   the monotonicity argument runs on a pure Z polynomial via
   Zle_Qle, QArith_base :966) *)
Definition piu_zz_p'Z (m : Z) : Z := 324 * (m * m) - 4719978 * m + 138304.

Lemma piu_zz_p'Z_qeq : forall m : Z,
  piu_zz_q_eval_P' (inject_Z m) == inject_Z (piu_zz_p'Z m).
Proof.
  intros m.
  unfold Qeq.
  unfold piu_zz_q_eval_P'.
  unfold piu_zz_p'Z.
  unfold inject_Z.
  cbn [Qnum Qden Qmult Qplus Qminus Qopp].
  nia.
Qed.

(* ================================================================= *)
(* piece one: C1-C4, rho pin-face calibration                         *)
(* ================================================================= *)

(* ---- C1 pi brackets: gap faces. Tree has only the (3,10/3) machine *)
(* (S10:9355/:9370); the 333/106-precision Machin alternating-series   *)
(* bracket machine is the KB41o tier-table increment-one item. The     *)
(* numeric sample face lives in kb41o_samples.py S1-01/02/03. -------- *)
Definition piu_zz_c1_pi_gt_333_106_face : Set :=
  real_lt (real_const (333 # 106)%Q) real_pi_geom.

Definition piu_zz_c1_pi_gt_103993_33102_face : Set :=
  real_lt (real_const (103993 # 33102)%Q) real_pi_geom.

(* ---- C2 c-constant sub-certificates (Q-proxies, vm_compute) ------- *)
(* sqrt3 < 26/15 via 3 < (26/15)^2 (sample S2-04: 675<676) *)
Lemma piu_zz_c2_sqrt3_lt_26_15 :
  S02_CauchyComplete.QltT (3 # 1)%Q ((26 # 15)%Q * (26 # 15)%Q).
Proof. vm_compute. reflexivity. Qed.

(* Pell chain sqrt3 < 1351/780 via 3 < (1351/780)^2 (S2-05) *)
Lemma piu_zz_c2_pell_sqrt3_lt_1351_780 :
  S02_CauchyComplete.QltT (3 # 1)%Q ((1351 # 780)%Q * (1351 # 780)%Q).
Proof. vm_compute. reflexivity. Qed.

(* e^(1312/5000) > 13/10: partial-sum lower proxy at N=5 (S2-08) *)
Lemma piu_zz_c2_exp_1312_5000_series_lb :
  S02_CauchyComplete.QltT (13 # 10)%Q (piu_zz_qexp_sum 5 (1312 # 5000)%Q).
Proof. vm_compute. reflexivity. Qed.

(* tight chain: e^(26163/100000) > 4053/3120 at N=12 (S2-10) *)
Lemma piu_zz_c2_exp_26163_series_lb :
  S02_CauchyComplete.QltT (4053 # 3120)%Q (piu_zz_qexp_sum 12 (26163 # 100000)%Q).
Proof. vm_compute. reflexivity. Qed.

(* pi/(2*sqrt3) > (333/106)/(2*(26/15)) rational identity (S2-06) *)
Lemma piu_zz_c2_c0_ratio_identity :
  S02_CauchyComplete.QeqT
    ((333 # 106)%Q / ((2 # 1)%Q * (26 # 15)%Q)) (4995 # 5512)%Q.
Proof. vm_compute. reflexivity. Qed.

(* log mount identity (3/4)*(26/15) == 13/10 (S2-07) *)
Lemma piu_zz_c2_log_mount_identity :
  S02_CauchyComplete.QeqT ((3 # 4)%Q * (26 # 15)%Q) (13 # 10)%Q.
Proof. vm_compute. reflexivity. Qed.

(* c0 coarse lower bound = 4995/5512 - 2624/10000 (S2-06/09 chain) *)
Definition piu_zz_c2_c0_lb_coarse : Q := (35486512 # 55120000)%Q.

Lemma piu_zz_c2_c0_compose_identity :
  S02_CauchyComplete.QeqT ((4995 # 5512)%Q - (2624 # 10000)%Q)
    piu_zz_c2_c0_lb_coarse.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c2_c0_lb_coarse_pos :
  S02_CauchyComplete.QltT (0 # 1)%Q piu_zz_c2_c0_lb_coarse.
Proof. vm_compute. reflexivity. Qed.

(* c0 tight lower bound: (103993/33102)/(2*(1351/780)) - 26163/100000;
   sample S2-11: > 64526943/10^8 (KB41b c0_tight = 0.64526943...) *)
Definition piu_zz_c2_c0_lb_tight : Q :=
  ((103993 # 33102)%Q / ((2 # 1)%Q * (1351 # 780)%Q)
    - (26163 # 100000)%Q)%Q.

Lemma piu_zz_c2_c0_tight_lb_gt :
  S02_CauchyComplete.QltT (64526943 # 100000000)%Q piu_zz_c2_c0_lb_tight.
Proof. vm_compute. reflexivity. Qed.

(* ---- C3 eq(18) root anchors (sign vm_compute; Sturm uniqueness =   *)
(* KB41b C3 EXACT, cited reference interface, not re-proved here) ---- *)
Lemma piu_zz_c3_P_21851_neg :
  S02_CauchyComplete.QltT (piu_zz_q_eval_P (21851 # 1)%Q) (0 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c3_P_21852_pos :
  S02_CauchyComplete.QltT (0 # 1)%Q (piu_zz_q_eval_P (21852 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

(* octant anchor: P(174813/8) < 0 (S3-14: 8^3*P = -1753086647500) *)
Lemma piu_zz_c3_P_174813_8_neg :
  S02_CauchyComplete.QltT (piu_zz_q_eval_P (174813 # 8)%Q) (0 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* single-point derivative anchor (S3-15: P'(15000) = 2100468304 > 0) *)
Lemma piu_zz_c3_Pp_15000_pos :
  S02_CauchyComplete.QltT (0 # 1)%Q (piu_zz_q_eval_P' (15000 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

(* monotonicity: P' > 0 on N >= 15000. The threshold premise is        *)
(* carried at Z (Z.of_nat n >= 15000): the nat literal 15000 trips the *)
(* abstract-large-number elaboration and blinds zify (fail-loud F9).   *)
(* lia-grade decomposition: x >= 0 and 324x - 4719978 >= 0 (both       *)
(* linear), multiplied by nia — an auxiliary closed-form arithmetic    *)
(* step, declared per red line 3. *)
Lemma piu_zz_c3_P'_pos_high :
  forall n : nat, (15000 <= Z.of_nat n)%Z ->
    S02_CauchyComplete.QleT' (0 # 1)%Q
      (piu_zz_q_eval_P' (inject_Z (Z.of_nat n))).
Proof.
  intros n Hn.
  apply S02_CauchyComplete.Qle_to_QleT'.
  rewrite (piu_zz_p'Z_qeq (Z.of_nat n)).
  change (inject_Z 0%Z <= inject_Z (piu_zz_p'Z (Z.of_nat n)))%Q.
  rewrite <- Zle_Qle.
  unfold piu_zz_p'Z.
  assert (Hx : (0 <= Z.of_nat n)%Z) by lia.
  assert (Hc : (0 <= 324 * Z.of_nat n - 4719978)%Z) by lia.
  nia.
Qed.

(* ---- C4 rho pin-face rational certificates (direct transcription) *)
(* coarse: rho_ZZ^2 proxy 223069/10^7 <= (3/20)^2 = 9/400 (S4-17) *)
Lemma piu_zz_c4_rhossq_le_9_400 :
  S02_CauchyComplete.QleT' (223069 # 10000000)%Q ((3 # 20)%Q * (3 # 20)%Q).
Proof. vm_compute. reflexivity. Qed.

(* tight: 2224101/10^8 <= (373/2500)^2 (S4-18) *)
Lemma piu_zz_c4_rhossq_le_373_2500_sq :
  S02_CauchyComplete.QleT' (2224101 # 100000000)%Q
    ((373 # 2500)%Q * (373 # 2500)%Q).
Proof. vm_compute. reflexivity. Qed.

(* tight <= coarse: (373/2500)^2 <= (3/20)^2 (S4-19) *)
Lemma piu_zz_c4_tight_sq_le_main_sq :
  S02_CauchyComplete.QleT' ((373 # 2500)%Q * (373 # 2500)%Q)
    ((3 # 20)%Q * (3 # 20)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ordering chain links 13/400<149/1000<373/2500<3/20<2/13<1/6 (S4-20) *)
Lemma piu_zz_c4_order_13_400_lt_149_1000 :
  S02_CauchyComplete.QltT (13 # 400)%Q (149 # 1000)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c4_order_149_1000_lt_373_2500 :
  S02_CauchyComplete.QltT (149 # 1000)%Q (373 # 2500)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c4_order_373_2500_lt_3_20 :
  S02_CauchyComplete.QltT (373 # 2500)%Q (3 # 20)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c4_order_3_20_lt_2_13 :
  S02_CauchyComplete.QltT (3 # 20)%Q (2 # 13)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c4_order_2_13_lt_1_6 :
  S02_CauchyComplete.QltT (2 # 13)%Q (1 # 6)%Q.
Proof. vm_compute. reflexivity. Qed.

(* slack identity: (3/20)/(373/2500) == 375/373 (S4-21, QeqT) *)
Lemma piu_zz_c4_slack_identity :
  S02_CauchyComplete.QeqT ((3 # 20)%Q / (373 # 2500)%Q) (375 # 373)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Honest-face note: rho_ZZ itself is not a Q object; the tree-side   *)
(* certificate content is pin admissibility (C4 pin-face lemmas + C3  *)
(* root anchors + C1/C2 proxy faces), consistent with the workorder   *)
(* sec.2 N6'-a row: non-transcribed design pin + certificate suite.   *)

(* ================================================================= *)
(* piece two: C5 (sigma assembly coverage) + C7 (N0 poly absorption)  *)
(* ================================================================= *)

(* ---- C5: N3^2 * e^(2(4-c)) <= 2^39, Q single-point faces ---------- *)
(* x_up = 2*(4 - c0_lb_coarse) (sample S5-22); E_up = S_30 + geometric *)
(* tail = kb41o qexp_ub verbatim (F4). *)
Definition piu_zz_c5_x_up : Q :=
  ((4 # 1)%Q - piu_zz_c2_c0_lb_coarse) * (2 # 1)%Q.

Definition piu_zz_c5_E_up : Q :=
  Qred ((piu_zz_qexp_sum 30 piu_zz_c5_x_up
         + piu_zz_qexp_tail 30 piu_zz_c5_x_up)%Q).

Definition piu_zz_c5_x_up_tight : Q :=
  ((4 # 1)%Q - piu_zz_c2_c0_lb_tight) * (2 # 1)%Q.

Definition piu_zz_c5_E_up_tight : Q :=
  Qred ((piu_zz_qexp_sum 30 piu_zz_c5_x_up_tight
         + piu_zz_qexp_tail 30 piu_zz_c5_x_up_tight)%Q).

(* coverage coarse chain (S5-22): 21852^2 * E_up <= 2^39 — this is the *)
(* Q face of sigma_ZZ <= 17 (KB41b C5 EXACT certificate). *)
Lemma piu_zz_c5_21852_sq_Eup_le_2pow39 :
  S02_CauchyComplete.QleT'
    (inject_Z 21852 * inject_Z 21852 * piu_zz_c5_E_up)%Q
    (Qpower (2 # 1)%Q 39%Z).
Proof. vm_compute. reflexivity. Qed.

(* coverage tight chain (S5-23) *)
Lemma piu_zz_c5_21852_sq_Eupt_le_2pow39 :
  S02_CauchyComplete.QleT'
    (inject_Z 21852 * inject_Z 21852 * piu_zz_c5_E_up_tight)%Q
    (Qpower (2 # 1)%Q 39%Z).
Proof. vm_compute. reflexivity. Qed.

(* real-exp bridge gap face (S03 consumer face): e^(x_up) <= E_up in   *)
(* real_le Set form. The judgment power of C5 concentrates here; the Q *)
(* lemmas above are the single-point numeric checks. *)
Definition piu_zz_c5_exp_bridge_face : Set :=
  real_le (cauchy_real_exp (real_const piu_zz_c5_x_up))
          (real_const piu_zz_c5_E_up).

(* ---- C7: N0 poly absorption account (KB41g 4-2 four-piece method,  *)
(* sister face of hcage_head/tail/all). N4 countersign slot (F1): the  *)
(* assembly constant C_asm is supplied by N4 at construction time; the *)
(* faces are Casm-indexed Set types so this unit stays axiom-free. --- *)
(* C* = 375^187 / (187 * 373^187), the beta=1 head judgment constant  *)
(* (KB41g 3-3.4: EXACT fraction; OFFSYS display 0.0145363011...). *)
Definition piu_zz_c7_Casm_bound_v187 : Q :=
  (Qpower (inject_Z 375) 187%Z
    / (inject_Z 187 * Qpower (inject_Z 373) 187%Z))%Q.

(* simple-fraction brackets of C* (S7-37/38, KB41g both sides) *)
Lemma piu_zz_c7_v187_bracket_lo :
  S02_CauchyComplete.QltT (1489765 # 102485838)%Q piu_zz_c7_Casm_bound_v187.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c7_v187_bracket_hi :
  S02_CauchyComplete.QltT piu_zz_c7_Casm_bound_v187 (6855632 # 471621491)%Q.
Proof. vm_compute. reflexivity. Qed.

(* N4 interface face: C_asm <= C* (QleT' direct form; at construction *)
(* time N4 instantiates Casm and vm_compute closes the point) *)
Definition piu_zz_c7_Casm_admissible (Casm : Q) : Set :=
  S02_CauchyComplete.QleT' Casm piu_zz_c7_Casm_bound_v187.

(* U-shape step-down: 375*(n-1) <= 373*n for 2 <= n <= 187 (S7-39;    *)
(* lia auxiliary step, KB41g 4-2(a) sanctioned form) *)
Lemma piu_zz_c7_absorb_step_dn :
  forall n : nat, (2 <= n)%nat -> (n <= 187)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z 375 * inject_Z (Z.of_nat (n - 1)))%Q
      (inject_Z 373 * inject_Z (Z.of_nat n))%Q.
Proof.
  intros n Hlo Hhi.
  apply S02_CauchyComplete.Qle_to_QleT'.
  rewrite <- (inject_Z_mult 375%Z).
  rewrite <- (inject_Z_mult 373%Z).
  rewrite <- Zle_Qle.
  lia.
Qed.

(* U-shape step-up: 373*(n+1) <= 375*n for n >= 187 (S7-40) *)
Lemma piu_zz_c7_absorb_step_up :
  forall n : nat, (187 <= n)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z 373 * inject_Z (Z.of_nat (n + 1)))%Q
      (inject_Z 375 * inject_Z (Z.of_nat n))%Q.
Proof.
  intros n Hlo.
  apply S02_CauchyComplete.Qle_to_QleT'.
  rewrite <- (inject_Z_mult 373%Z).
  rewrite <- (inject_Z_mult 375%Z).
  rewrite <- Zle_Qle.
  lia.
Qed.

(* U-shape endpoint anchors (S7-39/40 numeric faces) *)
Lemma piu_zz_c7_ushape_endpoint_dn :
  S02_CauchyComplete.QltT
    (inject_Z 375 * inject_Z 186)%Q (inject_Z 373 * inject_Z 187)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_c7_ushape_endpoint_up :
  S02_CauchyComplete.QltT
    (inject_Z 373 * inject_Z 188)%Q (inject_Z 375 * inject_Z 187)%Q.
Proof. vm_compute. reflexivity. Qed.

(* argmin 187 < N0 1348, column-constancy precondition (S7-41 face) *)
Lemma piu_zz_c7_argmin_lt_N0 :
  S02_CauchyComplete.QltT (inject_Z 187) (inject_Z 1348).
Proof. vm_compute. reflexivity. Qed.

(* head-account face (n < 1348): C_asm * n <= (375/373)^n — U-shape    *)
(* two branches + endpoint-187 single-point judgment; point-by-point  *)
(* enumeration of the 1347 candidates is forbidden (KB41g 4-4 C       *)
(* criterion). Construction (0.25-0.5 seat-day) belongs to N6'-b per  *)
(* the workorder topology. *)
Definition piu_zz_c7_absorb_head_face (Casm : Q) : Set :=
  forall n : nat, (n < 1348)%nat ->
    S02_CauchyComplete.QleT' (Casm * inject_Z (Z.of_nat n))%Q
      (Qpower (375 # 373)%Q (Z.of_nat n)).

(* tail base single point (S7-32 first-pass face): 1348*(373/2500)^1348 *)
(* <= (375/2500)^1348 (~11kbit, vm_compute) *)
Lemma piu_zz_c7_tail_base_1348 :
  S02_CauchyComplete.QleT'
    (inject_Z 1348 * Qpower (373 # 2500)%Q 1348%Z)%Q
    (Qpower (375 # 2500)%Q 1348%Z).
Proof. vm_compute. reflexivity. Qed.

(* N0 minimality: last violation at 1347 (S7-32 other half, as a       *)
(* positive strict fact): (375/2500)^1347 < 1347*(373/2500)^1347 *)
Lemma piu_zz_c7_tail_prev_violation_1347 :
  S02_CauchyComplete.QltT
    (Qpower (375 # 2500)%Q 1347%Z)
    (inject_Z 1347 * Qpower (373 # 2500)%Q 1347%Z)%Q.
Proof. vm_compute. reflexivity. Qed.

(* tail-account face (n >= 1348): n*(373/2500)^n <= (375/2500)^n —     *)
(* base vm_compute at 1348 + induction with the shared step-up lemma;  *)
(* construction belongs to N6'-b (head/tail share the step lemmas). *)
Definition piu_zz_c7_absorb_tail_face : Set :=
  forall n : nat, (1348 <= n)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.of_nat n) * Qpower (373 # 2500)%Q (Z.of_nat n))%Q
      (Qpower (375 # 2500)%Q (Z.of_nat n)).

(* all-n composition face: C_asm admissible -> C_asm*n <= (3/20)^n for *)
(* all n. Synthesis = KB41g 4-2 hcage_all (Qmult_power composition,    *)
(* ec_hval :674-678 technique). N0 four-tier table: beta=1 -> 1348     *)
(* main tier registered here; tiers beta=2/3/4 (2994/4750/6576) stay   *)
(* on the KB41g 4-4 A cross-table per the KB41o draft. *)
Definition piu_zz_c7_absorb_all_face (Casm : Q) : Set :=
  S02_CauchyComplete.QleT' Casm piu_zz_c7_Casm_bound_v187 ->
  forall n : nat,
    S02_CauchyComplete.QleT' (Casm * inject_Z (Z.of_nat n))%Q
      (Qpower (3 # 20)%Q (Z.of_nat n)).

(* ================================================================= *)
(* downstream notes (v2-r2 workorder): N6'-a consumes C4 pin-face     *)
(* lemmas (main pin + tight tier EXACT), C5 coverage lemmas + bridge  *)
(* face, C7 head/tail/all faces; C1-C3 full in-Coq chains = optional  *)
(* strengthening (KB41o tier-table two-reads, awaiting ruling).       *)
(* N6'-b consumes C7 step lemmas + endpoint anchors + head/tail/all   *)
(* faces (its B-tier three-piece sister face).                        *)
(* ================================================================= *)

Print Assumptions piu_zz_c2_sqrt3_lt_26_15.
Print Assumptions piu_zz_c2_pell_sqrt3_lt_1351_780.
Print Assumptions piu_zz_c2_exp_1312_5000_series_lb.
Print Assumptions piu_zz_c2_exp_26163_series_lb.
Print Assumptions piu_zz_c2_c0_ratio_identity.
Print Assumptions piu_zz_c2_log_mount_identity.
Print Assumptions piu_zz_c2_c0_compose_identity.
Print Assumptions piu_zz_c2_c0_lb_coarse_pos.
Print Assumptions piu_zz_c2_c0_tight_lb_gt.
Print Assumptions piu_zz_c3_P_21851_neg.
Print Assumptions piu_zz_c3_P_21852_pos.
Print Assumptions piu_zz_c3_P_174813_8_neg.
Print Assumptions piu_zz_c3_Pp_15000_pos.
Print Assumptions piu_zz_c3_P'_pos_high.
Print Assumptions piu_zz_c4_rhossq_le_9_400.
Print Assumptions piu_zz_c4_rhossq_le_373_2500_sq.
Print Assumptions piu_zz_c4_tight_sq_le_main_sq.
Print Assumptions piu_zz_c4_order_13_400_lt_149_1000.
Print Assumptions piu_zz_c4_order_149_1000_lt_373_2500.
Print Assumptions piu_zz_c4_order_373_2500_lt_3_20.
Print Assumptions piu_zz_c4_order_3_20_lt_2_13.
Print Assumptions piu_zz_c4_order_2_13_lt_1_6.
Print Assumptions piu_zz_c4_slack_identity.
Print Assumptions piu_zz_c5_21852_sq_Eup_le_2pow39.
Print Assumptions piu_zz_c5_21852_sq_Eupt_le_2pow39.
Print Assumptions piu_zz_c7_v187_bracket_lo.
Print Assumptions piu_zz_c7_v187_bracket_hi.
Print Assumptions piu_zz_c7_absorb_step_dn.
Print Assumptions piu_zz_c7_absorb_step_up.
Print Assumptions piu_zz_c7_ushape_endpoint_dn.
Print Assumptions piu_zz_c7_ushape_endpoint_up.
Print Assumptions piu_zz_c7_argmin_lt_N0.
Print Assumptions piu_zz_c7_tail_base_1348.
Print Assumptions piu_zz_c7_tail_prev_violation_1347.
