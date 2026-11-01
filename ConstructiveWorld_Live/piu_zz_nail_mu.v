(* ========================================================================= *)
(* Mission      : N6'-a main-nail registration and mu-conversion face for    *)
(*                the gammaP1 ZZ wave, (D) case: the main cage nail         *)
(*                rho = (3/20)^n (sigma = 17, E = 7, N0 = 1348; tight tier  *)
(*                373/2500 = B+ option; dead nail 13/400 = negative         *)
(*                control) and mu(sigma,rho) = 1 + sigma*ln2/ln(1/rho) with *)
(*                ln2/ln(20/3) as explicit rational bracket parameters      *)
(*                (honest interface); the KB41d C6 cross-check as exact Q   *)
(*                comparisons: mu(17,3/20) bracket >= mu_ZZ, bracket < 8    *)
(*                (slot-8), dead nail mu <= 7 < mu_ZZ; wave sample points   *)
(*                re-cast as vm_compute faces.                              *)
(* Dependencies : S02_CauchyComplete (QleT'/QeqT, qeq bridges),             *)
(*                piu_mu_criterion (piu_mu_and2), piu_zz_constants (zzQltT/ *)
(*                zzQleT/zzQeqT, mu_ZZ/ln2 constants); Stdlib QArith,       *)
(*                ZArith, Arith, Lqa, Qpower.                               *)
(* References   : KB41b/KB41d/KB41g/KB41h receipts (C1-C7 EXACT chain; C6   *)
(*                cross-check; head constant C(1); E=7 double-power);       *)
(*                KB41k receipt (its H12 ln-bracket helper computes         *)
(*                2*arctan, not 2*artanh; re-certified here); GEDAN-        *)
(*                gammaP1v2 work order v2-r2 (node N6'-a); Zeilberger-      *)
(*                Zudilin, Moscow J. Comb. Number Theory 9 (2020) 407-419.  *)
(* Constructivity: all statements Set-carried (zzQltT/zzQleT/zzQeqT,        *)
(*                QleT'/QeqT, sigT/piu_mu_and2); zero new Prop face; proofs *)
(*                are vm_compute on closed rationals; brackets machine-     *)
(*                certified exact (kb46_oracle.py v4, 44/44 PASS); real-    *)
(*                layer ln bridges are annotations; consumers N6'-b and N5. *)
(* Build        : coqc -native-compiler no -noglob -q                       *)
(*                -Q <certified vo tree> "" -Q <this dir> ""                *)
(*                piu_zz_nail_mu.v (Rocq 9.1.0, cpu_guard v3 wrap).         *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_constants.

Open Scope Q_scope.

(* ==== Section 1. Main-nail registration face ((D) case, KB41b 4.4) ==== *)

(* The main nail: cage bound (3/20)^n.  The old dead nail 13/400 and the
   tight tier 373/2500 are registered alongside: the tight tier is the
   documented B+ option (KB41b 4.4-2), the dead nail is the negative
   control of the sigma=12 era (Fork A, EXACT death four-fold). *)
Definition piu_zz_nail_rho : Q := (3 # 20)%Q.
Definition piu_zz_nail_rho_tight : Q := (373 # 2500)%Q.
Definition piu_zz_nail_rho_dead : Q := (13 # 400)%Q.
Definition piu_zz_nail_sigma : nat := 17%nat.
Definition piu_zz_nail_E : nat := 7%nat.
Definition piu_zz_nail_N0 : nat := 1348%nat.
Definition piu_zz_nail_argmin : nat := 187%nat.

(* Head-section constant of KB41g (beta=1 EXACT): C(1) = 375^187/(187*373^187).
   (# takes a positive literal denominator, so the ratio is carried as the
   division of two literal-denominator Q values; equal as rationals.) *)
Definition piu_zz_nail_C1 : Q :=
  ((375 ^ 187)%Z # 1)%Q / ((187 * 373 ^ 187)%Z # 1)%Q.

(* Exact rational order of the nail candidates (KB41b 4.2 chain, EXACT):
   13/400 < 149/1000 < 373/2500 < 3/20 < 2/13 < 1/6. *)
Lemma piu_zz_nail_order_dead_edge :
  zzQltT piu_zz_nail_rho_dead (149 # 1000)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_order_edge_tight :
  zzQltT (149 # 1000)%Q piu_zz_nail_rho_tight.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_order_tight_main :
  zzQltT piu_zz_nail_rho_tight piu_zz_nail_rho.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_order_main_fallback :
  zzQltT piu_zz_nail_rho (2 # 13)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_order_fallback_wide :
  zzQltT (2 # 13)%Q (1 # 6)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_le_half : zzQleT piu_zz_nail_rho (1 # 2)%Q.
Proof. vm_compute. exact tt. Qed.

(* C4 admissibility slot (KB41b C4 rough chain): the certificate bounds
   rho_ZZ^2 <= 2230690/10^8 machine-side; the nail slot needs only the
   exact Q step 0.02230690 < (3/20)^2 = 9/400. *)
Lemma piu_zz_nail_C4_slot :
  zzQltT (2230690 # 100000000)%Q ((9 # 400)%Q).
Proof. vm_compute. exact tt. Qed.

(* ==== Section 2. Dead-nail certificate face (13/400, base-free) ==== *)

(* KB41b base-2 reading of the death sentence: 13/400 < 2^(-2.43) as the
   pure integer power comparison 2^243 * 13^100 < 400^100. *)
Lemma piu_zz_nail_dead_base2 :
  zzQltT ((2 ^ 243 * 13 ^ 100)%Z # 1)%Q ((400 ^ 100)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Death mu-face at integer grain M=6: rho^6 * 2^17 <= 1 is the exact
   rational form of mu(17, rho) <= 7 (real-layer reading: 17*ln2/ln(1/rho)
   <= 6; ln monotonicity annotation, not proven in Q face). *)
Lemma piu_zz_nail_dead_mu7 :
  zzQltT ((13 ^ 6 * 2 ^ 17)%Z # 1)%Q ((400 ^ 6)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Separation: 7 < mu_ZZ (tree constant piu_zzc_mu_zz_lower = 7.103205334137). *)
Lemma piu_zz_nail_dead_separation :
  zzQltT (7 # 1)%Q piu_zzc_mu_zz_lower.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 3. E=7 criterion face and the q=1 escape anchor ==== *)

(* KB41h EXACT double-power criterion for E = ceil(17*ln2/ln(20/3)) = 7:
   sufficiency 2^17*3^7 < 20^7 and minimality 2^17*3^6 > 20^6. *)
Lemma piu_zz_nail_E7_sufficient :
  zzQltT ((2 ^ 17 * 3 ^ 7)%Z # 1)%Q ((20 ^ 7)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_E7_minimal :
  zzQltT ((20 ^ 6)%Z # 1)%Q ((2 ^ 17 * 3 ^ 6)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Window slope order 5/13 < 7/17 (KB41h slope band). *)
Lemma piu_zz_nail_slope_order : zzQltT (5 # 13)%Q (7 # 17)%Q.
Proof. vm_compute. exact tt. Qed.

(* Shared-constant anchors kept invariant by the (D) case:
   kappa = 2^14*3^7 = 35831808 and c0 = 1/71663616 (2^8*6^7). *)
Lemma piu_zz_nail_kappa_decomp :
  S02_CauchyComplete.QeqT ((2 ^ 14 * 3 ^ 7)%Z # 1)%Q (35831808 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma piu_zz_nail_c0_denom :
  S02_CauchyComplete.QeqT ((2 ^ 8 * 6 ^ 7)%Z # 1)%Q (71663616 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* q=1 escape anchor as a Set-carried existential: the witness index n=1
   satisfies both (D) window limbs (limb-1 form 2q*3^n <= 20^n at q=1;
   limb-3 anchor 2^17 <= kappa). *)
Definition piu_zz_nail_esc_q1 : Set :=
  sigT (fun n : nat =>
    piu_mu_and2
      (zzQleT ((2 * 3 ^ Z.of_nat n)%Z # 1)%Q ((20 ^ Z.of_nat n)%Z # 1)%Q)
      (zzQleT ((2 ^ 17)%Z # 1)%Q (35831808 # 1)%Q)).

Example piu_zz_nail_esc_q1_witness : piu_zz_nail_esc_q1.
Proof.
  exists 1%nat.
  apply piu_mu_and2_i; vm_compute; exact tt.
Qed.

(* ==== Section 4. Machine-sample face (KB41h core-step1 chain, witnesses) ==== *)

(* Core step-1 chain of the (D) case at the 7 KB41h sample points (n,q):
   the integer form 2q*3^n <= 20^n of the premise-conclusion link
   q*(3/20)^n <= 1/2  =>  2q*(3/20)^n <= 1. *)
Lemma piu_zz_nail_step1_n1_q1 :
  zzQleT ((2 * 1 * 3 ^ 1)%Z # 1)%Q ((20 ^ 1)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n2_q3 :
  zzQleT ((2 * 3 * 3 ^ 2)%Z # 1)%Q ((20 ^ 2)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n3_q5 :
  zzQleT ((2 * 5 * 3 ^ 3)%Z # 1)%Q ((20 ^ 3)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n5_q22 :
  zzQleT ((2 * 22 * 3 ^ 5)%Z # 1)%Q ((20 ^ 5)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n8_q300 :
  zzQleT ((2 * 300 * 3 ^ 8)%Z # 1)%Q ((20 ^ 8)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n10_q2000 :
  zzQleT ((2 * 2000 * 3 ^ 10)%Z # 1)%Q ((20 ^ 10)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_step1_n12_q10000 :
  zzQleT ((2 * 10000 * 3 ^ 12)%Z # 1)%Q ((20 ^ 12)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Witness anchors (KB41h/KB41j): (20/3)^2 >= 2^5, (20/3)^3 > 2^8,
   slope lower edge (20/3)^5 > 2^13. *)
Lemma piu_zz_nail_witness_a2 :
  zzQleT ((9 * 32)%Z # 1)%Q (400 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_witness_a3 :
  zzQltT ((27 * 256)%Z # 1)%Q (8000 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_witness_slope :
  zzQltT ((2 ^ 13 * 3 ^ 5)%Z # 1)%Q ((20 ^ 5)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Hcoef relaxation sample (sigma 12 -> 17 is a loosening): the tree sample
   |A_{1,0}| = 2392 (piu_zz_kernel_sum.v:1072) fits 2^17 with slack. *)
Lemma piu_zz_nail_hcoef_sample : zzQleT (2392 # 1)%Q ((2 ^ 17)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 5. C2/C3/C5 certificate anchor face (KB41b 4.3) ==== *)

(* C2 anchors: sqrt3 bounds are pure integer (coarse 26/15, fine Pell
   1351/780); the log bound 3*sqrt3/4 < 13/10 squares to 2700 < 2704. *)
Lemma piu_zz_nail_C2_sqrt3_coarse :
  zzQltT ((3 * 15 * 15)%Z # 1)%Q ((26 * 26)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_C2_sqrt3_pell :
  zzQltT ((3 * 780 * 780)%Z # 1)%Q ((1351 * 1351)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_C2_log_anchor : zzQltT (2700 # 1)%Q (2704 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* C2 rough Q chain: pi/(2*sqrt3) > 4995/5512 and log(3*sqrt3/4) < 1312/5000
   (the two transcendental anchors are machine-certified; the derived Q
   chain c >= 4995/5512 - 1312/5000 = 2217907/3445000 >= 643804/10^6 is
   exact and checked here). *)
Lemma piu_zz_nail_C2_rough_chain :
  S02_CauchyComplete.QeqT
    (((4995 # 5512)%Q - (1312 # 5000)%Q)%Q) (2217907 # 3445000)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma piu_zz_nail_C2_rough_lb :
  zzQleT (643804 # 1000000)%Q (2217907 # 3445000)%Q.
Proof. vm_compute. exact tt. Qed.

(* C3 (ZZ2020 Prop 2, eq (18)): P(N) = 108N^3 - 2359989N^2 + 138304N - 2048.
   Exact values at the bracketing integers pin the sign of P and the
   eighth-grid refinement 8^3 * P(174813/8) = -1753086647500 < 0
   (scaled polynomial registered alongside). *)
Definition piu_zz_nail_P3 (N : Z) : Z :=
  108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048%Z.

Definition piu_zz_nail_P3_scaled (N : Z) : Z :=
  108 * N ^ 3 - 8 * 2359989 * N ^ 2 + 64 * 138304 * N - 512 * 2048%Z.

Lemma piu_zz_nail_C3_P_lo :
  zzZeqT (piu_zz_nail_P3 21851) (-35652683625)%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_C3_P_hi :
  zzZeqT (piu_zz_nail_P3 21852) 15914984368%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_C3_P_eighth :
  zzZeqT (piu_zz_nail_P3_scaled 174813) (-1753086647500)%Z.
Proof. vm_compute. exact tt. Qed.

(* C5 anchor (sigma_ZZ <= 17): with N3 < 21852 (C3) and the machine
   e-series bound e^(2(4-c)) < 821 for c >= c_fine (Section 7 chain), the
   C5 inequality N3^2 * e^(2(4-c)) <= 2^39 reduces to the exact integer
   anchor 21852^2 * 821 <= 2^39 (margin 41 percent). *)
Lemma piu_zz_nail_C5_anchor :
  zzQleT ((21852 * 21852 * 821)%Z # 1)%Q ((2 ^ 39)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 6. C7/C1 head-section anchor face (KB41b C7, KB41g 3.1) ==== *)

(* C7 base point at N0 = 1348: 375^1348 >= 1348 * 373^1348 (11.5 kbit
   integer comparison; the full persistence account is N6'-b scope). *)
Lemma piu_zz_nail_C7_base :
  S02_CauchyComplete.QleT'
    ((1348 * 373 ^ 1348)%Z # 1)%Q ((375 ^ 1348)%Z # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* U-form bottom facts at argmin = 187: step-down 2*187 < 375 and
   step-up 373 < 2*187 (the lia-level seeds of the N6'-b head account). *)
Lemma piu_zz_nail_uform_down : zzQltT ((2 * 187)%Z # 1)%Q (375 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_uform_up : zzQltT (373 # 1)%Q ((2 * 187)%Z # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* C1 simple-fraction brackets (KB41g 3.4, EXACT convergents):
   1489765/102485838 < C(1) < 6855632/471621491. *)
Lemma piu_zz_nail_C1_bracket_lo :
  zzQltT (1489765 # 102485838)%Q piu_zz_nail_C1.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_C1_bracket_hi :
  zzQltT piu_zz_nail_C1 (6855632 # 471621491)%Q.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 7. mu-conversion cross-check face (KB41d C6) ==== *)

(* Honest interface: the conversion closed form mu(sigma,rho) =
   1 + sigma*ln2/ln(1/rho) takes ln2 and ln(1/rho) as explicit rational
   parameters (KB41d N6'-a row prescription).  No transcendental axiom. *)
Definition piu_zz_mu_cv (sigma : nat) (l2 lr : Q) : Q :=
  (1 # 1) + (Z.of_nat sigma # 1) * l2 / lr.

(* ln brackets, artanh series (all-positive terms) truncated at K=60 with
   an exact geometric tail bound: lo = 2*S_K, hi = lo + 2*z^(2K+3)/((2K+3)*(1-z^2)).
   Machine certificate: kb46_oracle.py v4 (Fraction-exact, 44/44 PASS).
   F1 fail-loud note: the kb41k_bank.py ln_bracket helper alternates series
   signs, which computes 2*arctan(z), NOT 2*artanh(z) - its H12 check passed
   vacuously on wrong values (17*2arctan(1/3)/2arctan(17/23) = 8.59);
   the H12 CONCLUSION is true and is re-certified here with the correct
   brackets (lemma piu_zz_nail_mu_E_ratio_lb below). *)
Definition piu_zz_nail_ln2_lo : Q := (7579350791922908493211057720610935844929417729631468282727247283553005448697049725177482185862013652346538 # 10934691800665017651093398878137532543940088361345495128670626547893838341287369225778453049716853631425575)%Q.
Definition piu_zz_nail_ln2_hi : Q := (90952209503074901918532692647331230139153012755577619392727016873656539208669468392798169337295626880005981 # 131216301607980211813120786537650390527281060336145941544047518574726060095448430709341436596602243577106900)%Q.
Definition piu_zz_nail_ln203_lo : Q := (468388198810532797116794638986615133875089744614040224324564231491421426663176418880638391007631807217186599379233422046303443981075715569507817530176535208026355870368824587625854866767565398841839169408517461542 # 246894346452582470204848189329526897452191806123893418102074649495500967958462814151547193870713534923591558456843081919723880517351844729551389941148919282973948220638189155493262182520187789270176611529691265325)%Q.
Definition piu_zz_nail_ln203_hi : Q := (3747105590484262381977066566766265974049774764008186521634777655456379382369524482996618990339999972494991279692433188510149956943410917398854707128155755672506281939794038967443403049117219015500700119633332176271 # 1975154771620659761638785514636215179617534448991147344816597195964007743667702513212377550965708279388732467654744655357791044138814757836411119529191354263791585765105513243946097460161502314161412892237530122600)%Q.

(* Bracket quality: widths below 10^-12 (actual 3.8e-61 and 2.6e-18). *)
Lemma piu_zz_nail_ln2_width :
  zzQltT (piu_zz_nail_ln2_hi - piu_zz_nail_ln2_lo)%Q (1 # 1000000000000)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_ln203_width :
  zzQltT (piu_zz_nail_ln203_hi - piu_zz_nail_ln203_lo)%Q (1 # 1000000000000)%Q.
Proof. vm_compute. exact tt. Qed.

(* Tree-constant consistency band (1e-15 tolerance, piu_zz_constants style):
   piu_zzc_ln2 = 0.6931471805599453 is the 16-digit truncation of ln2 and
   sits 9.4e-18 below the true value, i.e. just below the bracket lip. *)
Lemma piu_zz_nail_ln2_tree_band_lo :
  zzQltT (piu_zz_nail_ln2_lo - (1 # 1000000000000000))%Q piu_zzc_ln2.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_nail_ln2_tree_band_hi :
  zzQltT piu_zzc_ln2 (piu_zz_nail_ln2_hi + (1 # 1000000000000000))%Q.
Proof. vm_compute. exact tt. Qed.

(* THE cross-check (KB41d C6): mu(17,3/20) >= mu_ZZ, carried as
   piu_zzc_mu_zz_upper = 7.103205334138 < the lower mu bracket
   1 + 17*ln2_lo/ln203_hi = 7.21125820369... (real slack 0.108). *)
Definition piu_zz_mu_D_lower : Q :=
  piu_zz_mu_cv 17 piu_zz_nail_ln2_lo piu_zz_nail_ln203_hi.
Definition piu_zz_mu_D_upper : Q :=
  piu_zz_mu_cv 17 piu_zz_nail_ln2_hi piu_zz_nail_ln203_lo.

Lemma piu_zz_mu_D_ge_muzz : zzQltT piu_zzc_mu_zz_upper piu_zz_mu_D_lower.
Proof. vm_compute. exact tt. Qed.

(* Slot-8 compatibility, strict: the upper mu bracket stays below 8
   (equivalent real-layer reading: 17*ln2 < 7*ln(20/3), the E=7 face). *)
Lemma piu_zz_mu_D_lt_slot8 : zzQltT piu_zz_mu_D_upper (8 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* OFFSYS display pin (KB41d C6 / KB41h / KB41b CP20, 12-digit display
   7.211258203696...): the mu bracket pins the true rate inside a 1e-12
   window around the display point. *)
Lemma piu_zz_mu_D_band_lo :
  zzQltT piu_zz_mu_D_lower (7211258203697 # 1000000000000)%Q.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zz_mu_D_band_hi :
  zzQltT (7211258203696 # 1000000000000)%Q piu_zz_mu_D_upper.
Proof. vm_compute. exact tt. Qed.

(* H12 re-certification with correct brackets: 17*ln2_lo/ln203_hi exceeds
   the 29-digit truncation of mu_ZZ - 1 (610320533413700172750577342281/10^29). *)
Lemma piu_zz_nail_mu_E_ratio_lb :
  zzQltT (610320533413700172750577342281 # 100000000000000000000000000000)%Q
         (((17 # 1) * piu_zz_nail_ln2_lo / piu_zz_nail_ln203_hi)%Q).
Proof. vm_compute. exact tt. Qed.

(* C5 fine-chain registration: c_fine = pi/(2*sqrt3) - log(3*sqrt3/4)
   bracketed below by 480949442879/745346700000 (fine anchors pi > 103993/33102
   Machin, sqrt3 < 1351/780 Pell, log(3*sqrt3/4) <= 26163/100000 e-series;
   the three transcendental anchors are machine-certified in kb46_oracle v4). *)
Definition piu_zz_nail_c_fine_lb : Q := (480949442879 # 745346700000)%Q.

Lemma piu_zz_nail_c_fine_lb_pos : zzQltT (0 # 1)%Q piu_zz_nail_c_fine_lb.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 8. Assumption audit ==== *)

Print Assumptions piu_zz_nail_order_tight_main.
Print Assumptions piu_zz_nail_dead_base2.
Print Assumptions piu_zz_nail_E7_sufficient.
Print Assumptions piu_zz_nail_esc_q1_witness.
Print Assumptions piu_zz_nail_step1_n12_q10000.
Print Assumptions piu_zz_nail_C7_base.
Print Assumptions piu_zz_nail_C1_bracket_hi.
Print Assumptions piu_zz_mu_D_ge_muzz.
Print Assumptions piu_zz_mu_D_lt_slot8.
Print Assumptions piu_zz_nail_mu_E_ratio_lb.
