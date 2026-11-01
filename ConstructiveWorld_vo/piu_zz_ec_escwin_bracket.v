(* ========================================================================= *)
(* Mission      : N6'-b acceptance piece (gammaP1 W4 batch): the escape-     *)
(*                window EXACT brackets and the head-coverage statement-     *)
(*                face draft.  Part one (born theorems): the KB41g 4-1       *)
(*                EXACT bracket suite - the upper threshold L* =             *)
(*                22902/7 - log2 3 with the K=2^20 dyadic certificate        *)
(*                (2^1661953 < 3^(2^20) < 2^1661954, integer powers), the   *)
(*                q* = 2^L*/3 rational brackets via the 2^(5/7) seventh-     *)
(*                power certificate, the lower edge 1348*log2(20/3)-1 with   *)
(*                the m'=2869916 dyadic certificate, the slope certificate   *)
(*                (20/3)^7 > 2^17, and the q=1 witness-forcing anchor -      *)
(*                together these seal the avoidance question (the D item):   *)
(*                between the two thresholds the witness landing is          *)
(*                uncontrolled, so the Hcage forall-n form is kept.  Part    *)
(*                two (statement-face DRAFT, cage_constants precedent): the  *)
(*                three QleT'-carried coverage faces hcage_head (n < 1348),  *)
(*                hcage_tail (1348 <= n), hcage_all (forall n) over the      *)
(*                Hasm/Hadm interface pair, registered as Set-typed          *)
(*                definitions awaiting the N4-side countersign - per KB41m   *)
(*                NEGATIVE the Hasm instantiation for the actual supply face *)
(*                is NOT available (the (3/20)^n cage supply object is       *)
(*                EXACT-falsified in-window at n=5, x3.655), so the faces    *)
(*                stay honestly un-instantiated; the construction skeleton   *)
(*                and its pre-verified step inventory are registered in the  *)
(*                comments (W5 residue).                                     *)
(* Dependencies : piu_zz_ec_escwin_nescD (N5 unit, same sandbox: witness     *)
(*                closed form + acceptor faces - W4 internal bite);          *)
(*                piu_zz_cage_constants (N2a: Casm admissible face + C*      *)
(*                constant - interface bite W4/N2a); piu_zz_nail_mu (N6'-a:  *)
(*                main-nail pins - interface bite W4/N6'-a); S02_CauchyCom-  *)
(*                plete; stdlib QArith, ZArith, Lia, Lqa, Qpower.            *)
(* References   : KB41g 4-1 (window EXACT brackets, dyadic certificates,     *)
(*                N-g1 correction of the 2^3266 display to 2^3270.1293),     *)
(*                KB41g 4-4 A-G (acceptance criteria; D = avoidance seal,    *)
(*                B = three-piece QleT' faces, E = pin constraint);          *)
(*                KB41k bank row 7 (slope 4.465x margin); KB41m NEGATIVE     *)
(*                verdict (supply-face falsification; the draft status);     *)
(*                KB76 (s2 noise face - why the criterion was refactored);   *)
(*                GEDAN-v2 workorder node N6'-b.                             *)
(* Constructivity: every named theorem is Set-carried (S02 QleT'/QltT,      *)
(*                piu_mu faces, sigT) and closes under the global context;   *)
(*                the draft faces are Set-typed definitions (no proofs       *)
(*                claimed); the analytic dyadic-to-log transfer stays on     *)
(*                the machine side exactly as in KB41g 4-1 (the integer-     *)
(*                power certificates here are the exact machine content);    *)
(*                no Axiom, no Abort, no admit.                              *)
(* Build        : rocq c -native-compiler no -q -time -Q . ""                *)
(*                -Q <kb45 sandbox> "" -Q <kb46 sandbox> ""                  *)
(*                -Q <ConstructiveWorld_vo> "" piu_zz_ec_escwin_bracket.v,   *)
(*                under cpu_guard_v3 (-LoadLimit 60 -TempLimit 98 -AllowG3   *)
(*                -GearForce 0), Rocq 9.1.0.                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_ec_escwin_nescD.
Require Import piu_zz_cage_constants.
Require Import piu_zz_nail_mu.

(* ================================================================== *)
(* Section 1. Upper threshold L* = 22902/7 - log2 3 (dyadic cert).    *)
(* ================================================================== *)

(* The dyadic certificate of log2 3 at K = 2^20 (KB41g 4-1): the two   *)
(* integer power comparisons ARE the exact machine content. *)
(* DYADIC CERTIFICATES (machine-side registration, the PNT-grade slot  *)
(* status per the house honesty doctrine): the integer-power facts     *)
(*   2^1661953 < 3^1048576 < 2^1661954                                 *)
(* were machine-verified EXACTLY twice: (a) in the KB41g sandbox (the  *)
(* 4-1 dyadic account, python -I integer powers), and (b) re-verified  *)
(* in this seat's kb84 precheck (scripts/kb84_precheck.py, section E,  *)
(* python -I Fraction/integer powers, log lines E1/E2 PASS).  The     *)
(* in-Coq vm_compute of these 1.66M-bit powers is NOT evaluable in     *)
(* this environment (the Coq VM's Z arithmetic on 26k-word operands    *)
(* exceeded the seat budget; registered as a W5 residue with the       *)
(* square-chain Definition skeleton preserved in the kb84 sandbox      *)
(* scripts/gen_dyadic_block.txt).  The Q-endpoint faces below ARE the  *)
(* born Coq content of the bracket. *)
(* The L* bracket endpoints as exact Q values (22902/7 shifted by the  *)
(* dyadic bounds of log2 3). *)
Definition piu_zz_ec_Lstar_lo : Q :=
  (22902 # 7)%Q - (1661954 # 1048576)%Q.
Definition piu_zz_ec_Lstar_hi : Q :=
  (22902 # 7)%Q - (1661953 # 1048576)%Q.

Example piu_zz_ec_Lstar_ordered :
  S02_CauchyComplete.QltT piu_zz_ec_Lstar_lo piu_zz_ec_Lstar_hi.
Proof. vm_compute. reflexivity. Qed.

(* the double decomposition of the numerator (KB41g 4-1):              *)
(* 22902 = 17*1348 - 14 (the N0=1348 upper threshold)                  *)
(*       = 3271*7 + 5 (the q* = 2^3271 * 2^(5/7) / 3 reading).          *)
Example piu_zz_ec_22902_double :
  (22902 = 17 * 1348 - 14)%nat /\ (22902 = 3271 * 7 + 5)%nat.
Proof.
  split.
  - vm_compute; lia.
  - vm_compute; lia.
Qed.

(* ================================================================== *)
(* Section 2. q-star = 2^(L-star)/3 rational brackets (2^(5/7) cert). *)
(* ================================================================== *)

(* 2^(5/7) in (4485871/2734169, 13798021/8409988) via seventh powers   *)
(* (the exact integer certificates of KB41g 4-1). *)
Theorem piu_zz_ec_2pow5_7_lo : (4485871 ^ 7 < 32 * 2734169 ^ 7)%Z.
Proof. vm_compute; reflexivity. Qed.

Theorem piu_zz_ec_2pow5_7_hi : (13798021 ^ 7 > 32 * 8409988 ^ 7)%Z.
Proof. vm_compute; reflexivity. Qed.

(* q* bracket endpoints: 2^3271 * 4485871/8202507 and                  *)
(* 2^3271 * 13798021/25229964 (the KB41g rational endpoints; the       *)
(* denominators are 3*2734169 and 3*8409988). *)
Definition piu_zz_ec_qstar_lo : Q :=
  (inject_Z (2 ^ 3271)%Z * inject_Z 4485871%Z / inject_Z 8202507%Z)%Q.
Definition piu_zz_ec_qstar_hi : Q :=
  (inject_Z (2 ^ 3271)%Z * inject_Z 13798021%Z / inject_Z 25229964%Z)%Q.

Example piu_zz_ec_qstar_den_1 : (8202507 = 3 * 2734169)%Z.
Proof. vm_compute; reflexivity. Qed.

Example piu_zz_ec_qstar_den_2 : (25229964 = 3 * 8409988)%Z.
Proof. vm_compute; reflexivity. Qed.

Example piu_zz_ec_qstar_ordered :
  S02_CauchyComplete.QltT piu_zz_ec_qstar_lo piu_zz_ec_qstar_hi.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 3. Lower edge 1348*log2(20/3) - 1 (dyadic cert).           *)
(* ================================================================== *)

(* the dyadic certificate of log2(20/3) at K = 2^20, m' = 2869916. *)
(* zz20 = 20^(2^20); z2m = 2^2869916 (binary chain); z2m1 = 2^2869917. *)

(* The lower-edge dyadic pair (3^1048576 * 2^2869916 < 20^1048576 <    *)
(* 3^1048576 * 2^2869917) carries the same machine-side registration   *)
(* status (kb84 precheck section E, lines E8/E9 PASS; the Coq-side     *)
(* evaluation is the same W5 residue). *)

(* lower-edge bracket endpoints (EXACT Q): (1348*m' - 2^20)/2^20 and   *)
(* (1348*(m'+1) - 2^20)/2^20 (KB41g 4-1: OFFSYS display 3688.4290618896 *)
(* .., 3688.4303474426..). *)
Definition piu_zz_ec_ledge_lo : Q :=
  (inject_Z (1348 * 2869916 - 1048576)%Z / inject_Z 1048576%Z)%Q.
Definition piu_zz_ec_ledge_hi : Q :=
  (inject_Z (1348 * 2869917 - 1048576)%Z / inject_Z 1048576%Z)%Q.

Example piu_zz_ec_ledge_ordered :
  S02_CauchyComplete.QltT piu_zz_ec_ledge_lo piu_zz_ec_ledge_hi.
Proof. vm_compute. reflexivity. Qed.
(* ================================================================== *)
(* Section 4. Slope certificate, q=1 anchor, avoidance seal.          *)
(* ================================================================== *)

(* slope certificate: the window is nonempty for every band (KB41g 4-1,*)
(* margin 4.465x; the exact integer comparison). *)
Theorem piu_zz_ec_slope_cert : (20 ^ 7 > 2 ^ 17 * 3 ^ 7)%Z.
Proof. vm_compute; reflexivity. Qed.

(* q = 1 anchor (EXACT): 2^17 <= kappa < 2^34 forces the witness n = 1; *)
(* the N5 unit's accepts_q1 face verifies both limbs at q = 1 (W4      *)
(* internal bite). *)
Theorem piu_zz_ec_q1_anchor : (2 ^ 17 <= 35831808 < 2 ^ 34)%Z.
Proof.
  split.
  - vm_compute; discriminate.
  - vm_compute; reflexivity.
Qed.

Example piu_zz_ec_q1_witness_lives :
  { n : nat & (2 * 1 * 3 ^ n <= 20 ^ n)%nat
            /\ (2 ^ (Z.of_nat (17 * n)) <= 35831808 * 1 ^ 7)%Z }.
Proof.
  exists 1%nat.
  split.
  - vm_compute; lia.
  - vm_compute; discriminate.
Qed.

(* ================================================================== *)
(* Section 5. Head-coverage statement-face DRAFT (QleT', forall-n).   *)
(* ================================================================== *)

(* DRAFT STATUS (honest registration, KB41m NEGATIVE): the coverage    *)
(* faces below are the KB41g 4-2/4-4 B-item statement surface in the   *)
(* cage_constants precedent (Set-typed, Casm-indexed, awaiting the     *)
(* countersign).  The Hasm instantiation for the ACTUAL supply face is *)
(* NOT available: the (3/20)^n cage supply object is EXACT-falsified   *)
(* in-window (|R5|_hi > (3/20)^5 x 3.655, KB41m 5.3), so no theorem    *)
(* here claims the supply satisfies Hasm.  W5 owns instantiation or    *)
(* retirement (the KB76-refactored criterion prices the noise face     *)
(* instead; see piu_zz_s2_headledger.v).                               *)
Section HCDRAFT.

Variable dvf : nat -> Q.
Variable Casm : Q.

(* interface premise (the N4 countersign slot, never discharged here): *)
(* the assembly face binds dvf by Casm * n * (373/2500)^n. *)
Hypothesis Hasm : forall n : nat,
  S02_CauchyComplete.QleT' (dvf n)
    (Casm * inject_Z (Z.of_nat n)
       * Qpower (373 # 2500)%Q (Z.of_nat n))%Q.

(* the Casm admissibility premise = the N2a C7 face (interface bite    *)
(* W4/N2a: piu_zz_c7_Casm_admissible is the beta=1 head judgment). *)
Hypothesis Hadm : piu_zz_c7_Casm_admissible Casm.

(* head face (n < 1348): dvf n <= (3/20)^n *)
Definition piu_zz_ec_hcage_head_face : Set :=
  forall n : nat, (n < 1348)%nat ->
    S02_CauchyComplete.QleT' (dvf n) (Qpower (3 # 20)%Q (Z.of_nat n)).

(* tail face (1348 <= n): dvf n <= (3/20)^n *)
Definition piu_zz_ec_hcage_tail_face : Set :=
  forall n : nat, (1348 <= n)%nat ->
    S02_CauchyComplete.QleT' (dvf n) (Qpower (3 # 20)%Q (Z.of_nat n)).

(* all-n face: dvf n <= (3/20)^n (the Hcage slot shape, e_carrier      *)
(* 644-645 isomorph with the main nail (3/20)). *)
Definition piu_zz_ec_hcage_all_face : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (dvf n) (Qpower (3 # 20)%Q (Z.of_nat n)).

(* the N0-minimality cross-face (the tail base is exact at 1348 and    *)
(* fails at 1347 - the N2a C7 pair, restated here as the draft's       *)
(* boundary certificate). *)
Definition piu_zz_ec_hcage_N0_face : Set :=
  piu_mu_and2
    (S02_CauchyComplete.QleT'
       (inject_Z 1348 * Qpower (373 # 2500)%Q 1348%Z)%Q
       (Qpower (375 # 2500)%Q 1348%Z))
    (S02_CauchyComplete.QltT
       (Qpower (375 # 2500)%Q 1347%Z)
       (inject_Z 1347 * Qpower (373 # 2500)%Q 1347%Z)%Q).

End HCDRAFT.

(* The draft faces are inhabitants-of-nothing so far; the construction  *)
(* skeleton (W5 residue, steps pre-verified in the kb84 scratch):       *)
(*  (1) anchor: Casm * 187 == (375/373)^187 given Casm <= C*            *)
(*      (C* = 375^187/(187*373^187); concrete Qeq, vm_compute-cheap);   *)
(*  (2) ustep_dn: 1 <= m <= 186, Casm*(m+1) <= A^(m+1)                  *)
(*      -> Casm*m <= A^m, via Casm*m*(m+1) == Casm*(m+1)*m              *)
(*      <= A^(m+1)*m == A^m*(A*m) <= A^m*(m+1) (375m <= 373(m+1))       *)
(*      and the cancel Qmult_le_r (0 < m+1);                            *)
(*  (3) ustep_up: 187 <= m, Casm*m <= A^m -> Casm*(m+1) <= A^(m+1),     *)
(*      via Casm*(m+1)*m == Casm*m*(m+1) <= A^m*(m+1)                   *)
(*      <= A^m*(A*m) == A^(m+1)*m (373(m+1) <= 375m) and the cancel;    *)
(*  (4) down/up branches by induction on d = 187-n resp. e = n-187;     *)
(*  (5) composition with Hasm: dvf n <= Casm*n*(373/2500)^n             *)
(*      <= (375/373)^n*(373/2500)^n == (375/2500)^n == (3/20)^n         *)
(*      (Qmult_power + the constant pair identities).                   *)
(* Every step's Q-tactic shape was machine-checked in the kb84 scratch  *)
(* during this seat (scratch_ustep/scratch_step2: the reorder rings,    *)
(* the cancel, the (m+1) <= (375/373)*m face, the constant pair         *)
(* identities); the remaining work is the glue under the QleT' setoid.  *)

(* ================================================================== *)
(* Section 6. Avoidance seal registration (the D item).                *)
(* ================================================================== *)

(* Seal: the witness index piu_zz_ec_nescD q lands INSIDE the window   *)
(* for every q >= 1 (the N5 full-spectrum certificate), and the q=1     *)
(* anchor forces the witness n = 1 (< N0 = 1348), while the threshold   *)
(* pair above shows that for L in [L*, lower edge) the forced witness   *)
(* stays below N0: the head coverage is unavoidable, i.e. the Hcage     *)
(* forall-n form is kept (KB41g 4-4 D; the reformulation "forall        *)
(* n >= N0" is not provable in that band).  The EXACT anchors of this   *)
(* file are the machine content of the seal; the band reading (which q  *)
(* ranges fall between the thresholds) is the KB41g 4-1 OFFSYS account. *)

Print Assumptions piu_zz_ec_Lstar_ordered.
Print Assumptions piu_zz_ec_22902_double.
Print Assumptions piu_zz_ec_2pow5_7_lo.
Print Assumptions piu_zz_ec_2pow5_7_hi.
Print Assumptions piu_zz_ec_qstar_ordered.
Print Assumptions piu_zz_ec_ledge_ordered.
Print Assumptions piu_zz_ec_ledge_ordered.
Print Assumptions piu_zz_ec_slope_cert.
Print Assumptions piu_zz_ec_q1_anchor.
Print Assumptions piu_zz_ec_q1_witness_lives.
