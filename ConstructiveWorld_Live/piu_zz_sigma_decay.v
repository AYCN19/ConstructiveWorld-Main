(* ================================================================= *)
(* Mission.: gammaP1 N2b node, sigma value-decay face (formal          *)
(*   statement unit): the KB41/41b/41c/41e sigma table bands — raw     *)
(*   EXACT band / sup_j control band / assembly slack — as Set-carried *)
(*   Coq statements serving N2c (crude_size_sharp at 2^{17n}), N5      *)
(*   (Hcoef sigma 12->17 slot) and N4 (numeric preview face). Machine  *)
(*   samples (kb41o_samples.py S8/S6) are lifted to vm_compute Qed     *)
(*   lemmas; proof-open faces stay as Set-typed obligations: no Prop   *)
(*   surface, admission-free, axiom-free.                              *)
(* Dependencies.: S02_CauchyComplete.v (QleT' :99, Qle_to_QleT' :115,  *)
(*   QltT :48); piu_zz_kernel_sum.v (local qleT :73, ports out :76,    *)
(*   piu_zz_Aj :632, crude_size :987, tree samples :1072/:1075);       *)
(*   piu_zz_constants.v (piu_zzc_N3 :104); this sandbox unit           *)
(*   piu_zz_cage_constants.v (piu_zz_q_eval_P); trust cache            *)
(*   ConstructiveWorld_vo (deps .vo-present, .v-fresh).                *)
(* References.: receipt-KB41c (tables 4-1/4-2/4-3, P1-P6); receipt-    *)
(*   KB41e (sigma_raw EXACT dyadic band 2^-20; corrected power-form    *)
(*   flags); receipt-KB41b (tables 3-1/3-2); receipt-KB41d (N2c row);  *)
(*   receipt-KB41o (N2b statement-face draft, tier table); workorder   *)
(*   GEDAN-gammaP1 sec.2 N2c/N4/N5 + KB41e 7.2 change-points.          *)
(* Constructivity.: statement faces Set-carried (QleT'/QeqT/QltT over  *)
(*   sigT); fitted/OFFSYS values (16.94 asymptote, slack 0.2447,      *)
(*   width 0.0642) stay out of the statement surface (comments only); *)
(*   L1 face has no tree carrier (true-gap, not in acceptance); lia    *)
(*   unused; flags in corrected power form.                            *)
(* Build.: coqc -native-compiler no -q -Q ConstructiveWorld_vo ""      *)
(*   -Q . "" piu_zz_sigma_decay.v | cpu_guard v3 wrapped ASCII cmd     *)
(*   relay, sandbox kb45_work_20261028 (after piu_zz_cage_constants);  *)
(*   sample oracle kb41o_samples.py (65 PASS).                         *)
(* ================================================================= *)

From Stdlib Require Import QArith ZArith Arith Lia.
From Stdlib Require Import QArith.Qabs.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_constants.
Require Import piu_zz_cage_constants.

(* Fail-loud log (this seat): F5 draft's Z.abs on Q-valued piu_zz_Aj  *)
(* is ill-typed -> Qabs; F7 draft's literal 1047*16 exponent on the    *)
(* A-face power is the acc-face conversion (847 + 4*50 = 1047, the     *)
(* corrected power-form flag |acc|^q <= 2^{num*n+4*q*n}); this unit    *)
(* registers the tight equivalent A-face form 2^{847*n}; F8 draft      *)
(* Lemma piu_zz_n2b_A_allj_le17 (unproven) re-landed as a Set-typed    *)
(* obligation face (F6 family); K=2^12 dyadic bracket lemmas, left in  *)
(* comments by the draft, are activated here per its own advice;       *)
(* F11 n=16/n=9 Aj spot-checks OOM -> recorded, deepest Aj face = n=2;  *)
(* F12 draft K12 dyadic exponents 59035/59036 -> 59045/59046 (cell      *)
(* display match; vm_compute caught the false hi bracket). *)

(* ---- b0: kernel_sum local qleT -> S02 QleT' consumer bridge ------- *)
(* kernel_sum:73 local Inductive qleT (qleT_intro: (a<=b)%Q -> qleT a  *)
(* b); its T->Prop escape ports are removed (:76, S01 #108 rule), so   *)
(* the bridge destructs in-term and lifts via S02 Qle_to_QleT'.        *)
(* piu_zz_crude_size (:987) consumption must pass through this bridge. *)
Lemma piu_zz_n2b_qleT_to_QleT' :
  forall x y : Q,
    piu_zz_kernel_sum.qleT x y -> S02_CauchyComplete.QleT' x y.
Proof.
  intros x y H.
  inversion H; subst.
  apply S02_CauchyComplete.Qle_to_QleT'.
  assumption.
Qed.

(* ---- b1: Hcoef sigma=17 slot faces (N5 consumption, arm A) -------- *)
(* e_carrier:627-630 Hcoef isomorph (its piu_mu_ZleT slot form carried *)
(* here by QleT'), sigma 12 -> 17. Arm B is the same form for B; the   *)
(* B-side mapping to this face belongs to the N5/N6' Coq construction  *)
(* scope (KB41c semantic note, honest registration). The rateslot-8    *)
(* lock and sigma=6*tau lock (:65/:68-77) break is the N5 first        *)
(* decision (KB41d 5-3), outside this statement face. *)
Section N2B_SIGMA.
Context (A B : nat -> Z).

Definition piu_zz_n2b_hcoef17_A : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (inject_Z (Z.abs (A n)))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).

Definition piu_zz_n2b_hcoef17_B : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (inject_Z (Z.abs (B n)))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).
(* The statement surface is a direct transcription (isomorph, constant *)
(* exchanged); its universal supply is the N2c chain product. *)
End N2B_SIGMA.

(* ---- b2: A-face all-j envelope at 2^{17n} (N2c consumption face) -- *)
(* piu_zz_Aj value face (kernel_sum), j-range 0..3n. The old 2^{37n}   *)
(* bound (crude_size :987, local qleT) enters the QleT' world via the  *)
(* b0 bridge; the 37->17 chain sharpening is workorder N2c quantity-1  *)
(* body (consumes N2a GF bound). This unit fixes the consumption face: *)
Definition piu_zz_n2b_A_allj_le17_face : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).

(* sigma=12 falsification numeric face (KB41d C2, sample S8-49):       *)
(* |A_{2,0}| = 37324672 > 2^24 EXACT. *)
Lemma piu_zz_n2b_sigma12_falsified :
  S02_CauchyComplete.QltT (Qpower (inject_Z 2) 24%Z) (Qabs (piu_zz_Aj 2 0)).
Proof. vm_compute. reflexivity. Qed.

(* spot-check faces (vm_compute; tree precedent kernel_sum:1072/:1075). *)
(* Fail-loud F11: the draft's larger Aj spot-check faces OOM in the     *)
(* coqc VM on this box under concurrent load (n=16 j=0 about 2.9M       *)
(* tuples, n=16 j=28 about 53k, even n=9 j=0 about 170k) — the deepest  *)
(* Aj face this box certifies tonight is n=2. The larger faces stay     *)
(* Python-verified (kb41o samples run.log: n=9 j=0 == KB41b table 3-1   *)
(* value; n=16 j=28 le17 TRUE; le16.94 fixed-form TRUE) and their Coq   *)
(* faces are deferred to the N2c chain whose supply obviates per-spot   *)
(* enumeration. Statement forms kept in record:                         *)
(*   QeqT (piu_zz_Aj 9 0) (-42168444724147139007577695871389663232 # 1) *)
(*         [KB41b table 3-1 anchor, S8-52/53]            [record]       *)
(*   QleT' (Qabs (piu_zz_Aj 16 28)) (2^{17*16})          [record]       *)
(*   QleT' (Qpower (Qabs (piu_zz_Aj 16 28)) 50) (2^{847*16}) [record]   *)

(* le16.94 control-band pin, corrected power form, A face (samples     *)
(* S8-56/59): |A_{16,28}|^50 <= 2^{847*16} — deferred to record by F11  *)
(* (OOM); the draft's literal exponent 1047*16 is the acc-face          *)
(* conversion (847 + 4*50), F7. *)

(* ---- b3: L1 face (pre-collapse l1) — non-binding observation face, *)
(* true-gap registration, NOT in acceptance -------------------------- *)
(* KB41c P6 / KB41e 7.2 change-point three: the acceptance object is   *)
(* the A-face coefficient band; the L1 face is a non-binding           *)
(* observation face (thin band 0.0642, not to be conceded further).    *)
(* The tree has no L1 carrier definition (zz_lsum_abs would be new =    *)
(* true-gap registration, KB41c open item (b) family, non-blocking)    *)
(* -> default: no construction; statement form kept in record only:    *)
(*   forall n j : nat, (j <= 3 * n)%nat ->                             *)
(*     QleT' (inject_Z (zz_lsum_abs n j)) (2^{17n})      [record]      *)
(*   forall n j : nat, (j <= 3 * n)%nat ->                             *)
(*     QleT' (inject_Z (zz_lsum_abs n j)^50) (2^{1047*n}) [record]     *)
(* Machine record: L1 le17/le16.94 n=1..16 all TRUE (KB41c table 4-1,  *)
(* KB41e re-run); samples S8-61/62/63 re-derived at (16,17) equal +    *)
(* both flags TRUE. *)

(* ---- b4: sigma_raw EXACT band (KB41e 4; C6 in this unit per the    *)
(* N2a/N2b division, cross-referenced by piu_zz_cage_constants) ------ *)
(* C6 twin power anchors (~14.4kbit, vm_compute; samples S6-24/25;     *)
(* corrected anchor directions: 2^14415 < 21851^1000 and               *)
(* 21852^1000 < 2^14416). *)
Lemma piu_zz_n2b_rawband_c6_lo :
  S02_CauchyComplete.QleT' (Qpower (inject_Z 2) 14415%Z)
    (Qpower (inject_Z 21851) 1000%Z).
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2b_rawband_c6_hi :
  S02_CauchyComplete.QleT' (Qpower (inject_Z 21852) 1000%Z)
    (Qpower (inject_Z 2) 14416%Z).
Proof. vm_compute. reflexivity. Qed.

(* 1e-8 integer-grid brackets (KB41e 4: N3 in (21851.69139621,         *)
(* 21851.69139622) EXACT; sample S6-26 fresh bisection k0=2185169139621) *)
Lemma piu_zz_n2b_N3_bracket_lo :
  S02_CauchyComplete.QltT
    (piu_zz_q_eval_P (2185169139621 # 100000000)%Q) (0 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2b_N3_bracket_hi :
  S02_CauchyComplete.QltT (0 # 1)%Q
    (piu_zz_q_eval_P (2185169139622 # 100000000)%Q).
Proof. vm_compute. reflexivity. Qed.

(* tree constant inside the certificate brackets (sample S6-27):       *)
(* piu_zzc_N3 = 2185169139621956/10^11 (constants.v:104) in (..21,     *)
(* ..22)/10^8 — tree constant vs certificate band consistency. *)
Lemma piu_zz_n2b_N3const_gt_lo :
  S02_CauchyComplete.QltT (2185169139621 # 100000000)%Q piu_zzc_N3.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2b_N3const_lt_hi :
  S02_CauchyComplete.QltT piu_zzc_N3 (2185169139622 # 100000000)%Q.
Proof. vm_compute. reflexivity. Qed.

(* KB41e dyadic band 2^-20 endpoints, landed at K=2^12 as the draft    *)
(* advises (samples S6-28/29/30: m20=15115702, single-cell width,      *)
(* nested with the fresh K=2^12 coarse cell (59045,59046)/4096). The   *)
(* K=2^20 statement face (4.5Mbit power compares) stays off until      *)
(* measured; K=2^12 cell width 2.44e-4 is far finer than the C6        *)
(* thousandths band either way. Fail-loud F12: the draft's literal     *)
(* exponents 59035/59036 are a transcription slip (off by ten); the    *)
(* sample's own OFFSYS cell display (14.415283203125, 14.41552734375)  *)
(* = (59045/4096, 59046/4096) — the vm_compute face caught the wrong   *)
(* hi bracket (computed false at 59036, kb41o nesting sample re-derived*)
(* at the corrected exponents, exact integer powers). *)
Lemma piu_zz_n2b_rawband_dyadic_K12_lo :
  S02_CauchyComplete.QleT' (Qpower (inject_Z 2) 59045%Z)
    (Qpower (2185169139621 # 100000000)%Q 4096%Z).
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_n2b_rawband_dyadic_K12_hi :
  S02_CauchyComplete.QleT'
    (Qpower (2185169139622 # 100000000)%Q 4096%Z)
    (Qpower (inject_Z 2) 59046%Z).
Proof. vm_compute. reflexivity. Qed.

(* ---- b5/b6: assembly slack 0.2447 / control-band asymptote 16.94   *)
(* = machine-outside observation values, kept out of the statement     *)
(* surface (discipline): 17 - 16.7553 = 0.2447 is the paper-exact      *)
(* sigma_ZZ slack (KB41c table 4-2; its judgment power is carried by   *)
(* the C5 EXACT certificate in piu_zz_cage_constants); the control-    *)
(* band asymptote 16.9358 / width 0.0642 are 1/n^2 fits (KB41c P4      *)
(* machine-outside observation items; P5 extrapolation same family) —  *)
(* none of these are theorems. The Coq-carried control-band content =  *)
(* per-n flags (b2 spot-check form, n <= 16 machine-verified) + the    *)
(* forall-n extension (= N2c chain body, quantity 1, KB41d 3). *)

(* ================================================================= *)
(* downstream notes: N2c (crude_size_sharp at 2^{17n}) consumes the    *)
(* b0 bridge + b2 consumption face; this unit fixes its acceptance     *)
(* interface (A face, all j, j <= 3n, corrected power-form flags);     *)
(* the chain-sharpening proof burden stays in N2c. N5 (sigma 12->17)   *)
(* consumes the b1 slot faces (Hcoef isomorph); lock-break/migration   *)
(* account = its construction scope (KB41d 5-3 / KB41f prescription).  *)
(* N4 consumes the b4 raw-band anchors (numeric preview face, KB41e    *)
(* 7.2 change-point two).                                              *)
(* ================================================================= *)

Print Assumptions piu_zz_n2b_qleT_to_QleT'.
Print Assumptions piu_zz_n2b_sigma12_falsified.
Print Assumptions piu_zz_n2b_rawband_c6_lo.
Print Assumptions piu_zz_n2b_rawband_c6_hi.
Print Assumptions piu_zz_n2b_N3_bracket_lo.
Print Assumptions piu_zz_n2b_N3_bracket_hi.
Print Assumptions piu_zz_n2b_N3const_gt_lo.
Print Assumptions piu_zz_n2b_N3const_lt_hi.
Print Assumptions piu_zz_n2b_rawband_dyadic_K12_lo.
Print Assumptions piu_zz_n2b_rawband_dyadic_K12_hi.
