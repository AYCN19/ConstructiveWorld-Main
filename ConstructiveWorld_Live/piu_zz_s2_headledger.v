(* ========================================================================= *)
(* Mission      : N4 head-section upper-bound ledger (gammaP1 W4 batch) for  *)
(*                the s2(n) Mertens noise face after the KB41m beta=0        *)
(*                NEGATIVE verdict. The refactored criterion replaces the    *)
(*                retired KB61 account (window-sum factor-2 miss: 2.85698   *)
(*                vs corrected T2c = 5.8965 EXACT; lambda-account e^497      *)
(*                voided) by the KB76 max-form certificate                   *)
(*                |s2(n)| <= max(C1*n^(3/4), C2*n) for all n >= 41, carried  *)
(*                here as: (i) the EXACT rational brackets of C1 and C2*     *)
(*                (nats scale, straight from the certificate JSON),          *)
(*                (ii) the three-regime splice unifying the piece(i)/(ii)/   *)
(*                (iii) sup accounts into one uniform C2*-per-n eventual     *)
(*                face, (iii) the max-form two-branch union headline with    *)
(*                the C1 branch carried in the exact 4th-power Q face        *)
(*                (fractional exponent 3/4 never enters the Q surface),      *)
(*                (iv) the D10 Proposition 5.1 repair entry that closes the  *)
(*                piece(iii) domain gap (Buethe 2018 (1.7) covers u <= 1e19  *)
(*                only, n <~ 3.3e37; Dusart 2010 Prop 5.1 covers all x > 0   *)
(*                at the factor 36261/36260, absorbed by the T4c x2 margin), *)
(*                (v) the min-form ban faces (min form = registered false    *)
(*                proposition, R0; at n=41 the min branch is the C2* branch  *)
(*                whose domain starts at 1e10) and the KB61 retirement face. *)
(* Dependencies : piu_zz_nail_mu (N6'-a nail face; disambiguation of the two *)
(*                distinct C1 constants - interface bite W4/N6'-a);          *)
(*                piu_zz_sigma_decay (N2b bridge face - interface bite       *)
(*                W4/N2b); S02_CauchyComplete (QleT'/QltT); stdlib QArith,   *)
(*                ZArith, Lia, Lqa.                                          *)
(* References   : KB76 EXACT bracket certificate (out/kb76_cert_out.json,    *)
(*                md5 532efd16, max form per review correction; total        *)
(*                FAILS = 0); KB76 receipt sec.7 (min-form falsity, R0       *)
(*                pending, piece(iii) gap + D10 Prop 5.1 repair);           *)
(*                KB76 C3 package sec.2/5 (consumption shape, R0-R4 plan);   *)
(*                KB41m NEGATIVE verdict (beta=0 and every fixed-beta C_asm  *)
(*                criterion EXACT-falsified in-window; refactored criterion  *)
(*                is the s2-ledger form); KB41g 3-3.4 (beta=1 head judgment  *)
(*                constant, the OTHER C1); GEDAN-v2 workorder node N4.       *)
(* Constructivity: every named statement is Set-carried (S02 QleT'/QltT,     *)
(*                sigT, sum); the analytic inputs (Buethe 2018 (1.5)/(1.7),  *)
(*                Dusart 2010 Prop 5.1) stay explicit premise slots on       *)
(*                the abstract noise carriers, never discharged (PNT-grade   *)
(*                honesty, HLn_rate_up precedent); the certificate constants *)
(*                are exact Q literals with vm_compute anchors; 无公理依赖、  *)
(*                无未证假设; no Abort; every named statement closes under   *)
(*                the global context.                                        *)
(* Build        : rocq c -native-compiler no -q -time -Q . ""                *)
(*                -Q <kb45 sandbox> "" -Q <kb46 sandbox> ""                  *)
(*                -Q <ConstructiveWorld_vo> "" piu_zz_s2_headledger.v,       *)
(*                under cpu_guard_v3 (-LoadLimit 60 -TempLimit 98 -AllowG3   *)
(*                -GearForce 0), Rocq 9.1.0.                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_sigma_decay.
Require Import piu_zz_nail_mu.

(* ================================================================== *)
(* Section 1. KB76 EXACT constants (rational brackets, nats scale).   *)
(* ================================================================== *)

(* C1_ln: the s2 slope constant of the n^(3/4) branch (nats),          *)
(* EXACT bracket straight from kb76_cert_out.json headline.C1_ln.      *)
(* OFFSYS display anchor: 11.225349793842305. Distinct from the KB41g  *)
(* beta=1 head-judgment constant piu_zz_nail_C1 (disambiguated in      *)
(* Section 5).                                                         *)
Definition piu_zz_s2_C1ln_lo : Q :=
  (8699562498860208691355730096732144762701786083871533419018442819811406882215595639709037461340196619712923787635408038883
   # 774992553339618586996741811759189364574721259316888052317972020622108347088998856366962210685460180599548368162442444800)%Q.

Definition piu_zz_s2_C1ln_hi : Q :=
  (55099806807595798810791135316278595820246314188923098495942546810479335196651219472764516372057420820661649272222675509746039697
   # 4908515798574129456486617275903214711025210047742503884219036514574065158989809664520991399462163330336366187517394812928000000)%Q.

(* C2*_ln: the uniform s2-per-n slope of the O(n) branch (nats),       *)
(* EXACT bracket from kb76_cert_out.json headline.C2star_ln; sup of    *)
(* the three regime pieces (i) 0.020409@1e10, (ii) 0.000570@2.5e18,    *)
(* (iii) 0.019263@5e18 (OFFSYS display of the sup points).             *)
Definition piu_zz_s2_C2ln_lo : Q :=
  (50944616857563032033456430044546396925527280805751746889397262467078913254180634718580996063545028974372218490361642132098085767853
   # 2496181325527453700880664268175881257678063873961610113327270666470791800949321261941139185834364462483644939025514496000000000000000)%Q.

Definition piu_zz_s2_C2ln_hi : Q :=
  (61827896488467608654529608584185201508555625168207939950955392120826411734886989719366116774057240489417792182529877987628001371395001
   # 3029439617588281587794722734645033407198185803481346642403184576534712848449546141871868029158393621114294703466626416640000000000000000)%Q.

(* T2c: the corrected window-sum n^(3/4) coefficient (EXACT bracket),  *)
(* the constant that voids the KB61 old account (factor-2 miss).       *)
Definition piu_zz_s2_T2c_lo : Q :=
  (7329377233936730071788158976 # 1242996761548520344312840625)%Q.

Definition piu_zz_s2_T2c_hi : Q :=
  (9772502978582306762384211968 # 1657329015398027125750453125)%Q.

(* T4c: the tail window-account constant carrying the x2 margin that   *)
(* absorbs the D10 Prop 5.1 repair (EXACT bracket).                    *)
Definition piu_zz_s2_T4c_hi : Q :=
  (438664526111310821656083193781135426147999035227
   # 241845100692657243904184985625969896708974313472)%Q.

Lemma piu_zz_s2_brackets_sane_1 :
  S02_CauchyComplete.QltT piu_zz_s2_C1ln_lo piu_zz_s2_C1ln_hi.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_s2_brackets_sane_2 :
  S02_CauchyComplete.QltT piu_zz_s2_C2ln_lo piu_zz_s2_C2ln_hi.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_s2_brackets_sane_3 :
  S02_CauchyComplete.QltT piu_zz_s2_T2c_lo piu_zz_s2_T2c_hi.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_s2_T4c_pos : (0 < piu_zz_s2_T4c_hi)%Q.
Proof. unfold Qlt. cbn. lia. Qed.

(* repair-entry constant anchors (all concrete, vm_compute-cheap) *)
Example piu_zz_s2_Ck1 :
  (36261 # 36260)%Q == (1 # 1) + (1 # 36260)%Q.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_Ck2 :
  (1 # 2)%Q * (1 # 36260)%Q == (1 # 72520)%Q.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_Ck3 :
  (1 # 2)%Q + (1 # 72520)%Q == (36261 # 72520)%Q.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_Ck4 :
  S02_CauchyComplete.QltT (36261 # 72520)%Q (1 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 2. Domain anchors of the three regimes (EXACT).            *)
(* ================================================================== *)

(* ================================================================== *)
(* Section 3. KB61 retirement + min-form ban faces (R0 discipline).   *)
(* ================================================================== *)

(* Retirement face: the corrected window-sum constant T2c dominates    *)
(* the retired KB61 window-sum account 2.85698 (which missed the       *)
(* factor 2; KB76 cert sec.3), already by more than the factor 2.      *)
Lemma piu_zz_s2_T2c_retires_kb61 :
  S02_CauchyComplete.QltT
    ((285698 # 100000)%Q * (2 # 1)%Q)%Q
    piu_zz_s2_T2c_lo.
Proof. vm_compute. reflexivity. Qed.

(* Min-form ban, branch-selection face (EXACT): at n = 41 the min of   *)
(* the two branches takes the C2star branch (41 x C2^4 < C1^4 is the   *)
(* exact 4th-power form of C2 x 41 < C1 x 41^(3/4)).  Since the C2star *)
(* branch is certified only for n >= 1e10, the min-form headline is    *)
(* exactly the registered false proposition (KB76 receipt sec.7-1;     *)
(* counterexample n = 41: 10.3316 bit > 1.2072 bit).  Consumption is   *)
(* max-form only; this face is the machine-checkable reason.           *)
Lemma piu_zz_s2_min_branch_at_41 :
  S02_CauchyComplete.QltT
    (inject_Z 41 * Qpower piu_zz_s2_C2ln_hi 4%Z)%Q
    (Qpower piu_zz_s2_C1ln_lo 4%Z)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 3b. Regime bounds (exact Z literals on the Q-inject face). *)
(* ================================================================== *)

(* Regime bounds as exact Z literals carried on the Q-inject surface.  *)
(* (nat-typed thresholds are avoided: the unary nat encoding of 1e10-  *)
(* scale literals explodes under evaluation; every comparison below is *)
(* a Z-literal or a Q-inject comparison, all vm_compute-cheap.)        *)
Definition piu_zz_s2_w1 : Q := inject_Z 10000000000%Z.
Definition piu_zz_s2_w2 : Q := inject_Z 2500000000000000000%Z.
Definition piu_zz_s2_w3 : Q := inject_Z 5000000000000000000%Z.
Definition piu_zz_s2_t19 : Q := inject_Z 10000000000000000000%Z.

(* domain facts EXACT: 4 x 2.5e18 = 1e19 and 2 x 5e18 = 1e19 (the      *)
(* Buethe (1.5) window edge), sqrt(3x41) > 11 (non-degenerate start),  *)
(* the regime ordering, and the crossover n-star floor.                *)
Example piu_zz_s2_dom_4x : (inject_Z 4 * piu_zz_s2_w2 == piu_zz_s2_t19)%Q.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_dom_2x : (inject_Z 2 * piu_zz_s2_w3 == piu_zz_s2_t19)%Q.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_dom_sqrt : (11 * 11 < 3 * 41)%nat.
Proof. vm_compute; lia. Qed.

Example piu_zz_s2_w1_le_w2 :
  S02_CauchyComplete.QleT' piu_zz_s2_w1 piu_zz_s2_w2.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_s2_w2_le_w3 :
  S02_CauchyComplete.QleT' piu_zz_s2_w2 piu_zz_s2_w3.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_s2_crossover_floor :
  S02_CauchyComplete.QltT
    (piu_zz_s2_w1 * Qpower piu_zz_s2_C2ln_hi 4%Z)%Q
    (Qpower piu_zz_s2_C1ln_lo 4%Z)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 4. Three-regime splice (pieces i/ii/iii -> uniform C2star). *)
(* ================================================================== *)

(* Carrier: piu_zz_s2_face n = the absolute s2 noise face in nats      *)
(* (the absolute-value convention is built in).  The three regime      *)
(* hypotheses are the KB76 piece accounts:                             *)
(*   piece(i)   [1e10, 2.5e18]  B18-route,                             *)
(*   piece(ii)  (2.5e18, 5e18]  B18-windows + D10-at-4n,               *)
(*   piece(iii) (5e18, inf)     D10-windows + D10-at-4n (with the      *)
(*   repair entry of Section 6 closing its domain gap).  Each is an    *)
(*   explicit slot; the certificate owns their machine side.  Bounds   *)
(*   are Q-inject comparisons (decidable case-splits only, no          *)
(*   evaluation of the big constants).                                 *)
Section S2SPLICE.

Variable s2face : nat -> Q.

Hypothesis HPiece1 : forall n : nat,
  S02_CauchyComplete.QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)) ->
  S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
  S02_CauchyComplete.QleT' (s2face n)
    (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q.

Hypothesis HPiece2 : forall n : nat,
  S02_CauchyComplete.QleT' piu_zz_s2_w2 (inject_Z (Z.of_nat n)) ->
  S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w3 ->
  S02_CauchyComplete.QleT' (s2face n)
    (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q.

Hypothesis HPiece3 : forall n : nat,
  S02_CauchyComplete.QleT' piu_zz_s2_w3 (inject_Z (Z.of_nat n)) ->
  S02_CauchyComplete.QleT' (s2face n)
    (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q.

(* The splice: one uniform C2star-per-n face on the Q-carried domain   *)
(* w1 <= n (the KB76 headline domain fact: C2star valid n >= 1e10).    *)
Theorem piu_zz_s2_regime_splice : forall n : nat,
  S02_CauchyComplete.QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)) ->
  S02_CauchyComplete.QleT' (s2face n)
    (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q.
Proof.
  intros n Hw1.
  destruct (Qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w2) as [Hlt2 | Hge2].
  - apply HPiece1; [exact Hw1 |].
    apply S02_CauchyComplete.Qle_to_QleT'.
    apply Qlt_le_weak. exact Hlt2.
  - destruct (Qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w3) as [Hlt3 | Hge3].
    + apply HPiece2; [| apply S02_CauchyComplete.Qle_to_QleT';
        apply Qlt_le_weak; exact Hlt3].
      apply S02_CauchyComplete.Qle_to_QleT'. exact Hge2.
    + apply HPiece3. apply S02_CauchyComplete.Qle_to_QleT'. exact Hge3.
Qed.

(* The C1 branch in the exact 4th-power Q face: for the nonneg noise   *)
(* carrier, the s2 bound by C1 x n^(3/4) is carried as s2face(n)^4     *)
(* <= C1^4 x n^3 (integer exponents only; the fractional exponent 3/4  *)
(* never enters the Q surface).  Branch domain [41, 2.5e18].           *)
Hypothesis HC1branch : forall n : nat,
  S02_CauchyComplete.QleT' (inject_Z 41%Z) (inject_Z (Z.of_nat n)) ->
  S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
  S02_CauchyComplete.QleT' (Qpower (s2face n) 4%Z)
    (Qpower piu_zz_s2_C1ln_hi 4%Z * inject_Z (Z.of_nat (n * n * n)))%Q.

(* Max-form union: for every n >= 41 the noise face is bounded by the  *)
(* C2star branch (n >= 1e10, via the splice) or by the C1 branch       *)
(* (n < 1e10, inside the C1 domain).  This sum face is the exact       *)
(* Set-carried form of the max-form headline and is the replacement    *)
(* of the retired KB61 account.                                        *)
Theorem piu_zz_s2_head_maxform : forall n : nat,
  (41 <= n)%nat ->
  sum (S02_CauchyComplete.QleT' (s2face n)
         (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q)
      (S02_CauchyComplete.QleT' (Qpower (s2face n) 4%Z)
         (Qpower piu_zz_s2_C1ln_hi 4%Z
            * inject_Z (Z.of_nat (n * n * n)))%Q).
Proof.
  intros n Hn.
  destruct (Qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w1) as [Hlt1 | Hge1].
  - (* n < 1e10: the C1 branch, domain-internal *)
    right. apply HC1branch.
    + pose proof (proj1 (Nat2Z.inj_le 41 n) Hn) as HZ.
      change (Z.of_nat 41) with 41%Z in HZ.
      destruct (piu_mu_criterion.piu_mu_Zle_Qle 41%Z (Z.of_nat n) HZ) as [HQ].
      apply S02_CauchyComplete.Qle_to_QleT'. exact HQ.
    + apply S02_CauchyComplete.Qle_to_QleT'.
      pose proof (S02_CauchyComplete.QleT'_to_Qle _ _
        piu_zz_s2_w1_le_w2) as Hww.
      exact (Qle_trans _ _ _ (Qlt_le_weak _ _ Hlt1) Hww).
  - (* n >= 1e10: the C2star branch via the splice *)
    left. apply piu_zz_s2_regime_splice.
    apply S02_CauchyComplete.Qle_to_QleT'. exact Hge1.
Qed.

(* Tiling of the two branch domains over [41, inf) (all-Z face). *)
Example piu_zz_s2_branch_tile :
  (41 < 10000000000 /\ 10000000000 <= 2500000000000000000)%Z.
Proof.
  split.
  - vm_compute; reflexivity.
  - vm_compute; discriminate.
Qed.

End S2SPLICE.

(* ================================================================== *)
(* Section 6. D10 Prop 5.1 repair entry (piece(iii) domain gap).       *)
(* ================================================================== *)

(* The gap: piece(iii)'s rho-term cites Buethe 2018 (1.7) (x - theta(x) *)
(* > 0.05 sqrt(x), so theta(u) < u), valid only for u <= 1e19, i.e.     *)
(* n <~ 3.3e37 (OFFSYS pointer, KB76 receipt sec.7-2); beyond that the  *)
(* tail chain has no source.  The repair: Dusart 2010 Proposition 5.1   *)
(* (theta(x) - x < x/36260 for ALL x > 0) upgrades the rho source to    *)
(* the domain-free factor 36261/36260, absorbed by the T4c x2 margin.   *)
(* Carriers: thw u = the theta-window term in nats; rhow = the rho-term *)
(* share at the sup point; usedwin = the window-sum consumption at the  *)
(* sup point (the 0.8958-vs-1.8138 x2 margin account).  Instantiation  *)
(* belongs to the W5 chain-side calibration.                            *)
Section S2REPAIR.

Variable thw : Q -> Q.
Variable rhow usedwin : Q.

(* Buethe 2018 (1.7) face - the OLD source, domain-capped. *)
Hypothesis HB18_17 : forall u : Q,
  (u <= inject_Z 10000000000000000000%Z)%Q ->
  S02_CauchyComplete.QleT' (thw u) u.

(* Dusart 2010 Prop 5.1 face - the REPAIR source, domain-free. *)
Hypothesis HD10_P51 : forall u : Q,
  S02_CauchyComplete.QleT' (thw u) ((36261 # 36260)%Q * u)%Q.

(* the x2 margin: sup consumption fits in half the T4c budget, and the *)
(* rho share alone also fits in half the budget. *)
Hypothesis Hmargin :
  S02_CauchyComplete.QleT' (rhow + usedwin)%Q (piu_zz_s2_T4c_hi / 2)%Q.
Hypothesis Hrhoshare :
  S02_CauchyComplete.QleT' rhow (piu_zz_s2_T4c_hi / 2)%Q.

(* the repair-entry display bound: 1/36260 < 3/100000 (the 2.76e-5     *)
(* display of the receipt). *)
Example piu_zz_s2_D10P51_display :
  S02_CauchyComplete.QltT (1 # 36260)%Q (3 # 100000)%Q.
Proof. vm_compute. reflexivity. Qed.

(* Absorption: under the x2 margin the D10-upgraded rho share plus the *)
(* window consumption still fits inside the full T4c budget - the      *)
(* domain gap closes at ZERO numerical headcount (KB76 receipt         *)
(* sec.7-2: "completely absorbed by the T4c x2 margin").  Exact form:  *)
(* rhow x (36261/36260) + usedwin <= T4c, since rhow+usedwin <= T4c/2  *)
(* and rhow <= T4c/2 give rhow x k + usedwin = (rhow+usedwin)          *)
(* + rhow/36260 <= T4c/2 + T4c/(2 x 36260) < T4c.                      *)
Theorem piu_zz_s2_D10P51_absorbed :
  S02_CauchyComplete.QleT'
    (rhow * (36261 # 36260)%Q + usedwin)%Q
    piu_zz_s2_T4c_hi.
Proof.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hmargin) as Hm.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hrhoshare) as Hr.
  apply S02_CauchyComplete.Qle_to_QleT'.
  rewrite piu_zz_s2_Ck1.
  rewrite Qmult_plus_distr_r.
  rewrite Qmult_1_r.
  rewrite <- Qplus_assoc.
  rewrite (Qplus_comm (rhow * (1 # 36260)%Q) usedwin).
  rewrite Qplus_assoc.
  apply (Qle_trans _ (piu_zz_s2_T4c_hi * (1 # 2)%Q
                       + piu_zz_s2_T4c_hi * (1 # 72520)%Q)%Q).
  - apply Qplus_le_compat.
    + exact Hm.
    + apply (Qle_trans _ (piu_zz_s2_T4c_hi * (1 # 2)%Q
                           * (1 # 36260)%Q)%Q).
      * apply Qmult_le_compat_r. exact Hr.
        unfold Qle. cbn. lia.
      * rewrite <- Qmult_assoc.
        rewrite piu_zz_s2_Ck2.
        apply Qle_refl.
  - rewrite <- (Qmult_plus_distr_r piu_zz_s2_T4c_hi (1 # 2)%Q
                  (1 # 72520)%Q).
    rewrite piu_zz_s2_Ck3.
    assert (Hstep : ((36261 # 72520)%Q <= 1)%Q)
      by (apply Qlt_le_weak;
          exact (S02_CauchyComplete.QltT_to_Qlt _ _ piu_zz_s2_Ck4)).
    pose proof (proj2 (Qmult_le_l (36261 # 72520)%Q 1 piu_zz_s2_T4c_hi
                         piu_zz_s2_T4c_pos) Hstep) as Hfin.
    rewrite Qmult_1_r in Hfin.
    exact Hfin.
Qed.

End S2REPAIR.

(* ================================================================== *)
(* Section 7. Interface bites (first-wave meshing).                   *)
(* ================================================================== *)

(* Bite W4/N6'-a: the two C1 constants are DIFFERENT faces.  The nail  *)
(* unit's piu_zz_nail_C1 is the KB41g beta=1 head-judgment constant    *)
(* 375^187/(187 x 373^187) = 0.014536 (EXACT); the KB76 s2 slope       *)
(* C2star = 0.020409 (nats) is strictly larger.  Registered so         *)
(* downstream consumers cannot conflate the two.                       *)
Lemma piu_zz_s2_C1_disambiguation :
  S02_CauchyComplete.QltT piu_zz_nail_C1 piu_zz_s2_C2ln_lo.
Proof. vm_compute. reflexivity. Qed.

(* Bite W4/N2b: the head ledger composes with the N2b sigma-decay      *)
(* bands.  The refactored head criterion is the CONJUNCTION of the     *)
(* coefficient-side band slot (N2b's Hcoef sigma=17 face, arm A) and   *)
(* the noise-side uniform face of this file - registered here as the   *)
(* combined Set face the W5 assembly consumes.                         *)
(* The combined face carries the three piece interfaces (the exact     *)
(* premise shape of the discharged splice theorem) beside the N2b      *)
(* coefficient-side band slot - the premise bundle the W5 assembly     *)
(* supplies to piu_zz_s2_regime_splice / piu_zz_s2_head_maxform.       *)
Definition piu_zz_s2_head_combined_face (A B : nat -> Z) (s2f : nat -> Q) : Set :=
  piu_mu_and2
    (piu_zz_n2b_hcoef17_A A)
    (piu_mu_and3
      (forall n : nat,
         S02_CauchyComplete.QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)) ->
         S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
         S02_CauchyComplete.QleT' (s2f n)
           (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q)
      (forall n : nat,
         S02_CauchyComplete.QleT' piu_zz_s2_w2 (inject_Z (Z.of_nat n)) ->
         S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w3 ->
         S02_CauchyComplete.QleT' (s2f n)
           (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q)
      (forall n : nat,
         S02_CauchyComplete.QleT' piu_zz_s2_w3 (inject_Z (Z.of_nat n)) ->
         S02_CauchyComplete.QleT' (s2f n)
           (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q)).

Lemma piu_zz_s2_combined_intro : forall (A B : nat -> Z) (s2f : nat -> Q),
  (forall n : nat,
      S02_CauchyComplete.QleT' (inject_Z (Z.abs (A n)))
        (Qpower (inject_Z 2%Z) (Z.of_nat (17 * n)))%Q) ->
  (forall n : nat,
      S02_CauchyComplete.QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)) ->
      S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
      S02_CauchyComplete.QleT' (s2f n)
        (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  (forall n : nat,
      S02_CauchyComplete.QleT' piu_zz_s2_w2 (inject_Z (Z.of_nat n)) ->
      S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w3 ->
      S02_CauchyComplete.QleT' (s2f n)
        (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  (forall n : nat,
      S02_CauchyComplete.QleT' piu_zz_s2_w3 (inject_Z (Z.of_nat n)) ->
      S02_CauchyComplete.QleT' (s2f n)
        (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  piu_zz_s2_head_combined_face A B s2f.
Proof.
  intros A B s2f HA H1 H2 H3.
  apply piu_mu_and2_i.
  - exact HA.
  - apply piu_mu_and3_i.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

Print Assumptions piu_zz_s2_brackets_sane_1.
Print Assumptions piu_zz_s2_brackets_sane_2.
Print Assumptions piu_zz_s2_brackets_sane_3.
Print Assumptions piu_zz_s2_crossover_floor.
Print Assumptions piu_zz_s2_T2c_retires_kb61.
Print Assumptions piu_zz_s2_min_branch_at_41.
Print Assumptions piu_zz_s2_regime_splice.
Print Assumptions piu_zz_s2_head_maxform.
Print Assumptions piu_zz_s2_w1_le_w2.
Print Assumptions piu_zz_s2_w2_le_w3.
Print Assumptions piu_zz_s2_branch_tile.
Print Assumptions piu_zz_s2_combined_intro.
Print Assumptions piu_zz_s2_D10P51_display.
Print Assumptions piu_zz_s2_D10P51_absorbed.
Print Assumptions piu_zz_s2_Ck1.
Print Assumptions piu_zz_s2_Ck2.
Print Assumptions piu_zz_s2_Ck3.
Print Assumptions piu_zz_s2_Ck4.
Print Assumptions piu_zz_s2_C1_disambiguation.
