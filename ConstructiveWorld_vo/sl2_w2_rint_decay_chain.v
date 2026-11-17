(* sl2_w2_rint_decay_chain.v - the SL2 wave-2 remainder: the            *)
(* real-integral recast assembly chain and the elementary recast bricks *)
(* of the |I_n| bound ontology (contour route: registered backup only). *)
(* Mission. (1) The rate algebra: the Q power product identity and the  *)
(*  two-factor composition (normalization face x kernel certificate ->  *)
(*  the pi-anchored decay face). (2) The flagship chain: certificates   *)
(*  plus the band nu*rho <= 1/4 discharge the (B) Hval-direct live      *)
(*  consumption face via the landed band-end bridge. (3) The recast     *)
(*  bricks: square nonnegativity, quarter band, the kernel numerator    *)
(*  band on the unit square (division-free integrand form), the         *)
(*  geometric tail with its Qpower bridge. (4) ratio measurement        *)
(*  anchors (vm_compute-measured).                                     *)
(* Dependencies. Stdlib QArith/Qabs/ZArith/Arith/Lia/Qpower; sandbox    *)
(*  closure S02_CauchyComplete, piu_mu_criterion, piu_zz_e_carrier,     *)
(*  planb4_g1_witness, planb4_l2_dv_cast, planb3_g1_g2_design,          *)
(*  planb1_hcage_zerotouch_prescription, planb3_g1_calib,               *)
(*  sl2_anchor_carrier (sources from origin/main git objects only).     *)
(* Statement faces. sl12_w2_zsq_nonneg, sq_nonneg, le1_nonneg, flip,    *)
(*  amgm_band, sum_le_denom, quarter_band, kernel_num_band,             *)
(*  qpower_mul_alg, decay_compose, hval_from_certs (the flagship),      *)
(*  gpow, geo_sum, geo_tail, gpow_qpower, ratio + 4 measurement anchors.*)
(* References. [1] slot draft SL12 section 2 (supply faces). [2] the    *)
(*  SL12 survey 4.2/5/7 (the SL12-5 slice; the band end 1/4). [3]       *)
(*  CARRIER-SWAP ANNOTATION (interface-change obligation): the          *)
(*  fourslots hcage-slot face (planb4_l4_hcage_slot, the x = 1 l2_dv    *)
(*  carrier, (13/400)^n) is NOT re-cast here and must not be           *)
(*  discharged; the live consumption position is the (B) Hval-direct    *)
(*  face only; the carrier swap belongs to the landing step with the    *)
(*  migration ledger (zero tree writes). [4] landed sl2_anchor_carrier  *)
(*  and sl2_rint_recast. [5] piu_zz_gauss_pair, zzm1b_linform_bridge    *)
(*  (certified tables to n = 6). The ZZ2020 v2 source is absent on      *)
(*  disk: the two certificate inputs stay named breakthrough debts      *)
(*  (registered, not discharged). Provenance ledger: seat receipt only. *)
(* Constructivity. Postulate-free; all statements Set-carried (QleT',   *)
(*  QeqT, piu_mu_QleT, piu_mu_QltT, sigT); zero new Prop statements;    *)
(*  Defined transparent throughout; no solver at the flagship;          *)
(*  auxiliary leaf arithmetic may use lia.                              *)
(* Build. coqc -native-compiler no -q -Q <sandbox world> ""             *)
(*  sl2_w2_rint_decay_chain.v (E952 script form; needs                  *)
(*  sl2_anchor_carrier.vo on the load path).                            *)
(*  sl2_w2_rint_decay_chain.v (E952 script form; needs                  *)
(*  sl2_anchor_carrier.vo on the load path).                            *)
(*  sl2_w2_rint_decay_chain.v (E952 script form; needs the sandbox      *)
(*  closure with sl2_anchor_carrier.vo on the load path).               *)
(*  sl2_w2_rint_decay_chain.v (E952 script form; needs the sandbox       *)
(*  closure with sl2_anchor_carrier.vo on the load path).                *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_e_carrier.
Require Import planb4_g1_witness.
Require Import planb4_l2_dv_cast.
Require Import planb3_g1_g2_design.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb3_g1_calib.
Require Import sl2_anchor_carrier.

(* ==== Section 1: the rate algebra engine. ==== *)

(* the Q power product identity at positive rates: (a*b)^n == a^n*b^n.  *)
Lemma sl12_w2_qpower_mul_alg :
  forall (a b : Q) (n : nat),
  (0 < a)%Q -> (0 < b)%Q ->
  S02_CauchyComplete.QeqT (Qpower (a * b)%Q (Z.of_nat n))
    (Qpower a (Z.of_nat n) * Qpower b (Z.of_nat n))%Q.
Proof.
  intros a b n Ha Hb.
  assert (Ha0 : ~ a == 0) by (intro Hc; exact (Qlt_not_eq 0 a Ha (Qeq_sym a 0 Hc))).
  assert (Hb0 : ~ b == 0) by (intro Hc; exact (Qlt_not_eq 0 b Hb (Qeq_sym b 0 Hc))).
  assert (Hab0 : ~ (a * b)%Q == 0).
  { intro Hc. destruct (Qmult_integral a b Hc) as [H0 | H0].
    - exact (Ha0 H0).
    - exact (Hb0 H0). }
  induction n as [|k IH].
  - cbn [Z.of_nat]. apply qeq_imp_qeqT. rewrite !Qpower_0_r.
    ring.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    apply qeq_imp_qeqT.
    rewrite (Qpower_plus (a * b)%Q (Z.of_nat k) 1%Z Hab0).
    rewrite (Qpower_plus a (Z.of_nat k) 1%Z Ha0).
    rewrite (Qpower_plus b (Z.of_nat k) 1%Z Hb0).
    rewrite !Qpower_1_r.
    rewrite (qeqT_imp_qeq _ _ IH).
    ring.
Defined.

(* the two-factor composition: a pointwise normalization split (the     *)
(* anchor distance bounded by the normalization factor times the kernel *)
(* magnitude) with a rate for each factor composes into the decay face  *)
(* at the rate product. This is the ZZ2020 ledger shape (normalization  *)
(* times integral certificate), abstracted to its rate algebra.         *)
Lemma sl12_w2_decay_compose :
  forall (xpi : Q) (A B : nat -> Z) (qfac mag : nat -> Q) (nu rho : Q),
  (forall n : nat,
    S02_CauchyComplete.QleT' (sl12_dval_pi xpi (A n) (B n))
      (qfac n * mag n)%Q) ->
  (forall n : nat, (0 <= qfac n)%Q) ->
  (forall n : nat, (0 <= mag n)%Q) ->
  (0 < nu)%Q -> (0 < rho)%Q ->
  (forall n : nat,
    S02_CauchyComplete.QleT' (qfac n) (Qpower nu (Z.of_nat n))) ->
  (forall n : nat,
    S02_CauchyComplete.QleT' (mag n) (Qpower rho (Z.of_nat n))) ->
  (forall n : nat,
    S02_CauchyComplete.QleT' (sl12_dval_pi xpi (A n) (B n))
       (Qpower (nu * rho)%Q (Z.of_nat n))).
Proof.
  intros xpi A B qfac mag nu rho Hsplit Hqf0 Hmag0 Hnu Hrho Hqf Hmag n.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hsplit n)) as Hs.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hqf n)) as Hqf'.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hmag n)) as Hmag'.
  assert (Hdv0 : (0 <= sl12_dval_pi xpi (A n) (B n))%Q)
    by (unfold sl12_dval_pi; apply Qabs_nonneg).
  assert (Hqm0 : (0 <= qfac n * mag n)%Q)
    by exact (Qle_trans 0 (sl12_dval_pi xpi (A n) (B n))
               (qfac n * mag n) Hdv0 Hs).
  assert (Hq0 := Hqf0 n).
  assert (Hnup : (0 <= Qpower nu (Z.of_nat n))%Q)
    by (apply Qpower_0_le; apply Qlt_le_weak; exact Hnu).
  assert (Hrhop : (0 <= Qpower rho (Z.of_nat n))%Q)
    by (apply Qpower_0_le; apply Qlt_le_weak; exact Hrho).
  assert (Hm0 : (0 <= mag n)%Q) by exact (Hmag0 n).
  apply Qle_to_QleT'.
  apply (Qle_trans (sl12_dval_pi xpi (A n) (B n))
    (Qpower nu (Z.of_nat n) * Qpower rho (Z.of_nat n))%Q
    (Qpower (nu * rho)%Q (Z.of_nat n))).
  - apply (Qle_trans (sl12_dval_pi xpi (A n) (B n))
      (qfac n * mag n)%Q
      (Qpower nu (Z.of_nat n) * Qpower rho (Z.of_nat n))%Q).
    + exact Hs.
    + apply (Qle_trans (qfac n * mag n)%Q
        (Qpower nu (Z.of_nat n) * mag n)%Q
        (Qpower nu (Z.of_nat n) * Qpower rho (Z.of_nat n))%Q).
      * apply Qmult_le_compat_r; [exact Hqf' | exact Hm0].
      * rewrite (Qmult_comm (Qpower nu (Z.of_nat n)) (mag n)).
        rewrite (Qmult_comm (Qpower nu (Z.of_nat n)) (Qpower rho (Z.of_nat n))).
        apply Qmult_le_compat_r; [exact Hmag' | exact Hnup].
  - rewrite <- (qeqT_imp_qeq _ _ (sl12_w2_qpower_mul_alg nu rho n Hnu Hrho)).
    apply Qle_refl.
Defined.

(* the flagship discharge chain: the two certificate inputs plus the    *)
(* budget band (nu*rho <= 1/4) discharge the (B) Hval-direct live       *)
(* consumption face at the anchor carrier, through the landed band-end  *)
(* bridge sl12_decay_hval_direct. The certificate inputs themselves     *)
(* remain the named supply debts (see the Source route note above).     *)
Lemma sl12_w2_hval_from_certs :
  forall (xpi : Q) (A B : nat -> Z) (qfac mag : nat -> Q) (nu rho : Q),
  (forall n : nat,
    S02_CauchyComplete.QleT' (sl12_dval_pi xpi (A n) (B n))
      (qfac n * mag n)%Q) ->
  (forall n : nat, (0 <= qfac n)%Q) ->
  (forall n : nat, (0 <= mag n)%Q) ->
  (0 < nu)%Q -> (0 < rho)%Q ->
  (forall n : nat,
    S02_CauchyComplete.QleT' (qfac n) (Qpower nu (Z.of_nat n))) ->
  (forall n : nat,
    S02_CauchyComplete.QleT' (mag n) (Qpower rho (Z.of_nat n))) ->
  S02_CauchyComplete.QleT' (nu * rho)%Q (1 # 4)%Q ->
  sl12_hval_direct_face (sl12_dval_pi xpi) A B.
Proof.
  intros xpi A B qfac mag nu rho Hsplit Hqf0 Hmag0 Hnu Hrho Hqf Hmag Hband.
  apply (sl12_decay_hval_direct xpi A B (nu * rho)%Q Hband).
  exact (sl12_w2_decay_compose xpi A B qfac mag nu rho
          Hsplit Hqf0 Hmag0 Hnu Hrho Hqf Hmag).
Defined.

(* ==== Section 2: the elementary recast bricks. ==== *)

(* the Z-level square fact (the one nonlinear atom of the brick layer). *)
Lemma sl12_w2_zsq_nonneg : forall n : Z, (0 <= n * n)%Z.
Proof.
  intros n. destruct (Z_le_gt_dec n 0) as [H | H].
  - assert (Hpos : (0 <= - n)%Z) by lia.
    pose proof (Z.mul_nonneg_nonneg (- n) (- n) Hpos Hpos) as Hm.
    rewrite Z.mul_opp_l, Z.mul_opp_r, Z.opp_involutive in Hm.
    exact Hm.
  - apply Z.mul_nonneg_nonneg; lia.
Qed.

(* square nonnegativity (the engine behind the band lemmas).            *)
Lemma sl12_w2_sq_nonneg : forall t : Q, S02_CauchyComplete.QleT' 0 (t * t)%Q.
Proof.
  intros t. destruct t as [tn td].
  apply Qle_to_QleT'. unfold Qle. cbn.
  pose proof (sl12_w2_zsq_nonneg tn) as Hz. lia.
Qed.

(* the upper-unit nonnegativity helper: x <= 1 gives 0 <= 1 - x.        *)
Lemma sl12_w2_le1_nonneg : forall x : Q, (x <= 1)%Q -> (0 <= 1 - x)%Q.
Proof.
  intros x Hx.
  pose proof (Qopp_le_compat x 1 Hx) as Hn.
  assert (H1 : ((1 + (- 1))%Q <= (1 + (- x))%Q)).
  { apply Qplus_le_compat; [apply Qle_refl | exact Hn]. }
  assert (Hz : ((1 + (- 1))%Q == 0%Q)) by ring.
  rewrite Hz in H1.
  exact H1.
Defined.

(* the flip helper: a witness of 1 - u that is nonneg certifies u <= 1. *)
Lemma sl12_w2_flip : forall z u : Q,
  z == (1 - u)%Q -> (0 <= z)%Q -> (u <= 1)%Q.
Proof.
  intros z u H H0.
  assert (Hz1 : 1%Q == z + u) by (rewrite H; ring).
  apply (Qle_trans u (u + z) 1%Q).
  - pose proof (Qplus_le_compat u u 0 z (Qle_refl u) H0) as Hs.
    rewrite Qplus_0_r in Hs. exact Hs.
  - rewrite (Qplus_comm u z). rewrite Hz1. apply Qle_refl.
Defined.

(* the AM-GM band: for nonneg A B with A+B <= 1, A*B <= (1/4)*(A+B).    *)
Lemma sl12_w2_amgm_band : forall A B : Q,
  (0 <= A)%Q -> (0 <= B)%Q -> (A + B <= 1)%Q ->
  S02_CauchyComplete.QleT' (A * B)%Q ((1 # 4)%Q * (A + B))%Q.
Proof.
  intros A B HA HB Hu1.
  assert (Hu0 : (0 <= A + B)%Q)
    by (pose proof (Qplus_le_compat 0 A 0 B HA HB) as Hp0;
        rewrite !Qplus_0_l in Hp0; exact Hp0).
  assert (Hsq : S02_CauchyComplete.QleT' 0
    (((A - B) * (1 # 2))%Q * ((A - B) * (1 # 2)))%Q)
    by apply sl12_w2_sq_nonneg.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hsq) as Hsq'.
  apply Qle_to_QleT'.
  apply (Qle_trans (A * B)%Q
    ((A + B) * (1 # 2)%Q * ((A + B) * (1 # 2)))%Q
    ((1 # 4)%Q * (A + B))%Q).
  - (* leg1: A*B == P - S with S >= 0, hence A*B <= P (Qplus_le_r route). *)
    assert (HnegS : ((- ((A - B) * (1 # 2)%Q * ((A - B) * (1 # 2)))%Q) <= 0)%Q).
    { pose proof (Qopp_le_compat 0 ((A - B) * (1 # 2)%Q * ((A - B) * (1 # 2)))%Q
                   Hsq') as Hp2.
      assert (Hz0 : (- 0)%Q == 0%Q) by ring.
      rewrite Hz0 in Hp2. exact Hp2. }
    assert (Hleg : ((A + B) * (1 # 2)%Q * ((A + B) * (1 # 2))%Q
                    - ((A - B) * (1 # 2)%Q * ((A - B) * (1 # 2)))%Q
                    <= (A + B) * (1 # 2)%Q * ((A + B) * (1 # 2)))%Q).
    { destruct (Qplus_le_r (- ((A - B) * (1 # 2)%Q * ((A - B) * (1 # 2)))%Q) 0%Q
                ((A + B) * (1 # 2)%Q * ((A + B) * (1 # 2)))%Q) as [_ Hr].
      pose proof (Hr HnegS) as Hp.
      rewrite Qplus_0_r in Hp. exact Hp. }
    assert (Hid : (A * B == (A + B) * (1 # 2)%Q * ((A + B) * (1 # 2))%Q
                   - ((A - B) * (1 # 2)%Q * ((A - B) * (1 # 2)))%Q)%Q) by ring.
    rewrite Hid. exact Hleg.
  - (* leg2: P == u*u*(1/4) with u*u <= u, hence P <= u*(1/4). *)
    assert (Hsq4 : ((A + B) * (1 # 2)%Q * ((A + B) * (1 # 2)))%Q
                   == (A + B) * (A + B) * (1 # 4)%Q) by ring.
    rewrite Hsq4.
    assert (Huu : ((A + B) * (A + B))%Q <= 1 * (A + B)%Q)
      by (apply Qmult_le_compat_r; [exact Hu1 | exact Hu0]).
    apply (Qle_trans ((A + B) * (A + B) * (1 # 4))%Q
      ((A + B) * (1 # 4))%Q ((1 # 4)%Q * (A + B))%Q).
    + apply (Qle_trans ((A + B) * (A + B) * (1 # 4))%Q
        (1 * (A + B)%Q * (1 # 4))%Q ((A + B) * (1 # 4))%Q).
      * apply Qmult_le_compat_r; [exact Huu | unfold Qle; cbn; lia].
      * rewrite Qmult_1_l. apply Qle_refl.
    + rewrite (Qmult_comm (1 # 4)%Q (A + B)). apply Qle_refl.
Defined.

(* the cross term band: A := x*(1-y) plus B := y*(1-x) is at most       *)
(* 1 - x*y on the unit square (the complement square is nonneg).        *)
Lemma sl12_w2_sum_le_denom : forall x y : Q,
  (0 <= x)%Q -> (x <= 1)%Q -> (0 <= y)%Q -> (y <= 1)%Q ->
  (x * (1 - y)%Q + y * (1 - x)%Q <= 1 - x * y)%Q.
Proof.
  intros x y Hx0 Hx1 Hy0 Hy1.
  pose proof (sl12_w2_le1_nonneg x Hx1) as HxN.
  pose proof (sl12_w2_le1_nonneg y Hy1) as HyN.
  assert (Hc : (0 <= (1 - x)%Q * (1 - y))%Q)
    by (apply Qmult_le_0_compat; [exact HxN | exact HyN]).
  pose proof (Qplus_le_compat (x * (1 - y)%Q + y * (1 - x))%Q
               (x * (1 - y)%Q + y * (1 - x))%Q 0%Q
               ((1 - x) * (1 - y))%Q
               (Qle_refl (x * (1 - y)%Q + y * (1 - x)))%Q Hc) as Hstep.
  rewrite Qplus_0_r in Hstep.
  assert (Hid : ((1 - x * y)%Q
    == (x * (1 - y)%Q + y * (1 - x))%Q + (1 - x)%Q * (1 - y)%Q)) by ring.
  apply (Qle_trans (x * (1 - y)%Q + y * (1 - x))%Q
    (x * (1 - y)%Q + y * (1 - x)%Q + (1 - x)%Q * (1 - y))%Q
    (1 - x * y)%Q).
  - exact Hstep.
  - rewrite Hid. apply Qle_refl.
Defined.

(* the quarter band: x in the unit interval squeezes x*(1-x) under 1/4. *)
Lemma sl12_w2_quarter_band : forall x : Q,
  (0 <= x)%Q -> (x <= 1)%Q ->
  S02_CauchyComplete.QleT' (x * (1 - x))%Q (1 # 4)%Q.
Proof.
  intros x Hx0 Hx1.
  pose proof (sl12_w2_sq_nonneg (2 * x - 1)%Q) as Hs.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hs) as Hs'.
  assert (Hp : (0 <= ((2 * x - 1)%Q * (2 * x - 1)%Q * (1 # 4)%Q)%Q)).
  { apply Qmult_le_0_compat; [exact Hs' | unfold Qle; cbn; lia]. }
  assert (Hid : (1 # 4)%Q
    == x * (1 - x)%Q + ((2 * x - 1)%Q * (2 * x - 1)%Q * (1 # 4)%Q)%Q) by ring.
  apply Qle_to_QleT'. rewrite Hid.
  pose proof (Qplus_le_compat (x * (1 - x)%Q) (x * (1 - x)%Q) 0%Q
    ((2 * x - 1)%Q * (2 * x - 1)%Q * (1 # 4)%Q)
    (Qle_refl (x * (1 - x)%Q)) Hp) as Hstep.
  rewrite Qplus_0_r in Hstep. exact Hstep.
Defined.

(* the kernel numerator band on the unit square, in the pointwise       *)
(* division-free integrand form: the geometric-family kernel numerator  *)
(* N = x(1-x)y(1-y) stays under band * denominator (1/4)*(1-xy), i.e.   *)
(* the pointwise integrand N/(1-xy) stays under 1/4 on the unit square. *)
(* Route: factor N = A*B with A := x(1-y), B := y(1-x); the AM-GM band  *)
(* gives A*B <= (1/4)*(A+B); the cross-term band gives A+B <= 1-xy;     *)
(* monotonicity in the positive factor (1/4) composes the chain.        *)
Lemma sl12_w2_kernel_num_band : forall x y : Q,
  (0 <= x)%Q -> (x <= 1)%Q -> (0 <= y)%Q -> (y <= 1)%Q ->
  S02_CauchyComplete.QleT' (x * (1 - x)%Q * (y * (1 - y)))%Q
    ((1 # 4)%Q * (1 - x * y))%Q.
Proof.
  intros x y Hx0 Hx1 Hy0 Hy1.
  pose proof (sl12_w2_le1_nonneg x Hx1) as HxN.
  pose proof (sl12_w2_le1_nonneg y Hy1) as HyN.
  assert (HA0 : (0 <= x * (1 - y))%Q)
    by (apply Qmult_le_0_compat; [exact Hx0 | exact HyN]).
  assert (HB0 : (0 <= y * (1 - x))%Q)
    by (apply Qmult_le_0_compat; [exact Hy0 | exact HxN]).
  (* u := A+B <= 1: 1 - u == (1-x)*(1-y) + x*y, both terms nonneg.       *)
  assert (Hid2 : (((1 - x)%Q * (1 - y)%Q + x * y)%Q
                 == (1 - (x * (1 - y)%Q + y * (1 - x)))%Q)) by ring.
  assert (Hc2 : (0 + 0 <= (1 - x)%Q * (1 - y)%Q + x * y)%Q).
  { apply Qplus_le_compat;
      [apply Qmult_le_0_compat; [exact HxN | exact HyN]
      |apply Qmult_le_0_compat; [exact Hx0 | exact Hy0]]. }
  rewrite !Qplus_0_l in Hc2.
  assert (Hu1 : (x * (1 - y)%Q + y * (1 - x) <= 1)%Q)
    by (apply (sl12_w2_flip ((1 - x)%Q * (1 - y)%Q + x * y)
                 (x * (1 - y)%Q + y * (1 - x)) Hid2 Hc2)).
  (* the AM-GM band at A, B. *)
  pose proof (sl12_w2_amgm_band (x * (1 - y))%Q (y * (1 - x))%Q
                HA0 HB0 Hu1) as Ham.
  pose proof (sl12_w2_sum_le_denom x y Hx0 Hx1 Hy0 Hy1) as Hsum.
  (* compose: N == A*B <= (1/4)*(A+B) <= (1/4)*(1-xy). *)
  assert (Hfac : ((x * (1 - x)%Q * (y * (1 - y))%Q)
                 == (x * (1 - y))%Q * (y * (1 - x))%Q)) by ring.
  apply Qle_to_QleT'.
  rewrite Hfac.
  apply (Qle_trans ((x * (1 - y))%Q * (y * (1 - x)))%Q
    ((1 # 4)%Q * (x * (1 - y)%Q + y * (1 - x)))%Q
    ((1 # 4)%Q * (1 - x * y))%Q).
  - pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Ham) as Ham'.
    exact Ham'.
  - rewrite (Qmult_comm (1 # 4)%Q (x * (1 - y)%Q + y * (1 - x))).
    rewrite (Qmult_comm (1 # 4)%Q (1 - x * y)).
    apply Qmult_le_compat_r; [exact Hsum | unfold Qle; cbn; lia].
Defined.

(* ==== Section 3: the geometric tail brick (plain-Q engine). ==== *)

Fixpoint sl12_w2_gpow (r : Q) (m : nat) : Q :=
  match m with
  | O => 1%Q
  | S k => sl12_w2_gpow r k * r
  end.

Fixpoint sl12_w2_geo_sum (r : Q) (m : nat) : Q :=
  match m with
  | O => 0%Q
  | S k => sl12_w2_geo_sum r k + sl12_w2_gpow r k
  end.

(* the telescoping identity: (1-r) * sum_{k<m} r^k == 1 - r^m (plain Q  *)
(* multiplication world; no Qpower lemmas needed).                      *)
Lemma sl12_w2_geo_tail : forall (r : Q) (m : nat),
  ((1 - r)%Q * sl12_w2_geo_sum r m == 1 - sl12_w2_gpow r m)%Q.
Proof.
  intros r m. induction m as [|k IH].
  - cbn. ring.
  - cbn [sl12_w2_geo_sum sl12_w2_gpow].
    assert (Hd : ((1 - r)%Q * (sl12_w2_geo_sum r k + sl12_w2_gpow r k)%Q
                  == (1 - r)%Q * sl12_w2_geo_sum r k
                  + (1 - r)%Q * sl12_w2_gpow r k)%Q) by ring.
    rewrite Hd. rewrite IH. ring.
Defined.

(* the bridge to the tree power vocabulary at positive rates.           *)
Lemma sl12_w2_gpow_qpower : forall (r : Q) (m : nat),
  (0 < r)%Q ->
  S02_CauchyComplete.QeqT (sl12_w2_gpow r m) (Qpower r (Z.of_nat m)).
Proof.
  intros r m Hr.
  assert (Hr0 : ~ r == 0)
    by (intro Hc; exact (Qlt_not_eq 0 r Hr (Qeq_sym r 0 Hc))).
  induction m as [|k IH].
  - cbn [sl12_w2_gpow]. cbn [Z.of_nat]. apply qeq_imp_qeqT.
    rewrite Qpower_0_r. apply Qeq_refl.
  - cbn [sl12_w2_gpow].
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    apply qeq_imp_qeqT.
    rewrite (Qpower_plus r (Z.of_nat k) 1%Z Hr0). rewrite Qpower_1_r.
    rewrite (qeqT_imp_qeq _ _ IH). apply Qeq_refl.
Defined.

(* ==== Section 4: head-side measurement anchors. ==== *)

(* The head-band ratio at the pinned anchor, n := the frozen-table       *)
(* index: ratio n := dval(xpi; A n, B n) * epos(2n), the (B) Hval-direct *)
(* left-hand side. First-hand vm_compute measurements (probe rounds in   *)
(* the seat receipt; no cited figure retyped). Readouts: the ratio sits  *)
(* at 2.84e-1 near n = 5 and drops to the 1e-12 tail band; the tail is   *)
(* NOT monotone (the ratio dips at index 39 below index 40, and index 40 *)
(* sits below index 38). The value 5.907e-12 at index 40 matches the     *)
(* landed carrier's worst-margin note first-hand.                        *)
Definition sl12_w2_ratio (n : nat) : Q :=
  sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A n) (planb3_g1_B n)
    * piu_mu_epos (2%nat * n).

(* the tail dip: the ratio rises from index 39 to index 40. *)
Example sl12_w2_ratio_40_gt_39 :
  piu_mu_QltT (sl12_w2_ratio 39%nat) (sl12_w2_ratio 40%nat).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

(* the tail is not monotone: index 40 stays below index 38. *)
Example sl12_w2_ratio_38_gt_40 :
  piu_mu_QltT (sl12_w2_ratio 40%nat) (sl12_w2_ratio 38%nat).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

(* the saturation value at index 40, read out to four significant       *)
(* digits (5.907e-12, machine-certified window). *)
Example sl12_w2_ratio_40_window_lo :
  piu_mu_QltT (5907 # 1000000000000000)%Q (sl12_w2_ratio 40%nat).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_w2_ratio_40_window_hi :
  piu_mu_QltT (sl12_w2_ratio 40%nat) (5908 # 1000000000000000)%Q.
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

(* ==== Section 5: assumption audit. ==== *)

Print Assumptions sl12_w2_qpower_mul_alg.
Print Assumptions sl12_w2_decay_compose.
Print Assumptions sl12_w2_hval_from_certs.
Print Assumptions sl12_w2_zsq_nonneg.
Print Assumptions sl12_w2_sq_nonneg.
Print Assumptions sl12_w2_le1_nonneg.
Print Assumptions sl12_w2_flip.
Print Assumptions sl12_w2_amgm_band.
Print Assumptions sl12_w2_sum_le_denom.
Print Assumptions sl12_w2_quarter_band.
Print Assumptions sl12_w2_kernel_num_band.
Print Assumptions sl12_w2_geo_tail.
Print Assumptions sl12_w2_gpow_qpower.
Print Assumptions sl12_w2_ratio.
Print Assumptions sl12_w2_ratio_40_gt_39.
Print Assumptions sl12_w2_ratio_38_gt_40.
Print Assumptions sl12_w2_ratio_40_window_lo.
Print Assumptions sl12_w2_ratio_40_window_hi.
