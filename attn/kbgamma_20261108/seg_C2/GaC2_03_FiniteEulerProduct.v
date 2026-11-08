(* ConstructiveWorld-Main - the finite Euler product identity on the pair
   carrier, finalized prime-table form. *)
(** * GaC2_03_FiniteEulerProduct: the finite Euler product identity.
    Mission.  The finite Euler product main identity on the pair
      carrier, finalized prime-table form:
      eprod (pen_primes_upto N) (K_p) s = dsumCx (dpow s)
      (hl_lcm_upto N), i.e. prod_{p <= N} (sum_{k=0..K_p} p^{-k s}) =
      sum_{n | M_N} n^{-s},  M_N := hl_lcm_upto N,  K_p := plm_v p M_N
      ([fin_euler_prod_eq_dsum]).  Route M1: eprod = dsum(prodf_pow)
      by the prime-list head-peeling induction ([eprod_eq_dsum]; head
      prime fresh: [prime_list_fresh] via [plm_prime_dvd_mul] with the
      tree's Gauss face [plm_gauss]; the K-descent [dsum_pow_split]
      consumes the _f leaf's [dsum_peel_fresh] through the bridge
      [dpow_dfun], the stem's match-dpow and the _f witness-parametric
      dpow being the same match body).  Route M2:
      [prodf_pow_eq_hl_lcm] by [pr_lcm_eq_decomp] + [hl_id_eq] (with
      [plm_v]/[pr_mod0_dvd] faces underneath).  The specialization
      face: every 1 <= n <= N divides M_N ([hl_lcm_divide_all]), so
      [c_zeta_part] is the divisor sum cut at N ([c_zeta_part_cxsum]);
      [R_N] is the smooth tail and both the add face
      [zeta_part_add_R_N] and the sub face [zeta_part_sub_dsum] are
      supplied (the C2.04 consumption carrier).
    Dependencies.  Stdlib [Arith.Arith], [List] (+ [ListNotations]),
      [Lia].  Requires [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [CxRealPairCore]/[CxRealPairExpLog], [abl_Pr_core_01],
      [abl_Pr_lcmdecomp_04], [abl_Pr_lcm_eq], [abl_Pr_enum_02],
      [HansonLcm], [GaC2_01_DirichletPartialSum], [GaC2_03_a],
      [GaC2_03_b], [GaC2_03_c_eq_shim], [GaC2_03_d], [GaC2_03_e], and
      [GaC2_03_f] (required without Import; the stem redefines the
      witness-free match carrier names) of this development.
    References.  Card C2.03, drafts_C2.md C2.03; mathlib
      [EulerProduct/Basic.lean]
      prod_primesBelow_tsum_eq_tsum_smoothNumbers as the statement-face
      precedent (alignment only, absorption coeff 0.35, zero
      transplant).
    Constructivity.  Every named construction is carried by [Set]; the
      n = 0 branch of [dpow] is inert (divisor-sum indices are at
      least 1); no vm_compute in the stem (numeric certificates in the
      _cert face); every proof closes under the global context;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_FiniteEulerProduct.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98
      -AllowG3 -GearForce 0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.
Require Import abl_Pr_enum_02.
Require Import HansonLcm.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_03_a.
Require Import GaC2_03_b.
Require Import GaC2_03_c_eq_shim.
Require Import GaC2_03_d.
Require Import GaC2_03_e.
(* required without Import: the stem re-uses the witness-free match-carrier *)
(* names dpow / eblock; _f faces are referenced qualified.                  *)
Require GaC2_03_f.
From Stdlib Require Import Arith.Arith List.
Import ListNotations.
From Stdlib Require Import Lia.

Section FiniteEulerProduct.

(* The C2.01 premise family; the downstream consumer supplies nat_real_pos. *)
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).

(* ==== Section 1. The term, the geometric block, the block product ==== *)

(* The witness-free match carrier: identical body to the _f leaf's dfun,    *)
(* so dpow s = GaC2_03_f.dfun Hnpos s holds by pure conversion (the bridge  *)
(* to the _f peel faces; every divisor-sum index is >= 1, so the n = 0      *)
(* branch is inert).                                                        *)
Definition dpow (s : Cx) (n : nat) : Cx :=
  match n with
  | O => c_zero
  | S m => c_powq Hnpos (S m) (NatLe_one_S m) s
  end.

Lemma dpow_dfun : forall s : Cx, dpow s = GaC2_03_f.dfun Hnpos s.
Proof. reflexivity. Qed.

(* The multiplicative term law: destruct a and b first -- the product index *)
(* S a' * S b' is then constructor-headed (S-materialized), the stem match  *)
(* fires, and the closing shot is exactly c_powq_mult_law_gen with the      *)
(* NatLe_one_S witness at the converted index (kernel conversion; the       *)
(* probe-verified witness choice, zero index abstraction).                  *)
Lemma dpow_mult_law : forall (a b : nat) (s : Cx), (1 <= a)%nat -> (1 <= b)%nat ->
  c_eq (dpow s (a * b)) (c_mult (dpow s a) (dpow s b)).
Proof.
  intros a b s Ha Hb.
  destruct a as [|a']; [ lia | ].
  destruct b as [|b']; [ lia | ].
  exact (c_powq_mult_law_gen Hnpos (S a') (S b') (NatLe_one_S a') (NatLe_one_S b')
           (NatLe_one_S (b' + a' * S b')) s).
Qed.

(* 1^{-s} = 1 (re-exported from the _f leaf through the carrier bridge).    *)
Lemma dpow_one : forall s : Cx, c_eq (dpow s 1) c_one.
Proof. intro s. exact (GaC2_03_f.dpow_one Hnpos s). Qed.

(* The geometric block eblock p K s = p^{-s} + ... + p^{-K s} plus the      *)
(* empty-sum unit (bottom recursion; pairs with the K-descent).             *)
Fixpoint eblock (p K : nat) (s : Cx) : Cx :=
  match K with
  | O => c_one
  | S K' => c_plus (c_mult (dpow s p) (eblock p K' s)) c_one
  end.

Lemma eblock_S : forall (p K : nat) (s : Cx),
  c_eq (eblock p (S K) s) (c_plus (c_mult (dpow s p) (eblock p K s)) c_one).
Proof. intros p K s. apply c_eq_refl. Qed.

Fixpoint eprod (l : list nat) (K : nat -> nat) (s : Cx) : Cx :=
  match l with
  | nil => c_one
  | p :: l' => c_mult (eblock p (K p) s) (eprod l' K s)
  end.

Lemma eprod_cons : forall (K : nat -> nat) (p : nat) (l : list nat) (s : Cx),
  c_eq (eprod (p :: l) K s) (c_mult (eblock p (K p) s) (eprod l K s)).
Proof. intros K p l s. apply c_eq_refl. Qed.

(* ==== Section 2. cxsum glue faces ==== *)

Lemma cxsum_add : forall (A C : nat -> Cx) (B : nat),
  c_eq (cxsum (fun d => c_plus (A d) (C d)) B)
       (c_plus (cxsum A B) (cxsum C B)).
Proof. intros A C B. exact (GaC2_03_f.cxsum_add A C B). Qed.

Lemma cxsum_range_eq : forall (g : nat -> Cx) (E1 E2 : nat), E1 = E2 ->
  c_eq (cxsum g E1) (cxsum g E2).
Proof. intros g E1 E2 HE. rewrite HE. apply c_eq_refl. Qed.

Lemma cxsum_split_le : forall (g : nat -> Cx) (B E : nat), (B <= E)%nat ->
  c_eq (cxsum g E)
       (c_plus (cxsum g B)
               (cxsum (fun d => if Nat.ltb B d then g d else c_zero) E)).
Proof.
  intros g B E HBE.
  apply (c_eq_trans _ (cxsum g (B + (E - B)))).
  - apply cxsum_range_eq. lia.
  - apply (c_eq_trans _
             (c_plus (cxsum g B)
                     (cxsum (fun d => if Nat.ltb B d then g d else c_zero)
                            (B + (E - B))))).
    + apply cxsum_range_ext.
    + apply c_plus_congr; [ apply c_eq_refl | apply cxsum_range_eq; lia ].
Qed.

(* ==== Section 3. The prime-table product and the freshness face ==== *)

(* prodf_pow K l = prod_{p in l} p^{K p} (nil = 1). *)
Fixpoint prodf_pow (K : nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => 1
  | p :: l' => Nat.pow p (K p) * prodf_pow K l'
  end.

Lemma prodf_pow_cons : forall (K : nat -> nat) (p : nat) (l : list nat),
  prodf_pow K (p :: l) = Nat.pow p (K p) * prodf_pow K l.
Proof. reflexivity. Qed.

Lemma prodf_pow_ge1 : forall (K : nat -> nat) (l : list nat),
  (forall y : nat, In y l -> (1 <= y)%nat) -> (1 <= prodf_pow K l)%nat.
Proof.
  intros K l. induction l as [|p l' IH]; intros Hall.
  - apply Nat.le_refl.
  - cbn [prodf_pow].
    assert (Hp1 : (1 <= p)%nat) by (apply Hall; apply in_eq).
    assert (Hp0 : (p <> 0)%nat) by lia.
    assert (Hpow : (1 <= Nat.pow p (K p))%nat) by (apply pow_ge1; exact Hp0).
    assert (Hdvd : Nat.divide (Nat.pow p (K p))
                     (Nat.pow p (K p) * prodf_pow K l')).
    { exists (prodf_pow K l'). rewrite Nat.mul_comm. reflexivity. }
    assert (HB : (1 <= prodf_pow K l')%nat).
    { apply IH. intros y Hy. apply Hall. apply in_cons. exact Hy. }
    assert (HMP : (0 < Nat.pow p (K p) * prodf_pow K l')%nat).
    { apply (Nat.le_trans 1 (1 * 1)%nat).
      - rewrite Nat.mul_1_l. apply Nat.le_refl.
      - apply Nat.mul_le_mono; [ exact Hpow | exact HB ]. }
    apply (Nat.le_trans 1 (Nat.pow p (K p))
             (Nat.pow p (K p) * prodf_pow K l')).
    + exact Hpow.
    + apply Nat.divide_pos_le; [ exact HMP | exact Hdvd ].
Qed.

(* The head prime of a NoDup prime list is fresh for the tail's prime       *)
(* powers (Euclid descent: plm_prime_dvd_mul, with the tree's Gauss face    *)
(* plm_gauss inside).                                                       *)
Lemma prime_list_fresh : forall (l : list nat) (K : nat -> nat) (p0 : nat),
  NoDup l -> (forall y : nat, In y l -> pr_prime y) -> pr_prime p0 ->
  (In p0 l -> False) -> (Nat.divide p0 (prodf_pow K l) -> False).
Proof.
  intros l. induction l as [|q l' IH]; intros K p0 Hnd Hl Hp0 Hin Hdvd.
  - cbn [prodf_pow] in Hdvd. destruct Hdvd as [z Hz].
    destruct Hp0 as [Hp02 _].
    destruct z as [|z'].
    + cbn [Nat.mul] in Hz. discriminate Hz.
    + cbn [Nat.mul] in Hz. lia.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnq Hnd'].
    assert (Hl' : forall y : nat, In y l' -> pr_prime y).
    { intros y Hy. apply Hl. apply in_cons. exact Hy. }
    assert (Hin' : (In p0 l' -> False)).
    { intro Hx. apply Hin. apply in_cons. exact Hx. }
    assert (Hqp : pr_prime q) by (apply Hl; apply in_eq).
    destruct (plm_prime_dvd_mul p0 (Nat.pow q (K q)) (prodf_pow K l') Hp0 Hdvd)
      as [Hd1 | Hd2].
    + destruct (Nat.eq_dec p0 q) as [E|NE].
      -- exfalso. apply Hin. rewrite E. apply in_eq.
      -- assert (Hno : forall k : nat, (Nat.divide p0 (Nat.pow q k) -> False)).
         { intro k. induction k as [|k' IHk]; intro Hk.
           - cbn [Nat.pow] in Hk. destruct Hk as [z Hz].
             destruct Hp0 as [Hp02 _].
             destruct z as [|z'].
             ++ cbn [Nat.mul] in Hz. discriminate Hz.
             ++ cbn [Nat.mul] in Hz. lia.
           - cbn [Nat.pow] in Hk.
             destruct (plm_prime_dvd_mul p0 q (Nat.pow q k') Hp0 Hk)
               as [Ha | Hb].
             ++ destruct Hp0 as [Hp02 Hallp].
                assert (Hq0 : (0 < q)%nat).
                { destruct Hqp as [Hq2 _].
                  exact (Nat.le_trans 1 2 q (le_S 1 1 (le_n 1)) Hq2). }
                assert (Hp0q : (p0 <= q)%nat).
                { apply Nat.divide_pos_le; [ exact Hq0 | exact Ha ]. }
                assert (Hlt : (p0 < q)%nat).
                { destruct (proj1 (Nat.lt_eq_cases p0 q) Hp0q) as [Hlt | Heq].
                  - exact Hlt.
                  - exfalso. apply NE. exact Heq. }
                destruct Hqp as [Hq2 Hallq].
                apply (Hallq p0); [ exact Hp02 | exact Hlt | exact Ha ].
             ++ exact (IHk Hb). }
         apply (Hno (K q) Hd1).
    + exact (IH K p0 Hnd' Hl' Hp0 Hin' Hd2).
Qed.

(* ==== Section 4. The divisor-sum K-descent (through the _f peel) ==== *)

(* The one-step peel at a fresh prime: D(p^{S K} * M')                      *)
(*   = dpow p * D(p^K * M') + D(M').                                        *)
Lemma dsum_step_fresh : forall (p K M' : nat) (s : Cx),
  pr_prime p -> (2 <= p)%nat -> (1 <= M')%nat ->
  (Nat.divide p M' -> False) ->
  c_eq (dsumCx (dpow s) (Nat.pow p (S K) * M'))
       (c_plus (c_mult (dpow s p) (dsumCx (dpow s) (Nat.pow p K * M')))
               (dsumCx (dpow s) M')).
Proof.
  intros p K M' s Hp Hp2 HM' Hpm.
  destruct p as [|p']; [ exfalso; apply (Nat.nle_succ_0 1 Hp2) | ].
  rewrite (dpow_dfun s).
  exact (GaC2_03_f.dsum_peel_fresh Hnpos (S p') K M' s Hp Hp2
           (NatLe_one_S p') HM' Hpm).
Qed.

(* The K-fold block: D(p^K * M) = eblock(p,K) * D(M) at a fresh prime.      *)
Lemma dsum_pow_split : forall (p K M : nat) (s : Cx),
  pr_prime p -> (2 <= p)%nat -> (1 <= M)%nat ->
  (Nat.divide p M -> False) ->
  c_eq (dsumCx (dpow s) (Nat.pow p K * M))
       (c_mult (eblock p K s) (dsumCx (dpow s) M)).
Proof.
  intros p K. induction K as [|K IH]; intros M s Hp Hp2 HM Hpm.
  - rewrite Nat.pow_0_r, Nat.mul_1_l.
    apply (c_eq_trans _ (c_mult c_one (dsumCx (dpow s) M))).
    + apply c_eq_sym. apply cx_mult_one_l.
    + apply c_eq_refl.
  - apply (c_eq_trans _
             (c_plus (c_mult (dpow s p) (dsumCx (dpow s) (Nat.pow p K * M)))
                     (dsumCx (dpow s) M))).
    + apply dsum_step_fresh; assumption.
    + apply (c_eq_trans _
               (c_plus (c_mult (c_mult (dpow s p) (eblock p K s))
                          (dsumCx (dpow s) M))
                       (c_mult c_one (dsumCx (dpow s) M)))).
      * apply c_plus_congr.
        -- apply (c_eq_trans _
                    (c_mult (dpow s p)
                       (c_mult (eblock p K s) (dsumCx (dpow s) M)))).
           ++ apply c_mult_congr; [ apply c_eq_refl | ].
              ** exact (IH M s Hp Hp2 HM Hpm).
           ++ apply c_mult_assoc.
        -- apply c_eq_sym. apply cx_mult_one_l.
      * apply c_eq_sym. apply cx_distrib_r.
Qed.

(* ==== Section 5. The prime-table induction body and the main identity ==== *)

Lemma eprod_eq_dsum : forall (l : list nat) (K : nat -> nat) (s : Cx),
  NoDup l -> (forall x : nat, In x l -> pr_prime x) ->
  c_eq (eprod l K s) (dsumCx (dpow s) (prodf_pow K l)).
Proof.
  intros l. induction l as [|p0 l' IH]; intros Kq s Hnd Hl.
  - apply (c_eq_trans _ (GaC2_03_f.dfun Hnpos s 1)).
    + apply c_eq_sym. exact (GaC2_03_f.dpow_one Hnpos s).
    + apply c_eq_sym. exact (GaC2_03_f.dsum_one Hnpos s).
  - assert (Hp0 : pr_prime p0) by (apply Hl; cbn [In]; apply in_eq).
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnx Hnd'].
    assert (H2p0 : (2 <= p0)%nat) by (destruct Hp0 as [H2 _]; exact H2).
    assert (Hl' : forall y : nat, In y l' -> pr_prime y).
    { intros y Hy. apply Hl. apply in_cons. exact Hy. }
    assert (HM'1 : (1 <= prodf_pow Kq l')%nat).
    { apply prodf_pow_ge1. intros y Hy.
      exact (Nat.le_trans 1 2 y (le_S 1 1 (le_n 1)) (proj1 (Hl' y Hy))). }
    assert (Hfresh : (Nat.divide p0 (prodf_pow Kq l') -> False)).
    { apply (prime_list_fresh l' Kq p0 Hnd' Hl' Hp0).
      intro Hin. apply Hnx. exact Hin. }
    apply (c_eq_trans _ (c_mult (eblock p0 (Kq p0) s) (eprod l' Kq s))).
    * apply eprod_cons.
    * apply (c_eq_trans _
               (c_mult (eblock p0 (Kq p0) s)
                       (dsumCx (dpow s) (prodf_pow Kq l')))).
      -- apply c_mult_congr; [ apply c_eq_refl | exact (IH Kq s Hnd' Hl') ].
      -- rewrite prodf_pow_cons.
         apply c_eq_sym. apply dsum_pow_split;
             [ exact Hp0 | exact H2p0 | exact HM'1 | exact Hfresh ].
Qed.

(* The fold bridge: prodf_pow is the standard mul-fold over the mapped      *)
(* list (two distinct fixpoints, so the conversion needs list destruction). *)
Lemma prodf_pow_fold : forall (K : nat -> nat) (l : list nat),
  prodf_pow K l = fold_right Nat.mul 1 (map (fun p => Nat.pow p (K p)) l).
Proof.
  intros K l. induction l as [|p l' IH].
  - reflexivity.
  - cbn [prodf_pow map fold_right]. rewrite IH. reflexivity.
Qed.

(* M2: the lcm-table valuation is the prime-table exponent. *)
Lemma prodf_pow_eq_hl_lcm : forall N : nat,
  prodf_pow (fun p => plm_v p (hl_lcm_upto N)) (pen_primes_upto N)
  = hl_lcm_upto N.
Proof.
  intro N.
  rewrite (prodf_pow_fold (fun p => plm_v p (hl_lcm_upto N))
             (pen_primes_upto N)).
  symmetry. exact (hl_id_eq nat _ _ (pr_lcm_eq_decomp N)).
Qed.

(* The main identity: the finite Euler product, prime-table form. *)
Lemma fin_euler_prod_eq_dsum : forall (N : nat) (s : Cx),
  c_eq (eprod (pen_primes_upto N) (fun p => plm_v p (hl_lcm_upto N)) s)
       (dsumCx (dpow s) (hl_lcm_upto N)).
Proof.
  intros N s.
  apply (c_eq_trans _
           (dsumCx (dpow s)
              (prodf_pow (fun p => plm_v p (hl_lcm_upto N))
                         (pen_primes_upto N)))).
  - apply eprod_eq_dsum.
    + exact (plq_pen_nodup N).
    + intros x Hx. exact (proj1 (proj1 (pen_in_primes_upto x N) Hx)).
  - rewrite prodf_pow_eq_hl_lcm. apply c_eq_refl.
Qed.

(* ==== Section 6. The specialization face and the smooth tail ==== *)

Lemma c_zeta_part_cxsum : forall (N : nat) (s : Cx),
  c_eq (c_zeta_part Hnpos N s) (cxsum (dpow s) N).
Proof.
  intros N. induction N as [|N' IH]; intro s.
  - cbn [c_zeta_part cxsum]. apply c_eq_refl.
  - apply (c_eq_trans _ (c_plus (dpow s (S N')) (c_zeta_part Hnpos N' s))).
    + apply c_plus_comm.
    + apply c_plus_congr; [ apply c_eq_refl | exact (IH s) ].
Qed.

(* The smooth tail: the divisors of M_N beyond N. *)
Definition R_N (N : nat) (s : Cx) : Cx :=
  cxsum (fun d => if Nat.ltb N d then
                  (if dvdb d (hl_lcm_upto N) then dpow s d else c_zero)
                else c_zero) (hl_lcm_upto N).

(* The add face: D(M_N) = zeta_part N + R_N. *)
Lemma zeta_part_add_R_N : forall (N : nat) (s : Cx), (1 <= N)%nat ->
  c_eq (dsumCx (dpow s) (hl_lcm_upto N))
       (c_plus (c_zeta_part Hnpos N s) (R_N N s)).
Proof.
  intros N s HN1.
  assert (HNM : Nat.divide N (hl_lcm_upto N))
    by (apply (hl_lcm_divide_all N N); [ exact HN1 | apply Nat.le_refl ]).
  assert (HBN : (N <= hl_lcm_upto N)%nat).
  { apply (dvd_le N (hl_lcm_upto N)); [ exact HN1 | apply plq_lcm_pos | exact HNM ]. }
  apply (c_eq_trans _
           (c_plus (cxsum (fun d => if dvdb d (hl_lcm_upto N) then dpow s d
                            else c_zero) N)
                   (cxsum (fun d => if Nat.ltb N d then
                              (if dvdb d (hl_lcm_upto N) then dpow s d
                               else c_zero) else c_zero)
                          (hl_lcm_upto N)))).
  - unfold dsumCx. apply cxsum_split_le. exact HBN.
  - apply c_plus_congr.
    + apply (c_eq_trans _ (cxsum (dpow s) N)).
      * apply cxsum_ext. intros d Hd1 Hd2.
        assert (HdM : Nat.divide d (hl_lcm_upto N))
          by (apply (hl_lcm_divide_all N d); [ exact Hd1 | exact Hd2 ]).
        assert (Hdv : dvdb d (hl_lcm_upto N) = true)
          by (apply dvdb_of_divide; [ exact Hd1 | exact HdM ]).
        rewrite Hdv. apply c_eq_refl.
      * apply c_eq_sym. apply c_zeta_part_cxsum.
    + apply c_eq_refl.
Qed.

(* The sub face: R_N = D(M_N) - zeta_part N (the C2.04 tail carrier). *)
Lemma zeta_part_sub_dsum : forall (N : nat) (s : Cx), (1 <= N)%nat ->
  c_eq (R_N N s)
       (c_plus (dsumCx (dpow s) (hl_lcm_upto N))
               (c_opp (c_zeta_part Hnpos N s))).
Proof.
  intros N s HN1.
  apply (c_eq_trans _ (c_plus c_zero (R_N N s))).
  - apply c_eq_sym. apply c_plus_zero.
  - apply (c_eq_trans _
             (c_plus (c_plus (c_opp (c_zeta_part Hnpos N s))
                             (c_zeta_part Hnpos N s))
                     (R_N N s))).
    + apply c_plus_congr.
      * apply (c_eq_trans _
                 (c_plus (c_zeta_part Hnpos N s) (c_opp (c_zeta_part Hnpos N s)))).
        -- apply c_eq_sym. apply c_plus_opp.
        -- apply c_plus_comm.
      * apply c_eq_refl.
    + apply (c_eq_trans _
               (c_plus (c_opp (c_zeta_part Hnpos N s))
                       (c_plus (c_zeta_part Hnpos N s) (R_N N s)))).
      * apply c_eq_sym. apply c_plus_assoc.
      * apply (c_eq_trans _
                 (c_plus (c_opp (c_zeta_part Hnpos N s))
                         (dsumCx (dpow s) (hl_lcm_upto N)))).
        -- apply c_plus_congr.
           ++ apply c_eq_refl.
           ++ apply c_eq_sym. apply zeta_part_add_R_N. exact HN1.
        -- apply c_plus_comm.
Qed.

End FiniteEulerProduct.

(* ==== Section 7. Supply-face audit tail ==== *)

(* Named-item census of this stem:
   2 Definitions (dpow, R_N) + 3 Fixpoints (eblock, eprod, prodf_pow)
   + 20 Lemmas (dpow_dfun, dpow_mult_law, dpow_one, eblock_S, eprod_cons,
   cxsum_add, cxsum_range_eq, cxsum_split_le, prodf_pow_cons, prodf_pow_ge1,
   prime_list_fresh, dsum_step_fresh, dsum_pow_split, eprod_eq_dsum,
   prodf_pow_fold, prodf_pow_eq_hl_lcm, fin_euler_prod_eq_dsum,
   c_zeta_part_cxsum, zeta_part_add_R_N, zeta_part_sub_dsum);
   1 Section variable (Hnpos, discharged at End); zero vm_compute;
   zero assumed constants and zero abandoned proofs. *)
