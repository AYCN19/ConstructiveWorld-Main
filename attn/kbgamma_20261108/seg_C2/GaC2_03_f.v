(* ConstructiveWorld-Main - the divisor-sum induction machinery of the finite
   Euler product identity. *)
(** * GaC2_03_f: the divisor-sum peel leaf of node C2.03.
    Mission.  The divisor-sum induction machinery of the finite Euler
      product main identity: the witness-parametric term carrier
      [dpow] (n^{-s} at the stem positivity family; the NatLe 1 n
      witness is an explicit argument so products of indices never
      meet a stuck match), its unit, nonvanishing and multiplicative
      faces, the match-summand carrier [dfun] (the NatLe witness
      materializes at each positive index), the geometric block
      [eblock] (p^{-s} + ... + p^{-K s} plus the empty-sum unit), the
      divisor-sum glue (pointwise additivity of the range sum), the
      one-step peel of the divisor sum at a fresh prime
      [dsum_peel_fresh] (p-multiple reindexing half consuming
      [cxsum_reindex_mul] of the _a base leaf and [dvdb_mul_cancel] of
      the _d kernel, plus the coprime half by the Gauss descent
      [dvd_gcd_iter] of _d), and the K-fold block lemma
      [dsum_block_pow]: D(p^K * M') = eblock(p,K) * D(M'), the main
      identity's induction body.
    Dependencies.  Stdlib [Arith.Arith], [List], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [S10_KVQuantTrig] ([real_cos_one]), [CxRealPairCore]
      ([real_one_pt]), [CxRealPairExpLog] ([c_exp_zero]/
      [c_norm_sq_zero_intro]), [abl_Pr_core_01],
      [abl_Pr_lcmdecomp_04], [abl_Pr_lcm_eq],
      [GaC2_01_DirichletPartialSum] ([c_powq]/[c_powq_norm_sq]/
      [NatLe_one_S]/[c_of_real_wd]/[c_exp_wd]/[nat_real]),
      [GaC2_03_a] ([cxsum]/[dvdb]/[dsumCx]/[cxsum_reindex_mul]/
      [cxsum_scalar_l]/[dsumCx_range]), [GaC2_03_b] ([dvd_le]),
      [GaC2_03_c_eq_shim] (the [cx_eq] bounded automation tactic),
      [GaC2_03_d] ([dvd_gcd_iter]/[dvd_mul_cancel_l]/[dvd_mul_r]),
      and [GaC2_03_e] ([c_powq_mult_law_gen]/
      [cauchy_real_exp_inj]) of this development.
    References.  Card C2.03 (finite Euler identity; FTA pairing
      consumes the tree primality face), drafts_C2.md C2.03; the
      nonvanishing route follows the tree's log_inv faces (S07 weak
      trichotomy, S10 cos-one, S03 exp-positivity), zero transplant.
    Constructivity.  Every named construction is carried by [Set];
      negations are written P -> False (zero not/~ tokens); no
      vm_compute; every proof closes under the global context;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_f.v] compiles cleanly (exit 0), wrapped by
      [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce
      0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_03_a.
Require Import GaC2_03_b.
Require Import GaC2_03_c_eq_shim.
Require Import GaC2_03_d.
Require Import GaC2_03_e.
From Stdlib Require Import QArith.QArith QArith.Qabs.
(* Q_scope would swallow nat `*` (the GaC2_03_e lesson); close it right     *)
(* after the require -- only the Qeq head is consumed below.                *)
Close Scope Q_scope.
From Stdlib Require Import Arith.Arith List.
From Stdlib Require Import Lia.

Section FiniteEulerPeel.

(* The premise-parametrised positivity face of the embedding (the C2.01     *)
(* premise family).                                                         *)
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).

(* ==== Section 1. The term carrier and its faces ==== *)

(* n^{-s} at the stem's positivity family: witness-parametric (no match),   *)
(* so products of indices never meet a stuck reduction.                     *)
Definition dpow (s : Cx) (n : nat) (Hn : NatLe 1 n) : Cx :=
  c_powq Hnpos n Hn s.

(* The NatLe witness recovered from a positive divisibility test. *)
Lemma natle_of_dvdb : forall d N : nat, dvdb d N = true -> NatLe 1 d.
Proof.
  intros d N Hd. destruct d as [|d']; [ discriminate Hd | apply NatLe_one_S ].
Qed.

Lemma dpow_S : forall (s : Cx) (m : nat),
  dpow s (S m) (NatLe_one_S m) = c_powq Hnpos (S m) (NatLe_one_S m) s.
Proof. intros s m. reflexivity. Qed.

(* The unit embedding: nat_real 1 == real_one. *)
Lemma nat_real_one : real_eq (nat_real 1) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_const_proj, real_one_pt. unfold Qeq. simpl. ring.
Qed.

(* ln(nat_real 1) == 0: the right inverse (e^{ln x} == x) plus the unit     *)
(* embedding, closed by the exponential injectivity of the _e leaf.         *)
Lemma real_log_nat_one :
  real_eq (real_log (nat_real 1) (Hnpos 1 (NatLe_one_S 0))) real_zero.
Proof.
  apply cauchy_real_exp_inj.
  apply (real_eq_trans _ real_one).
  - apply (real_eq_trans _ (nat_real 1)).
    + exact (cw_log_exp_right (nat_real 1) (Hnpos 1 (NatLe_one_S 0))).
    + apply real_eq_sym. exact (nat_real_one).
  - apply real_eq_sym. exact cauchy_real_exp_zero.
Qed.

(* Small face: scaling the zero pair is the zero pair. *)
Lemma c_scale_zero : forall a : Real, c_eq (c_scale a c_zero) c_zero.
Proof.
  intros a. unfold c_scale, c_eq, cRe, cIm. split; simpl.
  - apply real_mult_zero.
  - apply real_mult_zero.
Qed.

(* 1^{-s} = 1 (the embedded-log unit face and c_exp_zero compose). *)
Lemma dpow_one : forall s : Cx, c_eq (dpow s 1 (NatLe_one_S 0)) c_one.
Proof.
  intro s.
  apply (c_eq_trans _ (c_powq Hnpos 1 (NatLe_one_S 0) s)).
  - apply c_eq_refl.
  - unfold c_powq.
    apply (c_eq_trans _
             (c_exp (c_scale (real_opp real_one)
                       (c_mult s (c_of_real real_zero))))).
    + apply c_exp_wd. apply c_scale_wd. apply c_mult_congr;
        [ apply c_eq_refl | apply c_of_real_wd ].
      exact (real_log_nat_one).
    + apply (c_eq_trans _ (c_exp (c_scale (real_opp real_one) c_zero))).
      * apply c_exp_wd. apply c_scale_wd. apply cx_mult_zero_r.
      * apply (c_eq_trans _ (c_exp c_zero)).
        -- apply c_exp_wd. apply c_scale_zero.
        -- exact (c_exp_zero).
Qed.

(* The term never vanishes: |n^{-s}|^2 = n^{-2 sig} has strictly positive   *)
(* real part (real-exponential positivity), so a zero term collapses the    *)
(* norm to zero -- contradiction.                                           *)
Lemma dpow_zero_contra : forall (s : Cx) (m : nat),
  c_eq (dpow s (S m) (NatLe_one_S m)) c_zero -> False.
Proof.
  intros s m H0.
  pose proof (c_powq_norm_sq Hnpos (S m) (NatLe_one_S m) s) as Hn.
  set (z' := real_plus (cRe s) (cRe s)).
  set (w' := real_log (nat_real (S m)) (Hnpos (S m) (NatLe_one_S m))).
  set (Q := c_of_real z').
  set (W := c_of_real w').
  set (E := c_scale (real_opp real_one) (c_mult Q W)).
  assert (Him0 : real_eq (cIm (c_mult Q W)) real_zero).
  { apply (real_eq_trans _
             (real_plus (real_mult z' real_zero) (real_mult real_zero w'))).
    - exact (real_eq_refl (real_plus (real_mult z' real_zero)
               (real_mult real_zero w'))).
    - apply (real_eq_trans _ (real_plus real_zero real_zero)).
      + exact (RealSetoid.real_eq_plus_compat (real_mult z' real_zero)
                 (real_mult real_zero w') real_zero real_zero
                 (real_mult_zero z')
                 (real_eq_trans (real_mult real_zero w')
                    (real_mult w' real_zero) real_zero
                    (real_mult_comm real_zero w')
                    (real_mult_zero w'))).
      + exact (real_plus_zero real_zero). }
  assert (Him : real_eq (cIm E) real_zero).
  { apply (real_eq_trans _ (real_mult (real_opp real_one) real_zero)).
    - exact (RealSetoid.real_eq_mult_compat (real_opp real_one)
               (cIm (c_mult Q W)) (real_opp real_one) real_zero
               (real_eq_refl (real_opp real_one)) Him0).
    - exact (real_mult_zero (real_opp real_one)). }
  assert (Hpos : real_lt real_zero
           (cRe (c_powq Hnpos (S m) (NatLe_one_S m) Q))).
  { change (cRe (c_powq Hnpos (S m) (NatLe_one_S m) Q))
      with (real_mult (cauchy_real_exp (cRe E)) (cauchy_real_cos (cIm E))).
    apply (real_lt_eq_lt real_zero (cauchy_real_exp (cRe E))).
    - exact (cauchy_real_exp_pos (cRe E)).
    - apply (real_eq_trans _
               (real_mult (cauchy_real_exp (cRe E)) real_one)).
      + apply real_eq_sym. exact (real_mult_one (cauchy_real_exp (cRe E))).
      + exact (RealSetoid.real_eq_mult_compat (cauchy_real_exp (cRe E))
                 real_one (cauchy_real_exp (cRe E))
                 (cauchy_real_cos (cIm E)) (real_eq_refl (cauchy_real_exp (cRe E)))
                 (real_eq_sym _ _
                    (real_eq_trans (cauchy_real_cos (cIm E))
                                 (cauchy_real_cos real_zero) real_one
                                 (real_cos_eq_compat (cIm E) real_zero Him)
                                 real_cos_one))). }
  (* the term's norm equals the positive real part and collapses to zero *)
  assert (Hn0 : real_eq (c_norm_sq (c_powq Hnpos (S m) (NatLe_one_S m) s))
                        real_zero).
  { apply (real_eq_trans _ (c_norm_sq c_zero)).
    - exact (cxrel_norm_sq _ _ H0).
    - exact (c_norm_sq_zero_intro c_zero (c_eq_refl c_zero)). }
  assert (Hne : real_eq real_zero
                  (cRe (c_powq Hnpos (S m) (NatLe_one_S m) Q)) -> False).
  { intro Hcon.
    destruct (real_lt_not_eq real_zero
             (cRe (c_powq Hnpos (S m) (NatLe_one_S m) Q)) Hpos Hcon). }
  apply Hne.
  apply (real_eq_trans _ (c_norm_sq (c_powq Hnpos (S m) (NatLe_one_S m) s))).
  - apply real_eq_sym. exact Hn0.
  - exact Hn.
Qed.

(* The multiplicative face of the term (from the _e leaf's gen form). *)
Lemma dpow_mult_law : forall (a b : nat) (Ha : NatLe 1 a) (Hb : NatLe 1 b)
    (s : Cx),
  c_eq (dpow s (a * b) (natle_mul a b Ha Hb))
       (c_mult (dpow s a Ha) (dpow s b Hb)).
Proof.
  intros a b Ha Hb s.
  exact (c_powq_mult_law_gen Hnpos a b Ha Hb (natle_mul a b Ha Hb) s).
Qed.

(* ==== Section 2. The divisor-sum carrier and the geometric block ==== *)

(* The divisor-summand: the match materializes the NatLe witness at each    *)
(* positive index (the n = 0 branch is inert: dvdb is false at 0).          *)
Definition dfun (s : Cx) : nat -> Cx :=
  fun d => match d with
           | O => c_zero
           | S m => dpow s (S m) (NatLe_one_S m)
           end.

Lemma dfun_S : forall (s : Cx) (m : nat),
  dfun s (S m) = dpow s (S m) (NatLe_one_S m).
Proof. intros s m. reflexivity. Qed.

(* eblock p Hp K s = p^{-s} + ... + p^{-K s} plus the empty-sum unit       *)
(* (bottom recursion, pairing with the divisor-sum peel                    *)
(* D_{K+1} = dpow p * D_K + D_0).                                          *)
Fixpoint eblock (p : nat) (Hp : NatLe 1 p) (K : nat) (s : Cx) : Cx :=
  match K with
  | O => c_one
  | S K' => c_plus (c_mult (dpow s p Hp) (eblock p Hp K' s)) c_one
  end.

Lemma eblock_S : forall (p : nat) (Hp : NatLe 1 p) (K : nat) (s : Cx),
  c_eq (eblock p Hp (S K) s)
       (c_plus (c_mult (dpow s p Hp) (eblock p Hp K s)) c_one).
Proof. intros p Hp K s. apply c_eq_refl. Qed.

(* ==== Section 3. The divisor-sum glue ==== *)

(* Pointwise additivity of the range sum. *)
Lemma cxsum_add : forall (A C : nat -> Cx) (B : nat),
  c_eq (cxsum (fun d => c_plus (A d) (C d)) B)
       (c_plus (cxsum A B) (cxsum C B)).
Proof.
  intros A C B. induction B as [|B' IH].
  - cbn [cxsum]. apply c_eq_sym. apply cx_plus_zero_l.
  - cbn [cxsum].
    apply (c_eq_trans _ (c_plus (c_plus (A (S B')) (C (S B')))
                                (c_plus (cxsum A B') (cxsum C B')))).
    + apply c_plus_congr; [ apply c_eq_refl | exact IH ].
    + apply (c_eq_trans _
               (c_plus (A (S B')) (c_plus (C (S B')) (c_plus (cxsum A B') (cxsum C B'))))).
      * apply c_eq_sym. apply c_plus_assoc.
      * apply (c_eq_trans _
                 (c_plus (A (S B')) (c_plus (cxsum A B') (c_plus (C (S B')) (cxsum C B'))))).
        -- apply c_plus_congr;
             [ apply c_eq_refl | apply cx_swap_inner ].
        -- exact (c_plus_assoc (A (S B')) (cxsum A B')
                    (c_plus (C (S B')) (cxsum C B'))).
Qed.

(* The divisor sum at the unit bound is the unit term. *)
Lemma dsum_one : forall s : Cx, c_eq (dsumCx (dfun s) 1) (dfun s 1).
Proof.
  intro s. unfold dsumCx. cbn [cxsum].
  replace (dvdb 1 1) with true by reflexivity.
  unfold dfun. cbn.
  apply (c_eq_trans _ (c_plus (dfun s 1) c_zero)).
  - apply c_eq_refl.
  - apply c_plus_zero_r.
Qed.

(* Divisor-sum transport along an equal bound. *)
Lemma dsumCx_eq_dom : forall (f : nat -> Cx) (x y : nat),
  x = y -> c_eq (dsumCx f x) (dsumCx f y).
Proof.
  intros f x y Hxy. rewrite Hxy. apply c_eq_refl.
Qed.

(* ==== Section 4. The one-step peel at a fresh prime ==== *)

(* The pointwise split of the divisor filter by the p-modulo test. *)
Lemma dsum_split_add : forall (p Y : nat) (s : Cx),
  c_eq (cxsum (fun d => if dvdb d (p * Y) then dfun s d else c_zero) (p * Y))
       (c_plus (cxsum (fun d => if dvdb d (p * Y) then
                          (if Nat.eqb (d mod p) 0 then dfun s d else c_zero)
                        else c_zero) (p * Y))
               (cxsum (fun d => if dvdb d (p * Y) then
                          (if Nat.eqb (d mod p) 0 then c_zero else dfun s d)
                        else c_zero) (p * Y))).
Proof.
  intros p Y s.
  apply (c_eq_trans _
           (cxsum (fun d => c_plus
                     (if dvdb d (p * Y) then
                        (if Nat.eqb (d mod p) 0 then dfun s d else c_zero)
                      else c_zero)
                     (if dvdb d (p * Y) then
                        (if Nat.eqb (d mod p) 0 then c_zero else dfun s d)
                      else c_zero)) (p * Y))).
  - apply cxsum_ext. intros d Hd1 Hd2.
    destruct (dvdb d (p * Y)) eqn:Ed.
    + destruct (Nat.eqb (d mod p) 0) eqn:Ep.
      * apply c_eq_sym. apply cx_plus_zero_r.
      * apply c_eq_sym. apply cx_plus_zero_l.
    + destruct (Nat.eqb (d mod p) 0) eqn:Ep.
      * exact (cx_plus_zero_l c_zero).
      * exact (cx_plus_zero_l c_zero).
  - apply cxsum_add.
Qed.

(* The p-multiple half: the p-multiple branch of the divisor sum of p * Y   *)
(* reindexes onto the divisor sum of Y with the scaled term: the g-summand  *)
(* carries the dpow-p factor (cxsum_scalar_l pulls it out), and the        *)
(* pointwise bridge applies the multiplicative term law at the             *)
(* S-materialized index: p is destructed to S p' so that S p' * S mm is a  *)
(* constructor-headed product; the dfun match therefore reduces and        *)
(* Nat.leb 1 (S p' * S mm) computes to true, whence every NatLe 1 witness  *)
(* there is convertible (NatLe = Id (leb ..) true, NatLe_lift's match      *)
(* fires).  The closing shot is exactly c_powq_mult_law_gen at that index, *)
(* closed by kernel conversion with no index abstraction anywhere.         *)
Lemma dsum_pmult_half : forall (p Y : nat) (s : Cx) (Hp : NatLe 1 p) (Hpp : (2 <= p)%nat),
  c_eq (cxsum (fun d => if dvdb d (p * Y) then
                        (if Nat.eqb (d mod p) 0 then dfun s d else c_zero)
                      else c_zero) (p * Y))
       (c_mult (dpow s p Hp) (dsumCx (dfun s) Y)).
Proof.
  intros p Y s Hp Hpp.
  destruct p as [|p']; [ lia | ].
  assert (Hq1 : (1 <= S p')%nat) by lia.
  apply (c_eq_trans _
           (cxsum (fun d => if Nat.eqb (d mod (S p')) 0 then
                      (if dvdb (d / S p') Y then
                         c_mult (dpow s (S p') Hp) (dfun s (d / S p'))
                       else c_zero)
                    else c_zero) (S p' * Y))).
  - apply cxsum_ext. intros d Hd1 Hd2.
    destruct (Nat.eqb (d mod (S p')) 0) eqn:Ep.
    + apply Nat.eqb_eq in Ep.
      destruct ((d / S p')%nat) as [|mm] eqn:Edp.
      * exfalso.
        assert (Hd0 : d = 0%nat).
        { pose proof (Nat.div_mod_eq d (S p')) as Hdm.
          rewrite Ep, Edp, Nat.add_0_r, Nat.mul_0_r in Hdm. exact Hdm. }
        rewrite Hd0 in Hd1. lia.
      * assert (Hde : d = (S p' * S mm)%nat).
        { pose proof (Nat.div_mod_eq d (S p')) as Hdm.
          rewrite Ep, Edp, Nat.add_0_r in Hdm. exact Hdm. }
        rewrite Hde.
        assert (H1mm : (1 <= S mm)%nat) by lia.
        destruct (dvdb (S mm) Y) eqn:Ey.
        -- assert (Hdv : dvdb (S p' * S mm) (S p' * Y) = true).
           { unfold dvdb. apply Nat.eqb_eq.
             apply (pr_dvd_mod0 (S p' * S mm) (S p' * Y)).
             - lia.
             - destruct (dvdb_spec_true (S mm) Y H1mm Ey) as [k Hk].
               exists k. rewrite Hk. ring. }
           rewrite Hdv.
           exact (c_powq_mult_law_gen Hnpos (S p') (S mm) Hp (NatLe_one_S mm)
                    (NatLe_one_S (mm + p' * S mm)) s).
        -- assert (Hnd : dvdb (S p' * S mm) (S p' * Y) = false).
           { assert (H1dv : (1 <= S p' * S mm)%nat) by lia.
             destruct (dvdb (S p' * S mm) (S p' * Y)) eqn:Ed2.
             - exfalso.
               apply (dvdb_spec_false (S mm) Y H1mm Ey).
               apply (dvd_mul_cancel_l (S p') (S mm) Y).
               + lia.
               + exact (dvdb_spec_true (S p' * S mm) (S p' * Y) H1dv Ed2).
             - reflexivity. }
           rewrite Hnd. apply c_eq_refl.
    + destruct (dvdb d (S p' * Y)) eqn:Ed.
      * apply c_eq_refl.
      * apply c_eq_refl.
  - apply (c_eq_trans _
             (cxsum (fun e => if dvdb e Y then
                                c_mult (dpow s (S p') Hp) (dfun s e)
                              else c_zero) Y)).
    + exact (cxsum_reindex_mul (S p') Y
               (fun e => if dvdb e Y then
                           c_mult (dpow s (S p') Hp) (dfun s e)
                         else c_zero) Hq1).
    + apply (c_eq_trans _
               (c_mult (dpow s (S p') Hp)
                  (cxsum (fun d => if dvdb d Y then dfun s d else c_zero) Y))).
      * apply (c_eq_trans _
                 (cxsum (fun d => c_mult (dpow s (S p') Hp)
                            (if dvdb d Y then dfun s d else c_zero)) Y)).
        -- apply cxsum_ext. intros e He1 He2.
           destruct (dvdb e Y) eqn:Ee.
           ++ apply c_eq_refl.
           ++ apply c_eq_sym. apply cx_mult_zero_r.
        -- exact (cxsum_scalar_l (dpow s (S p') Hp)
                    (fun d => if dvdb d Y then dfun s d else c_zero) Y).
      * apply c_eq_refl.
Qed.

(* The coprime half: at a fresh prime, the p-coprime divisors of p^{S K}    *)
(* M' are exactly the divisors of M' (Gauss descent).                       *)
Lemma dsum_coprime_fresh : forall (p K M' : nat) (s : Cx),
  pr_prime p -> (2 <= p)%nat -> (1 <= M')%nat ->
  (Nat.divide p M' -> False) ->
  c_eq (cxsum (fun d => if dvdb d (Nat.pow p (S K) * M') then
                        (if Nat.eqb (d mod p) 0 then c_zero else dfun s d)
                      else c_zero) (Nat.pow p (S K) * M'))
       (dsumCx (dfun s) M').
Proof.
  intros p K M' s Hp Hp2 HM' Hpm.
  assert (H1p : (1 <= p)%nat) by lia.
  apply (c_eq_trans _
           (cxsum (fun d => if dvdb d M' then dfun s d else c_zero)
              (Nat.pow p (S K) * M'))).
  - apply cxsum_ext. intros d Hd1 Hd2.
    destruct (Nat.eqb (d mod p) 0) eqn:Ep.
    + destruct (dvdb d M') eqn:EM.
      * exfalso. apply Hpm.
        apply (Nat.divide_trans p d M').
        -- apply (pr_mod0_dvd p d).
           ++ exact H1p.
           ++ apply Nat.eqb_eq. exact Ep.
        -- exact (dvdb_spec_true d M' Hd1 EM).
      * destruct (dvdb d (Nat.pow p (S K) * M')) eqn:Ed2c.
        -- apply c_eq_refl.
        -- apply c_eq_refl.
    + destruct (dvdb d (Nat.pow p (S K) * M')) eqn:Ed.
      * destruct (dvdb d M') eqn:EM.
        -- apply c_eq_refl.
        -- exfalso.
           apply (dvdb_spec_false d M').
           ++ lia.
           ++ exact EM.
           ++ apply (dvd_gcd_iter p (S K) M' d Hp Hd1 HM' Hpm).
              ** exact (dvdb_spec_true d (Nat.pow p (S K) * M') Hd1 Ed).
              ** intro Hpd.
                 assert (Hmod : (d mod p <> 0)%nat).
                 { apply (proj1 (Nat.eqb_neq (d mod p) 0)). exact Ep. }
                 apply Hmod.
                 exact (pr_dvd_mod0 p d H1p Hpd).
      * destruct (dvdb d M') eqn:EM.
        -- exfalso.
           apply (dvdb_spec_false d (Nat.pow p (S K) * M')).
           ++ lia.
           ++ exact Ed.
           ++ apply (dvd_mul_r (Nat.pow p (S K)) d M'
                    (dvdb_spec_true d M' Hd1 EM)).
        -- apply c_eq_refl.
  - apply c_eq_sym. apply dsumCx_range; [ exact HM' | ].
    assert (Hpg : (1 <= Nat.pow p (S K))%nat) by (apply pow_ge1; lia).
    assert (HM1 : (1 * M' <= Nat.pow p (S K) * M')%nat)
      by (apply Nat.mul_le_mono; lia).
    rewrite Nat.mul_1_l in HM1. exact HM1.
Qed.

(* The one-step peel: D(p^{S K} * M') = dpow p * D(p^K * M') + D(M') at a   *)
(* fresh prime.  The NatLe 1 p witness is an explicit premise (Hp1), so the *)
(* dpow witness never needs a transport.                                    *)
Lemma dsum_peel_fresh : forall (p K M' : nat) (s : Cx) (Hp : pr_prime p)
    (Hp2 : (2 <= p)%nat) (Hp1 : NatLe 1 p) (HM' : (1 <= M')%nat)
    (Hpm : Nat.divide p M' -> False),
  c_eq (dsumCx (dfun s) (Nat.pow p (S K) * M'))
       (c_plus (c_mult (dpow s p Hp1)
                        (dsumCx (dfun s) (Nat.pow p K * M')))
               (dsumCx (dfun s) M')).
Proof.
  intros p K M' s Hp Hp2 Hp1 HM' Hpm.
  rewrite Nat.pow_succ_r by lia.
  rewrite <- (Nat.mul_assoc p (Nat.pow p K) M').
  unfold dsumCx.
  apply (c_eq_trans _
           (c_plus (cxsum (fun d => if dvdb d (p * (Nat.pow p K * M')) then
                                     (if Nat.eqb (d mod p) 0 then dfun s d else c_zero)
                                   else c_zero) (p * (Nat.pow p K * M')))
                   (cxsum (fun d => if dvdb d (p * (Nat.pow p K * M')) then
                                     (if Nat.eqb (d mod p) 0 then c_zero else dfun s d)
                                   else c_zero) (p * (Nat.pow p K * M'))))).
  - apply dsum_split_add.
  - apply c_plus_congr.
    + apply (dsum_pmult_half p (Nat.pow p K * M') s Hp1 Hp2).
    + rewrite (Nat.mul_assoc p (Nat.pow p K) M').
      rewrite <- Nat.pow_succ_r by lia.
      apply (dsum_coprime_fresh p K M' s Hp Hp2 HM' Hpm).
Qed.

(* ==== Section 5. The K-fold block lemma ==== *)

(* D(p^K * M') = eblock(p,K) * D(M') -- the main identity's induction       *)
(* body.  The NatLe 1 p witness is an explicit premise (Hp1).               *)
Lemma dsum_block_pow : forall (p K M' : nat) (s : Cx) (Hp : pr_prime p)
    (Hp2 : (2 <= p)%nat) (Hp1 : NatLe 1 p) (HM' : (1 <= M')%nat)
    (Hpm : Nat.divide p M' -> False),
  c_eq (dsumCx (dfun s) (Nat.pow p K * M'))
       (c_mult (eblock p Hp1 K s) (dsumCx (dfun s) M')).
Proof.
  intros p K. induction K as [|K IH]; intros M' s Hp Hp2 Hp1 HM' Hpm.
  - rewrite Nat.pow_0_r, Nat.mul_1_l.
    apply (c_eq_trans _ (c_mult c_one (dsumCx (dfun s) M'))).
    + apply c_eq_sym. apply cx_mult_one_l.
    + apply c_eq_refl.
  - rewrite Nat.pow_succ_r by lia.
    rewrite <- (Nat.mul_assoc p (Nat.pow p K) M').
    apply (c_eq_trans _
             (c_plus (c_mult (dpow s p Hp1)
                        (dsumCx (dfun s) (Nat.pow p K * M')))
                     (dsumCx (dfun s) M'))).
    + apply (c_eq_trans _
               (c_plus (cxsum (fun d => if dvdb d (p * (Nat.pow p K * M')) then
                                          (if Nat.eqb (d mod p) 0 then dfun s d else c_zero)
                                        else c_zero) (p * (Nat.pow p K * M')))
                       (cxsum (fun d => if dvdb d (p * (Nat.pow p K * M')) then
                                          (if Nat.eqb (d mod p) 0 then c_zero else dfun s d)
                                        else c_zero) (p * (Nat.pow p K * M'))))).
      * unfold dsumCx. apply dsum_split_add.
      * apply c_plus_congr.
        -- apply (dsum_pmult_half p (Nat.pow p K * M') s Hp1 Hp2).
        -- rewrite (Nat.mul_assoc p (Nat.pow p K) M').
           rewrite <- Nat.pow_succ_r by lia.
           apply (dsum_coprime_fresh p K M' s Hp Hp2 HM' Hpm).
    + apply (c_eq_trans _
               (c_plus (c_mult (c_mult (dpow s p Hp1) (eblock p Hp1 K s))
                          (dsumCx (dfun s) M'))
                       (c_mult c_one (dsumCx (dfun s) M')))).
      * apply c_plus_congr.
        -- apply (c_eq_trans _
                    (c_mult (dpow s p Hp1)
                       (c_mult (eblock p Hp1 K s) (dsumCx (dfun s) M')))).
           ++ apply c_mult_congr.
              ** apply c_eq_refl.
              ** exact (IH M' s Hp Hp2 Hp1 HM' Hpm).
           ++ apply c_mult_assoc.
        -- apply c_eq_sym. apply cx_mult_one_l.
      * apply c_eq_sym. apply cx_distrib_r.
Qed.

End FiniteEulerPeel.

(* ==== Section 6. Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   3 Definitions (dpow, dfun, eblock) + 18 Lemmas (natle_of_dvdb, dpow_S,
   nat_real_one, real_log_nat_one, c_scale_zero, dpow_one, dpow_zero_contra,
   dpow_mult_law, dfun_S, eblock_S, cxsum_add, dsum_one, dsumCx_eq_dom,
   dsum_split_add, dsum_pmult_half, dsum_coprime_fresh, dsum_peel_fresh,
   dsum_block_pow); Section FiniteEulerPeel discharges with the Hnpos slot;
   zero vm_compute, zero assumed constants and zero abandoned proofs. *)
