(* ConstructiveWorld-Main - the nat-layer divisor-split kernel of the finite
   Euler product node (probe variant of the fresh-prime face). *)
(** * GaC2_03_d_probe: the divisor-split kernel leaf, probe variant.
    Mission.  The nat-layer divisor-split kernel consumed by the finite
      Euler product stem's prime-table induction body: the prime-power
      product table [prodf_pow] K l over a prime list l (the factored
      form of the segment's main table M_N, aligned with
      [pr_lcm_eq_decomp]), its positivity face, the divisibility
      transitivity and right-multiplying faces, the p-multiple
      cancellation faces (divisibility and the [dvdb] boolean test),
      the Gauss-elimination descent (a prime-coprime divisor of
      p^K * M divides M), the Set-sorted positivity witness for prime
      powers, and the fresh-prime face (a prime outside a distinct
      prime list never divides the list's prime-power product); this
      probe copy states the fresh-prime face with an explicit
      not-in-list premise ([prime_list_fresh_probe]).
    Dependencies.  Requires [abl_Pr_core_01] ([pr_prime] faces),
      [abl_Pr_lcmdecomp_04] ([plm_gauss]), [abl_Pr_lcm_eq]
      ([plq_gcd_1_of_nondvd]), [GaC2_03_a] ([dvdb]), and
      [GaC2_03_b] ([pr_prime_euclid]/[pow_fresh_prime_false]/
      [pow_ge1]/[dvd_le]) of this development; Stdlib
      [Arith.Arith], [List], [Lia].  The leaf-chain -> GaC2_03_b is a
      same-node dependency (Euclid's lemma lives in the _b kernel).
    References.  Card C2.03 (FTA pairing consumes the tree primality
      face), drafts_C2.md C2.03; proof bodies original to this
      segment (Bezout descent via [plm_gauss] and least-factor euclid
      descent, zero transplant).
    Constructivity.  Every named construction is carried by [Set];
      negations are written P -> False (zero not/~ tokens); no
      vm_compute; every proof closes under the global context;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_d_probe.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98
      -AllowG3 -GearForce 0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.
Require Import GaC2_03_a.
Require Import GaC2_03_b.
From Stdlib Require Import Arith.Arith List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ==== Section 1. The prime-power product table ==== *)

(* prodf_pow K l = prod_{p in l} p^(K p): the fold_right over the mapped    *)
(* list, exactly the factored form of pr_lcm_eq_decomp.                     *)
Definition prodf_pow (K : nat -> nat) (l : list nat) : nat :=
  fold_right Nat.mul 1 (map (fun p => Nat.pow p (K p)) l).

(* Head equation (definitional). *)
Lemma prodf_pow_cons : forall (K : nat -> nat) (x : nat) (l : list nat),
  prodf_pow K (x :: l) = Nat.pow x (K x) * prodf_pow K l.
Proof. intros K x l. reflexivity. Qed.

Lemma prodf_pow_ge1 : forall (K : nat -> nat) (l : list nat),
  (forall x : nat, In x l -> (x <> 0)%nat) ->
  (1 <= prodf_pow K l)%nat.
Proof.
  intros K l. induction l as [|x l IH]; intro Hnz.
  - cbn. lia.
  - rewrite prodf_pow_cons.
    assert (Hx0 : (x <> 0)%nat) by (apply Hnz; left; reflexivity).
    pose proof (pow_ge1 x (K x) Hx0) as Hx.
    assert (Hl0 : forall y : nat, In y l -> (y <> 0)%nat)
      by (intros y Hy; apply Hnz; right; exact Hy).
    pose proof (IH Hl0) as Hih.
    assert ((1 * 1 <= Nat.pow x (K x) * prodf_pow K l)%nat)
      by (apply Nat.mul_le_mono; assumption).
    lia.
Qed.

(* ==== Section 2. Divisibility transitivity and scaling faces ==== *)

(* Divisibility transitivity (witness composition). *)
Lemma dvd_trans : forall a b c : nat,
  Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof.
  intros a b c [k Hk] [j Hj]. exists (k * j).
  rewrite Hj, Hk. ring.
Qed.

(* Right-multiplying a divisibility by an arbitrary factor. *)
Lemma dvd_mul_r : forall a n M : nat,
  Nat.divide n M -> Nat.divide n (a * M).
Proof.
  intros a n M [k Hk]. exists (a * k). rewrite Hk. ring.
Qed.

(* Cancelling a positive factor p on the left of a divisibility. *)
Lemma dvd_mul_cancel_l : forall p d Y : nat, (p <> 0)%nat ->
  Nat.divide (p * d) (p * Y) -> Nat.divide d Y.
Proof.
  intros p d Y Hp [k Hk].
  assert (HY : p * Y = p * (k * d)).
  { rewrite Hk. ring. }
  rewrite (proj1 (Nat.mul_cancel_l Y (k * d) p Hp) HY).
  exists k. reflexivity.
Qed.

(* The divisibility test dvdb is invariant under cancelling a positive      *)
(* factor on both sides.                                                    *)
Lemma dvdb_mul_cancel : forall p d Y : nat, (p <> 0)%nat -> (1 <= d)%nat ->
  dvdb (p * d) (p * Y) = dvdb d Y.
Proof.
  intros p d Y Hp Hd. destruct d as [|d']; [ rewrite Nat.mul_0_r; reflexivity | ].
  replace (p * S d') with (S d' * p) by (apply Nat.mul_comm).
  destruct (dvdb (S d' * p) (p * Y)) eqn:E1.
  - assert (Hdvd : Nat.divide (S d' * p) (p * Y))
      by (apply (dvdb_spec_true (S d' * p) (p * Y)); [ lia | exact E1 ]).
    assert (HdY : Nat.divide (S d') Y).
    { apply (dvd_mul_cancel_l p (S d') Y); [ exact Hp | ].
      rewrite Nat.mul_comm. exact Hdvd. }
    assert (Hb2 : dvdb (S d') Y = true)
      by (apply dvdb_of_divide; [ lia | exact HdY ]).
    rewrite Hb2. reflexivity.
  - destruct (dvdb (S d') Y) eqn:E2; [ exfalso | reflexivity ].
    exfalso.
    assert (HdY : Nat.divide (S d') Y)
      by (apply (dvdb_spec_true (S d') Y); [ lia | exact E2 ]).
    assert (Hdvd : Nat.divide (S d' * p) (p * Y)).
    { replace (p * Y) with (Y * p) by (apply Nat.mul_comm).
      apply dvd_mul_both.
      - exact HdY.
      - exists 1. rewrite Nat.mul_1_l. reflexivity. }
    apply (dvdb_spec_false (S d' * p) (p * Y));
        [ nia | exact E1 | exact Hdvd ].
Qed.

(* ==== Section 3. The Gauss-elimination descent ==== *)

(* A prime-coprime divisor of p^K * M divides M (plm_gauss applied K        *)
(* times; the K-fold descent is a plain induction on K).                    *)
Lemma dvd_gcd_iter : forall (p K M n : nat),
  pr_prime p -> (1 <= n)%nat -> (1 <= M)%nat -> (Nat.divide p M -> False) ->
  Nat.divide n (Nat.pow p K * M) -> (Nat.divide p n -> False) ->
  Nat.divide n M.
Proof.
  intros p K. induction K as [|K IH]; intros M n Hp Hn1 HM Hpm Hdvd Hpn.
  - rewrite Nat.pow_0_r, Nat.mul_1_l in Hdvd. exact Hdvd.
  - assert (Hg : Nat.gcd n p = 1).
    { rewrite (Nat.gcd_comm n p).
      exact (plq_gcd_1_of_nondvd p n Hp Hn1 Hpn). }
    rewrite Nat.pow_succ_r in Hdvd by lia.
    rewrite <- Nat.mul_assoc in Hdvd.
    apply (IH M n Hp Hn1 HM Hpm); [ | exact Hpn ].
    apply (plm_gauss n p (Nat.pow p K * M) Hg).
    exact Hdvd.
Qed.

(* ==== Section 4. Positivity witness and the fresh-prime face ==== *)

(* Set-sorted positivity witness for prime powers (consumed by c_powq).     *)
Lemma natle_pow : forall p k : nat, (1 <= p)%nat -> NatLe 1 (Nat.pow p k).
Proof.
  intros p k Hp. apply NatLe_lift.
  apply (pow_ge1 p k). lia.
Qed.

(* A prime outside a distinct prime list never divides the list's           *)
(* prime-power product (euclid descent along the list).                     *)
Lemma prime_list_fresh_probe : forall (l : list nat) (K : nat -> nat) (q : nat),
  NoDup l -> (forall x : nat, In x l -> pr_prime x) -> pr_prime q ->
  (In q l -> False) ->
  Nat.divide q (prodf_pow K l) -> False.
Proof.
  intros l. induction l as [|x l IH]; intros Kq q Hnd Hl Hq Hnotin Hdvd.
  - cbn in Hdvd.
    assert (Hq2 : (2 <= q)%nat) by (destruct (pr_prime_parts q Hq); lia).
    assert (Hq1 : (q <= 1)%nat)
      by (apply (dvd_le q 1); [ lia | lia | exact Hdvd ]).
    lia.
  - (* Rocq 9.3: plain destruct on NoDup (x::l) generalises the compound index
       and yields a degenerate nil subgoal (In q [] = False, unprovable);
       inversion keeps only the cons case the rest of this proof assumes. *)
    inversion Hnd as [ | x0 l0' Hnx Hnd' ]; subst.
    assert (Hqx : (q <> x)%nat).
    { intro Heq. subst x. apply Hnotin. left. reflexivity. }
    assert (Hq2 : (2 <= q)%nat) by (destruct (pr_prime_parts q Hq); lia).
    rewrite prodf_pow_cons in Hdvd.
    destruct (pr_prime_euclid q (Nat.pow x (Kq x)) (prodf_pow Kq l)
                Hq Hq2 Hdvd) as [H1 | H2].
    + assert (Hxp : pr_prime x) by (apply Hl; left; reflexivity).
      assert (Hx2 : (2 <= x)%nat) by (destruct (pr_prime_parts x Hxp); lia).
      exfalso. apply (pow_fresh_prime_false x q (Kq x));
        [ exact Hxp | exact Hx2 | exact Hq | exact Hqx | exact H1 ].
    + assert (Hl' : forall y : nat, In y l -> pr_prime y)
        by (intros y Hy; apply Hl; right; exact Hy).
      assert (Hnotin' : In q l -> False)
        by (intro Hin; apply Hnotin; right; exact Hin).
      apply (IH Kq q Hnd' Hl' Hq Hnotin' H2).
Qed.

(* ==== Section 5. Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   1 Definition (prodf_pow) + 9 Lemmas; zero statements beyond them,
   zero vm_compute, zero assumed constants and zero abandoned proofs,
   zero Cx/Real content. *)
