(* ConstructiveWorld-Main - the nat-layer FTA-lite kernel of the finite
   Euler product node. *)
(** * GaC2_03_b: the number-theory kernel leaf of node C2.03.
    Mission.  The nat-layer FTA-lite kernel of the finite Euler product
      node: Euclid's lemma in the trial-division prime form [pr_prime]
      (cast here; stdlib has no Nat.prime/Nat.Coprime), the
      prime-power transfer (p^e | d*t with p nmid d gives p^e | t),
      the fresh-prime table invariant, the exponent table [Kexp] p N :=
      floor(log_p N) with its double-inequality characterization, the
      prime-power table [ptab] N m := prod_{q <= m prime} q^Kexp q N,
      the specialization faces (1 <= n <= N gives n | ptab N N; a
      divisor of ptab N N below M divides ptab M M), the
      divisor-excess comparison face (C2.05 consumption), and the
      prime-transfer face for the coprime split.  Statement-shape fix
      (drafts_C2.md C2.03 obligation L3): the draft's [Kexp]
      placeholder tested strict p < N and stops one division early
      (Kexp 2 10 = 2, but p^K <= N < p^(K+1) forces K = 3); the cut
      definition tests Nat.leb p N and satisfies the double inequality
      exactly.
    Dependencies.  Requires [abl_Pr_core_01] ([pr_prime]/
      [pr_prime_bool]/[pr_min_factor]) of this development; Stdlib
      [Arith.Arith], [Lia].  Zero Cx/Real content: this leaf is pure
      nat.
    References.  Card C2.03 (FTA pairing consumes the tree primality
      face; the HansonLcm power faces carry no Euclid lemma),
      drafts_C2.md C2.03 obligation L3; proof bodies original to this
      segment (least-witness boolean scan, zero transplant).  Divide
      convention: Nat.divide n m = exists k, m = k * n (witness
      right).
    Constructivity.  [pr_prime] is the Prop inference scaffold of
      [abl_Pr_core_01] (tree convention); negations are written
      P -> False (zero not/~ tokens); no vm_compute; every proof
      closes under the global context; [coqchk] reports zero assumed
      constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_b.v] compiles cleanly (exit 0), wrapped by
      [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce
      0 -CoreN 2). *)

Require Import abl_Pr_core_01.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ==== Section 1. Divisibility order and product faces ==== *)

(* A positive divisor of a positive number does not exceed it. *)
Lemma dvd_le : forall d n : nat, (1 <= d)%nat -> (1 <= n)%nat ->
  Nat.divide d n -> (d <= n)%nat.
Proof.
  intros d n Hd Hn [k Hk].
  assert (Hk1 : (1 <= k)%nat).
  { destruct k as [|k']; [ rewrite Nat.mul_0_l in Hk; lia | lia ]. }
  assert (Hge : (1 * d <= k * d)%nat) by (apply Nat.mul_le_mono_r; exact Hk1).
  rewrite Nat.mul_1_l in Hge. lia.
Qed.

(* Divisibility is preserved by right-multiplying both sides. *)
Lemma dvd_mul_both : forall a b c d : nat,
  Nat.divide a b -> Nat.divide c d -> Nat.divide (a * c) (b * d).
Proof.
  intros a b c d [k Hk] [j Hj]. exists (k * j).
  rewrite Hk, Hj. ring.
Qed.

(* The div_mod distribution identity (used to cancel one factor). *)
Lemma div_mod_mul_distr : forall q s t : nat, (s <> 0)%nat ->
  (q / s) * (s * t) + q mod s * t = q * t.
Proof.
  intros q s t Hs. pose proof (Nat.div_mod q s Hs) as Hdm.
  transitivity ((s * (q / s) + q mod s) * t).
  - ring.
  - rewrite <- Hdm. reflexivity.
Qed.

(* Cancellation: a positive common divisor of x + y and x divides y. *)
Lemma dvd_add_cancel : forall a x y : nat, (1 <= a)%nat ->
  Nat.divide a (x + y) -> Nat.divide a x -> Nat.divide a y.
Proof.
  intros a x y Ha [k Hk] [j Hj].
  assert (Hjk : (j <= k)%nat).
  { assert (Hm1 : (j * a <= k * a)%nat) by (rewrite <- Hj, <- Hk; lia).
    destruct (le_lt_dec j k) as [Hc | Hc]; [ exact Hc | exfalso ].
    assert (Hap : (0 < a)%nat) by lia.
    assert (Hlt : (a * k < a * j)%nat)
      by (apply (proj1 (Nat.mul_lt_mono_pos_l a k j Hap)); exact Hc).
    lia. }
  exists (k - j).
  assert (Hba : (j * a <= k * a)%nat) by (apply Nat.mul_le_mono_r; exact Hjk).
  pose proof (Nat.mul_sub_distr_r k j a) as Hms.
  rewrite Hms. lia.
Qed.

(* One is a positive prime power (used at the dvd_le applications). *)
Lemma pow_ge1 : forall p e : nat, (p <> 0)%nat -> (1 <= Nat.pow p e)%nat.
Proof.
  intros p e Hpv.
  pose proof (Nat.pow_le_mono_r p 0 e Hpv (Nat.le_0_l e)) as H.
  rewrite Nat.pow_0_r in H. exact H.
Qed.

(* The two projections of the trial-division primality scaffold. *)
Lemma pr_prime_parts : forall n : nat, pr_prime n ->
  (2 <= n)%nat /\ (forall d : nat, (2 <= d)%nat -> (d < n)%nat ->
                            Nat.divide d n -> False).
Proof. intros n H. exact H. Qed.

(* ==== Section 2. Euclid's lemma (trial-division prime form) ==== *)

(* Least-witness boolean scan: ntz F fuel start walks start, start+1, ...   *)
(* while the fuel lasts, returning the first r with F r = true.             *)
Fixpoint ntz (F : nat -> bool) (fuel start : nat) : nat :=
  match fuel with
  | O => start
  | S fu => if F start then start else ntz F fu (S start)
  end.

(* The scan result stays at or above its starting point. *)
Lemma ntz_ge : forall (F : nat -> bool) (fuel start : nat),
  (start <= ntz F fuel start)%nat.
Proof.
  intros F fuel. induction fuel as [|fu IH]; intros start.
  - apply Nat.le_refl.
  - simpl. destruct (F start).
    + apply Nat.le_refl.
    + apply (Nat.le_trans start (S start) _); [ lia | apply IH ].
Qed.

(* Spec: if a witness b (start <= b < start + fuel) satisfies F b = true,   *)
(* the scan returns the least witness in [start, b].                        *)
Lemma ntz_spec : forall (F : nat -> bool) (fuel start b : nat),
  (start <= b)%nat -> (b < start + fuel)%nat ->
  F b = true ->
  (forall y : nat, (1 <= y)%nat -> (y < start)%nat -> F y = false) ->
  F (ntz F fuel start) = true /\
  (ntz F fuel start <= b)%nat /\
  (forall y : nat, (1 <= y)%nat -> (y < ntz F fuel start)%nat -> F y = false).
Proof.
  intros F fuel. induction fuel as [|fu IH]; intros start b Hle Hlt Hb Hinv.
  - exfalso. lia.
  - simpl. destruct (F start) eqn:Ef.
    + repeat split; [ exact Ef | exact Hle | exact Hinv ].
    + assert (Hsb : (start < b)%nat).
      { destruct (Nat.eq_dec start b) as [Heq | Hne]; [ | lia ].
        rewrite <- Heq in Hb. rewrite Ef in Hb. discriminate Hb. }
      apply (IH (S start) b); [ lia | lia | exact Hb | ].
      intros y Hy1 Hy2. destruct (Nat.eq_dec y start) as [Heq | Hne].
      * rewrite Heq, Ef. reflexivity.
      * apply Hinv; lia.
Qed.

(* Euclid's lemma for the tree trial-division primality pr_prime: a prime   *)
(* dividing a product divides one factor.  Route: reduce a to a mod p, then *)
(* descend along the least r in [1, b] with p | r * (a mod p); the descent  *)
(* shows r | p, primality pins r in {1, p}, and each pin closes one side.   *)
Lemma pr_prime_euclid : forall (p a b : nat),
  pr_prime p -> (2 <= p)%nat ->
  Nat.divide p (a * b) -> Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b Hp Hp2 Hdvd.
  assert (Hpv : (p <> 0)%nat) by lia.
  assert (Hp1 : (1 <= p)%nat) by lia.
  set (q := a / p). set (a' := a mod p).
  pose proof (Nat.div_mod a p Hpv) as Hdm.
  assert (Hdmf : a = p * q + a') by (fold q; fold a'; exact Hdm).
  assert (Halt : (a' < p)%nat) by (apply (Nat.mod_upper_bound a p Hpv)).
  destruct b as [|b'].
  - right. exists 0. ring.
  - (* p divides a' * (S b') *)
    assert (Hpab : Nat.divide p (a' * S b')).
    { unfold Nat.divide in Hdvd. destruct Hdvd as [k Hk].
      assert (Hsum : Nat.divide p (p * (q * S b') + a' * S b')).
      { exists k. rewrite <- Hk, Hdmf. ring. }
      apply (dvd_add_cancel p (p * (q * S b')) (a' * S b') Hp1).
      - exact Hsum.
      - exists (q * S b'). ring. }
    destruct (Nat.eq_dec a' 0) as [Hz | Hnz].
    + left. exists q. rewrite Hdmf, Hz, Nat.add_0_r. ring.
    + assert (Ha1 : (1 <= a')%nat) by lia.
      (* least-witness scan over [1, S b'] *)
      set (F := fun y : nat => Nat.eqb ((y * a') mod p) 0).
      assert (HFb : F (S b') = true).
      { unfold F. apply Nat.eqb_eq. rewrite Nat.mul_comm.
        apply (pr_dvd_mod0 p (a' * S b') Hp1 Hpab). }
      destruct (ntz_spec F (S b') 1 (S b')) as [HFr [Hrb Hmin]];
        [ lia | lia | exact HFb | intros y Hy1 Hy2; exfalso; lia | ].
      set (r := ntz F (S b') 1).
      assert (Hr1 : (1 <= r)%nat) by (unfold r; apply (ntz_ge F (S b') 1)).
      assert (HpHr : Nat.divide p (r * a')).
      { unfold F in HFr. apply Nat.eqb_eq in HFr.
        apply (pr_mod0_dvd p (r * a') Hp1 HFr). }
      (* r | p: the remainder of p modulo r cannot be a smaller witness *)
      assert (Hr0 : (r <> 0)%nat) by lia.
      pose proof (Nat.div_mod p r Hr0) as Hdmr.
      assert (Hmr : (p mod r < r)%nat) by (apply Nat.mod_upper_bound; exact Hr0).
      assert (Hpsa : Nat.divide p (p mod r * a')).
      { apply (dvd_add_cancel p ((p / r) * (r * a')) (p mod r * a') Hp1).
        - rewrite (div_mod_mul_distr p r a' Hr0). exists a'. ring.
        - unfold Nat.divide in HpHr. destruct HpHr as [k Hk].
          exists (k * (p / r)). rewrite Hk. ring. }
      assert (Hs0 : (p mod r = 0)%nat).
      { destruct (Nat.eq_dec (p mod r) 0) as [Ez | Enz]; [ exact Ez | exfalso ].
        assert (HF : F (p mod r) = true).
        { unfold F. apply Nat.eqb_eq.
          apply (pr_dvd_mod0 p ((p mod r) * a') Hp1 Hpsa). }
        assert (Hfin : F (p mod r) = false) by (apply (Hmin (p mod r)); lia).
        rewrite HF in Hfin. discriminate Hfin. }
      assert (Hrp : Nat.divide r p).
      { exists (p / r). transitivity (r * (p / r) + p mod r).
        - exact Hdmr.
        - rewrite Hs0. ring. }
      (* primality pins r in {1, p} *)
      assert (Hrlep : (r <= p)%nat)
        by (apply (dvd_le r p); [ exact Hr1 | lia | exact Hrp ]).
      destruct (Nat.eq_dec r 1) as [Heq1 | Hne1].
      * left. rewrite Heq1, Nat.mul_1_l in HpHr.
        rewrite Hdmf.
        apply (Nat.divide_add_r p (p * q) a').
        -- exists q. ring.
        -- exact HpHr.
      * assert (Hrp' : (r = p)%nat).
        { destruct (Nat.eq_dec r p) as [E | E]; [ exact E | exfalso ].
          destruct (pr_prime_parts p Hp) as [_ Hnodiv].
          apply (Hnodiv r); [ lia | lia | exact Hrp ]. }
        (* r = p divides b: descend on the remainder of b modulo r *)
        pose proof (Nat.div_mod (S b') r Hr0) as Hdmb.
        assert (Hmr2 : (S b' mod r < r)%nat) by (apply Nat.mod_upper_bound; exact Hr0).
        assert (Hpsb : Nat.divide p (S b' mod r * a')).
        { apply (dvd_add_cancel p ((S b' / r) * (r * a')) (S b' mod r * a') Hp1).
          - rewrite (div_mod_mul_distr (S b') r a' Hr0).
            rewrite Nat.mul_comm. exact Hpab.
          - unfold Nat.divide in HpHr. destruct HpHr as [k Hk].
            exists (k * (S b' / r)). rewrite Hk. ring. }
        right.
        assert (Hs'0 : (S b' mod r = 0)%nat).
        { destruct (Nat.eq_dec (S b' mod r) 0) as [Ez | Enz]; [ exact Ez | exfalso ].
          assert (HF : F (S b' mod r) = true).
          { unfold F. apply Nat.eqb_eq.
            apply (pr_dvd_mod0 p ((S b' mod r) * a') Hp1 Hpsb). }
          assert (Hfin : F (S b' mod r) = false) by (apply (Hmin (S b' mod r)); lia).
          rewrite HF in Hfin. discriminate Hfin. }
        exists (S b' / r). rewrite <- Hrp'.
        { transitivity (r * (S b' / r) + S b' mod r).
          - exact Hdmb.
          - rewrite Hs'0. ring. }
Qed.

(* ==== Section 3. Prime-power transfer faces ==== *)

(* A prime power dividing d * t, with the prime not dividing d, divides t. *)
Lemma pow_dvd_contra : forall (p d t e : nat),
  pr_prime p -> (2 <= p)%nat ->
  (Nat.divide p d -> False) ->
  Nat.divide (Nat.pow p e) (d * t) -> Nat.divide (Nat.pow p e) t.
Proof.
  intros p d t e Hp Hp2 Hpd.
  assert (Hne : (p <> 0)%nat) by lia.
  revert t. induction e as [|e IH]; intros t Hdvd.
  - exists t. rewrite Nat.pow_0_r. ring.
  - assert (Hpe : Nat.pow p (S e) = p * Nat.pow p e)
      by (apply Nat.pow_succ_r; lia).
    unfold Nat.divide in Hdvd. destruct Hdvd as [k Hk].
    assert (Hdt : Nat.divide p (d * t)).
    { exists (k * Nat.pow p e). rewrite Hk, Hpe. ring. }
    destruct (pr_prime_euclid p d t Hp Hp2 Hdt) as [Hd' | Ht'];
      [ exfalso; apply Hpd; exact Hd' | ].
    unfold Nat.divide in Ht'. destruct Ht' as [j Hj].
    assert (Hj' : Nat.divide (Nat.pow p e) j).
    { apply IH.
      assert (Hchain : d * j * p = k * Nat.pow p e * p).
      { replace (d * j * p) with (d * (j * p)) by ring.
        rewrite <- Hj, Hk, Hpe. ring. }
      exists k.
      exact (proj1 (Nat.mul_cancel_r (d * j) (k * Nat.pow p e) p Hne) Hchain). }
    unfold Nat.divide in Hj'. destruct Hj' as [j' Hj'].
    exists j'.
    replace t with (j * p) by (symmetry; exact Hj).
    replace j with (j' * Nat.pow p e) by (symmetry; exact Hj').
    rewrite Hpe. ring.
Qed.

(* A fresh prime never divides the prime power of a distinct prime. *)
Lemma pow_fresh_prime_false : forall (p d K : nat),
  pr_prime p -> (2 <= p)%nat -> pr_prime d -> (d <> p)%nat ->
  Nat.divide d (Nat.pow p K) -> False.
Proof.
  intros p d K Hp Hp2 Hd Hne. induction K as [|K IH]; intro Hdvd.
  - rewrite Nat.pow_0_r in Hdvd.
    destruct (pr_prime_parts d Hd) as [Hd2 _].
    assert (Hd1 : (d <= 1)%nat)
      by (apply (dvd_le d 1); [ lia | lia | exact Hdvd ]).
    lia.
  - assert (Hps : Nat.pow p (S K) = p * Nat.pow p K)
      by (apply Nat.pow_succ_r; lia).
    rewrite Hps in Hdvd.
    destruct (pr_prime_parts d Hd) as [Hd2 _].
    destruct (pr_prime_euclid d p (Nat.pow p K) Hd Hd2 Hdvd) as [H1 | H2].
    + exfalso.
      assert (Hdp : (d <= p)%nat) by (apply (dvd_le d p); [ lia | lia | exact H1 ]).
      destruct (Nat.eq_dec d p) as [E | E]; [ exfalso; apply Hne; exact E | ].
      destruct (pr_prime_parts p Hp) as [_ Hnodiv].
      apply (Hnodiv d); [ lia | lia | exact H1 ].
    + apply (IH H2).
Qed.

(* ==== Section 4. The exponent table Kexp and its characterization ==== *)

(* Kexp p N = floor(log_p N): recursion divides N by p while p <= N.        *)
(* The division recursion is not structurally decreasing, so the cast runs  *)
(* on a fuel parameter (fuel N suffices: each step strictly shrinks N for   *)
(* p >= 2); Kaux_irrel pins fuel-independence.                              *)
(* (Knife-time fix of the draft placeholder: Nat.leb, not strict Nat.ltb;   *)
(* see the header note, drafts_C2.md C2.03 obligation L3.)                  *)
Fixpoint Kaux (fuel p N : nat) : nat :=
  match fuel with
  | O => 0
  | S fu =>
      match N with
      | O => 0
      | S m => if Nat.leb p (S m) then S (Kaux fu p (Nat.div (S m) p)) else 0
      end
  end.

Definition Kexp (p N : nat) : nat := Kaux (S N) p N.

(* The division step strictly shrinks the value for p >= 2. *)
Lemma div_shrink : forall p m : nat, (2 <= p)%nat -> (1 <= S m)%nat ->
  (S m / p < S m)%nat.
Proof.
  intros p m Hp Hm.
  assert (Hpv : (p <> 0)%nat) by lia.
  assert (Hdm : S m = p * (S m / p) + S m mod p) by (apply Nat.div_mod; exact Hpv).
  assert (Hmr : (S m mod p < p)%nat) by (apply Nat.mod_upper_bound; exact Hpv).
  destruct (le_lt_dec (S m) (S m / p)) as [Hcase | Hcase]; [ exfalso | exact Hcase ].
  assert ((2 * S m <= p * S m)%nat) by (apply Nat.mul_le_mono_r; lia).
  assert ((p * S m <= p * (S m / p))%nat) by (apply Nat.mul_le_mono_l; lia).
  lia.
Qed.

(* The unfolding equation of Kaux at positive fuel. *)
Lemma Kaux_equation : forall (f p m : nat), Kaux (S f) p (S m) =
  (if Nat.leb p (S m) then S (Kaux f p (Nat.div (S m) p)) else 0).
Proof. intros. reflexivity. Qed.

(* Fuel-independence of Kaux (each recursive step needs fuel >= the value). *)
Lemma Kaux_irrel : forall (f1 f2 p N : nat), (2 <= p)%nat ->
  (N <= f1)%nat -> (N <= f2)%nat -> Kaux f1 p N = Kaux f2 p N.
Proof.
  intros f1. induction f1 as [|f1 IH]; intros f2 p N Hp H1 H2.
  - assert (N = 0)%nat by lia. subst N. destruct f2; reflexivity.
  - destruct N as [|m].
    + destruct f2; reflexivity.
    + destruct f2 as [|f2']; [ lia | ].
      destruct (Nat.leb p (S m)) eqn:E.
      * assert (Hq : (S m / p < S m)%nat) by (apply div_shrink; lia).
        assert (H1' : Kaux (S f1) p (S m) = S (Kaux f1 p (S m / p))).
        { rewrite Kaux_equation, E. reflexivity. }
        assert (H2' : Kaux (S f2') p (S m) = S (Kaux f2' p (S m / p))).
        { rewrite Kaux_equation, E. reflexivity. }
        rewrite H1', H2'. f_equal. apply IH; lia.
      * rewrite !Kaux_equation, E. reflexivity.
Qed.

(* Double inequality: 2 <= p, 1 <= N gives p^Kexp p N <= N < p^(Kexp p N + 1). *)
Lemma Kexp_char : forall (p N : nat), (2 <= p)%nat -> (1 <= N)%nat ->
  (Nat.pow p (Kexp p N) <= N)%nat /\ (N < Nat.pow p (S (Kexp p N)))%nat.
Proof.
  intros p N Hp.
  assert (Hpv : (p <> 0)%nat) by lia.
  revert N.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun N : nat => (1 <= N)%nat ->
      (Nat.pow p (Kexp p N) <= N)%nat /\
      (N < Nat.pow p (S (Kexp p N)))%nat)).
  intros N IH HN.
  destruct N as [|m]; [ exfalso; lia | ].
  destruct (Nat.leb p (S m)) eqn:E.
  - assert (Hle : (p <= S m)%nat) by (apply Nat.leb_le; exact E).
    assert (Hdm : S m = p * (S m / p) + S m mod p) by (apply Nat.div_mod; exact Hpv).
    assert (Hmr : (S m mod p < p)%nat) by (apply Nat.mod_upper_bound; exact Hpv).
    assert (Hq : (S m / p < S m)%nat) by (apply div_shrink; lia).
    assert (Hge1 : (1 <= S m / p)%nat).
    { destruct (S m / p) as [|q'] eqn:Eq; [ exfalso; lia | lia ]. }
    destruct (IH (S m / p) Hq Hge1) as [Hlo Hhi].
    assert (Hstep : Kexp p (S m) = S (Kexp p (S m / p))).
    { unfold Kexp.
      assert (Hfe : Kaux (S (S m)) p (S m) = S (Kaux (S m) p (S m / p))).
      { rewrite Kaux_equation, E. reflexivity. }
      rewrite Hfe. f_equal.
      symmetry. apply Kaux_irrel; lia. }
    rewrite Hstep. split.
    + rewrite Nat.pow_succ_r by lia.
      assert ((p * Nat.pow p (Kexp p (S m / p)) <= p * (S m / p))%nat)
        by (apply Nat.mul_le_mono_l; exact Hlo).
      lia.
    + rewrite Nat.pow_succ_r by lia.
      assert (Hmono : (p * S (S m / p)
                       <= p * Nat.pow p (S (Kexp p (S m / p))))%nat)
        by (apply Nat.mul_le_mono_l; lia).
      lia.
  - assert (Hgt : (S m < p)%nat) by (apply (proj1 (Nat.leb_gt p (S m)) E)).
    assert (Hstep : Kexp p (S m) = 0).
    { unfold Kexp. rewrite Kaux_equation, E. reflexivity. }
    rewrite Hstep. split.
    + rewrite Nat.pow_0_r. lia.
    + rewrite Nat.pow_succ_r by lia.
      rewrite Nat.pow_0_r, Nat.mul_1_r. lia.
Qed.

(* ==== Section 5. The prime-power table ptab ==== *)

(* ptab N m = prod_{q <= m, q prime} q^(Kexp q N)  (the main identity's     *)
(* table M_N, exponents frozen at the outer bound N).                       *)
Fixpoint ptab (N m : nat) : nat :=
  match m with
  | O => 1
  | S m' => if pr_prime_bool (S m') then ptab N m' * Nat.pow (S m') (Kexp (S m') N)
            else ptab N m'
  end.

Lemma ptab_ge1 : forall N m : nat, (1 <= ptab N m)%nat.
Proof.
  intros N m. induction m as [|m IH].
  - cbn [ptab]. lia.
  - cbn [ptab]. destruct (pr_prime_bool (S m)).
    + pose proof (pow_ge1 (S m) (Kexp (S m) N) (Nat.neq_succ_0 m)) as Hp1.
      assert ((1 * 1 <= ptab N m * Nat.pow (S m) (Kexp (S m) N))%nat)
        by (apply Nat.mul_le_mono; assumption).
      lia.
    + exact IH.
Qed.

(* A prime strictly above the table prefix never divides the table. *)
Lemma ptab_fresh_prime : forall N m d : nat,
  pr_prime d -> (m < d)%nat -> Nat.divide d (ptab N m) -> False.
Proof.
  intros N m. induction m as [|m IH]; intros d Hd Hmd Hdvd.
  - cbn [ptab] in Hdvd.
    assert (Hd1 : (d <= 1)%nat)
      by (apply (dvd_le d 1); [ lia | lia | exact Hdvd ]).
    destruct (pr_prime_parts d Hd) as [Hd2 _]. lia.
  - assert (Hd2 : (2 <= d)%nat) by (destruct (pr_prime_parts d Hd); lia).
    cbn [ptab] in Hdvd. destruct (pr_prime_bool (S m)) eqn:Ep.
    + apply pr_prime_bool_spec in Ep.
      assert (Hnp : (d <> S m)%nat) by lia.
      destruct (pr_prime_euclid d (ptab N m)
                  (Nat.pow (S m) (Kexp (S m) N)) Hd Hd2 Hdvd) as [H1 | H2].
      * apply (IH d Hd); [ lia | exact H1 ].
      * exfalso. apply (pow_fresh_prime_false (S m) d (Kexp (S m) N));
          [ exact Ep
          | destruct (pr_prime_parts (S m) Ep); lia
          | exact Hd | exact Hnp | exact H2 ].
    + apply (IH d Hd); [ lia | exact Hdvd ].
Qed.

(* Single-factor face: a prime power with exponent within the table's       *)
(* allocation divides the table.                                            *)
Lemma ptab_single_factor : forall (N m p e : nat),
  pr_prime p -> (p <= m)%nat -> (e <= Kexp p N)%nat ->
  Nat.divide (Nat.pow p e) (ptab N m).
Proof.
  intros N m p e Hp Hpm Hep.
  assert (Hp2 : (2 <= p)%nat) by (destruct (pr_prime_parts p Hp); lia).
  induction m as [|m IH].
  - exfalso. lia.
  - cbn [ptab]. destruct (pr_prime_bool (S m)) eqn:Ep.
    + apply pr_prime_bool_spec in Ep.
      destruct (Nat.eq_dec p (S m)) as [Hpe | Hplt].
      * rewrite <- Hpe.
        assert (HpeK : Nat.divide (Nat.pow p e) (Nat.pow p (Kexp p N))).
        { assert (Hsplit : Nat.pow p (Kexp p N)
                           = Nat.pow p e * Nat.pow p (Kexp p N - e)).
          { assert (HKe : e + (Kexp p N - e) = Kexp p N) by lia.
            rewrite <- HKe at 1.
            rewrite Nat.pow_add_r. reflexivity. }
          rewrite Hsplit.
          exists (Nat.pow p (Kexp p N - e)).
          rewrite Nat.mul_comm. reflexivity. }
        unfold Nat.divide in HpeK. destruct HpeK as [j Hj].
        exists (ptab N m * j). rewrite <- Nat.mul_assoc.
        rewrite <- Hj. reflexivity.
      * assert (Hpm2 : (p <= m)%nat) by lia.
        assert (Hdvd : Nat.divide (Nat.pow p e) (ptab N m))
          by (apply IH; exact Hpm2).
        unfold Nat.divide in Hdvd. destruct Hdvd as [k Hk].
        unfold Nat.divide. exists (k * Nat.pow (S m) (Kexp (S m) N)).
        simpl. rewrite Hk. ring.
    + assert (Hnp : pr_prime (S m) -> False).
      { intro Hpp.
        assert (Heq : pr_prime_bool (S m) = true)
          by (apply (proj2 (pr_prime_bool_spec (S m))); exact Hpp).
        rewrite Heq in Ep. discriminate Ep. }
      assert (Hplt : (p <> S m)%nat).
      { intro Heq. apply Hnp. rewrite <- Heq. exact Hp. }
      assert (Hpm2 : (p <= m)%nat) by lia.
      apply IH. exact Hpm2.
Qed.

(* Pointwise-exponent monotone product divisibility. *)
Lemma ptab_dvd_exponents : forall (N N' m : nat),
  (forall q : nat, pr_prime q -> (q <= m)%nat -> (Kexp q N <= Kexp q N')%nat) ->
  Nat.divide (ptab N m) (ptab N' m).
Proof.
  intros N N' m. induction m as [|m IH]; intro Hmono.
  - unfold Nat.divide. exists 1. rewrite Nat.mul_1_l. reflexivity.
  - cbn [ptab]. destruct (pr_prime_bool (S m)) eqn:Ep.
    + apply pr_prime_bool_spec in Ep.
      apply dvd_mul_both.
      * apply IH. intros q Hq Hqm. apply Hmono; [ exact Hq | lia ].
      * assert (Hle : (Kexp (S m) N <= Kexp (S m) N')%nat)
          by (apply Hmono; [ exact Ep | lia ]).
        replace (Kexp (S m) N')
          with (Kexp (S m) N' - Kexp (S m) N + Kexp (S m) N) by lia.
        rewrite Nat.pow_add_r.
        unfold Nat.divide.
        exists (Nat.pow (S m) (Kexp (S m) N' - Kexp (S m) N)). reflexivity.
    + apply (IH (fun q Hq Hqm => Hmono q Hq (Nat.le_trans q m (S m) Hqm
                                      (Nat.le_succ_diag_r m)))).
Qed.

(* ==== Section 6. p-part peeling ==== *)

(* Every positive n splits as d * p^e with p not dividing d (e = 0 allowed). *)
Lemma peel_p : forall (p n : nat), (2 <= p)%nat -> (1 <= n)%nat ->
  { d : nat & { e : nat & n = d * Nat.pow p e
                         /\ (Nat.divide p d -> False) /\ (1 <= d)%nat } }.
Proof.
  intros p n Hp.
  assert (Hpv : (p <> 0)%nat) by lia.
  revert n.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun n : nat => (1 <= n)%nat ->
      { d : nat & { e : nat & n = d * Nat.pow p e
                            /\ (Nat.divide p d -> False) /\ (1 <= d)%nat } })).
  intros n IH Hn.
  destruct (Nat.eq_dec (n mod p) 0) as [Hz | Hnz].
  - assert (Hdm : n = p * (n / p) + n mod p) by (apply Nat.div_mod; exact Hpv).
    rewrite Hz, Nat.add_0_r in Hdm.
    assert (Hq1 : (1 <= n / p)%nat).
    { destruct (n / p) as [|q'] eqn:Eq; [ exfalso; lia | lia ]. }
    assert (Hqlt : (n / p < n)%nat).
    { destruct (n / p) as [|q'] eqn:Eq; [ lia | ].
      assert ((2 * S q' <= p * S q')%nat) by (apply Nat.mul_le_mono_r; lia).
      lia. }
    destruct (IH (n / p) Hqlt Hq1) as [d [e [Hde [Hpd Hd1]]]].
    exists d. exists (S e). split; [ | split ].
    + rewrite Hdm, Hde, Nat.pow_succ_r by lia. ring.
    + exact Hpd.
    + exact Hd1.
  - exists n. exists 0. split; [ | split ].
    + rewrite Nat.pow_0_r, Nat.mul_1_r. reflexivity.
    + intro Hcon. apply Hnz.
      apply (pr_dvd_mod0 p n); [ lia | exact Hcon ].
    + exact Hn.
Qed.

(* ==== Section 7. The specialization and divisor-comparison faces ==== *)

(* Specialization: every n in [1, N] divides the table ptab N N (the finite *)
(* Euler identity's "sum_{n <= N} is a sub-sum" face, card C2.03).          *)
Lemma ptab_covers : forall (N n : nat), (1 <= n)%nat -> (n <= N)%nat ->
  Nat.divide n (ptab N N).
Proof.
  intros N.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun n : nat => (1 <= n)%nat -> (n <= N)%nat -> Nat.divide n (ptab N N))).
  intros n IH Hn1 HnN.
  assert (HN1 : (1 <= N)%nat) by lia.
  destruct n as [|m]; [ exfalso; lia | ].
  destruct (Nat.eq_dec (S m) 1) as [Heq1 | Hne1].
  - rewrite Heq1. unfold Nat.divide. exists (ptab N N).
    rewrite Nat.mul_1_r. reflexivity.
  - assert (Hn2 : (2 <= S m)%nat) by lia.
    destruct (pr_min_factor_exists (S m) Hn2) as [p [Hpn Hpp]].
    assert (Hp2 : (2 <= p)%nat) by (destruct (pr_prime_parts p Hpp); lia).
    assert (Hpv : (p <> 0)%nat) by lia.
    assert (Hmod0 : (S m) mod p = 0)
      by (apply (pr_dvd_mod0 p (S m)); [ lia | exact Hpn ]).
    assert (Hsm : S m = p * (S m / p) + S m mod p) by (apply Nat.div_mod; exact Hpv).
    rewrite Hmod0, Nat.add_0_r in Hsm.
    assert (Hd1 : (1 <= S m / p)%nat).
    { destruct (S m / p) as [|q'] eqn:Eq; [ exfalso; lia | lia ]. }
    destruct (peel_p p (S m) Hp2 Hn1) as [d [e [Hde [Hpd Hd1']]]].
  assert (He1 : (1 <= e)%nat).
  { destruct e as [|e']; [ | lia ].
    rewrite Nat.pow_0_r, Nat.mul_1_r in Hde.
    exfalso. apply Hpd. rewrite <- Hde. exact Hpn. }
  assert (Hpe1 : (1 <= Nat.pow p e)%nat) by (apply pow_ge1; exact Hpv).
  assert (Hdvpe : Nat.divide (Nat.pow p e) (S m))
    by (exists d; rewrite Hde; reflexivity).
  assert (Hpele : (Nat.pow p e <= S m)%nat)
    by (apply (dvd_le (Nat.pow p e) (S m));
        [ exact Hpe1 | exact Hn1 | exact Hdvpe ]).
  assert (Hdlt : (d < S m)%nat).
  { assert (H2e : (2 <= Nat.pow p e)%nat).
    { pose proof (Nat.pow_le_mono_r p 1 e Hpv He1) as H1.
      rewrite Nat.pow_1_r in H1. lia. }
    assert (Hdmul : (2 * d <= Nat.pow p e * d)%nat)
      by (apply Nat.mul_le_mono_r; exact H2e).
    lia. }
  assert (HdN : (d <= N)%nat) by lia.
  assert (Hdd : Nat.divide d (ptab N N)) by (apply (IH d Hdlt Hd1' HdN)).
  (* exponent allocation: e <= Kexp p N *)
  assert (HpeN : (Nat.pow p e <= N)%nat) by lia.
  destruct (Kexp_char p N Hp2 HN1) as [HKlo HKhi].
  assert (HeK : (e <= Kexp p N)%nat).
  { destruct (Nat.le_gt_cases e (Kexp p N)) as [H | H]; [ exact H | exfalso ].
    assert ((Nat.pow p (S (Kexp p N)) <= Nat.pow p e)%nat)
      by (apply Nat.pow_le_mono_r; [ lia | lia ]).
    lia. }
  (* p <= N and the single-factor face *)
  assert (Hpm : (p <= S m)%nat)
    by (apply (dvd_le p (S m)); [ lia | lia | exact Hpn ]).
  assert (HpN : (p <= N)%nat) by lia.
  assert (HpeTab : Nat.divide (Nat.pow p e) (ptab N N))
    by (apply (ptab_single_factor N N p e Hpp HpN HeK)).
  (* coprime assembly: d | ptab, p^e | ptab, p nmid d gives d * p^e | ptab *)
  unfold Nat.divide in Hdd. destruct Hdd as [t Ht].
  assert (Hpet : Nat.divide (Nat.pow p e) t).
  { apply (pow_dvd_contra p d t e Hpp Hp2 Hpd).
    rewrite Nat.mul_comm, <- Ht. exact HpeTab. }
  unfold Nat.divide in Hpet. destruct Hpet as [j Hj].
  unfold Nat.divide. exists j. rewrite Ht, Hj, Hde. ring.
Qed.

(* Divisor comparison below M: a divisor of ptab N N that is at most M      *)
(* divides ptab M M (M <= N; the C2.05 Cauchy face consumes this).          *)
Lemma ptab_dvd_below : forall (N M n : nat), (M <= N)%nat -> (1 <= n)%nat ->
  (n <= M)%nat -> Nat.divide n (ptab N N) -> Nat.divide n (ptab M M).
Proof.
  intros N M n HMN.
  revert n.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun n : nat => (1 <= n)%nat -> (n <= M)%nat -> Nat.divide n (ptab N N) ->
                    Nat.divide n (ptab M M))).
  intros n IH Hn1 HnM HdN.
  assert (HM1 : (1 <= M)%nat) by lia.
  destruct n as [|m]; [ exfalso; lia | ].
  destruct (Nat.eq_dec (S m) 1) as [Heq | Hne].
  - rewrite Heq. unfold Nat.divide. exists (ptab M M).
    rewrite Nat.mul_1_r. reflexivity.
  - assert (Hn2 : (2 <= S m)%nat) by lia.
    destruct (pr_min_factor_exists (S m) Hn2) as [p [Hpn Hpp]].
    assert (Hp2 : (2 <= p)%nat) by (destruct (pr_prime_parts p Hpp); lia).
    assert (Hpv : (p <> 0)%nat) by lia.
    assert (Hmod0 : (S m) mod p = 0)
      by (apply (pr_dvd_mod0 p (S m)); [ lia | exact Hpn ]).
    assert (Hsm : S m = p * (S m / p) + S m mod p) by (apply Nat.div_mod; exact Hpv).
    rewrite Hmod0, Nat.add_0_r in Hsm.
    assert (Hd1 : (1 <= S m / p)%nat).
    { destruct (S m / p) as [|q'] eqn:Eq; [ exfalso; lia | lia ]. }
    destruct (peel_p p (S m) Hp2 Hn1) as [d [e [Hde [Hpd Hd1']]]].
    assert (He1 : (1 <= e)%nat).
    { destruct e as [|e']; [ | lia ].
      rewrite Nat.pow_0_r, Nat.mul_1_r in Hde.
      exfalso. apply Hpd. rewrite <- Hde. exact Hpn. }
    assert (Hpe1 : (1 <= Nat.pow p e)%nat) by (apply pow_ge1; exact Hpv).
    assert (Hdvpe : Nat.divide (Nat.pow p e) (S m))
      by (exists d; rewrite Hde; reflexivity).
    assert (Hpele : (Nat.pow p e <= S m)%nat)
      by (apply (dvd_le (Nat.pow p e) (S m));
          [ exact Hpe1 | exact Hn1 | exact Hdvpe ]).
    assert (Hdlt : (d < S m)%nat).
    { assert (H2e : (2 <= Nat.pow p e)%nat).
      { pose proof (Nat.pow_le_mono_r p 1 e Hpv He1) as H1.
        rewrite Nat.pow_1_r in H1. lia. }
      assert (Hdmul : (2 * d <= Nat.pow p e * d)%nat)
        by (apply Nat.mul_le_mono_r; exact H2e).
      lia. }
    assert (HdM : (d <= M)%nat) by lia.
    assert (Hdn : Nat.divide d (S m)) by (exists (Nat.pow p e); rewrite Hde; ring).
    assert (Hdd : Nat.divide d (ptab N N)).
    { unfold Nat.divide in HdN. destruct HdN as [k Hk].
      exists (k * Nat.pow p e). rewrite Hk, Hde. ring. }
    assert (HdMM : Nat.divide d (ptab M M)) by (apply (IH d Hdlt Hd1' HdM Hdd)).
    destruct (Kexp_char p M Hp2 HM1) as [HKloM HKhiM].
    destruct (Nat.le_gt_cases e (Kexp p M)) as [HeK | HeK].
    + assert (HpM : (p <= M)%nat).
      { destruct (Nat.le_gt_cases p M) as [H | H]; [ exact H | exfalso ].
        assert (Hple : (p <= Nat.pow p e)%nat).
        { pose proof (Nat.pow_le_mono_r p 1 e Hpv He1) as H1.
          rewrite Nat.pow_1_r in H1. exact H1. }
        lia. }
      unfold Nat.divide in HdMM. destruct HdMM as [t Ht].
      assert (HpeTabM : Nat.divide (Nat.pow p e) (ptab M M))
        by (apply (ptab_single_factor M M p e Hpp HpM HeK)).
      assert (Hpet : Nat.divide (Nat.pow p e) t).
      { apply (pow_dvd_contra p d t e Hpp Hp2 Hpd).
        rewrite Nat.mul_comm, <- Ht. exact HpeTabM. }
      unfold Nat.divide in Hpet. destruct Hpet as [j Hj].
      unfold Nat.divide. exists j. rewrite Ht, Hj, Hde. ring.
    + exfalso.
      assert ((Nat.pow p (S (Kexp p M)) <= Nat.pow p e)%nat)
        by (apply Nat.pow_le_mono_r; [ lia | lia ]).
      lia.
Qed.

(* Divisor-excess comparison: a divisor of ptab N N that is not a divisor   *)
(* of ptab M M (M <= N) must exceed M.                                      *)
Lemma ptab_excess_gt : forall (N M n : nat), (M <= N)%nat -> (1 <= n)%nat ->
  Nat.divide n (ptab N N) -> (Nat.divide n (ptab M M) -> False) ->
  (M < n)%nat.
Proof.
  intros N M n HMN Hn1 HdN HnMM.
  destruct (Nat.le_gt_cases n M) as [HnM | HnM].
  - exfalso. apply (HnMM (ptab_dvd_below N M n HMN Hn1 HnM HdN)).
  - exact HnM.
Qed.

(* ==== Section 8. The prime-transfer face for the coprime split ==== *)

(* Transfer: n | B * p^(S j) with a prime p not dividing n gives n | B * p^j *)
(* (the descending face of the stem's coprime-restricted sum, C2.03/C2.04). *)
Lemma dvd_transfer_prime : forall (p B n j : nat),
  pr_prime p -> (2 <= p)%nat -> (Nat.divide p n -> False) ->
  Nat.divide n (B * Nat.pow p (S j)) -> Nat.divide n (B * Nat.pow p j).
Proof.
  intros p B n j Hp Hp2 Hpn Hdvd.
  assert (Hne : (p <> 0)%nat) by lia.
  assert (Hpsucc : Nat.pow p (S j) = p * Nat.pow p j)
    by (apply Nat.pow_succ_r; lia).
  unfold Nat.divide in Hdvd. destruct Hdvd as [k Hk].
  assert (Hkn : n * k = B * Nat.pow p (S j)) by (rewrite Hk; ring).
  assert (Hpnk : Nat.divide p (n * k)).
  { exists (B * Nat.pow p j). rewrite Hkn, Hpsucc. ring. }
  destruct (pr_prime_euclid p n k Hp Hp2 Hpnk) as [H1 | H2];
    [ exfalso; apply Hpn; exact H1 | ].
  unfold Nat.divide in H2. destruct H2 as [k' Hk'].
  assert (Hk'n : k' * p * n = B * Nat.pow p (S j)).
  { replace (k' * p) with k by (exact Hk').
    apply (eq_sym Hk). }
  assert (Hchain2 : k' * n * p = B * Nat.pow p j * p).
  { transitivity (B * Nat.pow p (S j)).
    - rewrite (eq_sym Hk'n). ring.
    - rewrite Hpsucc. ring. }
  exists k'. symmetry.
  exact (proj1 (Nat.mul_cancel_r (k' * n) (B * Nat.pow p j) p Hne) Hchain2).
Qed.

(* ==== Section 9. Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   24 Lemmas + 3 Fixpoints (ntz, Kaux, ptab) + 1 Definition (Kexp);
   zero statements beyond them, zero vm_compute, zero assumed constants
   and zero abandoned proofs, zero Cx/Real content. *)
