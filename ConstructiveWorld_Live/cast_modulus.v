(** * cast_modulus: the family-one modulus function k(b) for the Machin
      partial-sum sequence.

    Mission.  Cast the exploration-volume section-two modulus face
    k(b) = least k with w_k(b) <= c0 / (4 * max(|b|,1)^11)  (canonical
    script chong1_exit_core.py:120-122, grid-checked there) as a
    Set-carried constructive function with its full specification:

      mach_modulus_k_of_b : forall b : Q,
        sigT (fun k => And
          (QleT' (mach_own_modulus k) (mach_modulus_target b))
          (forall m, NatLe (S m) k -> QltT (mach_modulus_target b)
                                           (mach_own_modulus m)))

    where mach_own_modulus k = 16 * a_{k+1}(1/5) + 4 * a_{k+1}(1/239)
    is the atan_tail_bound tail width of the Machin sequence (the
    direct-consequence face mach_modulus_tail is proved below from
    atan_tail_bound, S11_TP3B5.v:301), mach_modulus_target b =
    (1 # 71663616) / (4 * q_pow (Qmax (Qabs b) 1) 11) is the c0/(4 *
    max(|b|,1)^11) budget with c0 = 1/71663616 (canonical script
    :110-111/:121), and the second component is the minimality clause
    of the mu-operator (every m < k overshoots the budget).

    Dependencies.  S01_BaseRing (NatLe / NatLe_drop, And),
    S02_CauchyComplete (QleT'/QltT carriers and their bridges, qeq_le
    / qeq_imp_qle), S03_QExp (q_pow and its lemmas, q_le_div_le,
    Qmult_lt_0_compat, Qmult_le_0_compat), S11_TP3B5 (arctan_partial,
    atan_mag, atan_tail_bound).  Stdlib: QArith, Qminmax (Qmax),
    ZArith (Z.log2), Lia, Lqa.

    References.  atan_tail_bound = S11_TP3B5.v:301; atan_mag =
    S11_TP3B5.v:60; q_pow = S03_QExp.v:36; mach_mdot /
    mach_own_modulus faces = canonical script chong1_exit_core.py:65/
    :73 (exploration-volume section two); k(b) face = chong1_exit_
    core.py:120-122 (k_of, expo = 11); c0 = chong1_exit_core.py:110-
    111; M1:438 prescription (P7 bridge-level assembly); anchor values
    k(1) = 5, k(2) = 7, k(113) = 21, k(10^6) = 52 = canonical script
    1g lines (independently recomputed by the evaluation probe).

    Constructivity.  Zero axioms, zero admitted goals; every named
    statement is Set-carried (sigT / And-as-prod / QleT' / QltT /
    NatLe).  The mu is realized by a fuelled linear search over the
    decidable Qle_bool predicate; the fuel bound 11*s(b)+7 with s(b) =
    Z.to_nat (Z.log2 (|num b| + 1)) + 1 is proved to satisfy the
    budget via the elementary geometric decay of the tail width (the
    |x|^(2k+1)/(2k+1) closed form of atan_mag from S11).  No
    vm_compute on large constants in the deliverable; the 3695-bit
    numerator route and the forbidden routes (family-2 native
    clearing, family-4 same-index shortcut) are never touched.  The
    Qlt/Qle Prop predicates appear only as interior scaffolding
    consumed from in-library statements.

    Build.  coqc -native-compiler no -q -Q . "" cast_modulus.v  (world
    directory holding S01-S15, UpReqIrrationalCriterion, PiEnvelope,
    mach_fold_q, mach_atan_addsub, mach_fold_chain compiled). *)

Require Import S01_BaseRing S02_CauchyComplete S03_QExp S11_TP3B5.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax ZArith.
From Stdlib Require Import Lqa.

(* ============================================================ *)
(* Section 1.  Statement-face definitions (transcriptions).      *)
(* ============================================================ *)

(* Machin partial sum: mdot k = 16*S_k(1/5) - 4*S_k(1/239), the same
   face as the bridge cast, transcribed from the canonical script :65.
   Needed here to state the atan_tail_bound direct-consequence face of
   the tail width below. *)
Definition mach_mdot (k : nat) : Q :=
  16 * arctan_partial k (1 # 5) - 4 * arctan_partial k (1 # 239).

(* Machin own modulus: w k = 16*a_{k+1}(1/5) + 4*a_{k+1}(1/239), the
   atan_tail_bound tail width of the Machin sequence from depth k
   (canonical script :73). *)
Definition mach_own_modulus (k : nat) : Q :=
  16 * atan_mag (Datatypes.S k) (1 # 5)
  + 4 * atan_mag (Datatypes.S k) (1 # 239).

(* Family-one budget: c0 / (4 * max(|b|,1)^11) with c0 = 1/71663616
   (canonical script :110-111/:121, expo = 11). *)
Definition mach_modulus_target (b : Q) : Q :=
  (1 # 71663616) / (4 * q_pow (Qmax (Qabs b) 1) 11).

(* Digit-count parameter s(b): any nat with max(|b|,1) <= 2^s serves as
   the base of the fuel bound; Z.log2 of |numerator|+1 is the
   computable choice. *)
Definition mach_modulus_s (b : Q) : nat :=
  Z.to_nat (Z.log2 (Z.abs (Qnum b) + 1)) + 1.

(* Fuel: an explicit depth proven (Section 4) to satisfy the budget,
   bounding the least k from above so the linear search terminates. *)
Definition mach_modulus_fuel (b : Q) : nat :=
  11 * mach_modulus_s b + 7.

(* Decidable budget predicate: Qle_bool on the rationals. *)
Definition mach_modulus_bool (tgt : Q) (k : nat) : bool :=
  Qle_bool (mach_own_modulus k) tgt.

(* Fuelled linear search for the least k with the budget satisfied:
   walk upward from k while the predicate is false, stop at the first
   hit, return k when the fuel runs out (the fuel of Section 4 always
   suffices, by mach_modulus_bool_fuel). *)
Fixpoint mach_first_le (tgt : Q) (fuel k : nat) : nat :=
  match fuel with
  | O => k
  | Datatypes.S f =>
      if mach_modulus_bool tgt k then k
      else mach_first_le tgt f (Datatypes.S k)
  end.

(* ============================================================ *)
(* Section 2.  The atan_tail_bound direct-consequence face.      *)
(* ============================================================ *)

(* atan_tail_bound (S11_TP3B5.v:301) gives
   |arctan_partial n x - arctan_partial m x| <= atan_mag (S m) x for
   m <= n; combining the two component series with the factor weights
   16 and 4 gives: the gap of the Machin partial sums at depths k and
   n is at most w k, the Machin own modulus.  Proof structure
   transcribed from the bridge cast. *)
Lemma mach_modulus_tail : forall k n : nat, (k <= n)%nat ->
  QleT' (Qabs (mach_mdot k - mach_mdot n)) (mach_own_modulus k).
Proof.
  intros k n Hkn.
  assert (Hu5 : Qlt 0 (1 # 5)) by (unfold Qlt; simpl; lia).
  assert (Hu239 : Qlt 0 (1 # 239)) by (unfold Qlt; simpl; lia).
  assert (Hu5T : QleT' (Qabs (1 # 5)) 1).
  { apply Qle_to_QleT'.
    rewrite (Qabs_pos (1 # 5) (Qlt_le_weak 0 (1 # 5) Hu5)).
    change (1 * 1 <= 1 * 5)%Z. lia. }
  assert (Hu239T : QleT' (Qabs (1 # 239)) 1).
  { apply Qle_to_QleT'.
    rewrite (Qabs_pos (1 # 239) (Qlt_le_weak 0 (1 # 239) Hu239)).
    change (1 * 1 <= 1 * 239)%Z. lia. }
  apply Qle_to_QleT'.
  pose proof (atan_tail_bound (1 # 5) k n Hu5T Hkn) as HA.
  pose proof (atan_tail_bound (1 # 239) k n Hu239T Hkn) as HB.
  assert (Habs16 : Qabs 16 == 16)
    by (apply Qabs_pos; change (0 * 1 <= 16 * 1)%Z; lia).
  assert (Habs4 : Qabs 4 == 4)
    by (apply Qabs_pos; change (0 * 1 <= 4 * 1)%Z; lia).
  rewrite (Qabs_Qminus (mach_mdot k) (mach_mdot n)).
  assert (Hexp : mach_mdot n - mach_mdot k ==
                 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                 - 4 * (arctan_partial n (1 # 239)
                        - arctan_partial k (1 # 239)))
    by (unfold mach_mdot; ring).
  rewrite Hexp.
  assert (Htri : Qle (Qabs (16 * (arctan_partial n (1 # 5)
                                 - arctan_partial k (1 # 5))
                          - 4 * (arctan_partial n (1 # 239)
                                 - arctan_partial k (1 # 239))))
                      (16 * Qabs (arctan_partial n (1 # 5)
                                  - arctan_partial k (1 # 5))
                       + 4 * Qabs (arctan_partial n (1 # 239)
                                   - arctan_partial k (1 # 239)))).
  { assert (Hpm : 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                  - 4 * (arctan_partial n (1 # 239)
                         - arctan_partial k (1 # 239))
                  == 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                     + (- (4 * (arctan_partial n (1 # 239)
                                - arctan_partial k (1 # 239)))))
      by ring.
    rewrite Hpm.
    apply (Qle_trans _ (Qabs (16 * (arctan_partial n (1 # 5)
                                    - arctan_partial k (1 # 5)))
                        + Qabs (- (4 * (arctan_partial n (1 # 239)
                                       - arctan_partial k (1 # 239))))) _).
    - apply Qabs_triangle.
    - rewrite (Qabs_Qmult 16 (arctan_partial n (1 # 5)
                              - arctan_partial k (1 # 5))).
      rewrite Habs16.
      rewrite (Qabs_opp (4 * (arctan_partial n (1 # 239)
                             - arctan_partial k (1 # 239)))).
      rewrite (Qabs_Qmult 4 (arctan_partial n (1 # 239)
                             - arctan_partial k (1 # 239))).
      rewrite Habs4.
      apply qeq_imp_qle. ring. }
  apply (Qle_trans _ (16 * Qabs (arctan_partial n (1 # 5)
                                    - arctan_partial k (1 # 5))
                      + 4 * Qabs (arctan_partial n (1 # 239)
                                  - arctan_partial k (1 # 239))) _).
  - exact Htri.
  - apply Qplus_le_compat.
    + rewrite (Qmult_comm 16 (Qabs (arctan_partial n (1 # 5)
                                   - arctan_partial k (1 # 5)))).
      rewrite (Qmult_comm 16 (atan_mag (Datatypes.S k) (1 # 5))).
      apply Qmult_le_compat_r.
      * exact HA.
      * change (0 * 1 <= 16 * 1)%Z. lia.
    + rewrite (Qmult_comm 4 (Qabs (arctan_partial n (1 # 239)
                                   - arctan_partial k (1 # 239)))).
      rewrite (Qmult_comm 4 (atan_mag (Datatypes.S k) (1 # 239))).
      apply Qmult_le_compat_r.
      * exact HB.
      * change (0 * 1 <= 4 * 1)%Z. lia.
Qed.

(* ============================================================ *)
(* Section 3.  Elementary Q-arithmetic bookkeeping.              *)
(* ============================================================ *)

(* Left-multiplication form of Qmult_le_compat_r (the left variant is
   absent in this environment; obtained by commuting the factors). *)
Lemma mach_Qmult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z Hxy Hz.
  assert (H1 : x * z <= y * z) by (apply (Qmult_le_compat_r x y z); assumption).
  apply (Qle_trans _ (x * z)).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (y * z)).
    + exact H1.
    + apply qeq_le. ring.
Qed.

(* q_pow is monotone in its base for nonnegative bases. *)
Lemma mach_q_pow_mono : forall (n : nat) (x y : Q),
  Qle 0 y -> Qle y x -> Qle (q_pow y n) (q_pow x n).
Proof.
  intros n x y Hy0 Hyx.
  induction n as [| n IH].
  - change (q_pow y 0) with 1. change (q_pow x 0) with 1.
    apply qeq_le. ring.
  - rewrite (q_pow_succ y n). rewrite (q_pow_succ x n).
    apply (Qle_trans _ (x * q_pow y n)).
    + apply (Qmult_le_compat_r y x (q_pow y n)); [exact Hyx|].
      apply (q_pow_nonneg y n). exact Hy0.
    + apply (mach_Qmult_le_compat_l (q_pow y n) (q_pow x n) x).
      * exact IH.
      * exact (Qle_trans _ _ _ Hy0 Hyx).
Qed.

(* q_pow distributes over multiplication of the base. *)
Lemma mach_q_pow_mult_distr : forall (n : nat) (x y : Q),
  q_pow (x * y) n == q_pow x n * q_pow y n.
Proof.
  intros n x y.
  induction n as [| n IH].
  - reflexivity.
  - rewrite (q_pow_succ (x * y) n). rewrite (q_pow_succ x n).
    rewrite (q_pow_succ y n). rewrite IH. ring.
Qed.

(* q_pow of an integer-literal base stays an integer literal. *)
Lemma mach_q_pow_int_lit : forall (nz : Z) (k : nat),
  q_pow (nz # 1) k == ((nz ^ (Z.of_nat k))%Z # 1).
Proof.
  intros nz k.
  induction k as [| k IH].
  - reflexivity.
  - rewrite (q_pow_succ (nz # 1) k).
    replace (Z.of_nat (Datatypes.S k)) with (Z.succ (Z.of_nat k)) by lia.
    rewrite Z.pow_succ_r by lia.
    rewrite IH. reflexivity.
Qed.

(* q_pow of the unit-fraction literal (1/5) at depth 17 stays a unit-
   fraction literal (the only literal-pow instance the fuel chain
   needs; the positive-scope exponent notation demands a positive
   exponent, so the general nat-exponent form is stated at this single
   depth and closes definitionally). *)
Lemma mach_q_pow_1_5_17 : q_pow (1 # 5) 17 == (1 # 762939453125)%Q.
Proof.
  reflexivity.
Qed.

(* q_pow of a strictly positive base is strictly positive. *)
Lemma mach_q_pow_pos : forall (n : nat) (x : Q),
  Qlt 0 x -> Qlt 0 (q_pow x n).
Proof.
  intros n x Hx.
  induction n as [| n IH].
  - change (q_pow x 0) with 1. unfold Qlt. simpl. lia.
  - rewrite (q_pow_succ x n).
    apply (Qmult_lt_0_compat x (q_pow x n)); [exact Hx | exact IH].
Qed.

(* atan_mag k x is at most the pure power |x|^(2k+1): the 1/(2k+1)
   factor of the S11 closed form only shrinks a nonnegative quantity. *)
Lemma mach_atan_mag_le_pow : forall (k : nat) (x : Q),
  Qle (atan_mag k x) (q_pow (Qabs x) (2 * k + 1)).
Proof.
  intros k x. unfold atan_mag.
  assert (HD1 : Qle 1 ((Z.of_nat (2 * k + 1)) # 1))
    by (unfold Qle; simpl; lia).
  assert (HDpos : Qlt 0 ((Z.of_nat (2 * k + 1)) # 1)) by apply atan_odd_pos.
  assert (Hne : ~ ((Z.of_nat (2 * k + 1)) # 1 == 0))
    by (unfold Qeq; simpl; lia).
  pose proof (Qmult_inv_r ((Z.of_nat (2 * k + 1)) # 1) Hne) as Hinv.
  apply (Qle_trans _
    ((q_pow (Qabs x) (2 * k + 1) * ((Z.of_nat (2 * k + 1)) # 1))
     / ((Z.of_nat (2 * k + 1)) # 1))).
  - apply (Qle_div_same_denom (q_pow (Qabs x) (2 * k + 1))
             (q_pow (Qabs x) (2 * k + 1) * ((Z.of_nat (2 * k + 1)) # 1))
             ((Z.of_nat (2 * k + 1)) # 1) HDpos).
    apply (Qle_trans _ (q_pow (Qabs x) (2 * k + 1) * 1)).
    + apply qeq_le. ring.
    + apply (mach_Qmult_le_compat_l 1 ((Z.of_nat (2 * k + 1)) # 1)
               (q_pow (Qabs x) (2 * k + 1))).
      * exact HD1.
      * apply (q_pow_nonneg (Qabs x) (2 * k + 1)). apply Qabs_nonneg.
  - apply qeq_le.
    unfold Qdiv.
    apply (Qeq_trans _
      (q_pow (Qabs x) (2 * k + 1)
       * (((Z.of_nat (2 * k + 1)) # 1) * / ((Z.of_nat (2 * k + 1)) # 1)))).
    + ring.
    + rewrite Hinv. ring.
Qed.

(* A false Qle_bool is a strict reversed inequality. *)
Lemma mach_Qle_bool_false_lt : forall u v : Q,
  Qle_bool u v = false -> Qlt v u.
Proof.
  intros u v Hb. unfold Qle_bool in Hb.
  apply Z.leb_nle in Hb.
  unfold Qlt. lia.
Qed.

(* ============================================================ *)
(* Section 4.  The fuel bound: an explicit depth in the budget.  *)
(* ============================================================ *)

(* max(|b|,1) is at most 2^(s(b)) by the Z.log2 upper spec. *)
Lemma mach_modulus_M_le_2s : forall b : Q,
  Qle (Qmax (Qabs b) 1) (((2 ^ (Z.of_nat (mach_modulus_s b)))%Z) # 1).
Proof.
  intro b. destruct b as [nu du].
  assert (Hdu : (0 < Z.pos du)%Z) by (destruct du; simpl; lia).
  assert (HNpos : (0 < Z.abs nu + 1)%Z) by (assert (H0 := Z.abs_nonneg nu); lia).
  assert (HAbs : Qle (Qabs (nu # du)) ((Z.abs nu + 1)%Z # 1)).
  { change (Qabs (nu # du)) with (Z.abs nu # du).
    unfold Qle. simpl. nia. }
  assert (HOne : Qle 1 ((Z.abs nu + 1)%Z # 1)).
  { unfold Qle. simpl. lia. }
  assert (HMax : Qle (Qmax (Qabs (nu # du)) 1) ((Z.abs nu + 1)%Z # 1)).
  { apply (Q.max_lub _ _ ((Z.abs nu + 1)%Z # 1)); assumption. }
  assert (Hlog : (Z.abs nu + 1 < 2 ^ Z.succ (Z.log2 (Z.abs nu + 1)))%Z).
  { destruct (Z.log2_spec (Z.abs nu + 1) HNpos) as [Hlo Hhi]. exact Hhi. }
  assert (Hge : (0 <= Z.log2 (Z.abs nu + 1))%Z) by apply Z.log2_nonneg.
  assert (Heq : Z.succ (Z.log2 (Z.abs nu + 1))
                = Z.of_nat (mach_modulus_s (nu # du))).
  { unfold mach_modulus_s. simpl.
    assert (Hid : Z.of_nat (Z.to_nat (Z.log2 (Z.abs nu + 1)))
                  = Z.log2 (Z.abs nu + 1))
      by (apply Z2Nat.id; lia).
    lia. }
  assert (HPow : Qle ((Z.abs nu + 1)%Z # 1)
                     (((2 ^ (Z.of_nat (mach_modulus_s (nu # du))))%Z) # 1)).
  { unfold Qle. simpl. rewrite <- Heq. lia. }
  apply (Qle_trans _ ((Z.abs nu + 1)%Z # 1)); assumption.
Qed.

(* Telescoping geometric step: once 0 <= M <= 2^s, the products
   (1/5)^(k*s) * M^k stay below 1 for every k, because (1/5)^s * M is
   at most (2/5)^s <= 1 and the remaining factor telescopes by
   induction. *)
Lemma mach_modulus_geometric : forall (s : nat) (M : Q),
  Qle 0 M -> Qle M (((2 ^ (Z.of_nat s))%Z) # 1) ->
  forall k : nat, Qle (q_pow (1 # 5) (k * s) * q_pow M k) 1.
Proof.
  intros s M HM0 HM k.
  induction k as [| k IH].
  - change (q_pow (1 # 5) (0 * s)) with 1.
    change (q_pow M 0) with 1.
    apply qeq_le. ring.
  - rewrite Nat.mul_succ_l.
    rewrite (q_pow_succ M k).
    rewrite (atan_q_pow_add (1 # 5) (k * s) s).
    assert (Hpair : Qle (q_pow (1 # 5) s * M) 1).
    { apply (Qle_trans _ (q_pow (1 # 5) s * (((2 ^ (Z.of_nat s))%Z) # 1))).
      - apply (mach_Qmult_le_compat_l M _ (q_pow (1 # 5) s)); [exact HM|].
        apply (q_pow_nonneg (1 # 5) s). unfold Qle. simpl. lia.
      - rewrite <- (mach_q_pow_int_lit 2%Z s).
        setoid_rewrite <- (mach_q_pow_mult_distr s (1 # 5) (2 # 1)).
        assert (E25 : ((1 # 5) * (2 # 1))%Q == (2 # 5)%Q)
          by (unfold Qeq; simpl; lia).
        setoid_rewrite E25.
        apply (atan_pow_le_one (2 # 5) s).
        + unfold Qle. simpl. lia.
        + unfold Qle. simpl. lia. }
    apply (Qle_trans _ ((q_pow (1 # 5) s * M)
                        * (q_pow (1 # 5) (k * s) * q_pow M k))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((q_pow (1 # 5) s * M) * 1)).
      * apply (mach_Qmult_le_compat_l (q_pow (1 # 5) (k * s) * q_pow M k) 1
                 (q_pow (1 # 5) s * M)).
        -- exact IH.
        -- apply (Qmult_le_0_compat (q_pow (1 # 5) s) M).
           ++ apply (q_pow_nonneg (1 # 5) s).
              unfold Qle. simpl. lia.
           ++ exact HM0.
      * apply (Qle_trans _ (q_pow (1 # 5) s * M)).
        -- apply qeq_le. ring.
        -- exact Hpair.
Qed.

(* The fuel depth satisfies the budget: the full geometric chain.
   With K = 11*s+7 the tail width obeys
     w_K * 4 * M^11 * 71663616
       <= 20 * (1/5)^(22*s+17) * 4 * M^11 * 71663616
       =  20 * (1/5)^17 * 4 * 71663616
          * ((1/5)^(11*s) * M^11) * (1/5)^(11*s)
       <=  5733089280 / 5^17  <= 1,
   using the telescoping lemma at k = 11 and the decay of (1/5)^(11*s);
   scaling back by 1/71663616 yields w_K <= c0 / (4 * M^11). *)
Lemma mach_modulus_w_fuel_le : forall b : Q,
  Qle (mach_own_modulus (mach_modulus_fuel b)) (mach_modulus_target b).
Proof.
  intro b.
  assert (HMpos : Qlt 0 (Qmax (Qabs b) 1)).
  { apply (Qlt_le_trans 0 1 (Qmax (Qabs b) 1)).
    - unfold Qlt. simpl. lia.
    - apply Q.le_max_r. }
  assert (HMge0 : Qle 0 (Qmax (Qabs b) 1)) by (apply (Qlt_le_weak 0 _); exact HMpos).
  assert (HM : Qle (Qmax (Qabs b) 1)
                   (((2 ^ (Z.of_nat (mach_modulus_s b)))%Z) # 1))
    by apply mach_modulus_M_le_2s.
  assert (HM11pos : Qlt 0 (q_pow (Qmax (Qabs b) 1) 11))
    by (apply (mach_q_pow_pos 11 (Qmax (Qabs b) 1)); exact HMpos).
  assert (H40 : Qlt 0 (4 * q_pow (Qmax (Qabs b) 1) 11))
    by (apply (Qmult_lt_0_compat 4 (q_pow (Qmax (Qabs b) 1) 11));
        [unfold Qlt; simpl; lia | exact HM11pos]).
  assert (Hge0 : Qle 0 (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616)).
  { apply (Qlt_le_weak 0 (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616)).
    apply (Qmult_lt_0_compat (4 * q_pow (Qmax (Qabs b) 1) 11) 71663616).
    - exact H40.
    - unfold Qlt. simpl. lia. }
  assert (H5pos : Qlt 0 (q_pow (1 # 5) 17))
    by (apply (mach_q_pow_pos 17 (1 # 5)); unfold Qlt; simpl; lia).
  assert (Hfac : Qle 0 (20 * q_pow (1 # 5) 17 * 4 * 71663616)).
  { apply (Qlt_le_weak 0 (20 * q_pow (1 # 5) 17 * 4 * 71663616)).
    apply (Qmult_lt_0_compat (20 * q_pow (1 # 5) 17 * 4) 71663616).
    - apply (Qmult_lt_0_compat (20 * q_pow (1 # 5) 17) 4).
      + apply (Qmult_lt_0_compat 20 (q_pow (1 # 5) 17)).
        * unfold Qlt. simpl. lia.
        * exact H5pos.
      + unfold Qlt. simpl. lia.
    - unfold Qlt. simpl. lia. }
  assert (Hsplit : q_pow (1 # 5) (2 * mach_modulus_fuel b + 3)
                   == q_pow (1 # 5) (22 * mach_modulus_s b)
                      * q_pow (1 # 5) 17).
  { replace (2 * mach_modulus_fuel b + 3)%nat
      with ((22 * mach_modulus_s b) + 17)%nat.
    - rewrite (atan_q_pow_add (1 # 5) (22 * mach_modulus_s b) 17).
      reflexivity.
    - unfold mach_modulus_fuel. ring. }
  assert (H22s : q_pow (1 # 5) (22 * mach_modulus_s b)
                 == q_pow (1 # 5) (11 * mach_modulus_s b)
                    * q_pow (1 # 5) (11 * mach_modulus_s b)).
  { replace (22 * mach_modulus_s b)%nat
      with ((11 * mach_modulus_s b) + (11 * mach_modulus_s b))%nat by ring.
    rewrite (atan_q_pow_add (1 # 5) (11 * mach_modulus_s b)
                            (11 * mach_modulus_s b)).
    reflexivity. }
  assert (HB18 : Qle (q_pow (1 # 5) (11 * mach_modulus_s b)
                      * q_pow (Qmax (Qabs b) 1) 11) 1).
  { apply (mach_modulus_geometric (mach_modulus_s b) (Qmax (Qabs b) 1)
            HMge0 HM 11). }
  assert (HA11 : Qle (q_pow (1 # 5) (11 * mach_modulus_s b)) 1).
  { apply (atan_pow_le_one (1 # 5) (11 * mach_modulus_s b)).
    - unfold Qle. simpl. lia.
    - unfold Qle. simpl. lia. }
  assert (Hprod : Qle (q_pow (1 # 5) (11 * mach_modulus_s b)
                       * q_pow (Qmax (Qabs b) 1) 11
                       * q_pow (1 # 5) (11 * mach_modulus_s b)) 1).
  { apply (Qle_trans _ (1 * q_pow (1 # 5) (11 * mach_modulus_s b))).
    - apply (Qmult_le_compat_r (q_pow (1 # 5) (11 * mach_modulus_s b)
                                * q_pow (Qmax (Qabs b) 1) 11) 1
              (q_pow (1 # 5) (11 * mach_modulus_s b))).
      + exact HB18.
      + apply (q_pow_nonneg (1 # 5) (11 * mach_modulus_s b)).
        unfold Qle. simpl. lia.
    - apply (Qle_trans _ (q_pow (1 # 5) (11 * mach_modulus_s b))).
      + apply qeq_le. ring.
      + exact HA11. }
  assert (Hconst : Qle (20 * q_pow (1 # 5) 17 * 4 * 71663616) 1).
  { rewrite mach_q_pow_1_5_17.
    change ((20 * (1 # 762939453125) * 4 * 71663616)%Q)
      with ((5733089280 # 762939453125)%Q).
    unfold Qle. simpl. lia. }
  assert (Hw : Qle (mach_own_modulus (mach_modulus_fuel b))
                   (20 * q_pow (1 # 5) (2 * mach_modulus_fuel b + 3))).
  { unfold mach_own_modulus.
    assert (Ha5 : Qle (atan_mag (Datatypes.S (mach_modulus_fuel b)) (1 # 5))
                      (q_pow (1 # 5) (2 * mach_modulus_fuel b + 3))).
    { replace (2 * mach_modulus_fuel b + 3)%nat
        with (2 * Datatypes.S (mach_modulus_fuel b) + 1)%nat by lia.
      apply (mach_atan_mag_le_pow (Datatypes.S (mach_modulus_fuel b)) (1 # 5)). }
    assert (Ha239 : Qle (atan_mag (Datatypes.S (mach_modulus_fuel b)) (1 # 239))
                        (q_pow (1 # 239) (2 * mach_modulus_fuel b + 3))).
    { replace (2 * mach_modulus_fuel b + 3)%nat
        with (2 * Datatypes.S (mach_modulus_fuel b) + 1)%nat by lia.
      apply (mach_atan_mag_le_pow (Datatypes.S (mach_modulus_fuel b)) (1 # 239)). }
    assert (Hm : Qle (q_pow (1 # 239) (2 * mach_modulus_fuel b + 3))
                     (q_pow (1 # 5) (2 * mach_modulus_fuel b + 3))).
    { apply (mach_q_pow_mono _ (1 # 5) (1 # 239)).
      - unfold Qle. simpl. lia.
      - unfold Qle. simpl. lia. }
    apply (Qle_trans _ (16 * q_pow (1 # 5) (2 * mach_modulus_fuel b + 3)
                        + 4 * q_pow (1 # 5) (2 * mach_modulus_fuel b + 3))).
    - apply Qplus_le_compat.
      + apply (mach_Qmult_le_compat_l _ _ 16 Ha5).
        unfold Qle. simpl. lia.
      + apply (mach_Qmult_le_compat_l _ _ 4 (Qle_trans _ _ _ Ha239 Hm)).
        unfold Qle. simpl. lia.
    - apply qeq_le. ring. }
  setoid_rewrite Hsplit in Hw.
  setoid_rewrite H22s in Hw.
  assert (HC : Qle (mach_own_modulus (mach_modulus_fuel b)
                     * (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616)) 1).
  { apply (Qle_trans _
      ((20 * ((q_pow (1 # 5) (11 * mach_modulus_s b)
               * q_pow (1 # 5) (11 * mach_modulus_s b))
              * q_pow (1 # 5) 17))
       * (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616))).
    - apply (Qmult_le_compat_r _ _ (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616)).
      + exact Hw.
      + exact Hge0.
    - assert (E1 : (20 * ((q_pow (1 # 5) (11 * mach_modulus_s b)
                           * q_pow (1 # 5) (11 * mach_modulus_s b))
                          * q_pow (1 # 5) 17))
                   * (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616)
                   == 20 * q_pow (1 # 5) 17 * 4 * 71663616
                      * (q_pow (1 # 5) (11 * mach_modulus_s b)
                         * q_pow (Qmax (Qabs b) 1) 11
                         * q_pow (1 # 5) (11 * mach_modulus_s b)))
      by ring.
      rewrite E1.
      apply (Qle_trans _ ((20 * q_pow (1 # 5) 17 * 4 * 71663616) * 1)).
      + apply (mach_Qmult_le_compat_l _ 1
                 (20 * q_pow (1 # 5) 17 * 4 * 71663616)).
        * exact Hprod.
        * exact Hfac.
      + assert (E2 : (20 * q_pow (1 # 5) 17 * 4 * 71663616) * 1
                     == 20 * q_pow (1 # 5) 17 * 4 * 71663616) by ring.
        setoid_rewrite E2.
        exact Hconst. }
  unfold mach_modulus_target. unfold Qdiv.
  assert (HMne : ~ ((4 * q_pow (Qmax (Qabs b) 1) 11) == 0))
    by (apply q_neq_of_lt; exact H40).
  pose proof (Qmult_inv_r (4 * q_pow (Qmax (Qabs b) 1) 11) HMne) as HMinv.
  assert (Hcne : ~ ((71663616 # 1) == 0)) by (unfold Qeq; simpl; lia).
  pose proof (Qmult_inv_r (71663616 # 1) Hcne) as Hcinv.
  assert (Hs1 : Qle ((mach_own_modulus (mach_modulus_fuel b)
                      * (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616))
                     * /(71663616 # 1))
                    (1 * /(71663616 # 1))).
  { apply (Qmult_le_compat_r _ _ (/(71663616 # 1))).
    - exact HC.
    - apply (Qinv_le_0_compat (71663616 # 1)).
      unfold Qle. simpl. lia. }
  assert (E3 : (mach_own_modulus (mach_modulus_fuel b)
                * (4 * q_pow (Qmax (Qabs b) 1) 11 * 71663616))
               * /(71663616 # 1)
               == mach_own_modulus (mach_modulus_fuel b)
                  * (4 * q_pow (Qmax (Qabs b) 1) 11)).
  { apply (Qeq_trans _
      (mach_own_modulus (mach_modulus_fuel b)
       * (4 * q_pow (Qmax (Qabs b) 1) 11
          * ((71663616 # 1) * /(71663616 # 1))))).
    - ring.
    - rewrite Hcinv. ring. }
  assert (E4 : 1 * /(71663616 # 1) == (1 # 71663616)) by reflexivity.
  setoid_rewrite E3 in Hs1.
  setoid_rewrite E4 in Hs1.
  assert (E6r : (mach_own_modulus (mach_modulus_fuel b)
                 * (4 * q_pow (Qmax (Qabs b) 1) 11))
                * /(4 * q_pow (Qmax (Qabs b) 1) 11)
                == mach_own_modulus (mach_modulus_fuel b)).
  { apply (Qeq_trans _
      (mach_own_modulus (mach_modulus_fuel b)
       * ((4 * q_pow (Qmax (Qabs b) 1) 11)
          * /(4 * q_pow (Qmax (Qabs b) 1) 11)))).
    - ring.
    - rewrite HMinv. ring. }
  apply (Qle_trans _
    ((mach_own_modulus (mach_modulus_fuel b)
      * (4 * q_pow (Qmax (Qabs b) 1) 11))
     * /(4 * q_pow (Qmax (Qabs b) 1) 11))).
  - apply qeq_le. exact (Qeq_sym _ _ E6r).
  - apply (Qmult_le_compat_r _ _ (/(4 * q_pow (Qmax (Qabs b) 1) 11))).
    + exact Hs1.
    + apply (Qinv_le_0_compat (4 * q_pow (Qmax (Qabs b) 1) 11)).
      apply (Qlt_le_weak 0 (4 * q_pow (Qmax (Qabs b) 1) 11)). exact H40.
Qed.

(* The fuel depth passes the decidable budget predicate. *)
Lemma mach_modulus_bool_fuel : forall b : Q,
  mach_modulus_bool (mach_modulus_target b) (mach_modulus_fuel b) = true.
Proof.
  intro b. unfold mach_modulus_bool.
  apply (proj2 (Qle_bool_iff (mach_own_modulus (mach_modulus_fuel b))
                             (mach_modulus_target b))).
  apply mach_modulus_w_fuel_le.
Qed.

(* ============================================================ *)
(* Section 5.  The search specification.                         *)
(* ============================================================ *)

(* If the budget holds at depth K and the search is fuelled past K,
   the search returns a depth satisfying the budget whose every
   predecessor fails it: the mu-operator clauses. *)
Lemma mach_first_le_spec : forall fuel k K tgt,
  (k <= K)%nat -> (K < k + fuel)%nat -> mach_modulus_bool tgt K = true ->
  mach_modulus_bool tgt (mach_first_le tgt fuel k) = true
  /\ (forall m : nat, (m < mach_first_le tgt fuel k)%nat -> (k <= m)%nat ->
      mach_modulus_bool tgt m = false).
Proof.
  intro fuel. induction fuel as [| f IH]; intros k K tgt HkK HKf HK.
  - exfalso. lia.
  - cbn [mach_first_le].
    destruct (mach_modulus_bool tgt k) eqn:Eb.
    + split; [exact Eb |].
      intros m Hm Hkm. exfalso. lia.
    + assert (Hne : k <> K).
      { intro He. subst K. rewrite Eb in HK. discriminate. }
      assert (HkK' : (Datatypes.S k <= K)%nat) by lia.
      assert (HKf' : (K < Datatypes.S k + f)%nat) by lia.
      destruct (IH (Datatypes.S k) K tgt HkK' HKf' HK) as [HB HS].
      split; [exact HB |].
      intros m Hm Hkm.
      destruct (Nat.eq_dec m k) as [Heq|Hne2].
      * subst m. rewrite Eb. reflexivity.
      * apply (HS m Hm). lia.
Qed.

(* ============================================================ *)
(* Section 6.  The modulus function k(b).                        *)
(* ============================================================ *)

(* The family-one modulus function: k(b) is the least depth whose
   Machin tail width fits the c0/(4*max(|b|,1)^11) budget, delivered
   with its budget face and its minimality face. *)
Definition mach_modulus_k_of_b (b : Q) :
  sigT (fun k : nat => And
    (QleT' (mach_own_modulus k) (mach_modulus_target b))
    (forall m : nat, NatLe (Datatypes.S m) k ->
      QltT (mach_modulus_target b) (mach_own_modulus m))).
Proof.
  refine (existT _ (mach_first_le (mach_modulus_target b)
                    (Datatypes.S (mach_modulus_fuel b)) 0) _).
  split.
  - assert (Hlt : (mach_modulus_fuel b
                   < 0 + Datatypes.S (mach_modulus_fuel b))%nat) by lia.
    destruct (mach_first_le_spec (Datatypes.S (mach_modulus_fuel b)) 0
                (mach_modulus_fuel b) (mach_modulus_target b)
                (Nat.le_0_l (mach_modulus_fuel b)) Hlt
                (mach_modulus_bool_fuel b)) as [HB HS].
    apply Qle_to_QleT'.
    unfold mach_modulus_bool in HB.
    apply (proj1 (Qle_bool_iff _ _)).
    exact HB.
  - assert (Hlt : (mach_modulus_fuel b
                   < 0 + Datatypes.S (mach_modulus_fuel b))%nat) by lia.
    destruct (mach_first_le_spec (Datatypes.S (mach_modulus_fuel b)) 0
                (mach_modulus_fuel b) (mach_modulus_target b)
                (Nat.le_0_l (mach_modulus_fuel b)) Hlt
                (mach_modulus_bool_fuel b)) as [HB HS].
    intros m Hm.
    assert (Hltm : (m < mach_first_le (mach_modulus_target b)
                      (Datatypes.S (mach_modulus_fuel b)) 0)%nat).
    { apply NatLe_drop in Hm. lia. }
    pose proof (HS m Hltm (Nat.le_0_l m)) as Hfalse.
    apply Qlt_to_QltT.
    apply (mach_Qle_bool_false_lt (mach_own_modulus m) (mach_modulus_target b)).
    unfold mach_modulus_bool in Hfalse.
    exact Hfalse.
Defined.

Print Assumptions mach_modulus_k_of_b.
