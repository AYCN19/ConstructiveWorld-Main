(* sl12_w3_zz2020_transcript.v - born transcription of the ZZ2020
   Lemma faces (arXiv:1912.06345v2) with machine sample anchors.
   Ticket: SL12 ticket SL2-b supply line / SL1 coupling (T3 certificate
   delivery, wave three; GD single number external per provenance).
   Mission: cast the three ZZ2020 lemma faces in the born Set idiom
   (zero postulates, v2 body numbering) and anchor each on small
   samples (per-section boundary notes record what is not cast).
   Statement inventory: sl12_w3_zq; the Q-polynomial toolkit
   (padd/pmul/ppow/pshift/qneg5/q10/bin_num/factZ/binZ); sl12_w3_Gpoly
   with pole Taylor coefficients sl12_w3_gcoef; sl12_w3_Acoef; the
   even-numerator anchor of R(-x) = R(x); the five faces and anchors
   named in their section headers below.
   Source routing: pickup volume hexit-ZZ2020 (arXiv:1912.06345v2 HTML
   single source, md5 6344f7fc..., export mirror); equation numbers
   follow the v2 body numbering (Lemma 1 = eq. (4); the padic-clearing
   header cites eq. (5), a registered drift); the eq. (9) flat-quote
   ambiguity resolves to the literal /j reading.
   Dependencies: piu_zz_padic_clearing; planb4_g1_witness;
   sl1_phi_divides_L; stdlib QArith, ZArith, Arith, Qpower, List, Lia.
   References: pickup volume hexit-ZZ2020 sections 5.2-5.6; slot
   statement draft SL12 section 2.2; survey volume sections 4.2/5.1.
   Constructivity: Set-carried bool/Id faces; zero global assumptions,
   zero proof surrender, zero solver closers; anchors are vm_compute
   boolean pins (Qed kept per the upstream anchor registration);
   definitions, faces, and lemmas are Defined.
   Build: coqc -native-compiler no -q -Q world "" sl12_w3_zz2020_transcript.v
   (script form via the driver; output to the sandbox OUT directory).
   Related registrations: consumes the wave-two SL1 world closure
   (byte-identical sources and vo trust cache); the window-inclusion
   lemma feeds sl12_w3_sl1_certs.v. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import piu_zz_padic_clearing.
Require Import planb4_g1_witness.
Require Import sl1_phi_divides_L.

Import ListNotations.

(* ==== Section 1: the rational integrality probe ==== *)

(* A rational number is an integer exactly when its reduced form has
   denominator one (decidable boolean form). *)
Definition sl12_w3_zq (q : Q) : bool :=
  Pos.eqb (Qden (Qred q)) 1%positive.

(* ==== Section 2: the Q-polynomial toolkit (coefficient lists, index = degree) ==== *)

Fixpoint sl12_w3_padd (p q : list Q) : list Q :=
  match p with
  | [] => q
  | a :: p' =>
      match q with
      | [] => p
      | b :: q' => (a + b)%Q :: sl12_w3_padd p' q'
      end
  end.

Fixpoint sl12_w3_pmul (p q : list Q) : list Q :=
  match p with
  | [] => []
  | a :: p' =>
      sl12_w3_padd (map (fun x => (a * x)%Q) q)
                   (0%Q :: sl12_w3_pmul p' q)
  end.

Fixpoint sl12_w3_ppow (p : list Q) (k : nat) : list Q :=
  match k with
  | O => [1%Q]
  | S k' => sl12_w3_pmul p (sl12_w3_ppow p k')
  end.

Definition sl12_w3_pshift (p : list Q) (k : nat) : list Q :=
  repeat 0%Q k ++ p.

(* (-5)^k over Q (the shift centre is the pole x = -5). *)
Fixpoint sl12_w3_qneg5 (k : nat) : Q :=
  match k with
  | O => 1%Q
  | S k' => Qopp (5 # 1)%Q * sl12_w3_qneg5 k'
  end.

(* 10^k over Q. *)
Fixpoint sl12_w3_q10 (k : nat) : Q :=
  match k with
  | O => 1%Q
  | S k' => (10 * sl12_w3_q10 k')%Q
  end.

(* the binomial coefficient C(k, i) over Z (multiplicative form with an
   exact final division; zero for i > k).  The naive Pascal recursion
   is exponential in k and unusable at the pole degrees here. *)
Fixpoint sl12_w3_bin_num (k i t : nat) : Z :=
  match t with
  | O => 1%Z
  | S t' => (Z.of_nat (k - i + S t') * sl12_w3_bin_num k i t')%Z
  end.

Fixpoint sl12_w3_factZ (t : nat) : Z :=
  match t with
  | O => 1%Z
  | S t' => (Z.of_nat (S t') * sl12_w3_factZ t')%Z
  end.

Definition sl12_w3_binZ (k i : nat) : Z :=
  if Nat.leb i k
  then Z.div (sl12_w3_bin_num k i i) (sl12_w3_factZ i)
  else 0%Z.

(* ==== Section 3: the ZZ2020 numerator polynomial and its pole expansion ==== *)

(* G(x) = 5 * x^(2n) * (x^4 + 6 x^2 + 25)^(2n): the numerator of the
   ZZ2020 rational form R(x) = G(x) / ((5+x)^(3n+1) (5-x)^(3n+1)) after
   clearing one denominator factor (pickup volume section 5.2). *)
Definition sl12_w3_Hpoly : list Q := [25%Q; 0%Q; 6%Q; 0%Q; 1%Q].

Definition sl12_w3_Gpoly (n : nat) : list Q :=
  sl12_w3_pmul (sl12_w3_pshift [5%Q] (2 * n))
               (sl12_w3_ppow sl12_w3_Hpoly (2 * n)).

(* Taylor coefficients of G at the pole: G(-5 + u) = sum_i g_i u^i. *)
Fixpoint sl12_w3_tay (a : list Q) (i k : nat) : Q :=
  match a with
  | [] => 0%Q
  | x :: a' =>
      (x * (sl12_w3_binZ k i # 1)%Q * sl12_w3_qneg5 (k - i))%Q
      + sl12_w3_tay a' i (S k)
  end.

Definition sl12_w3_gcoef (n i : nat) : Q :=
  sl12_w3_tay (sl12_w3_Gpoly n) i 0.

(* The partial-fraction coefficients of eq. (3): with u = 5 + x the
   factor (5 - x)^{-(3n+1)} expands as
   sum_k C(3n+k, k) u^k / 10^(3n+1+k), and the coefficient of
   (5+x)^{-(j+1)} reads A_j = [u^(3n-j)] of the product. *)
Definition sl12_w3_Afrom (n m : nat) : Q :=
  fold_right (fun (i : nat) (acc : Q) =>
      (((sl12_w3_gcoef n i
         * (sl12_w3_binZ (3 * n + (m - i)) (m - i) # 1)%Q
         / sl12_w3_q10 (3 * n + 1 + (m - i)))%Q + acc)%Q))
    0%Q (seq 0 (S m)).

Definition sl12_w3_Acoef (n j : nat) : Q :=
  sl12_w3_Afrom n (3 * n - j).

(* eq. (10) boundary note: the Gamma / Prime-Number-Theorem asymptotic
   of the pickup volume is an analytic limit face and stays outside the
   born Set idiom; it is registered, not cast. *)

(* ==== Section 4: the symmetry clause R(-x) = R(x) (even-numerator form) ==== *)

(* The denominator (25 - x^2)^(3n+1) is even, so R(-x) = R(x) reduces
   to the numerator being an even polynomial: all odd-degree
   coefficients of G vanish (machine-checked over n <= 6). *)
Definition sl12_w3_Rpoly_even (n : nat) : bool :=
  forallb (fun i => Qeq_bool (nth i (sl12_w3_Gpoly n) 0%Q) 0%Q)
          (filter Nat.odd (seq 0 (S (10 * n)))).

Example sl12_w3_Rpoly_even_anchor :
  forallb (fun n => sl12_w3_Rpoly_even n) (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 5: Lemma 1 = eq. (4), the scaled-coefficient integrality ==== *)

(* Quote face (pickup volume section 5.3, v2 body numbering):
   2^(-floor((5n+3j)/2)+1) * 5^(-j) * A_j is an integer for
   j = 0, ..., 3n.  The negative exponents read as division: the
   scaled coefficient divides A_j by 2^(floor((5n+3j)/2)-1) * 5^j. *)
Definition sl12_w3_L1_scaled (n j : nat) : Q :=
  (Qpower (2 # 1)%Q (Z.of_nat 1 - Z.of_nat ((5 * n + 3 * j) / 2))
   * Qpower (1 # 5)%Q (Z.of_nat j) * sl12_w3_Acoef n j)%Q.

Definition sl12_w3_Lemma1_face : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    BidT (sl12_w3_zq (sl12_w3_L1_scaled n j)).

Definition sl12_w3_L1_grid (n : nat) : bool :=
  forallb (fun j => sl12_w3_zq (sl12_w3_L1_scaled n j)) (seq 0 (S (3 * n))).

(* Machine anchor: the quote face holds on the full grid n <= 6
   (each j = 0 .. 3n), matching the exact-rational mirror. *)
Example sl12_w3_L1_anchor :
  forallb (fun n => sl12_w3_L1_grid n) (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 6: Lemma 2 = the P_n set clause (read after eq. (6)) ==== *)

(* Subset face (pickup volume section 5.4, verbatim shape): every
   member of P_n is a prime in (5, 2n].  Primality and the lower bound
   5 < p are zz_in_Pn components already; the upper bound p <= 2n
   follows because p > 2n forces n mod p = n, contradicting the
   window component p <= 2 (n mod p). *)
Lemma sl12_w3_Pn_le_2n : forall n p : nat,
  BidT (zz_in_Pn n p) -> BidT (Nat.leb p (2 * n)).
Proof.
  intros n p H. apply BidT_elim in H. unfold zz_in_Pn in H.
  apply Bool.andb_true_iff in H. destruct H as [Hp Hr].
  apply Bool.andb_true_iff in Hr. destruct Hr as [H5 Hr].
  apply Bool.andb_true_iff in Hr. destruct Hr as [_ Hr].
  apply Bool.andb_true_iff in Hr. destruct Hr as [Hw1 _].
  apply BidT_intro.
  destruct (Nat.leb p (2 * n)) eqn:Eb.
  - reflexivity.
  - exfalso.
    apply Nat.leb_gt in Eb.
    apply (proj1 (Nat.ltb_lt 5 p)) in H5.
    apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    assert (Hnp : (n < p)%nat) by lia.
    rewrite (Nat.mod_small n p Hnp) in Hw1.
    lia.
Defined.

(* Window-inclusion face: for n >= 4 the prime window (3n/2, 2n] is
   contained in P_n.  On this window the fractional part {n/p} equals
   n/p itself (p > n), so both window components hold directly; the
   primality, lower-bound, and square-root components follow from
   p >= 7 and 2p > 3n.  This face is the structural bridge from the
   ZZ2020 window to the SL1 Phi-band supply line. *)
Lemma sl12_w3_window_in_Pn : forall n p : nat, (4 <= n)%nat ->
  zz_primeb p = true -> (3 * n < 2 * p)%nat -> (p <= 2 * n)%nat ->
  BidT (zz_in_Pn n p).
Proof.
  intros n p Hn Hprime Hwin Hle. apply BidT_intro. unfold zz_in_Pn.
  apply Bool.andb_true_iff. split; [exact Hprime |].
  apply Bool.andb_true_iff. split.
  - apply (proj2 (Nat.ltb_lt 5 p)).
    assert (Hp7 : (7 <= p)%nat) by lia.
    lia.
  - apply Bool.andb_true_iff. split.
    + apply (proj2 (Nat.ltb_lt (3 * n) (p * p))).
      assert (Hpn : (n < p)%nat) by lia.
      assert (Hpp : (3 * p <= p * p)%nat) by nia.
      lia.
    + apply Bool.andb_true_iff. split.
      * apply (proj2 (Nat.leb_le p (2 * (n mod p)))).
        assert (Hnp : (n < p)%nat) by lia.
        rewrite (Nat.mod_small n p Hnp). exact Hle.
      * apply (proj2 (Nat.ltb_lt (3 * (n mod p)) (2 * p))).
        assert (Hnp : (n < p)%nat) by lia.
        rewrite (Nat.mod_small n p Hnp). exact Hwin.
Defined.

(* Non-vacuity sample anchors: the P_n window is empty for n <= 3 and
   these samples carry real members (exact-rational mirror agrees). *)
Example sl12_w3_Pn_member_anchor :
  zz_in_Pn 4 7 = true /\ zz_in_Pn 6 11 = true /\ zz_in_Pn 7 11 = true /\
  zz_in_Pn 7 13 = true /\ zz_in_Pn 8 13 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The Lemma 2 divisibility property on samples: for p in P_n and
   j with p | j (sampled j = 0 and j = p), the reduced form of A_j has
   numerator 0 modulo p and denominator prime to p. *)
Definition sl12_w3_q_0mod (p : nat) (q : Q) : bool :=
  andb (Z.eqb (Z.rem (Qnum (Qred q)) (Z.of_nat p)) 0%Z)
       (negb (Z.eqb (Z.rem (Z.pos (Qden (Qred q))) (Z.of_nat p)) 0%Z)).

Definition sl12_w3_L2_prop_check (n p j : nat) : bool :=
  sl12_w3_q_0mod p (sl12_w3_Acoef n j).

Example sl12_w3_L2_prop_anchor :
  sl12_w3_L2_prop_check 4 7 0 = true /\ sl12_w3_L2_prop_check 4 7 7 = true /\
  sl12_w3_L2_prop_check 6 11 0 = true /\ sl12_w3_L2_prop_check 6 11 11 = true /\
  sl12_w3_L2_prop_check 7 11 0 = true /\ sl12_w3_L2_prop_check 7 11 11 = true /\
  sl12_w3_L2_prop_check 7 13 0 = true /\ sl12_w3_L2_prop_check 7 13 13 = true /\
  sl12_w3_L2_prop_check 8 13 0 = true /\ sl12_w3_L2_prop_check 8 13 13 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ==== Section 7: Lemma 3 = eq. (9) and the Phi-divides-lcm face ==== *)

(* The L_n integrality face: Phi_n divides lcm(1..4n), so the ZZ2020
   L_n = lcm(1..4n) / Phi_n is an integer for every n.  Proven by
   consuming the in-tree divisibility theorem (its witness q satisfies
   q * Phi_n = lcm(1..4n)), which yields the boolean remainder check. *)
Lemma sl12_w3_L3_Lint_face : forall n : nat,
  BidT (Z.eqb (planb4_L n mod planb4_Phi n) 0%Z).
Proof.
  intro n.
  pose proof (sl1_phi_divides_L n) as Hw. destruct Hw as [q Hq].
  apply Bid_elim in Hq.
  assert (HB : Bdiv (planb4_Phi n) (planb4_L n)).
  { exists q. apply Bid_intro. rewrite Z.mul_comm. exact Hq. }
  apply BidT_intro. exact (Bdiv_eqb _ _ HB).
Defined.

(* Machine anchor of the divisibility face over n <= 40 (the shared
   table domain of the wave-two anchors). *)
Definition sl12_w3_L3_Lint_check (n : nat) : bool :=
  Z.eqb (planb4_L n mod planb4_Phi n) 0%Z.

Example sl12_w3_L3_Lint_anchor :
  forallb (fun n => sl12_w3_L3_Lint_check n) (seq 0 41) = true.
Proof. vm_compute. reflexivity. Qed.

(* eq. (9) face, literal /j reading: L_n * 10^(-j) * A_j / j is an
   integer for n >= 1 and 1 <= j <= 3n (the j = 0 endpoint is excluded
   by the division; the mirror confirmed the /j reading and refuted
   the /j! reading from n = 2).  Born statement; the forall-n proof is
   the remaining supply debt of the transcription. *)
Definition sl12_w3_L3_eq9_scaled (n j : nat) : Q :=
  (inject_Z (planb4_LZn n) * Qpower (1 # 10)%Q (Z.of_nat j)
   * sl12_w3_Acoef n j / (Z.of_nat j # 1)%Q)%Q.

Definition sl12_w3_L3_eq9_face : Set :=
  forall n j : nat, (1 <= n)%nat -> (1 <= j)%nat -> (j <= 3 * n)%nat ->
    BidT (sl12_w3_zq (sl12_w3_L3_eq9_scaled n j)).

(* Machine anchor of the eq. (9) face over the grid n = 1..6,
   j = 1 .. 3n. *)
Definition sl12_w3_L3_eq9_check (n j : nat) : bool :=
  sl12_w3_zq (sl12_w3_L3_eq9_scaled n j).

Example sl12_w3_L3_eq9_anchor :
  forallb (fun n => forallb (fun j => sl12_w3_L3_eq9_check n j) (seq 1 (3 * n)))
          (seq 1 6) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sl12_w3_Lemma1_face.
Print Assumptions sl12_w3_Pn_le_2n.
Print Assumptions sl12_w3_window_in_Pn.
Print Assumptions sl12_w3_L3_Lint_face.
Print Assumptions sl12_w3_L3_eq9_face.
Print Assumptions sl12_w3_Rpoly_even_anchor.
Print Assumptions sl12_w3_L1_anchor.
Print Assumptions sl12_w3_Pn_member_anchor.
Print Assumptions sl12_w3_L2_prop_anchor.
Print Assumptions sl12_w3_L3_Lint_anchor.
Print Assumptions sl12_w3_L3_eq9_anchor.
