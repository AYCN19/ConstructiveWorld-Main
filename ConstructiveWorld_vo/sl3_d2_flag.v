(* ================================================================= *)
(* sl3_d2_flag.v - SL3 debt D-SL3-2: the n >= 3 finite flag.           *)
(* Mission.: Z-exact direct-ratio finite flag over the kernel-sum      *)
(*   table A_{n,j} (piu_zz_Aj), parameterized by the sigma slot s.     *)
(*   The in-tree flag piu_zz_n2c_finite_le17_flag (n2c:129-132)        *)
(*   stalls under vm_compute at n = 3 on the unary zz_Tnat products    *)
(*   (n2c:150-156); this unit recasts the flag over a Z-domain         *)
(*   binary carrier (sl3_binomZ / sl3_Tbin / sl3_coef_bin /            *)
(*   sl3_term_bin / sl3_aj_bin), proves the carrier agreement chain    *)
(*   against piu_zz_Aj, welds the binary flag to the PROVEN tree       *)
(*   spec piu_zz_n2c_finite_le17_spec (n2c:135-148), and lands the     *)
(*   discharged s = 17 composite sl3_aj_flag_spec_at_17.               *)
(* Faces. Born (SL3 slot draft section 1.2, verbatim, unproven):       *)
(*   sl3_aj_finite_flag_body, sl3_aj_finite_flag_spec.  Proven here:   *)
(*   the carrier agreement chain, the Qle_bool congruence pair, the    *)
(*   flag welds, sl3_aj_flag_spec_at_17, n = 1,2 certificates.         *)
(* Dependencies.: S02_CauchyComplete; piu_zz_gauss_pair;               *)
(*   piu_zz_kernel_sum; piu_zz_n2c_sigma_assembly (proven spec).       *)
(* Constructivity.: all statements Set-carried; zero new Prop          *)
(*   surface; zero axioms, zero admitted proofs; exact Q order test    *)
(*   over Z-domain binary arithmetic; Qred per fold step.              *)
(* Build.: coqc -native-compiler no -q -Q ConstructiveWorld_Live ""    *)
(*   -Q sl3_sbx/_d2out "" sl3_d2_flag.v (Rocq 9.3.0).                  *)
(* ================================================================= *)
From Stdlib Require Import QArith ZArith Arith Lia List QArith.Qabs Qring.
From Stdlib Require Import Morphisms Setoid.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import piu_zz_gauss_pair.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_n2c_sigma_assembly.

(* ================================================================= *)
(* Section 1. Born statement faces (SL3 slot draft section 1.2,        *)
(* verbatim).  The body face is the flag; the spec face is the         *)
(* discharge contract carried as a born statement (honestly            *)
(* unproven; at s = 17 the composite over the binary flag is           *)
(* discharged below via the weld sl3_aj_flag_spec_at_17).              *)
(* ================================================================= *)

Definition sl3_aj_finite_flag_body (s : nat) (n : nat) : bool :=
  forallb (fun j => Qle_bool (Qabs (piu_zz_Aj n j))
                             (Qpower (inject_Z 2) (Z.of_nat (s * n))))
          (zz_seq (3 * n + 1)).

Definition sl3_aj_finite_flag_spec (s : nat) : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    sl3_aj_finite_flag_body s n = true ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* At s = 17 the born body face is definitionally the tree flag. *)
Lemma sl3_draft_body_agrees_tree_flag : forall n : nat,
  sl3_aj_finite_flag_body 17 n = piu_zz_n2c_finite_le17_flag n.
Proof. intros n. reflexivity. Defined.

(* the born body face itself certifies on the tree-side domain n = 1,2 *)
Lemma sl3_aj_finite_flag_body_17_n1 : sl3_aj_finite_flag_body 17 1 = true.
Proof. vm_compute. reflexivity. Defined.

Lemma sl3_aj_finite_flag_body_17_n2 : sl3_aj_finite_flag_body 17 2 = true.
Proof. vm_compute. reflexivity. Defined.

(* ================================================================= *)
(* Section 2. Z-exact binary carrier.  Same mathematical table as      *)
(* piu_zz_Aj, every arithmetic step in binary Z: the binomial is the   *)
(* Pascal recursion over Z (binary adds), the powers are Z.pow, and    *)
(* the fold reduces with Qred per step so the accumulator cannot       *)
(* blow up unreduced denominators.  The index enumeration zz_Mj and    *)
(* the Gauss product zz_big are reused from the tree unchanged, so     *)
(* the carrier differs from piu_zz_Aj only where the unary nat trap    *)
(* lives.                                                              *)
(* ================================================================= *)

Fixpoint sl3_binomZ (n k : nat) {struct n} : Z :=
  match k with
  | O => 1%Z
  | S k' =>
      match n with
      | O => 0%Z
      | S n' => sl3_binomZ n' k' + sl3_binomZ n' (S k')
      end
  end.

Definition sl3_Tbin (n : nat) (m : zz6) : Z :=
  match m with
  | (m0, m1, m2, m3, m4, m5) =>
      sl3_binomZ (3 * n + m0) m0 *
      (sl3_binomZ (2 * n) m1 *
       (sl3_binomZ (2 * n) m2 *
        (sl3_binomZ (2 * n) m3 * (sl3_binomZ (2 * n) m4 * sl3_binomZ (2 * n) m5))))
  end.

Definition sl3_coef_bin (n j : nat) (m0 m1 m2 m3 m4 m5 : nat) : Q :=
  zz_sign (m1 + m2 + m3 + m4 + m5) *
  ((sl3_Tbin n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
  ((2 ^ Z.of_nat (4 * n + j + m1)) # 2)%Q *
  ((5 ^ Z.of_nat j) # 1)%Q.

Definition sl3_term_bin (n j : nat) (m : zz6) : gz :=
  match m with
  | (m0, m1, m2, m3, m4, m5) =>
      gz_scale (sl3_coef_bin n j m0 m1 m2 m3 m4 m5) (zz_big m2 m3 m4 m5)
  end.

Fixpoint sl3_qsum_red (L : list Q) : Q :=
  match L with
  | [] => 0%Q
  | x :: L' => Qred (x + sl3_qsum_red L')
  end.

Definition sl3_aj_bin (n j : nat) : Q :=
  sl3_qsum_red (map (fun m => gz_Re (sl3_term_bin n j m)) (zz_Mj n j)).

Definition sl3_bin_flag_body (s n : nat) : bool :=
  forallb (fun j => Qle_bool (Qabs (sl3_aj_bin n j))
                             (Qpower (inject_Z 2) (Z.of_nat (s * n))))
          (zz_seq (3 * n + 1)).

(* ================================================================= *)
(* Section 3. The agreement chain: every step is a proven lemma; the   *)
(* chain welds the binary flag to the draft flag and the draft flag    *)
(* to the proven tree spec.                                            *)
(* ================================================================= *)

(* the binomial identity: the unary Pascal recursion and the binary    *)
(* Z-domain Pascal recursion agree as integers                         *)

Lemma sl3_binomZ_nat_ok : forall n k : nat, Z.of_nat (binomP n k) = sl3_binomZ n k.
Proof.
  intros n k. revert k.
  induction n as [| n IH]; intros k; destruct k as [| k'];
  cbn [binomP sl3_binomZ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Nat2Z.inj_add, (IH k'), (IH (S k')). reflexivity.
Defined.

Lemma sl3_znat_pow_ok : forall b k : nat,
  Z.of_nat (b ^ k)%nat = ((Z.of_nat b) ^ (Z.of_nat k))%Z.
Proof.
  intros b k. induction k as [| k IH].
  - reflexivity.
  - cbn [Nat.pow]. rewrite Nat2Z.inj_mul, IH, Nat2Z.inj_succ.
    rewrite (Z.pow_succ_r (Z.of_nat b) (Z.of_nat k) (Nat2Z.is_nonneg k)).
    reflexivity.
Defined.

(* component-unpacked form (the zz_T_nat_le statement precedent,       *)
(* kernel_sum:293): Rocq 9.3 rejects the nested-bracket intro pattern  *)
(* for the six-fold product, so the components are quantified          *)
(* directly and the index tuple is reconstructed inside the statement. *)
Lemma sl3_Tbin_ok : forall (n m0 m1 m2 m3 m4 m5 : nat),
  piu_zz_T n (m0, m1, m2, m3, m4, m5) = sl3_Tbin n (m0, m1, m2, m3, m4, m5).
Proof.
  intros n m0 m1 m2 m3 m4 m5.
  unfold piu_zz_T, zz_Tnat, sl3_Tbin.
  rewrite !Nat2Z.inj_mul.
  rewrite (sl3_binomZ_nat_ok (3 * n + m0) m0).
  rewrite (sl3_binomZ_nat_ok (2 * n) m1).
  rewrite (sl3_binomZ_nat_ok (2 * n) m2).
  rewrite (sl3_binomZ_nat_ok (2 * n) m3).
  rewrite (sl3_binomZ_nat_ok (2 * n) m4).
  rewrite (sl3_binomZ_nat_ok (2 * n) m5).
  reflexivity.
Defined.

(* the propositional projection of the Set-carried equality            *)
Lemma sl3_qeqT_imp_eq : forall a b : Q, qeqT a b -> (a == b)%Q.
Proof.
  intros a b h. destruct h as [a0 b0 e].
  exact e.
Defined.

(* coefficient agreement: only the three atomic identities differ      *)
Lemma sl3_coef_bin_agree : forall (n j m0 m1 m2 m3 m4 m5 : nat),
  qeqT (zz_coef n j m0 m1 m2 m3 m4 m5)
       (sl3_coef_bin n j m0 m1 m2 m3 m4 m5).
Proof.
  intros n j m0 m1 m2 m3 m4 m5.
  apply qeqT_intro. unfold zz_coef, sl3_coef_bin.
  rewrite (sl3_Tbin_ok n m0 m1 m2 m3 m4 m5).
  rewrite (sl3_znat_pow_ok 2 (4 * n + j + m1)).
  rewrite (sl3_znat_pow_ok 5 j).
  apply Qeq_refl.
Defined.

(* real part of a scaled Gauss value equals the scaled real part       *)
Lemma sl3_gz_scale_re : forall (c : Q) (z : gz),
  qeqT (gz_Re (gz_scale c z)) (c * gz_Re z)%Q.
Proof.
  intros c [a b]. apply qeqT_intro. cbn [gz_scale gz_mul gz_Re gz_Im]. ring.
Defined.

(* term-level agreement of the real parts (component-unpacked form)    *)
Lemma sl3_term_re_agree : forall (n j m0 m1 m2 m3 m4 m5 : nat),
  qeqT (gz_Re (zz_term n j (m0, m1, m2, m3, m4, m5)))
       (gz_Re (sl3_term_bin n j (m0, m1, m2, m3, m4, m5))).
Proof.
  intros n j m0 m1 m2 m3 m4 m5.
  unfold zz_term, sl3_term_bin.
  eapply qeqT_trans
    with (zz_coef n j m0 m1 m2 m3 m4 m5 * gz_Re (zz_big m2 m3 m4 m5))%Q.
  - apply sl3_gz_scale_re.
  - eapply qeqT_trans
      with (sl3_coef_bin n j m0 m1 m2 m3 m4 m5 * gz_Re (zz_big m2 m3 m4 m5))%Q.
    + apply qeqT_mul_r. apply sl3_coef_bin_agree.
    + apply qeqT_sym. apply sl3_gz_scale_re.
Defined.

(* the Qred fold computes the same value as the raw Qsum fold          *)
Lemma sl3_qsum_red_correct : forall L : list Q, qeqT (sl3_qsum_red L) (zz_Qsum L).
Proof.
  induction L as [| x L IH].
  - apply qeqT_refl.
  - cbn [sl3_qsum_red zz_Qsum fold_right].
    apply qeqT_intro. rewrite Qred_correct.
    assert (Hi : (sl3_qsum_red L == zz_Qsum L)%Q)
      by exact (sl3_qeqT_imp_eq _ _ IH).
    rewrite Hi. apply Qeq_refl.
Defined.

(* fold congruence under pointwise term agreement                      *)
Lemma sl3_qsum_map_ext : forall (f g : zz6 -> Q) (L : list zz6),
  (forall x : zz6, qeqT (f x) (g x)) ->
  qeqT (zz_Qsum (map f L)) (zz_Qsum (map g L)).
Proof.
  intros f g L H. induction L as [| x L IH].
  - apply qeqT_refl.
  - cbn [map]. unfold zz_Qsum. cbn [fold_right].
    assert (Hx : (f x == g x)%Q) by exact (sl3_qeqT_imp_eq _ _ (H x)).
    assert (HL : (zz_Qsum (map f L) == zz_Qsum (map g L))%Q)
      by exact (sl3_qeqT_imp_eq _ _ IH).
    apply qeqT_intro. rewrite Hx, HL. apply Qeq_refl.
Defined.

(* the carrier agreement: sl3_aj_bin computes piu_zz_Aj                *)
Lemma sl3_aj_bin_agree : forall n j : nat,
  qeqT (sl3_aj_bin n j) (piu_zz_Aj n j).
Proof.
  intros n j. unfold sl3_aj_bin.
  apply qeqT_trans
    with (zz_Qsum (map (fun m => gz_Re (sl3_term_bin n j m)) (zz_Mj n j))).
  - apply sl3_qsum_red_correct.
  - apply qeqT_trans with (zz_Qsum (map gz_Re (zz_terms n j))).
    + unfold zz_terms. rewrite (map_map (zz_term n j) gz_Re (zz_Mj n j)).
      apply sl3_qsum_map_ext. intros m. apply qeqT_sym.
      destruct m as [[[[[m0 m1] m2] m3] m4] m5]. apply sl3_term_re_agree.
    + apply qeqT_sym. apply piu_zz_Aj_rational.
Defined.

(* ================================================================= *)
(* Qle_bool congruence under Qeq, both argument positions.  The        *)
(* comparison is S02's Qcompare-reflecting Qle_bool, so the case       *)
(* analysis goes through Qcompare_spec (the same three-way shape the   *)
(* S02 bridge lemmas use); every contradiction case is closed with     *)
(* Q-level order chains, no arithmetic on raw Z products.              *)
(* ================================================================= *)

Lemma sl3_qle_bool_left : forall a b c : Q,
  a == b -> Qle_bool a c = Qle_bool b c.
Proof.
  intros a b c Hab.
  unfold Qle_bool.
  destruct (Qcompare_spec a c) as [Eac | Haltc | Hclta];
  destruct (Qcompare_spec b c) as [Ebc | Haltb | Hcltb]; try reflexivity.
  - exfalso.
    assert (Hba : (b <= a)%Q) by (apply qeq_imp_qle; apply Qeq_sym; exact Hab).
    assert (Hlt : (a < b)%Q).
    { apply (Qle_lt_trans a c b). apply qeq_imp_qle. exact Eac. exact Hcltb. }
    exact (Qlt_irrefl a (Qlt_le_trans a b a Hlt Hba)).
  - exfalso.
    assert (Hba : (b <= a)%Q) by (apply qeq_imp_qle; apply Qeq_sym; exact Hab).
    assert (Hlt : (a < b)%Q) by exact (Qlt_trans a c b Haltc Hcltb).
    exact (Qlt_irrefl a (Qlt_le_trans a b a Hlt Hba)).
  - exfalso.
    assert (Hb : (b < a)%Q).
    { apply (Qle_lt_trans b c a). apply qeq_imp_qle. exact Ebc. exact Hclta. }
    apply (Qlt_irrefl b).
    apply (Qlt_le_trans b a b). exact Hb. apply qeq_imp_qle. exact Hab.
  - exfalso.
    assert (Hb : (b < a)%Q) by exact (Qlt_trans b c a Haltb Hclta).
    apply (Qlt_irrefl b).
    apply (Qlt_le_trans b a b). exact Hb. apply qeq_imp_qle. exact Hab.
Defined.

Lemma sl3_qle_bool_right : forall a c d : Q,
  c == d -> Qle_bool a c = Qle_bool a d.
Proof.
  intros a c d Hcd.
  unfold Qle_bool.
  destruct (Qcompare_spec a c) as [Eac | Haltc | Hclta];
  destruct (Qcompare_spec a d) as [Ead | Haltd | Hdlta]; try reflexivity.
  - exfalso.
    assert (Hac : (a <= c)%Q) by (apply qeq_imp_qle; exact Eac).
    assert (Hcd2 : (c <= d)%Q) by (apply qeq_imp_qle; exact Hcd).
    assert (Had : (a <= d)%Q) by exact (Qle_trans a c d Hac Hcd2).
    exact (Qlt_irrefl d (Qlt_le_trans d a d Hdlta Had)).
  - exfalso.
    assert (Had : (a <= d)%Q).
    { apply (Qle_trans a c d). apply Qlt_le_weak. exact Haltc.
      apply qeq_imp_qle. exact Hcd. }
    exact (Qlt_irrefl d (Qlt_le_trans d a d Hdlta Had)).
  - exfalso.
    assert (Had : (a <= d)%Q) by (apply qeq_imp_qle; exact Ead).
    assert (Hlt : (c < d)%Q) by exact (Qlt_le_trans c a d Hclta Had).
    exact (Qlt_irrefl c (Qlt_le_trans c d c Hlt (qeq_imp_qle d c (Qeq_sym c d Hcd)))).
  - exfalso.
    assert (Hlt : (c < d)%Q) by exact (Qlt_le_trans c a d Hclta (Qlt_le_weak a d Haltd)).
    exact (Qlt_irrefl c (Qlt_le_trans c d c Hlt (qeq_imp_qle d c (Qeq_sym c d Hcd)))).
Defined.

(* ================================================================= *)
(* Flag-level welds.                                                   *)
(* ================================================================= *)

Lemma sl3_flag_pointwise : forall (s n j : nat),
  Qle_bool (Qabs (sl3_aj_bin n j)) (Qpower (inject_Z 2) (Z.of_nat (s * n))) =
  Qle_bool (Qabs (piu_zz_Aj n j)) (Qpower (inject_Z 2) (Z.of_nat (s * n))).
Proof.
  intros s n j.
  destruct (sl3_aj_bin_agree n j) as [x0 y0 e].
  apply (sl3_qle_bool_left _ _ _ (Qabs_wd _ _ e)).
Defined.

Lemma sl3_forallb_ext : forall (f g : nat -> bool) (L : list nat),
  (forall x : nat, f x = g x) -> forallb f L = forallb g L.
Proof.
  intros f g L H. induction L as [| x L IH].
  - reflexivity.
  - cbn [forallb]. rewrite (H x), IH. reflexivity.
Defined.

Lemma sl3_bin_flag_eq_draft : forall s n : nat,
  sl3_bin_flag_body s n = sl3_aj_finite_flag_body s n.
Proof.
  intros s n. unfold sl3_bin_flag_body, sl3_aj_finite_flag_body.
  apply (sl3_forallb_ext
          (fun j => Qle_bool (Qabs (sl3_aj_bin n j))
                             (Qpower (inject_Z 2) (Z.of_nat (s * n))))
          (fun j => Qle_bool (Qabs (piu_zz_Aj n j))
                             (Qpower (inject_Z 2) (Z.of_nat (s * n))))
          (zz_seq (3 * n + 1))).
  intros x. apply sl3_flag_pointwise.
Defined.

(* the discharged composite at s = 17: a true binary flag discharges   *)
(* the sharp face pointwise, via the PROVEN tree spec                  *)
Lemma sl3_aj_flag_spec_at_17 :
  forall n j : nat, (j <= 3 * n)%nat ->
    sl3_bin_flag_body 17 n = true ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (17 * n))).
Proof.
  intros n j Hj H.
  apply (piu_zz_n2c_finite_le17_spec n j Hj).
  change (sl3_aj_finite_flag_body 17 n = true).
  rewrite <- (sl3_bin_flag_eq_draft 17 n).
  exact H.
Defined.

(* binary-carrier sanity anchors on the tree-side domain n = 1,2       *)
Lemma sl3_bin_flag_17_n1 : sl3_bin_flag_body 17 1 = true.
Proof. vm_compute. reflexivity. Defined.

Lemma sl3_bin_flag_17_n2 : sl3_bin_flag_body 17 2 = true.
Proof. vm_compute. reflexivity. Defined.

(* ================================================================= *)
(* Section 4. Assumption audit.                                        *)
(* ================================================================= *)

Print Assumptions sl3_binomZ_nat_ok.
Print Assumptions sl3_znat_pow_ok.
Print Assumptions sl3_Tbin_ok.
Print Assumptions sl3_coef_bin_agree.
Print Assumptions sl3_term_re_agree.
Print Assumptions sl3_qsum_red_correct.
Print Assumptions sl3_qsum_map_ext.
Print Assumptions sl3_aj_bin_agree.
Print Assumptions sl3_qle_bool_left.
Print Assumptions sl3_qle_bool_right.
Print Assumptions sl3_flag_pointwise.
Print Assumptions sl3_forallb_ext.
Print Assumptions sl3_bin_flag_eq_draft.
Print Assumptions sl3_draft_body_agrees_tree_flag.
Print Assumptions sl3_aj_flag_spec_at_17.
Print Assumptions sl3_aj_finite_flag_body_17_n1.
Print Assumptions sl3_aj_finite_flag_body_17_n2.
Print Assumptions sl3_bin_flag_17_n1.
Print Assumptions sl3_bin_flag_17_n2.
