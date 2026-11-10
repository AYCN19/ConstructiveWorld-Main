(* ConstructiveWorld-Main - leaf a of the three-cosine racing engine: the rational transport kit. *)
(** * GaC3_Z03_NonzeroLine_a: leaf a of node C3-Z03.

    Mission.  Leaf a of the three-cosine racing engine (node C3-Z03,
    segment C3): the rational transport kit and the Q-level congruence
    kit.  Part 0a moves the strict and weak rational orders along Qeq
    (the numeric Qlt/Qle definitions are comparison-based, so the
    transport goes through Qlt_alt and the Qcompare_comp proper
    instance); the two-sided absolute-value faces (the negation below
    the absolute value, the value itself below its absolute value, and
    the lower-bound transfer along an absolute value) feed the
    Real-level relax kit of leaf b.  The cosine term kit is
    ring-congruent through the q_pow setoid face [q_pow_wd] of S03
    (term congruence and partial-sum congruence), the consumption base
    of the pointwise cosine face in leaf b.  The racing-engine core
    (the real-part bridge, the combined carrier and its equality face)
    lives in the stem [GaC3_Z03_NonzeroLine]; the relax-order kit and
    the Real assistants live in leaf b [GaC3_Z03_NonzeroLine_b]; the
    discharge and racing faces live in [GaC3_Z03_NonzeroLine_race];
    the literal radius certificates live in
    [GaC3_Z03_NonzeroLine_cert].

    Dependencies.  Stdlib [QArith.QArith] (with [Qabs] and [Qring]);
    [S03_QExp] ([q_pow_wd]); [S10_KVQuantTrig] ([cos_term],
    [cos_partial]).

    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163 (the three-cosine weighted inequality assembled on these
    term faces); drafts_C3.md C3-Z03 (the racing skeleton, the
    explicit-radius obligation); cards_C3 C3-Z03 (the three-cosine
    nonvanishing argument).

    Constructivity.  Set-sorted rational order transports and
    congruences; zero assumed constants, zero abandoned proofs, zero
    classical choice; Print Assumptions of every named item reads
    Closed under the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_Z03_NonzeroLine_a.v] from the work directory through the
    dependency-closure build (50_toolkit/build_deposit.py); acceptance
    runs use 50_toolkit/accept_node.py and write accept/<node>.json. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 0a. The rational transport kit: Qeq moves the strict and weak    *)
(* orders (the numeric Qlt/Qle definitions are comparison-based, so the  *)
(* transport goes through Qlt_alt and the Qcompare_comp proper instance).*)
(* ===================================================================== *)

Lemma qeq_lt_l : forall a b c : Q, Qeq a b -> Qlt b c -> Qlt a c.
Proof.
  intros a b c Hab Hbc.
  apply Qlt_alt in Hbc. apply Qlt_alt.
  rewrite (Qcompare_comp a b Hab c c (Qeq_refl c)). exact Hbc.
Qed.

Lemma qeq_lt_r : forall a b c : Q, Qeq b c -> Qlt a b -> Qlt a c.
Proof.
  intros a b c Hbc Hab.
  apply Qlt_alt in Hab. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c Hbc). exact Hab.
Qed.

Lemma qeq_le_l : forall a b c : Q, Qeq a b -> Qle b c -> Qle a c.
Proof.
  intros a b c Hab Hbc.
  apply Qle_alt in Hbc. apply Qle_alt.
  rewrite (Qcompare_comp a b Hab c c (Qeq_refl c)). exact Hbc.
Qed.

Lemma qeq_le_r : forall a b c : Q, Qeq b c -> Qle a b -> Qle a c.
Proof.
  intros a b c Hbc Hab.
  apply Qle_alt in Hab. apply Qle_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c Hbc). exact Hab.
Qed.

Lemma qeq_minus_r0 : forall a z : Q, Qeq z 0 -> Qeq (a - z) a.
Proof.
  intros a z Hz.
  assert (H1 : Qeq (a - z) (a - 0))
    by exact (Qminus_comp a a (Qeq_refl a) z 0 Hz).
  assert (H2 : Qeq (a - 0) a) by ring.
  exact (Qeq_trans _ _ _ H1 H2).
Qed.

(* The negation is below the absolute value (the weak half of the       *)
(* triangle fact). *)
Lemma qopp_le_abs : forall u : Q, Qle (- u) (Qabs u).
Proof.
  intro u. destruct (Q_dec u 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    exact (qeq_le_r (- u) (- u) (Qabs u)
             (Qeq_sym (Qabs u) (- u) Habs) (Qle_refl (- u))).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    assert (Hneg : Qle (- u) 0)
      by exact (Qopp_le_compat 0 u (Qlt_le_weak 0 u Hcgt)).
    exact (qeq_le_r (- u) u (Qabs u) (Qeq_sym (Qabs u) u Habs)
             (Qle_trans (- u) 0 u Hneg (Qlt_le_weak 0 u Hcgt))).
  - assert (H0u : Qle 0 u) by exact (qeq_le_l 0 u u (Qeq_sym u 0 Hc) (Qle_refl u)).
    assert (Habs : Qabs u == u) by exact (Qabs_pos u H0u).
    assert (Hneg : Qle (- u) 0) by exact (Qopp_le_compat 0 u H0u).
    exact (qeq_le_r (- u) u (Qabs u) (Qeq_sym (Qabs u) u Habs)
             (Qle_trans (- u) 0 u Hneg H0u)).
Qed.

(* The mirrored half: the value itself is below its absolute value. *)
Lemma qself_le_abs : forall u : Q, Qle u (Qabs u).
Proof.
  intro u. destruct (Q_dec u 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    assert (Hle : Qle u (- u)).
    { apply (Qle_trans u 0 (- u)).
      - apply Qlt_le_weak. exact Hclt.
      - exact (Qopp_le_compat u 0 (Qlt_le_weak u 0 Hclt)). }
    exact (qeq_le_r u (- u) (Qabs u) (Qeq_sym (Qabs u) (- u) Habs) Hle).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    exact (qeq_le_r u u (Qabs u) (Qeq_sym (Qabs u) u Habs) (Qle_refl u)).
  - assert (H0u : Qle 0 u) by exact (qeq_le_l 0 u u (Qeq_sym u 0 Hc) (Qle_refl u)).
    assert (Habs : Qabs u == u) by exact (Qabs_pos u H0u).
    exact (qeq_le_r u u (Qabs u) (Qeq_sym (Qabs u) u Habs) (Qle_refl u)).
Qed.

(* The two-sided face: an absolute value below b puts -b below the value. *)
Lemma qabs_lb : forall a b : Q, Qlt 0 b -> Qlt (Qabs a) b -> Qlt (- b) a.
Proof.
  intros a b Hb Hab.
  destruct (Q_dec a 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs a == - a) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    assert (Hneg : Qlt (- a) b)
      by exact (qeq_lt_l (- a) (Qabs a) b (Qeq_sym (Qabs a) (- a) Habs) Hab).
    assert (Hopp : Qlt (- b) (- (- a))) by (apply (Qopp_lt_compat (- a) b); exact Hneg).
    apply (qeq_lt_r (- b) (- (- a)) a).
    * ring.
    * exact Hopp.
  - assert (Habs : Qabs a == a) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    assert (Hlowlt : Qlt (- b) (Qabs a)).
    { apply (Qlt_le_trans (- b) 0 (Qabs a)).
      - apply (Qopp_lt_compat 0 b). exact Hb.
      - apply Qabs_nonneg. }
    exact (qeq_lt_r (- b) (Qabs a) a Habs Hlowlt).
  - apply (qeq_lt_r (- b) 0 a).
    * exact (Qeq_sym a 0 Hc).
    * apply (Qopp_lt_compat 0 b). exact Hb.
Qed.

(* The Q-level congruence of the cosine partial sums (the term kit is   *)
(* ring-congruent through the q_pow setoid face q_pow_wd of S03). *)
Lemma z03_sc_cos_term_congr : forall (j : nat) (x y : Q),
  Qeq x y -> Qeq (cos_term j x) (cos_term j y).
Proof.
  intros j x y H. unfold cos_term.
  rewrite (q_pow_wd x y (2 * j) H). ring.
Qed.

Lemma z03_sc_cos_partial_congr : forall (n : nat) (x y : Q),
  Qeq x y -> Qeq (cos_partial n x) (cos_partial n y).
Proof.
  intros n x y H. induction n as [| n IH]; simpl.
  - apply z03_sc_cos_term_congr. exact H.
  - apply (Qeq_trans (cos_partial n x + cos_term (Datatypes.S n) x)
                     (cos_partial n y + cos_term (Datatypes.S n) x)
                     (cos_partial n y + cos_term (Datatypes.S n) y)).
    + exact (Qplus_comp (cos_partial n x) (cos_partial n y) IH
               (cos_term (Datatypes.S n) x) (cos_term (Datatypes.S n) x)
               (Qeq_refl (cos_term (Datatypes.S n) x))).
    + exact (Qplus_comp (cos_partial n y) (cos_partial n y)
               (Qeq_refl (cos_partial n y))
               (cos_term (Datatypes.S n) x) (cos_term (Datatypes.S n) y)
               (z03_sc_cos_term_congr (Datatypes.S n) x y H)).
Qed.
