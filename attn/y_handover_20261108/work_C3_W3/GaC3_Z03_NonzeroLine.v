(* ConstructiveWorld-Main - the three-cosine nonvanishing line engine. *)

(** * GaC3_Z03_NonzeroLine: the three-cosine racing engine for the
    nonvanishing line Re s = 1.

    Mission.  Node C3-Z03 (segment C3): the constructive core of the
    three-cosine nonvanishing argument.  Part 1 (assumption-free)
    assembles the von Mangoldt weighted partial sums [z01_manpart] (Z01)
    at the three racing points under the 3-4-1 weights and proves the
    combined real part asymptotically nonnegative ([z03_comb_nonneg],
    the tree-native form of the ZZ logderiv_zeta_ineq architecture).
    Part 2 casts the racing contradiction in explicit-radius slot form
    ([z03_racing_contra]): under the registered premise slots (the
    four-term main part at the offset d, the sigma-term and the
    doubled-ordinate upper bounds) and the explicit window arithmetic,
    the nonnegativity face yields False.  The literal zeta-carrier
    statement awaits the eta-continuation supply face; the slot form
    is the consumption shape of the certified V03 pattern.

    Dependencies.  [S01_BaseRing], [S02_CauchyComplete] (order faces),
    [S03_QExp] ([q_pow_wd]), [S07_RealSetoidExpLog] (RealSetoid compat,
    exp), [S10_KVQuantTrig] ([cauchy_real_cos]), [CxRealPairCore] +
    [CxRealPairExpLog] (base pair), [GaC2_Iface_DS] ([c_powq],
    [nat_real_pos] via the leaf import), [GaC3_Z01_LogDerivSeries]
    ([z01_lam], [z01_manpart]), [GaC3_Z02_ThreeCosine] (identity and
    pointwise square face); Stdlib [QArith] (with [Qring]), [Arith],
    [Lia].

    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163 (the three-cosine weighted inequality); drafts_C3.md C3-Z03
    (racing skeleton, explicit-radius obligation); cards_C3 C3-Z03
    (multiplicity main part).  The four-term main-part slot is the
    registered open supply face (zero factorization route).

    Constructivity.  Every named construction is carried by [Set]; the
    nonnegativity face is carried by [real_ge_relax] (the asymptotic
    order, per the Z02 precedent on the equality-versus-positivity
    obstruction).  Zero assumed constants, zero abandoned proofs, zero
    classical choice; the premise slots leave as explicit arguments at
    End, so Print Assumptions of every named item reads Closed under
    the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_Z03_NonzeroLine.v] from the work directory, single compile
    lane under the thermal guard wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_Z02_ThreeCosine.

Local Open Scope Q_scope.

(* The shared pointwise normalisation: expand the real-level sums and   *)
(* products down to the rational approximations, then close by ring.    *)
Ltac z03_pt :=
  repeat (first [rewrite real_mult_proj | rewrite real_plus_proj
                | rewrite real_opp_proj]);
  repeat match goal with
         | [ |- context[projT1 real_one ?n] ] => progress (rewrite (real_one_pt n))
         | [ |- context[projT1 real_zero ?n] ] => progress (rewrite (real_zero_pt n))
         | [ |- context[projT1 (real_const ?c) ?n] ] =>
             progress (rewrite (real_const_proj c n))
         end;
  ring.

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

(* ===================================================================== *)
(* Part 0. The fixed premise witness, the natural log, and the small      *)
(* order-algebra kit.                                                     *)
(* ===================================================================== *)

(* The canonical positivity witness of the embedded naturals (the C2.02  *)
(* leaf face), fixed once as the premise argument of the Z01 carriers.   *)
Definition z03npos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n) :=
  nat_real_pos.

(* The natural logarithm on the embedded naturals. *)
Definition z03_lnreal (n : nat) (Hn : NatLe 1 n) : Real :=
  real_log (nat_real n) (z03npos n Hn).

(* Left multiplication by a positive real preserves real_le. *)
Lemma z03_le_mult_l : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  exact (RealSetoid.real_le_compat (real_mult a c) (real_mult c a)
           (real_mult b c) (real_mult c b)
           (real_mult_comm a c) (real_mult_comm b c)
           (real_le_mult_compat a b c Hc Hab)).
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

(* Pointwise-equal arguments give equal cosines (the construction      *)
(* samples the argument approximation directly, real_cos_proj). *)
Lemma z03_cos_peq : forall a b : Real,
  (forall k : nat, projT1 a k == projT1 b k) ->
  real_eq (cauchy_real_cos a) (cauchy_real_cos b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro k.
  rewrite (real_cos_proj a k), (real_cos_proj b k).
  assert (Hcc : Qeq (cos_partial k (projT1 a k)) (cos_partial k (projT1 b k)))
    by (apply (z03_sc_cos_partial_congr k); exact (H k)).
  rewrite Hcc. ring.
Qed.

(* Pointwise-equal arguments give equal exponentials. *)
Lemma z03_exp_peq : forall a b : Real,
  (forall k : nat, projT1 a k == projT1 b k) ->
  real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b H. apply cauchy_real_exp_wd.
  apply real_eq_of_zero_diff. intro k. rewrite (H k). ring.
Qed.

(* ===================================================================== *)
(* Part 0b. The relax-order kit (the asymptotic nonnegativity faces).    *)
(* ===================================================================== *)

(* A real equal to zero is asymptotically nonnegative. *)
Lemma z03_eq_ge0relax : forall X : Real,
  real_eq X real_zero -> real_ge_relax X real_zero.
Proof.
  intros X Heq eps Heps. destruct (Heq eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n (NatLe_lift N n Hn)).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (projT1 real_zero n - projT1 X n)
           (Qabs (projT1 X n - projT1 real_zero n)) eps).
  - assert (Hpm : Qeq (projT1 real_zero n - projT1 X n)
                    (- (projT1 X n - projT1 real_zero n))) by ring.
    exact (qeq_le_l (projT1 real_zero n - projT1 X n)
             (- (projT1 X n - projT1 real_zero n))
             (Qabs (projT1 X n - projT1 real_zero n)) Hpm
             (qopp_le_abs (projT1 X n - projT1 real_zero n))).
  - exact (QltT_to_Qlt _ _ HN).
Qed.

(* The asymptotic nonnegativity face is closed under addition. *)
Lemma z03_relax0_plus : forall X Y : Real,
  real_ge_relax X real_zero -> real_ge_relax Y real_zero ->
  real_ge_relax (real_plus X Y) real_zero.
Proof.
  intros X Y HX HY eps Heps.
  assert (Hh : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  destruct (HX (eps / 2)%Q Hh) as [N1 HN1].
  destruct (HY (eps / 2)%Q Hh) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (H1 : QltT (projT1 real_zero n - projT1 X n) (eps / 2))
    by (apply HN1; lia).
  assert (H2 : QltT (projT1 real_zero n - projT1 Y n) (eps / 2))
    by (apply HN2; lia).
  apply Qlt_to_QltT.
  assert (Hexp : (projT1 real_zero n - projT1 (real_plus X Y) n)%Q
                 == ((projT1 real_zero n - projT1 X n)
                     + (projT1 real_zero n - projT1 Y n))%Q).
  { rewrite (real_plus_proj X Y n).
    rewrite (real_zero_pt n). ring. }
  apply (Qlt_le_trans (projT1 real_zero n - projT1 (real_plus X Y) n)
           (eps / 2 + eps / 2)%Q eps).
  - apply (qeq_lt_l _ (projT1 real_zero n - projT1 X n
                       + (projT1 real_zero n - projT1 Y n))
           (eps / 2 + eps / 2)%Q Hexp).
    apply Qplus_lt_compat; apply QltT_to_Qlt; assumption.
  - assert (Hf : Qeq (eps / 2 + eps / 2)%Q eps) by field.
    exact (qeq_le_l _ eps eps Hf (Qle_refl eps)).
Qed.

(* A nonnegative real weight times a pointwise-nonnegative real is      *)
(* asymptotically nonnegative: the strict case carries the pointwise    *)
(* sign, the zero case transfers through the equality. *)
Lemma z03_wy_relax : forall W Y : Real,
  real_le real_zero W -> (forall k : nat, Qle 0 (projT1 Y k)) ->
  real_ge_relax (real_mult W Y) real_zero.
Proof.
  intros W Y HW HY. unfold real_le in HW. destruct HW as [Hlt | Heq].
  - destruct Hlt as [e0 [He0 [N HN]]].
    apply (real_ge_relax_of_pointwise (real_mult W Y) real_zero N).
    intros n Hn. specialize (HN n (NatLe_lift N n Hn)).
    rewrite real_mult_proj.
    assert (Hw2 : Qlt 0 (projT1 W n)).
    { apply QltT_to_Qlt in He0. apply QltT_to_Qlt in HN.
      assert (Hm2 : Qlt e0 (projT1 W n)).
      { apply (qeq_lt_r e0 (projT1 W n - projT1 real_zero n) (projT1 W n)).
        - exact (qeq_minus_r0 (projT1 W n) (projT1 real_zero n)
                   (real_zero_pt n)).
        - exact HN. }
      exact (Qlt_trans 0 e0 (projT1 W n) He0 Hm2). }
    apply Qmult_le_0_compat.
    + apply Qlt_le_weak. exact Hw2.
    + apply HY.
  - apply z03_eq_ge0relax.
    apply (real_eq_trans (real_mult W Y) (real_mult real_zero Y) real_zero).
    + apply RealSetoid.real_eq_mult_compat;
        [exact (real_eq_sym real_zero W Heq) | apply real_eq_refl].
    + exact (real_eq_trans (real_mult real_zero Y) (real_mult Y real_zero)
               real_zero (real_mult_comm real_zero Y) (real_mult_zero Y)).
Qed.

(* The strict order shifts along a common summand. *)
Lemma z03_lt_add_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt. destruct Hlt as [e0 [He0 [N HN]]].
  exists e0. split; [exact He0 |].
  exists N. intros n Hn.
  assert (Hr : (projT1 (real_plus b c) n - projT1 (real_plus a c) n)%Q
               == (projT1 b n - projT1 a n)%Q).
  { rewrite (real_plus_proj b c n), (real_plus_proj a c n). ring. }
  apply Qlt_to_QltT.
  apply (qeq_lt_r e0 _ _ (Qeq_sym _ _ Hr)).
  apply QltT_to_Qlt. apply (HN n Hn).
Qed.

(* The strict order transfers along an equality on the larger side. *)
Lemma z03_lt_eq_r : forall x y z : Real,
  real_lt x y -> real_eq y z -> real_lt x z.
Proof.
  intros x y z Hlt Heq. destruct Hlt as [e0 [He0 [N HN]]].
  assert (Hh : QltT 0 (e0 / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 e0 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact He0. }
  destruct (Heq (e0 / 2)%Q Hh) as [N1 HN1].
  exists (e0 / 2)%Q. split; [exact Hh |].
  exists (Nat.max N N1). intros n Hn.
  assert (Hlt' : QltT e0 (projT1 y n - projT1 x n))
    by (apply HN; apply NatLe_lift;
        apply Nat.le_trans with (Nat.max N N1);
        [ apply Nat.le_max_l | apply NatLe_drop; exact Hn ]).
  assert (Heq' : QltT (Qabs (projT1 y n - projT1 z n)) (e0 / 2))
    by (apply HN1; apply NatLe_lift;
        apply Nat.le_trans with (Nat.max N N1);
        [ apply Nat.le_max_r | apply NatLe_drop; exact Hn ]).
  apply Qlt_to_QltT.
  assert (Hz2 : Qlt (projT1 y n - projT1 z n) (e0 / 2)).
  { apply (Qle_lt_trans (projT1 y n - projT1 z n)
             (Qabs (projT1 y n - projT1 z n)) (e0 / 2)).
    - exact (qself_le_abs (projT1 y n - projT1 z n)).
    - apply QltT_to_Qlt. exact Heq'. }
  assert (Hzylow : Qlt (- (e0 / 2)) (projT1 z n - projT1 y n)).
  { apply (qabs_lb (projT1 z n - projT1 y n) (e0 / 2)).
    - apply QltT_to_Qlt. exact Hh.
    - apply (qeq_lt_l (Qabs (projT1 z n - projT1 y n))
               (Qabs (projT1 y n - projT1 z n)) (e0 / 2)).
      + apply (Qeq_trans (Qabs (projT1 z n - projT1 y n))
                 (Qabs (- (projT1 y n - projT1 z n)))
                 (Qabs (projT1 y n - projT1 z n))).
        * apply Qabs_wd. ring.
        * apply Qabs_opp.
      + apply QltT_to_Qlt. exact Heq'. }
  assert (Hsum : Qlt (e0 + (- (e0 / 2)))
                   ((projT1 y n - projT1 x n)
                    + (projT1 z n - projT1 y n))).
  { apply Qplus_lt_compat.
    - apply QltT_to_Qlt. exact Hlt'.
    - exact Hzylow. }
  assert (Hmid : Qlt (e0 / 2)
                   ((projT1 y n - projT1 x n)
                    + (projT1 z n - projT1 y n))).
  { assert (Hprem : Qeq (e0 + (- (e0 / 2))) (e0 / 2)) by field.
    apply (qeq_lt_l (e0 / 2) _ _ (Qeq_sym _ _ Hprem) Hsum). }
  assert (Hkey : Qeq ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n))
                   (projT1 z n - projT1 x n)) by ring.
  exact (qeq_lt_r (e0 / 2) _ _ Hkey Hmid).
Qed.

(* The equality-transfer mirror of the Z02 relax transfer. *)
Lemma z03_eq_relax_sym : forall a b : Real,
  real_eq a b -> real_ge_relax a real_zero -> real_ge_relax b real_zero.
Proof.
  intros a b Hab Ha.
  exact (GaC3_Z02_eq_relax_transfer b a (real_eq_sym a b Hab) Ha).
Qed.

(* The asymptotic nonnegativity face is jointly incompatible with a     *)
(* strictly negative position carrying a positive margin. *)
Lemma z03_relax_lt_false : forall X : Real,
  real_ge_relax X real_zero -> real_lt X real_zero -> False.
Proof.
  intros X Hr Hl. destruct Hl as [e0 [He0 [N2 HN2]]].
  destruct (Hr e0 He0) as [N1 HN1].
  specialize (HN1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)).
  specialize (HN2 (Nat.max N1 N2)
    (NatLe_lift N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2))).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  exact (Qlt_irrefl _ (Qlt_trans _ _ _ HN2 HN1)).
Qed.

(* ===================================================================== *)
(* Part 1. The three-point Lambda-weighted carrier and its nonnegativity *)
(* face (assumption-free).                                               *)
(* ===================================================================== *)

(* The canonical exponential and cosine factors on the embedded         *)
(* naturals: exp(-sg * ln n) and cos(-t * ln n). *)
Definition z03_eterm (n : nat) (Hn : NatLe 1 n) (sg : Real) : Real :=
  cauchy_real_exp (real_mult (real_opp sg) (z03_lnreal n Hn)).

Definition z03_coterm (n : nat) (Hn : NatLe 1 n) (t : Real) : Real :=
  cauchy_real_cos (real_mult (real_opp t) (z03_lnreal n Hn)).

(* The real part of the exponential term at the point (sg, t): the      *)
(* polar face exp(-sg*ln n) * cos(-t*ln n).  The bridge splits into the *)
(* conversion face (the c_powq components reduce to the literal form)   *)
(* and the pointwise argument-cleaning face. *)
Lemma z03_cre_powq : forall (n : nat) (Hn : NatLe 1 n) (sg t : Real),
  real_eq (cRe (c_powq z03npos n Hn (sg, t)))
          (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)).
Proof.
  intros n Hn sg t.
  apply (real_eq_trans _
    (real_mult (cauchy_real_exp (real_mult (real_opp real_one)
                   (real_plus (real_mult sg (z03_lnreal n Hn))
                              (real_opp (real_mult t real_zero)))))
               (cauchy_real_cos (real_mult (real_opp real_one)
                   (real_plus (real_mult sg real_zero)
                              (real_mult t (z03_lnreal n Hn))))))).
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_mult_compat.
    + apply z03_exp_peq. intro k. z03_pt.
    + apply z03_cos_peq. intro k. z03_pt.
Qed.

(* The real part distributes over the complex sum. *)
Lemma z03_cre_plus : forall z w : Cx,
  real_eq (cRe (c_plus z w)) (real_plus (cRe z) (cRe w)).
Proof.
  intros z w. apply real_eq_of_zero_diff. intro k.
  rewrite (cRe_plus_pt z w k), (real_plus_proj (cRe z) (cRe w) k). ring.
Qed.

(* The real part of a scaled complex number is the scaled real part     *)
(* (conversion face). *)
Lemma z03_cre_scale : forall (a : Real) (z : Cx),
  real_eq (cRe (c_scale a z)) (real_mult a (cRe z)).
Proof. intros a z. apply real_eq_refl. Qed.

(* The real part of the Z01 von Mangoldt partial sum, mirrored on the   *)
(* real line. *)
Fixpoint z03_resum (N : nat) (s : Cx) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S m => real_plus (z03_resum m s)
             (real_mult (z01_lam (Datatypes.S m))
                        (cRe (c_powq z03npos (Datatypes.S m) (NatLe_one_S m) s)))
  end.

Lemma z03_cre_manpart : forall (N : nat) (s : Cx),
  real_eq (cRe (z01_manpart z03npos N s)) (z03_resum N s).
Proof.
  intro N. induction N as [| N IH]; intro s.
  - cbn [z01_manpart z03_resum]. apply real_eq_refl.
  - cbn [z01_manpart z03_resum].
    apply (real_eq_trans _ (real_plus (cRe (z01_manpart z03npos N s))
             (cRe (c_scale (z01_lam (Datatypes.S N))
                      (c_powq z03npos (Datatypes.S N) (NatLe_one_S N) s))))).
    + apply z03_cre_plus.
    + apply RealSetoid.real_eq_plus_compat.
      * exact (IH s).
      * apply z03_cre_scale.
Qed.

(* The combined Cx carrier: the Z01 partial sums at the three racing    *)
(* points, assembled with the 3-4-1 weights (the ZZ logderiv_zeta_ineq  *)
(* assembly face). *)
Definition z03_comb (N : nat) (sg t : Real) : Cx :=
  c_plus (c_scale (real_const 3) (z01_manpart z03npos N (sg, real_zero)))
         (c_plus (c_scale (real_const 4) (z01_manpart z03npos N (sg, t)))
                 (z01_manpart z03npos N (sg, real_plus t t))).

(* The real-line mirror of the combined carrier: the per-term square    *)
(* form of the Z02 identity weighted by the Lambda weight and the       *)
(* exponential factor. *)
Fixpoint z03_sqsum (N : nat) (sg t : Real) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S m => real_plus (z03_sqsum m sg t)
             (real_mult (real_mult (z01_lam (Datatypes.S m))
                                   (z03_eterm (Datatypes.S m) (NatLe_one_S m) sg))
                        (real_mult (real_const 2)
                           (real_mult (real_plus real_one
                                        (z03_coterm (Datatypes.S m) (NatLe_one_S m) t))
                                      (real_plus real_one
                                        (z03_coterm (Datatypes.S m) (NatLe_one_S m) t)))))
  end.

(* The per-term core: the weighted three-point real part is the weight  *)
(* times the square form at the ordinate argument. *)
Lemma z03_cre_tri : forall (n : nat) (Hn : NatLe 1 n) (sg t : Real),
  real_eq (real_mult (z01_lam n)
            (real_plus (real_mult (real_const 3)
                         (cRe (c_powq z03npos n Hn (sg, real_zero))))
                       (real_plus (real_mult (real_const 4)
                                    (cRe (c_powq z03npos n Hn (sg, t))))
                                  (cRe (c_powq z03npos n Hn (sg, real_plus t t))))))
          (real_mult (real_mult (z01_lam n) (z03_eterm n Hn sg))
                     (real_mult (real_const 2)
                        (real_mult (real_plus real_one (z03_coterm n Hn t))
                                   (real_plus real_one (z03_coterm n Hn t))))).
Proof.
  intros n Hn sg t.
  apply (real_eq_trans _
    (real_mult (z01_lam n)
       (real_plus (real_mult (real_const 3)
                    (real_mult (z03_eterm n Hn sg)
                       (cauchy_real_cos
                          (real_mult (real_opp real_zero) (z03_lnreal n Hn)))))
                  (real_plus (real_mult (real_const 4)
                               (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)))
                             (real_mult (z03_eterm n Hn sg)
                                (cauchy_real_cos
                                   (real_mult (real_opp (real_plus t t))
                                              (z03_lnreal n Hn)))))))).
  - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
    apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat;
        [apply real_eq_refl | exact (z03_cre_powq n Hn sg real_zero)].
    + apply RealSetoid.real_eq_plus_compat.
      * apply RealSetoid.real_eq_mult_compat;
          [apply real_eq_refl | exact (z03_cre_powq n Hn sg t)].
      * exact (z03_cre_powq n Hn sg (real_plus t t)).
  - apply (real_eq_trans _
      (real_mult (z01_lam n)
         (real_mult (z03_eterm n Hn sg)
                    (real_plus (real_const 3)
                               (real_plus (real_mult (real_const 4)
                                            (z03_coterm n Hn t))
                                          (cauchy_real_cos
                                             (real_plus
                                                (real_mult (real_opp t)
                                                           (z03_lnreal n Hn))
                                                (real_mult (real_opp t)
                                                           (z03_lnreal n Hn))))))))).
    + (* the zero-ordinate cosine is 1 and the doubled-ordinate cosine   *)
      (* is the doubled argument; then the ring form factors out       *)
      apply (real_eq_trans _
        (real_mult (z01_lam n)
           (real_plus (real_mult (real_const 3)
                        (real_mult (z03_eterm n Hn sg) real_one))
                      (real_plus (real_mult (real_const 4)
                                   (real_mult (z03_eterm n Hn sg) (z03_coterm n Hn t)))
                                 (real_mult (z03_eterm n Hn sg)
                                    (cauchy_real_cos
                                       (real_plus (real_mult (real_opp t)
                                                          (z03_lnreal n Hn))
                                                  (real_mult (real_opp t)
                                                             (z03_lnreal n Hn))))))))).
      { apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        apply RealSetoid.real_eq_plus_compat.
        - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
          apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
          apply (real_eq_trans _ (cauchy_real_cos real_zero)).
          * apply z03_cos_peq. intro k. z03_pt.
          * exact real_cos_one.
        - apply RealSetoid.real_eq_plus_compat.
          + apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply z03_cos_peq. intro k. z03_pt.
          + apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
            apply z03_cos_peq. intro k. z03_pt. }
      { apply real_eq_of_zero_diff. intro k. z03_pt. }
    + (* the Z02 identity at the ordinate argument, then the weight     *)
      (* association *)
      apply (real_eq_trans _
        (real_mult (z01_lam n)
           (real_mult (z03_eterm n Hn sg)
                      (real_mult (real_const 2)
                         (real_mult (real_plus real_one (z03_coterm n Hn t))
                                    (real_plus real_one (z03_coterm n Hn t))))))).
      * apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        exact (GaC3_Z02_three_cosine_sq
                 (real_mult (real_opp t) (z03_lnreal n Hn))).
      * apply real_eq_of_zero_diff. intro k. z03_pt.
Qed.

(* The combined carrier's real part equals the square-form sum. *)
Theorem z03_comb_sqsum_eq : forall (N : nat) (sg t : Real),
  real_eq (cRe (z03_comb N sg t)) (z03_sqsum N sg t).
Proof.
  intro N. induction N as [| N IH]; intros sg t.
  - cbn [z03_sqsum]. apply real_eq_of_zero_diff. intro k.
    cbn [z03_comb z01_manpart c_plus c_scale cRe cIm fst snd c_zero]. z03_pt.
  - cbn [z03_sqsum].
    apply (real_eq_trans _
      (real_plus
        (real_plus (real_mult (real_const 3)
                     (cRe (z01_manpart z03npos N (sg, real_zero))))
                   (real_plus (real_mult (real_const 4)
                                (cRe (z01_manpart z03npos N (sg, t))))
                              (cRe (z01_manpart z03npos N (sg, real_plus t t)))))
        (real_mult (z01_lam (Datatypes.S N))
                   (real_plus (real_mult (real_const 3)
                                (cRe (c_powq z03npos (Datatypes.S N)
                                        (NatLe_one_S N) (sg, real_zero))))
                              (real_plus (real_mult (real_const 4)
                                           (cRe (c_powq z03npos (Datatypes.S N)
                                                   (NatLe_one_S N) (sg, t))))
                                         (cRe (c_powq z03npos (Datatypes.S N)
                                                 (NatLe_one_S N)
                                                 (sg, real_plus t t)))))))).
    + (* the regrouping of the unfolded step (same atom families) *)
      apply real_eq_of_zero_diff. intro k.
      cbn [z03_comb z01_manpart c_plus c_scale cRe cIm fst snd]. z03_pt.
    + apply RealSetoid.real_eq_plus_compat.
      * (* the N-level three-sum: the assembly face composed with the IH *)
        assert (Hsmall : real_eq
                   (real_plus (real_mult (real_const 3)
                                (cRe (z01_manpart z03npos N (sg, real_zero))))
                              (real_plus (real_mult (real_const 4)
                                           (cRe (z01_manpart z03npos N (sg, t))))
                                         (cRe (z01_manpart z03npos N
                                                 (sg, real_plus t t)))))
                   (cRe (z03_comb N sg t))).
        { apply real_eq_of_zero_diff. intro k.
          cbn [z03_comb c_plus c_scale cRe cIm fst snd]. z03_pt. }
        exact (real_eq_trans _ _ _ Hsmall (IH sg t)).
      * exact (z03_cre_tri (Datatypes.S N) (NatLe_one_S N) sg t).
Qed.

(* The weight factor is nonnegative: the von Mangoldt weight is         *)
(* nonnegative and the exponential factor is positive. *)
Lemma z03_ew_pos : forall (n : nat) (Hn : NatLe 1 n) (sg : Real),
  real_le real_zero (real_mult (z01_lam n) (z03_eterm n Hn sg)).
Proof.
  intros n Hn sg. destruct (z01_lam_ge0 n) as [Hlt | Heq].
  - apply (real_lt_le_iff real_zero (real_mult (z01_lam n) (z03_eterm n Hn sg))).
    left.
    apply (real_lt_eq_lt real_zero (real_mult (z03_eterm n Hn sg) (z01_lam n))
             (real_mult (z01_lam n) (z03_eterm n Hn sg))
             (real_eq_lt_lt real_zero
                (real_mult (z03_eterm n Hn sg) real_zero)
                (real_mult (z03_eterm n Hn sg) (z01_lam n))
                (real_eq_sym _ _ (real_mult_zero (z03_eterm n Hn sg)))
                (real_lt_mult_compat real_zero (z01_lam n)
                   (z03_eterm n Hn sg)
                   (cauchy_real_exp_pos
                      (real_mult (real_opp sg) (z03_lnreal n Hn))) Hlt))
             (real_mult_comm (z03_eterm n Hn sg) (z01_lam n))).
  - apply (RealSetoid.real_eq_le real_zero
             (real_mult (z01_lam n) (z03_eterm n Hn sg))).
    apply real_eq_sym.
    apply (real_eq_trans (real_mult (z01_lam n) (z03_eterm n Hn sg))
             (real_mult real_zero (z03_eterm n Hn sg)) real_zero).
    + exact (RealSetoid.real_eq_mult_compat (z01_lam n) (z03_eterm n Hn sg)
               real_zero (z03_eterm n Hn sg) (real_eq_sym real_zero (z01_lam n) Heq)
               (real_eq_refl _)).
    + exact (real_eq_trans (real_mult real_zero (z03_eterm n Hn sg))
               (real_mult (z03_eterm n Hn sg) real_zero) real_zero
               (real_mult_comm real_zero (z03_eterm n Hn sg))
               (real_mult_zero (z03_eterm n Hn sg))).
Qed.

(* The square-form sum is asymptotically nonnegative. *)
Theorem z03_sqsum_ge0 : forall (N : nat) (sg t : Real),
  real_ge_relax (z03_sqsum N sg t) real_zero.
Proof.
  intro N. induction N as [| N IH]; intros sg t.
  - cbn [z03_sqsum].
    apply (real_ge_relax_of_pointwise real_zero real_zero 0).
    intros n Hn. apply Qle_refl.
  - cbn [z03_sqsum]. apply z03_relax0_plus.
    + apply IH.
    + apply z03_wy_relax.
      * apply z03_ew_pos.
      * intro k.
        exact (GaC3_Z02_sq_pointwise_nonneg
                 (real_mult (real_opp t) (z03_lnreal (Datatypes.S N) (NatLe_one_S N))) k).
Qed.

(* Main face 1: the combined real part is asymptotically nonnegative. *)
Theorem z03_comb_nonneg : forall (N : nat) (sg t : Real),
  real_ge_relax (cRe (z03_comb N sg t)) real_zero.
Proof.
  intros N sg t.
  apply (z03_eq_relax_sym _ _ (real_eq_sym _ _ (z03_comb_sqsum_eq N sg t))).
  exact (z03_sqsum_ge0 N sg t).
Qed.

(* ===================================================================== *)
(* Part 2. The racing contradiction in explicit-radius slot form.         *)
(* ===================================================================== *)

Section Z03_Race.

(* The ordinate and the racing offset: the point family sigma + i*t     *)
(* with sigma = 1 + d and d > 0 rational. *)
Variable t : Real.
Variable d : Q.
Hypothesis Hd : QltT 0 d.

(* The balancing truncation and the two upper-bound slots (the          *)
(* sigma-term and the doubled-ordinate term). *)
Variable Nrace : nat.
Variables B3 B2 : Real.

(* The three racing points. *)
Definition z03_sg : Real := real_plus real_one (real_const d).
Definition z03_p0 : Cx := (z03_sg, real_zero).
Definition z03_p1 : Cx := (z03_sg, t).
Definition z03_p2 : Cx := (z03_sg, real_plus t t).

(* The four-term main-part slot: the real part of the von Mangoldt      *)
(* partial sum at sigma + i*t stays below the explicit m >= 1 main      *)
(* part -1/(2d) at the balancing truncation (the registered open        *)
(* supply face; the zero factorization route discharges it). *)
Hypothesis Hmain4 :
  real_le (cRe (z01_manpart z03npos Nrace z03_p1))
          (real_opp (real_const (Qinv (2 * d)))).

(* The sigma-term and doubled-ordinate upper-bound slots. *)
Hypothesis Hsig3 :
  real_le (cRe (z01_manpart z03npos Nrace z03_p0)) B3.
Hypothesis Htwo :
  real_le (cRe (z01_manpart z03npos Nrace z03_p2)) B2.

(* The racing margin constant m0 = 1/(2d), positive by Hd. *)
Definition z03_m0 : Real := real_const (Qinv (2 * d)).

Lemma z03_m0_pos : real_lt real_zero z03_m0.
Proof.
  apply QltT_to_Qlt in Hd.
  assert (H2 : Qlt 0 2) by reflexivity.
  assert (H2d : Qlt 0 (2 * d)) by exact (Qmult_lt_0_compat 2 d H2 Hd).
  exact (real_const_pos (Qinv (2 * d))
           (Qlt_to_QltT _ _ (Qinv_lt_0_compat (2 * d) H2d))).
Qed.

(* The racing contradiction: under the explicit window arithmetic       *)
(* 3*B3 + B2 < 4*m0 the nonnegativity face of Part 1 fails. *)
Theorem z03_racing_contra :
  real_lt (real_plus (real_mult (real_const 3) B3) B2)
          (real_mult (real_const 4) z03_m0) ->
  False.
Proof.
  intro Hwin.
  assert (Hnneg : real_ge_relax (cRe (z03_comb Nrace z03_sg t)) real_zero)
    by exact (z03_comb_nonneg Nrace z03_sg t).
  (* the split of the combined real part *)
  assert (Hsplit : real_eq (cRe (z03_comb Nrace z03_sg t))
    (real_plus (real_mult (real_const 3) (cRe (z01_manpart z03npos Nrace z03_p0)))
               (real_plus (real_mult (real_const 4)
                            (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))).
  { apply real_eq_of_zero_diff. intro k.
    cbn [z03_comb c_plus c_scale cRe cIm fst snd].
    unfold z03_p0, z03_p1, z03_p2. z03_pt. }
  (* the upper-bound chain *)
  assert (Hupper : real_le
    (real_plus (real_mult (real_const 3) (cRe (z01_manpart z03npos Nrace z03_p0)))
               (real_plus (real_mult (real_const 4)
                            (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))
    (real_plus (real_mult (real_const 3) B3)
               (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2))).
  { apply real_le_plus_compat.
    - apply z03_le_mult_l.
      + apply real_const_pos. compute. reflexivity.
      + exact Hsig3.
    - apply real_le_plus_compat.
      + apply z03_le_mult_l.
        * apply real_const_pos. compute. reflexivity.
        * exact Hmain4.
      + exact Htwo. }
  (* the association to the window shape *)
  assert (Hassoc : real_eq
    (real_plus (real_mult (real_const 3) B3)
               (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2))
    (real_plus (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) (real_opp z03_m0)))).
  { apply real_eq_of_zero_diff. intro k. z03_pt. }
  assert (Hle : real_le (cRe (z03_comb Nrace z03_sg t))
    (real_plus (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) (real_opp z03_m0)))).
  { apply (real_le_trans
             (cRe (z03_comb Nrace z03_sg t))
             (real_plus (real_mult (real_const 3)
                          (cRe (z01_manpart z03npos Nrace z03_p0)))
                        (real_plus (real_mult (real_const 4)
                             (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))).
    - apply (RealSetoid.real_eq_le _ _ Hsplit).
    - apply (real_le_trans _
               (real_plus (real_mult (real_const 3) B3)
                          (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2)) _).
      + exact Hupper.
      + apply (RealSetoid.real_eq_le _ _ Hassoc). }
  (* the shifted window *)
  assert (Hlt0 : real_lt (real_plus (real_plus (real_mult (real_const 3) B3) B2)
                                  (real_mult (real_const 4) (real_opp z03_m0)))
                         real_zero).
  { apply (z03_lt_eq_r (real_plus (real_plus (real_mult (real_const 3) B3) B2)
                          (real_mult (real_const 4) (real_opp z03_m0)))
              (real_plus (real_mult (real_const 4) z03_m0)
                         (real_mult (real_const 4) (real_opp z03_m0))) real_zero).
    - apply (z03_lt_add_r (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) z03_m0)
               (real_mult (real_const 4) (real_opp z03_m0)) Hwin).
    - apply (real_eq_trans
               (real_plus (real_mult (real_const 4) z03_m0)
                          (real_mult (real_const 4) (real_opp z03_m0)))
               (real_plus (real_mult (real_const 4) z03_m0)
                          (real_opp (real_mult (real_const 4) z03_m0)))).
      + apply real_eq_of_zero_diff. intro k. z03_pt.
      + apply real_plus_opp. }
  (* the joint incompatibility *)
  apply (z03_relax_lt_false (cRe (z03_comb Nrace z03_sg t)) Hnneg).
  apply (real_le_lt_trans _ _ _ Hle Hlt0).
Qed.

End Z03_Race.

(* ===================================================================== *)
(* Part 3. The explicit radius literal (the Q-level window witness).      *)
(* ===================================================================== *)

(* The radius literal d = 1/64: the offset stays positive and the       *)
(* racing margin 4*(1/(2d)) computes to 128. *)
Definition z03_radius_lit : Q := (1 # 64)%Q.

Lemma z03_radius_pos : QltT 0 z03_radius_lit.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.

Lemma z03_radius_margin :
  QeqT (4 * Qdiv 1 (2 * z03_radius_lit)) (Qmake 128 1)%Q.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.
