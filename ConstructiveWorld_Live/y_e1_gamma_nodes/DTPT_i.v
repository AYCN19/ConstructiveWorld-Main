(* ConstructiveWorld-Main - the cozero-ideal stem of the DTPT base library *)

(** * DTPT_i: the cozero-ideal stem of the DTPT base library (stem I of fourteen).

    Mission.  merged block S2, the counting of the cozero ideal: the Q-algebra load-bearing pieces (zero divisors, squares, square sums), the zero region fiber and the cozero region, union/intersection/subset closure of the ideal, and the element-wise complementarity face.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g], [DTPT_h]

    References.  the DTPT base library of the constructive development (the judged-code truth-predicate line); statements conserved verbatim from the boxed original piece; consumed by the later stems of this node.

    Constructivity.  All carriers [Set]; conclusions in Set-valued order
    predicates and equality forms; zero assumed constants; zero admissions;
    every proof closes by Qed.

    Build.  [coqc -q -native-compiler no] under the acceptance build
    faces, [cpu_guard v3] wrapped. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.
Require Import DTPT_a.
Require Import DTPT_b.
Require Import DTPT_c.
Require Import DTPT_d.
Require Import DTPT_e.
Require Import DTPT_f.
Require Import DTPT_g.
Require Import DTPT_h.
(* ============================================================
   merged block S2 (section 13): the merge of DTPT_CoZero.v - the counting of the cozero ideal
   source piece DTPT-U10 (the gap unit COZIDEAL; the U10R repaired face). Only the standalone-file
   Require/Import/Open Scope headers and Module shell lines were peeled off (carried uniformly by
   this file's header, including the Sorting.Sorted addition) - after the merge the content sits inside Module DTPT, and its references to the DTPT
   base modules (qadd_le/Qle_0_sub' etc.) became same-file direct references, semantically unchanged;
   comments, all proof bodies, the Qed face and the Print Assumptions audit exits are zero-change verbatim migrations.
   ============================================================ *)
(* ============================================================
   DTPT_CoZero.v - the counting of the cozero ideal (DTPT-U10, gap unit COZIDEAL)
   source-text comparison: digital universe - entropy-phase trialism, base .txt section 2.5 definition 2.5.3 (lines 219-226):
     'if a measure cannot be defined, express it with the cozero ideal: P_0, P_infinity are in the ideal, P_mid is not in the ideal,'
       where the ideal may be read as 'the negligible boundary sets in a suitable sense.'
   counting caliber (an all-Set finite world w : list Q):
     - a region   = a sublist of w (order-preserving extraction, multiplicities faithful);
     - an observable = phi : Q -> Q, zero-tested by Qeq_bool;
     - the zero region fiber phi w = filter (fun x => Qeq_bool (phi x) 0) w;
     - the ideal over w = { fiber phi w : phi an observable }, i.e. the counting of 'negligible sets'.
   the ideal axiom face (the theorem correspondences of this piece):
     - the empty region is in the ideal (the constant-one fiber); the full region is in the ideal (the constant-zero fiber);
     - union closure (main): fiber (phi * psi) and fiber phi union fiber psi agree element-wise
       - load-bearing piece = Q has no zero divisors (a*b == 0 iff a == 0 or b == 0, direct Z resolution);
     - intersection closure (main piece): fiber (phi^2 + psi^2) and fiber phi intersect fiber psi agree element-wise
       - load-bearing pieces = Q squares are nonnegative (direct Z three-way resolution) + the square-sum zero sandwich;
     - subset closure (main piece): any sublist of w is directly constructed into the ideal via the indicator-zero function.
   the cozero face (bonus): cozero phi w = filter (negb (Qeq_bool (phi x) 0)) w,
     element-wise complementary to fiber (length sum = list length, disjoint, covering).
   membership caliber declaration: region membership always uses the record-level In (stdlib List).
     the value-level Qeq caliber does not preserve zeros for arbitrary phi (a non-extensional counterexample: phi reads the low bits of the Qnum),
     hence the fiber membership characterization must use In - exactly the semantics of filter_In, not a downgrade.
   dependencies: DTPT (the qadd_le / Qle_0_sub' family + Open Q_scope); stdlib QArith/List.
   discipline: zero assumed constants and zero admissions; nat always explicit %nat; closed by Qed throughout.
   ============================================================ *)
(* the standalone-file Require/Import/Open Scope headers (Require DTPT, From Stdlib
   QArith/List/Arith/Lia, Import ListNotations, Open Scope Q_scope,
   Import DTPT.DTPT, the Module DTPT_CoZero shell) were removed at merge time. *)

(* ========== section 1, Q-algebra load-bearing pieces: zero divisors / squares / square sums ========== *)

(* the Qeq -> Qle bridge (stdlib 9.0 has no Qeq_le: after unfolding Qeq both sides are the same terms as the unfolded Qle) *)
Lemma qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* Q has no zero divisors, positive decomposition (closed in two segments by Z.mul_eq_0 at the Z level) *)
Lemma qmul_eq0_fwd : forall a b : Q, (a * b == 0)%Q -> a == 0 \/ b == 0.
Proof.
  intros [an ad] [bn bd] H.
  unfold Qmult, Qeq in H; simpl in H.
  repeat rewrite Z.mul_1_r in H.
  apply Z.mul_eq_0 in H.
  destruct H as [H|H]; [left|right]; unfold Qeq; simpl; lia.
Qed.

(* zero-divisor introduction (left/right) *)
Lemma qmul_eq0_intro_l : forall a b : Q, a == 0 -> (a * b == 0)%Q.
Proof.
  intros [an ad] b Hab. unfold Qeq in Hab; simpl in Hab.
  assert (Han : (an = 0)%Z) by lia.
  destruct b as [bn bd]. unfold Qmult, Qeq; simpl.
  rewrite Han. reflexivity.
Qed.

Lemma qmul_eq0_intro_r : forall a b : Q, b == 0 -> (a * b == 0)%Q.
Proof.
  intros a [bn bd] Hbb. unfold Qeq in Hbb; simpl in Hbb.
  assert (Hbn : (bn = 0)%Z) by lia.
  destruct a as [an ad]. unfold Qmult, Qeq; simpl.
  rewrite Hbn. lia.
Qed.

(* the zero-divisor characterization (the load-bearing piece of union closure) *)
Lemma qmul_eq0_iff : forall a b : Q, (a * b == 0)%Q <-> (a == 0 \/ b == 0).
Proof.
  intros a b. split.
  - apply qmul_eq0_fwd.
  - intros [H|H]; [apply qmul_eq0_intro_l | apply qmul_eq0_intro_r]; exact H.
Qed.

(* Q squares are nonnegative (the Z-level Znum three-way split: Z0/Zpos/Zneg are all square-nonnegative) *)
Lemma qsq_nonneg : forall x : Q, (0 <= x * x)%Q.
Proof.
  intros [xn xd]. unfold Qmult, Qle. simpl.
  destruct xn as [| p | p]; simpl; lia.
Qed.

(* a zero square implies a zero factor *)
Lemma qsq_eq0 : forall x : Q, (x * x == 0)%Q -> x == 0.
Proof.
  intros x H. destruct (qmul_eq0_fwd x x H) as [Hx|Hx]; exact Hx.
Qed.

(* a zero square sum implies both factors zero (the order sandwich: 0 <= a^2 <= a^2 + b^2 == 0, closed by antisymmetry) *)
Lemma qsum_sq_zero : forall a b : Q, (a * a + b * b == 0)%Q -> a == 0 /\ b == 0.
Proof.
  intros a b Hsum.
  assert (Hs1 : (a * a <= a * a + b * b)%Q).
  { assert (Hs0 : (a * a + 0 <= a * a + b * b)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle1 : (a * a <= 0)%Q)
    by (apply (Qle_trans (a * a) (a * a + b * b) 0);
        [exact Hs1 | apply qeq_le; exact Hsum]).
  assert (Hs2 : (b * b <= b * b + a * a)%Q).
  { assert (Hs0 : (b * b + 0 <= b * b + a * a)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle2 : (b * b <= 0)%Q)
    by (apply (Qle_trans (b * b) (b * b + a * a) 0);
        [exact Hs2 | apply qeq_le; apply Qeq_trans with (a * a + b * b);
         [apply Qplus_comm | exact Hsum]]).
  assert (Hz1 : (a * a == 0)%Q) by (apply Qle_antisym; [exact Hle1 | apply qsq_nonneg]).
  assert (Hz2 : (b * b == 0)%Q) by (apply Qle_antisym; [exact Hle2 | apply qsq_nonneg]).
  split.
  - apply qsq_eq0; exact Hz1.
  - apply qsq_eq0; exact Hz2.
Qed.

(* the reverse construction: both factors zero implies a zero square sum *)
Lemma qsum_sq_zero_intro : forall a b : Q,
  a == 0 -> b == 0 -> (a * a + b * b == 0)%Q.
Proof.
  intros a b Ha Hb.
  assert (Haa : (a * a == 0)%Q) by (apply qmul_eq0_intro_l; exact Ha).
  assert (Hbb : (b * b == 0)%Q) by (apply qmul_eq0_intro_l; exact Hb).
  destruct a as [an ad]; destruct b as [bn bd].
  unfold Qeq in Haa, Hbb; simpl in Haa, Hbb.
  assert (Han : (an = 0)%Z) by lia.
  assert (Hbn : (bn = 0)%Z) by lia.
  unfold Qmult, Qplus, Qeq; simpl.
  rewrite Han, Hbn. reflexivity.
Qed.

(* the zero-test boolean face: the product observable vanishes iff one factor vanishes (the union-closure key) *)
Lemma qmul_fiber_key : forall p q : Q,
  Qeq_bool (p * q) 0 = true <-> (Qeq_bool p 0 = true \/ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qmul_eq0_iff in Hb.
    destruct Hb as [H|H]; [left|right]; apply Qeqb_true_of; exact H.
  - intros [Hb|Hb]; apply Qeq_bool_iff; apply qmul_eq0_iff;
      [left|right]; apply Qeq_bool_iff; exact Hb.
Qed.

(* the zero-test boolean face: the square-sum observable vanishes iff both factors vanish (the intersection-closure key) *)
Lemma qsum_sq_fiber_key : forall p q : Q,
  Qeq_bool (p * p + q * q) 0 = true <-> (Qeq_bool p 0 = true /\ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qsum_sq_zero in Hb.
    destruct Hb as [H1 H2]; split; apply Qeqb_true_of; assumption.
  - intros [Hp Hq]. apply Qeq_bool_iff. apply qsum_sq_zero_intro.
    + apply Qeq_bool_iff; exact Hp.
    + apply Qeq_bool_iff; exact Hq.
Qed.

(* ========== section 2: the zero region fiber and the cozero region ========== *)

(* the zero region: the order-preserving sublist of the elements of w on which the observable vanishes *)
Definition fiber (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => Qeq_bool (f x) 0) w.

(* the cozero region: the order-preserving sublist of the elements of w on which the observable is nonzero (the complement face of fiber) *)
Definition cozero (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => negb (Qeq_bool (f x) 0)) w.

(* the membership characterization (the record-level In caliber, closed via filter_In with explicit terms - HO-unify immune) *)
Lemma fiber_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) <-> (In x w /\ Qeq_bool (f x) 0 = true).
Proof.
  intros f w x. unfold fiber.
  exact (filter_In (fun y : Q => Qeq_bool (f y) 0) x w).
Qed.

Lemma cozero_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (cozero f w) <-> (In x w /\ Qeq_bool (f x) 0 = false).
Proof.
  intros f w x. unfold cozero.
  rewrite (filter_In (fun y : Q => negb (Qeq_bool (f y) 0)) x w).
  split.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
Qed.

(* ========== section 3, main union closure: the product observable decomposes into the union of zero divisors ========== *)

(* source-text semantics: negligible sets are closed under finite unions - in the zero-region language this is
   fiber (phi * psi) w = fiber phi w union fiber psi w (element-wise agreement),
   load-bearing piece = Q has no zero divisors, qmul_eq0_iff. *)
Theorem fiber_mul_union : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * g y) w) <-> (In x (fiber f w) \/ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qmul_fiber_key in Hb.
    destruct Hb as [H|H]; [left|right]; split; assumption.
  - intros [Hp|Hp].
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. left. exact (proj2 Hp).
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. right. exact (proj2 Hp).
Qed.

(* ========== section 4, main piece, intersection closure: the square-sum observable decomposes into the intersection of zero divisors ========== *)

(* source-text semantics: negligible sets are closed under finite intersections - in the zero-region language this is
   fiber (phi^2 + psi^2) w = fiber phi w intersect fiber psi w (element-wise agreement),
   load-bearing pieces = Q squares are nonnegative + the square-sum zero sandwich qsum_sq_zero. *)
Theorem fiber_sumsq_inter : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * f y + g y * g y) w)
  <-> (In x (fiber f w) /\ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qsum_sq_fiber_key in Hb.
    destruct Hb as [H1 H2]; split; split; assumption.
  - intros [[Hin H1] [_ H2]]. split; [exact Hin|].
    apply qsum_sq_fiber_key. split; assumption.
Qed.

(* ========== section 5: the ideal axiom face - empty region / full region / subset closure ========== *)

(* the empty region is in the ideal: the constant-one observable is nonzero everywhere, so the zero region is empty *)
Theorem fiber_one_empty : forall w : list Q,
  fiber (fun _ : Q => 1) w = [].
Proof.
  induction w as [| a t IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* the full region is in the ideal: the constant-zero observable vanishes everywhere, so the zero region is the whole list
   (the degenerate face of the ideal swallowing the full region; for the exclusion that makes the ideal a 'proper ideal' see the source text P_mid not in the ideal) *)
Theorem fiber_zero_full : forall w : list Q,
  fiber (fun _ : Q => 0) w = w.
Proof.
  induction w as [| a t IH].
  - reflexivity.
  - unfold fiber in *. simpl in *. rewrite IH. reflexivity.
Qed.

(* a Leibniz equality decider for Q: Q is a Z x positive record, and in_dec needs a Leibniz-shaped decider
   (the stdlib Qeq_dec is Qeq-shaped and does not type-check when fed to in_dec; Qeq-boolean membership testing
   also disagrees with the record-level In - 0#1 and 0#2 differ at term level - so it is self-built directly, zero assumed constants) *)
Definition Q_dec : forall x y : Q, {x = y} + {x <> y}.
Proof.
  intros [an ad] [bn bd].
  destruct (Z.eq_dec an bn) as [Hn|Hn]; destruct (positive_eq_dec ad bd) as [Hd|Hd].
  - left. rewrite Hn, Hd. reflexivity.
  - right. intros He. apply Hd. congruence.
  - right. intros He. apply Hn. congruence.
  - right. intros He. apply Hd. congruence.
Defined.

(* the pointwise characterization of the indicator: chi_l x = 0 iff x is in l (the Leibniz record-level caliber) *)
Lemma chi_spec : forall (l : list Q) (x : Q),
  Qeq_bool (if in_dec Q_dec x l then 0 else 1) 0 = true <-> In x l.
Proof.
  intros l x. destruct (in_dec Q_dec x l) as [Hi|Hni].
  - split; [intros _; exact Hi | intros _; reflexivity].
  - split.
    + intro Hb. cbv in Hb. discriminate.
    + intro Hi. exfalso. apply Hni. exact Hi.
Qed.

(* the indicator-zero function: any sublist l of w is directly constructed as a fiber via chi_l := '0 if y is in l, else 1',
   - the direct-construction face of subset closure (membership level, record-level In both ways) *)
Lemma fiber_indicator : forall (l w : list Q) (x : Q),
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w)
  <-> (In x w /\ In x l).
Proof.
  intros l w x. rewrite fiber_in. cbv beta. rewrite chi_spec.
  split; intros H; exact H.
Qed.

(* subset closure (the second ideal axiom): l subset of fiber phi w implies l enters the ideal via the indicator-zero function
   - the carrier face of the source-text P_0, P_infinity in the ideal: every boundary-phase region is the zero subregion of some observable *)
Theorem ideal_sub_closed : forall (l : list Q) (f : Q -> Q) (w : list Q) (x : Q),
  (forall y : Q, In y l -> In y (fiber f w)) ->
  In x l ->
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w).
Proof.
  intros l f w x Hsub Hxl. apply fiber_indicator. split.
  - exact (proj1 (proj1 (fiber_in f w x) (Hsub x Hxl))).
  - exact Hxl.
Qed.

(* ========== section 6: the cozero face - element-wise complementarity of cozero and fiber ========== *)

(* the length sum = the list length (a multiplicity-faithful dichotomy) *)
Theorem fiber_cozero_length : forall (f : Q -> Q) (w : list Q),
  (length (fiber f w) + length (cozero f w))%nat = length w.
Proof.
  intros f w. unfold fiber, cozero.
  induction w as [| a t IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool (f a) 0); simpl; lia.
Qed.

(* disjointness: the zero region and the cozero region share no element *)
Theorem fiber_cozero_disjoint : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> ~ In x (cozero f w).
Proof.
  intros f w x H1 H2.
  apply fiber_in in H1. apply cozero_in in H2.
  destruct H1 as [_ Hb1]. destruct H2 as [_ Hb2].
  rewrite Hb1 in Hb2. discriminate.
Qed.

(* covering: every element of the world lies on one of the two sides *)
Theorem fiber_cozero_cover : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) \/ In x (cozero f w)).
Proof.
  intros f w x Hw.
  destruct (Qeq_bool (f x) 0) eqn:Ef.
  - left. apply fiber_in. split; assumption.
  - right. apply cozero_in. split; assumption.
Qed.

(* the complement-face characterization: within the world, x lands in the zero region iff it does not land in the cozero region (an element-wise dichotomy) *)
Theorem fiber_cozero_compl : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) <-> ~ In x (cozero f w)).
Proof.
  intros f w x Hw. split.
  - intros H1 Hc. exact (fiber_cozero_disjoint f w x H1 Hc).
  - intros Hn. apply (fiber_cozero_cover f w x) in Hw.
    destruct Hw as [H|H]; [exact H | exfalso; apply Hn; exact H].
Qed.

(* ========== section 7, final audit: Print Assumptions (the G4 gate) ========== *)

Print Assumptions fiber_mul_union.
Print Assumptions fiber_sumsq_inter.
Print Assumptions ideal_sub_closed.
Print Assumptions fiber_cozero_compl.
Print Assumptions fiber_cozero_length.

