(* ConstructiveWorld-Main - the Dirichlet test face of the alternating    *)
(* block: the Abel window carrier and the eta series statement face.      *)

(** * GaC2_07_DirichletTestAbel: node C2-07, the Dirichlet test face.

    Mission.  Node C2-07 (segment C2, slot W2), the constructive face
    of the Dirichlet test: the window sum carriers of the Abel partial
    summation ([c_abssum], [c_wsum]), the sign carrier [alt_sign], the
    eta column ([eta_term], [eta_part]), the machine cluster closed
    now ([alt_sign_step], [eta_part_zero], [eta_part_step],
    [abssum_zero], [wsum_zero_le], [c_of_real_plus_opp],
    [c_norm_sq_mone_face], [abssum_alt_pair], [c_norm_sq_zero_le_one],
    [r_neg_one_mult_l], [eta_sgn_bounded_pair] (the card B=1 supply
    row, the parity-pair form), [eta_term_real_axis],
    [abel_tri_pair_step]), and the two named statement faces of the
    card, minted at the statement-carrier form with the proof routes
    registered (fail-loud): [abel_tail] (the card (1) Abel window
    bound 2 B a_{M+1} in the squared house form, the section slot
    discharged as explicit premise arguments, the C2-17 house
    convention) and [eta_conv_uniform] (the card eta-row tail
    relation with the uniform floor bound 2 (N+1)^(-sigma0), the eta
    value entering as the explicit premise argument).
    Registered adaptations over the sketch (drafts_C2.md C2.07):
    (i) the Section slot discharged as explicit premise arguments;
    (ii) nat bounds carried by the Set-sorted [NatLe] (the C2-01
    red-line A ruling); (iii) the sketch window pseudo-form realized
    on the C2-01 house conditional prefix shape; (iv) the sketch
    [alt_sign] stdlib slot realized as the explicit parity sign
    carrier; (v) the to-zero modulus slot minted as the premise
    carrier [abel_tozero_slot] (the finite window bound does not
    consume it); (vi) the eta value enters [eta_conv_uniform] as the
    explicit premise argument: the sketch t-free uniform tail face is
    registered FALSE on the unbounded imaginary face (stationary-phase
    census: violation 1.12x at |t| = 30 up to 17.52x at |t| = 5000 on
    s = 1/2 + i t against the card constant); the discharge row is
    the real-axis leaf slot (the card's own instantiation lives on
    the real line, the Leibniz bracketing route).
    Proof-body state (fail-loud): [abel_tail] consumes the n-fold
    linear triangle face registered open at L-C2.02-C of the C2-02
    casting (not L0 stock; the C1-14 face is the two-fold step only,
    consumed as [abel_tri_pair_step]); the body closes when the
    supply row lands.  [eta_conv_uniform] closes on the real axis
    when the leaf slot lands (the completion machine
    [real_cauchy_complete] is L0 stock; the route consumes the C2-06
    rows [r_npow_anti] / [r_npow_diff_nonneg]).

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
    Requires [S01_BaseRing] (selective [NatLe] import), [S02]
    (the real carrier and the order algebra), [S03] ([cauchy_real_exp]),
    [S07] ([real_log], the RealSetoid bundle), [CxRealPairCore],
    [CxRealPairExpLog], [GaC1_Iface_Cx] (the L1 interface; the C1-14
    two-fold step consumed in [abel_tri_pair_step]),
    [GaC2_01_DirichletPartialSum] ([c_powq] discharged signature,
    [nat_real], [NatLe_one_S], [c_of_real], [c_plus_zero_r]),
    [GaC2_02_AbsConvTailBound_a] (the algebra leaves [r_le_of_eq],
    [r_mult_opp_l], [r_opp_invol], [c_of_real_mult_gen],
    [c_of_real_scale_gen], [c_of_real_wd], [nat_real_pos],
    [c_norm_sq_wd]), [GaC2_06_AltMonoFace] ([r_npow_at], the card
    C2-06 premise rows); zero cross-segment requires beyond the L1
    interface.

    References.  cards_C2.md C2.07 card; drafts_C2.md C2.07 sketch
    (the adaptations above); gamma_module_spec.md section 3.3 the W2
    row; Titchmarsh Ch.1 the Dirichlet test and Abel summation
    (statement architecture only); Montgomery-Vaughan Ch.1; the
    certificate-face numeric census run of this casting.

    Constructivity.  Every named construction is carried by [Set];
    the order premises are the Set-sorted [real_lt] / [real_le]; the
    parity conjunction is the Set-sorted [And]; no Section wrapper,
    no assumed constant, no abandoned proof; the machine cluster
    proofs close under the global context; the two named faces are
    well-formed Set statement carriers with the routes registered.

    Build.  [coqc -native-compiler no -q -Q <l0_local> "" -Q <build>
    "" GaC2_07_DirichletTestAbel.v] from the flat build directory,
    thermal guard wrapper; acceptance runs
    [50_toolkit/accept_node.py --node C2.07] with the certificate
    face [GaC2_07_DirichletTestAbel_cert] (Q-sample band). *)


Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_06_AltMonoFace.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.Arith Lia.

Local Open Scope Q_scope.

(* Section 1. The sign and window carriers. *)

(* The alternating sign carrier: -1 at 0, +1 at 1, one opp per step.     *)
Fixpoint alt_sign (n : nat) : Real :=
  match n with
  | O => real_opp real_one
  | S m => real_opp (alt_sign m)
  end.

(* The prefix sum carrier of the sketch: the sum over the first N        *)
(* indices of the column.                                                *)
Fixpoint c_abssum (N : nat) (b : nat -> Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (c_abssum m b) (b m)
  end.

(* The window sum carrier sum_{M<n<=N} a_n b_n, the sketch window form   *)
(* realized on the C2-01 house conditional prefix shape.                 *)
Fixpoint c_wsum (M N : nat) (a : nat -> Real) (b : nat -> Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (c_wsum M m a b)
             (if Nat.ltb M (S m) then c_scale (a (S m)) (b (S m)) else c_zero)
  end.

(* The squared carrier (the sketch [sq] name; the C2-17 same shape).     *)
Definition sq (x : Real) : Real := real_mult x x.

(* The card to-zero modulus slot (adaptation (v)).                       *)
Definition abel_tozero_slot (a beta : nat -> Real) : Set :=
  And (forall n : nat, real_le (a n) (beta n))
      (sigT (fun M0 : nat =>
        forall n : nat, NatLe M0 n -> real_le (beta n) (beta M0))).

(* Section 2. The eta column. *)

(* The eta term: the alternating sign times the n^{-s} carrier.          *)
Definition eta_term
  (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
  (n : nat) (Hn : NatLe 1 n) (s : Cx) : Cx :=
  c_scale (alt_sign n) (c_powq Hnpos n Hn s).

(* The eta partial sum column (the sketch name [eta_part]).              *)
Fixpoint eta_part
  (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
  (N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (eta_part Hnpos m s) (eta_term Hnpos (S m) (NatLe_one_S m) s)
  end.

(* The complex sign column used by the modulus supply row.               *)
Definition eta_sgn_cx (n : nat) : Cx := c_of_real (alt_sign n).

(* Section 3. The machine cluster (all bodies close). *)

Lemma alt_sign_step : forall n : nat,
  real_eq (alt_sign (S n)) (real_opp (alt_sign n)).
Proof. intro n. simpl. apply real_eq_refl. Qed.

Lemma eta_part_zero :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (s : Cx), c_eq (eta_part Hnpos 0 s) c_zero.
Proof. intros Hnpos s. apply c_eq_refl. Qed.

Lemma eta_part_step :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (N : nat) (s : Cx),
  c_eq (eta_part Hnpos (S N) s)
       (c_plus (eta_part Hnpos N s)
               (eta_term Hnpos (S N) (NatLe_one_S N) s)).
Proof. intros Hnpos N s. apply c_eq_refl. Qed.

Lemma abssum_zero : forall b : nat -> Cx, c_eq (c_abssum 0 b) c_zero.
Proof. intro b. apply c_eq_refl. Qed.

Lemma wsum_zero_le : forall (M N : nat) (a : nat -> Real) (b : nat -> Cx),
  NatLe N M -> c_eq (c_wsum M N a b) c_zero.
Proof.
  intros M N a b. revert M. induction N as [|m IH]; intros M HNM.
  - cbn [c_wsum]. apply c_eq_refl.
  - cbn [c_wsum].
    assert (Hltb : Nat.ltb M (S m) = false).
    { exact (proj2 (Nat.ltb_ge M (S m)) (NatLe_drop _ _ HNM)). }
    rewrite Hltb.
    apply (c_eq_trans _ (c_wsum M m a b)).
    + apply c_plus_zero_r.
    + apply IH. apply NatLe_lift.
      apply Nat.le_trans with (S m);
        [apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM].
Qed.

(* x + (-x) collapses on the embedded line.                              *)
Lemma c_of_real_plus_opp : forall x : Real,
  c_eq (c_plus (c_of_real x) (c_of_real (real_opp x))) c_zero.
Proof.
  intro x. destruct x as [u Hu].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n;
    unfold c_plus, c_of_real, cRe, cIm; simpl; ring.
Qed.

(* The pointwise face of the odd parity value against 1 * 1.             *)
Lemma c_norm_sq_mone_face :
  real_eq (c_norm_sq (c_of_real (real_opp real_one)))
          (real_mult real_one real_one).
Proof.
  apply real_eq_of_zero_diff. intro n.
  destruct real_one as [uo Ho]. simpl. ring.
Qed.

(* The parity faces of the sign column (the B=1 supply row base).        *)
Lemma abssum_alt_pair : forall k : nat,
  And (real_eq (alt_sign (2 * k)%nat) (real_opp real_one))
      (And (c_eq (c_abssum (2 * k)%nat eta_sgn_cx) c_zero)
           (c_eq (c_abssum (S (2 * k))%nat eta_sgn_cx)
                 (c_of_real (real_opp real_one)))).
Proof.
  induction k as [|k IH].
  - split; [| split].
    + simpl. apply real_eq_refl.
    + apply abssum_zero.
    + cbn [c_abssum eta_sgn_cx alt_sign]. apply c_plus_zero.
  - destruct IH as [Hsign [Heven Hodd]].
    assert (Hmul : (2 * S k)%nat = (S (S (2 * k)))%nat) by lia.
    split.
    + rewrite Hmul. simpl.
      apply (real_eq_trans _ (alt_sign (2 * k)%nat)).
      * exact (r_opp_invol (alt_sign (2 * k)%nat)).
      * exact Hsign.
    + rewrite Hmul. cbn [c_abssum]. split.
      * apply (c_eq_trans _
          (c_plus (c_abssum (2 * k)%nat eta_sgn_cx)
             (c_plus (eta_sgn_cx (2 * k)%nat)
                     (eta_sgn_cx (S (2 * k)%nat))))).
        -- apply c_eq_sym. apply c_plus_assoc.
        -- apply (c_eq_trans _
             (c_plus (c_abssum (2 * k)%nat eta_sgn_cx) c_zero)).
           ++ apply c_plus_congr;
              [apply c_eq_refl | apply c_of_real_plus_opp].
           ++ apply (c_eq_trans _ (c_abssum (2 * k)%nat eta_sgn_cx)).
              ** apply c_plus_zero_r.
              ** exact Heven.
      * apply (c_eq_trans _
          (c_plus (c_plus (c_abssum (2 * k)%nat eta_sgn_cx)
                     (eta_sgn_cx (2 * k)%nat))
                  (c_plus (eta_sgn_cx (S (2 * k)%nat))
                     (eta_sgn_cx (S (S (2 * k)%nat)))))).
        -- apply c_eq_sym. apply c_plus_assoc.
        -- apply (c_eq_trans _
             (c_plus (c_plus (c_abssum (2 * k)%nat eta_sgn_cx)
                        (eta_sgn_cx (2 * k)%nat))
                     c_zero)).
           ++ apply c_plus_congr;
              [apply c_eq_refl | apply c_of_real_plus_opp].
           ++ apply (c_eq_trans _
                (c_plus (c_abssum (2 * k)%nat eta_sgn_cx)
                   (eta_sgn_cx (2 * k)%nat))).
              ** apply c_plus_zero_r.
              ** apply (c_eq_trans _
                   (c_plus c_zero (eta_sgn_cx (2 * k)%nat))).
                 --- apply c_plus_congr; [exact Heven | apply c_eq_refl].
                 --- apply (c_eq_trans _ (eta_sgn_cx (2 * k)%nat)).
                     +++ apply c_plus_zero.
                     +++ apply c_of_real_wd. exact Hsign.
Qed.

(* The zero value sits strictly inside the unit band (the even face).    *)
Lemma c_norm_sq_zero_le_one :
  real_le (c_norm_sq c_zero) (real_mult real_one real_one).
Proof.
  apply (real_lt_le_iff real_zero (real_mult real_one real_one)). left.
  exists (1#2)%Q. split.
  - reflexivity.
  - exists 0%nat. intros n Hn.
    change (QltT (1#2)%Q
       (projT1 (real_mult real_one real_one) n
          - projT1 (c_norm_sq c_zero) n)).
    reflexivity.
Qed.

(* The card B=1 supply row (the parity-pair form): both prefix sums of   *)
(* each parity pair stay within modulus 1.  The single-index form needs  *)
(* the parity splitter row and stays with the leaf slot.                 *)
Lemma eta_sgn_bounded_pair : forall k : nat,
  And (real_le (c_norm_sq (c_abssum (2 * k)%nat eta_sgn_cx))
             (real_mult real_one real_one))
      (real_le (c_norm_sq (c_abssum (S (2 * k))%nat eta_sgn_cx))
             (real_mult real_one real_one)).
Proof.
  intro k. destruct (abssum_alt_pair k) as [_ [Heven Hodd]]. split.
  - apply (real_le_trans _ (c_norm_sq c_zero)).
    + apply r_le_of_eq. apply c_norm_sq_wd. exact Heven.
    + exact c_norm_sq_zero_le_one.
  - apply (real_le_trans _ (c_norm_sq (c_of_real (real_opp real_one)))).
    + apply r_le_of_eq. apply c_norm_sq_wd. exact Hodd.
    + apply r_le_of_eq. exact c_norm_sq_mone_face.
Qed.

(* The left-one negative scaling face: (-1) * x equals -x.               *)
Lemma r_neg_one_mult_l : forall x : Real,
  real_eq (real_mult (real_opp real_one) x) (real_opp x).
Proof.
  intro x. apply (real_eq_trans _ (real_opp (real_mult real_one x))).
  - exact (r_mult_opp_l real_one x).
  - apply RealSetoid.real_eq_opp_compat.
    apply (real_eq_trans _ (real_mult x real_one)).
    + apply real_mult_comm.
    + exact (real_mult_one x).
Qed.

(* The real-axis reduction of the eta term (the instantiation bridge).   *)
Lemma eta_term_real_axis :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (n : nat) (Hn : NatLe 1 n) (sg : Real),
  c_eq (eta_term Hnpos n Hn (c_of_real sg))
       (c_of_real (real_mult (alt_sign n)
          (cauchy_real_exp
             (real_mult (real_opp sg)
                (real_log (nat_real n) (Hnpos n Hn)))))).
Proof.
  intros Hnpos n Hn sg. unfold eta_term, c_powq.
  apply (c_eq_trans _ (c_scale (alt_sign n)
    (c_exp (c_of_real
       (real_mult (real_opp real_one)
          (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))))).
  - apply c_scale_wd. apply c_exp_wd.
    apply (c_eq_trans _
      (c_scale (real_opp real_one)
         (c_of_real
            (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))).
    + apply c_scale_wd. exact (c_of_real_mult_gen sg
         (real_log (nat_real n) (Hnpos n Hn))).
    + exact (c_of_real_scale_gen (real_opp real_one)
         (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))).
  - apply (c_eq_trans _
      (c_scale (alt_sign n)
         (c_of_real
            (cauchy_real_exp
               (real_mult (real_opp real_one)
                  (real_mult sg
                     (real_log (nat_real n) (Hnpos n Hn)))))))).
    + apply c_scale_wd. apply c_exp_real.
    + apply (c_eq_trans _ (c_of_real
        (real_mult (alt_sign n)
           (cauchy_real_exp
              (real_mult (real_opp real_one)
                 (real_mult sg
                    (real_log (nat_real n) (Hnpos n Hn)))))))).
      * exact (c_of_real_scale_gen (alt_sign n)
            (cauchy_real_exp
               (real_mult (real_opp real_one)
                  (real_mult sg
                     (real_log (nat_real n) (Hnpos n Hn)))))).
      * apply c_of_real_wd.
        apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
        apply cauchy_real_exp_wd.
        apply (real_eq_trans _
          (real_mult (real_mult (real_opp real_one) sg)
             (real_log (nat_real n) (Hnpos n Hn)))).
        -- apply real_mult_assoc.
        -- apply RealSetoid.real_eq_mult_compat;
             [exact (r_neg_one_mult_l sg) | apply real_eq_refl].
Qed.

(* The Abel route two-fold step through the L1 interface (the n-fold     *)
(* linear supply row stays registered open).                             *)
Lemma abel_tri_pair_step : forall (u v : Cx) (d : Q), QltT 0 d ->
  real_lt (c_norm_sq (c_plus u v))
          (real_plus (real_mult (real_const (2#1))
                        (real_plus (c_norm_sq u) (c_norm_sq v)))
                     (real_const d)).
Proof. intros u v d Hd. exact (gaC1_14_norm_sq_pair_lt u v d Hd). Qed.

(* Section 4. The two named statement faces (card-verbatim names). *)

(* Statement carrier of [abel_tail]: the card (1) Abel window bound.     *)
(* Route: the telescoping identity with the bounded-prefix triangle;     *)
(* consumes the n-fold linear triangle face open at L-C2.02-C.           *)
Definition abel_tail
  (a : nat -> Real) (b : nat -> Cx) (B : Real)
  (Ha_anti : forall m n : nat, NatLe m n -> real_le (a n) (a m))
  (Hb_bounded : forall N : nat,
     real_le (c_norm_sq (c_abssum N b)) (real_mult B B)) : Set :=
  forall (M N : nat), NatLe (S M) N ->
    real_le (c_norm_sq (c_wsum M N a b))
            (sq (real_mult (real_const (2#1)) (real_mult B (a (S M))))).

(* Statement carrier of [eta_conv_uniform]: the card eta-row tail        *)
(* relation (adaptation (vi); route: the real-axis Leibniz bracketing    *)
(* through the C2-06 rows and the L0 completion machine; the body        *)
(* closes on the real axis when the leaf slot lands).                    *)
Definition eta_conv_uniform
  (sig0 : Real) (Hs0 : real_lt real_zero sig0)
  (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
  (s : Cx) (eta_s : Cx) : Set :=
  forall N : nat,
    real_le (c_norm_sq (c_plus (eta_part Hnpos N s) (c_opp eta_s)))
            (sq (real_mult (real_const (2#1))
                   (r_npow_at sig0 Hnpos (S N) (NatLe_one_S N)))).
