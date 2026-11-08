(* ConstructiveWorld-Main - van der Corput A-process toolkit leaves on the Q-step phasor carrier. *)

(** * GaC3_V01_VdCSecond_b: Q-pair phasor toolkit leaf B.

    Mission.  Node C3-V01 (segment C3), toolkit leaf B: the Q-pair
    phasor carrier [GaC3_V01_phasor] and its algebra, the
    component-sum micro-kit [GaC3_V01_scomp], the all-zero absorption
    face, the aligned-pair walk [GaC3_V01_opwalk] with the
    correlation carrier, the aligned-pair nth bridge
    [GaC3_V01_nth_pair_sum], and the two-index transpose of finite
    double sums.  Q is the non-canonical pair type, so all phasor
    algebra is discharged at the Q-component level ([pnorm2]/[pdot]
    identities); pair equality is used only where it is structural.
    Consumes leaf A.

    Dependencies.  [GaC3_V01_VdCSecond_a] (toolkit leaf A),
    [GaC3_P01_LineIntegralDef], [GaC3_P02_LineIntegralAlg] (vertex
    type as the phasor carrier), [GaC3_P03_MLEstimate] (order
    micro-helpers), [S01_BaseRing] ([Id] bool-reflection carrier for
    the all-zero check); Stdlib [QArith], [Arith], [Lia], [List].

    References.  The van der Corput A-process inequality
    (Graham-Kolesnik, van der Corput's method of exponential sums,
    A-process chapter; Iwaniec-Kowalski Ch. 8); cards_C3 C3-V01;
    drafts_C3 V01 statement skeleton (rebuilt on the Q-step phasor
    carrier per the P01/P03 Q-step doctrine).

    Constructivity.  Set-carried statements; zero assumed constants,
    zero abandoned proofs, zero classical choice; all numerics stay
    in Q (decidable, exact); [lia] is used only for nat index
    bookkeeping.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
      GaC3_V01_VdCSecond_b.v] compiles cleanly (exit 0) from the work
      directory (sandbox pair), single compile lane under the
      cpu_guard v3 wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require S01_BaseRing.
Require Import GaC3_V01_VdCSecond_a.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P03_MLEstimate.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. The Q-pair phasor carrier and its algebra.                  *)
(* ===================================================================== *)

Definition GaC3_V01_phasor : Set := GaC3_P02_vertex.

Definition GaC3_V01_pzero : GaC3_V01_phasor := (0, 0).

Definition GaC3_V01_pdot (z w : GaC3_V01_phasor) : Q :=
  fst z * fst w + snd z * snd w.

Definition GaC3_V01_pnorm2 (z : GaC3_V01_phasor) : Q := GaC3_V01_pdot z z.

Definition GaC3_V01_pplus (z w : GaC3_V01_phasor) : GaC3_V01_phasor :=
  (fst z + fst w, snd z + snd w).

(* Set bearer for the all-zero check (S01 NatLe / S02 QleT' Id pattern):  *)
(* the check is a computation (Qeq_bool), not a Prop premise.              *)
Definition GaC3_V01_allzero (z : GaC3_V01_phasor) : Set :=
  S01_BaseRing.Id (andb (Qeq_bool (fst z) 0) (Qeq_bool (snd z) 0)) true.

(* Bridge (elim): Set bearer -> Q component equalities. *)
Lemma GaC3_V01_allzero_elim : forall z : GaC3_V01_phasor,
  GaC3_V01_allzero z -> fst z == 0 /\ snd z == 0.
Proof.
  intro z. unfold GaC3_V01_allzero. intro H.
  destruct (andb (Qeq_bool (fst z) 0) (Qeq_bool (snd z) 0)) eqn:E.
  - apply andb_true_iff in E. destruct E as [E1 E2].
    split.
    + exact (Qeq_bool_eq (fst z) 0 E1).
    + exact (Qeq_bool_eq (snd z) 0 E2).
  - inversion H.
Qed.

(* Bridge (intro): Q component equalities -> Set bearer. *)
Lemma GaC3_V01_allzero_intro : forall z : GaC3_V01_phasor,
  fst z == 0 -> snd z == 0 -> GaC3_V01_allzero z.
Proof.
  intros z Hz1 Hz2. unfold GaC3_V01_allzero.
  rewrite (Qeq_eq_bool (fst z) 0 Hz1), (Qeq_eq_bool (snd z) 0 Hz2).
  apply S01_BaseRing.id_refl.
Qed.

Definition GaC3_V01_hd0 (l : list GaC3_V01_phasor) : GaC3_V01_phasor :=
  match l with
  | nil => GaC3_V01_pzero
  | w :: _ => w
  end.

Fixpoint GaC3_V01_wphas (l : list GaC3_V01_phasor) : GaC3_V01_phasor :=
  match l with
  | nil => GaC3_V01_pzero
  | z :: l' => GaC3_V01_pplus z (GaC3_V01_wphas l')
  end.

Definition GaC3_V01_scomp (f : GaC3_V01_phasor -> Q) (l : list GaC3_V01_phasor) : Q :=
  GaC3_V01_qsum (map f l).

Definition GaC3_V01_sR (l : list GaC3_V01_phasor) : Q := GaC3_V01_scomp fst l.

Definition GaC3_V01_sI (l : list GaC3_V01_phasor) : Q := GaC3_V01_scomp snd l.

Definition GaC3_V01_plist_dot (l : list GaC3_V01_phasor) : Q :=
  GaC3_V01_scomp GaC3_V01_pnorm2 l.

Lemma GaC3_V01_pdot_zero_r : forall z : GaC3_V01_phasor,
  GaC3_V01_pdot z GaC3_V01_pzero == 0.
Proof. intro z. unfold GaC3_V01_pdot, GaC3_V01_pzero. cbn [fst snd]. ring. Qed.

Lemma GaC3_V01_pdot_zero_l : forall z : GaC3_V01_phasor,
  GaC3_V01_pdot GaC3_V01_pzero z == 0.
Proof. intro z. unfold GaC3_V01_pdot, GaC3_V01_pzero. cbn [fst snd]. ring. Qed.

Lemma GaC3_V01_pnorm2_zero : GaC3_V01_pnorm2 GaC3_V01_pzero == 0.
Proof. unfold GaC3_V01_pnorm2. apply GaC3_V01_pdot_zero_r. Qed.

Lemma GaC3_V01_pnorm2_plus : forall z w : GaC3_V01_phasor,
  GaC3_V01_pnorm2 (GaC3_V01_pplus z w)
  == GaC3_V01_pnorm2 z + (2 * GaC3_V01_pdot z w + GaC3_V01_pnorm2 w)%Q.
Proof.
  intros z w. unfold GaC3_V01_pnorm2, GaC3_V01_pplus, GaC3_V01_pdot.
  cbn [fst snd]. ring.
Qed.

Lemma GaC3_V01_pdot_sym : forall z w : GaC3_V01_phasor,
  GaC3_V01_pdot z w == GaC3_V01_pdot w z.
Proof. intros z w. unfold GaC3_V01_pdot. ring. Qed.

Lemma GaC3_V01_pdot_plus_r : forall z w u : GaC3_V01_phasor,
  GaC3_V01_pdot z (GaC3_V01_pplus w u) == GaC3_V01_pdot z w + GaC3_V01_pdot z u.
Proof.
  intros z w u. unfold GaC3_V01_pdot, GaC3_V01_pplus. cbn [fst snd]. ring.
Qed.

Lemma GaC3_V01_pdot_plus_l : forall z w u : GaC3_V01_phasor,
  GaC3_V01_pdot (GaC3_V01_pplus z w) u == GaC3_V01_pdot z u + GaC3_V01_pdot w u.
Proof.
  intros z w u. unfold GaC3_V01_pdot, GaC3_V01_pplus. cbn [fst snd]. ring.
Qed.

(* The phasor sum of an all-zero list is all-zero (componentwise). *)
Lemma GaC3_V01_allzero_pplus : forall z w : GaC3_V01_phasor,
  GaC3_V01_allzero z -> GaC3_V01_allzero w -> GaC3_V01_allzero (GaC3_V01_pplus z w).
Proof.
  intros z w Hz Hw.
  pose proof (GaC3_V01_allzero_elim z Hz) as HzE.
  pose proof (GaC3_V01_allzero_elim w Hw) as HwE.
  destruct HzE as [Hz1 Hz2]. destruct HwE as [Hw1 Hw2].
  apply GaC3_V01_allzero_intro.
  - unfold GaC3_V01_pplus. cbn [fst]. rewrite Hz1, Hw1. ring.
  - unfold GaC3_V01_pplus. cbn [snd]. rewrite Hz2, Hw2. ring.
Qed.

Lemma GaC3_V01_wphas_zero_comp : forall l : list GaC3_V01_phasor,
  (forall x, In x l -> GaC3_V01_allzero x) -> GaC3_V01_allzero (GaC3_V01_wphas l).
Proof.
  induction l as [| z l IH]; intro Hz.
  - apply GaC3_V01_allzero_intro; reflexivity.
  - cbn [GaC3_V01_wphas]. apply GaC3_V01_allzero_pplus.
    + apply Hz. apply in_eq.
    + apply IH. intros x Hx. apply Hz. exact (in_cons z x l Hx).
Qed.

(* The singleton-sum component faces: pnorm2/pdot of wphas (l ++ [x]).   *)
Lemma GaC3_V01_wphas_sing_dot : forall (z : GaC3_V01_phasor)
  (A : list GaC3_V01_phasor) (x : GaC3_V01_phasor),
  GaC3_V01_pdot z (GaC3_V01_wphas (A ++ (x :: nil)))
  == GaC3_V01_pdot z (GaC3_V01_wphas A) + GaC3_V01_pdot z x.
Proof.
  intros z A x.
  induction A as [| y A' IH].
  - cbn [app GaC3_V01_wphas]. rewrite GaC3_V01_pdot_plus_r.
    rewrite GaC3_V01_pdot_zero_r. ring.
  - cbn [app GaC3_V01_wphas]. rewrite GaC3_V01_pdot_plus_r.
    rewrite IH. cbn [GaC3_V01_wphas]. rewrite GaC3_V01_pdot_plus_r.
    ring.
Qed.

Lemma GaC3_V01_wphas_sing_norm2 : forall (A : list GaC3_V01_phasor)
  (x : GaC3_V01_phasor),
  GaC3_V01_pnorm2 (GaC3_V01_wphas (A ++ (x :: nil)))
  == GaC3_V01_pnorm2 (GaC3_V01_wphas A)
     + (2 * GaC3_V01_pdot (GaC3_V01_wphas A) x + GaC3_V01_pnorm2 x)%Q.
Proof.
  intros A x.
  induction A as [| y A' IH].
  - cbn [app GaC3_V01_wphas].
    rewrite GaC3_V01_pnorm2_plus.
    rewrite GaC3_V01_pdot_zero_r, GaC3_V01_pnorm2_zero.
    rewrite GaC3_V01_pdot_zero_l.
    cbn [GaC3_V01_wphas]. ring.
  - cbn [app GaC3_V01_wphas].
    rewrite GaC3_V01_pnorm2_plus.
    rewrite (GaC3_V01_wphas_sing_dot y A' x).
    rewrite IH. cbn [GaC3_V01_wphas].
    rewrite GaC3_V01_pnorm2_plus.
    rewrite GaC3_V01_pdot_plus_l.
    ring.
Qed.

(* ===================================================================== *)
(* Section 3. The scomp micro-kit.                                        *)
(* ===================================================================== *)

Lemma GaC3_V01_scomp_cons : forall (f : GaC3_V01_phasor -> Q)
  (x : GaC3_V01_phasor) (l : list GaC3_V01_phasor),
  GaC3_V01_scomp f (x :: l) == f x + GaC3_V01_scomp f l.
Proof. intros f x l. reflexivity. Qed.

Lemma GaC3_V01_scomp_add : forall (f g : GaC3_V01_phasor -> Q)
  (l : list GaC3_V01_phasor),
  GaC3_V01_scomp (fun x => f x + g x)%Q l == GaC3_V01_scomp f l + GaC3_V01_scomp g l.
Proof.
  intros f g l. unfold GaC3_V01_scomp. induction l as [| x l' IH].
  - cbn [map GaC3_V01_qsum]. ring.
  - cbn [map GaC3_V01_qsum]. rewrite IH. apply GaC3_V01_qplus_exchange.
Qed.

Lemma GaC3_V01_scomp_mul_l : forall (c : Q) (f : GaC3_V01_phasor -> Q)
  (l : list GaC3_V01_phasor),
  GaC3_V01_scomp (fun x => c * f x)%Q l == c * GaC3_V01_scomp f l.
Proof.
  intros c f l. unfold GaC3_V01_scomp. induction l as [| x l' IH].
  - cbn [map GaC3_V01_qsum]. ring.
  - cbn [map GaC3_V01_qsum]. rewrite IH. ring.
Qed.

(* scomp over an all-zero list vanishes, for any f vanishing on all-zero *)
(* phasors (the per-f supplier lives at the consumer).                   *)
Lemma GaC3_V01_scomp_allzero0 : forall (f : GaC3_V01_phasor -> Q)
  (l : list GaC3_V01_phasor),
  (forall z, GaC3_V01_allzero z -> f z == 0) ->
  (forall x, In x l -> GaC3_V01_allzero x) -> GaC3_V01_scomp f l == 0.
Proof.
  intros f l Hf0. induction l as [| z l IH]; intro Hz.
  - reflexivity.
  - assert (Ez : f z == 0) by (apply Hf0; apply Hz; apply in_eq).
    unfold GaC3_V01_scomp in *. cbn [map GaC3_V01_qsum].
    rewrite Ez, IH.
    + ring.
    + intros x Hx. apply Hz. exact (in_cons z x l Hx).
Qed.

Lemma GaC3_V01_f_wphas_nth : forall (f : GaC3_V01_phasor -> Q)
  (l : list GaC3_V01_phasor),
  (forall z w : GaC3_V01_phasor, f (GaC3_V01_pplus z w) == f z + f w) ->
  f GaC3_V01_pzero == 0 ->
  f (GaC3_V01_wphas l)
  == GaC3_V01_qsum (map (fun i => f (nth i l GaC3_V01_pzero)) (seq 0 (length l))).
Proof.
  intros f l Hfp Hf0. induction l as [| z l' IH].
  - exact Hf0.
  - cbn [GaC3_V01_wphas length seq map GaC3_V01_qsum].
    rewrite Hfp. rewrite IH.
    rewrite (GaC3_V01_map_seq_S Q (fun i => f (nth i (z :: l') GaC3_V01_pzero)) (length l')).
    cbv beta. cbn [nth]. reflexivity.
Qed.

(* The scomp of the firstn prefix equals the full scomp when the tail is  *)
(* all-zero (nth-form hypothesis; per-f zero supplier).                  *)
Lemma GaC3_V01_scomp_firstn_allzero : forall (f : GaC3_V01_phasor -> Q)
  (W : list GaC3_V01_phasor) (n : nat),
  (forall z, GaC3_V01_allzero z -> f z == 0) ->
  (forall p, (n <= p < length W)%nat -> GaC3_V01_allzero (nth p W GaC3_V01_pzero)) ->
  GaC3_V01_scomp f (firstn n W) == GaC3_V01_scomp f W.
Proof.
  intros f W n Hf0 Hall.
  destruct (le_lt_dec n (length W)) as [Hle | Hgt].
  - unfold GaC3_V01_scomp.
    rewrite <- (GaC3_V01_nth_seq_sum GaC3_V01_phasor f (firstn n W) GaC3_V01_pzero).
    rewrite <- (GaC3_V01_nth_seq_sum GaC3_V01_phasor f W GaC3_V01_pzero).
    rewrite firstn_length_le by exact Hle.
    rewrite (GaC3_V01_qsum_ext
               (fun i => f (nth i (firstn n W) GaC3_V01_pzero))
               (fun i => f (nth i W GaC3_V01_pzero)) n 0%nat).
    + assert (Hsplit : (length W = n + (length W - n))%nat) by lia.
      rewrite Hsplit.
      rewrite (seq_app n (length W - n) 0%nat).
      rewrite map_app. rewrite GaC3_V01_qsum_app.
      assert (Etail : GaC3_V01_qsum
                 (map (fun i => f (nth i W GaC3_V01_pzero))
                      (seq ((0 + n)%nat) (length W - n))) == 0).
      { rewrite (GaC3_V01_qsum_ext
                   (fun i => f (nth i W GaC3_V01_pzero))
                   (fun _ => 0) (length W - n) (0 + n)%nat).
        - apply GaC3_V01_qsum_map_0.
        - intros i Hi. cbv beta. apply Hf0. apply Hall. lia. }
      rewrite Etail. symmetry. apply Qplus_0_r.
    + intros i Hi. cbv beta.
      rewrite (GaC3_V01_nth_firstn GaC3_V01_phasor GaC3_V01_pzero n i W (proj2 Hi)).
      reflexivity.
  - rewrite firstn_all2 by lia. reflexivity.
Qed.

(* ===================================================================== *)
(* Section 4. The aligned-pair walk, correlation, and the nth bridge.     *)
(* ===================================================================== *)

Fixpoint GaC3_V01_opwalk (A : Type) (op : A -> A -> Q) (xs ys : list A) : Q :=
  match xs with
  | nil => 0
  | x :: xs' =>
      match ys with
      | nil => 0
      | y :: ys' => op x y + GaC3_V01_opwalk A op xs' ys'
      end
  end.

Definition GaC3_V01_corr (d : nat) (zs : list GaC3_V01_phasor) : Q :=
  GaC3_V01_opwalk GaC3_V01_phasor GaC3_V01_pdot zs (skipn d zs).

Lemma GaC3_V01_corr0_plist_dot : forall zs : list GaC3_V01_phasor,
  GaC3_V01_corr 0 zs == GaC3_V01_plist_dot zs.
Proof.
  intro zs. unfold GaC3_V01_corr, GaC3_V01_plist_dot, GaC3_V01_scomp.
  revert zs. induction zs as [| z zs' IH].
  - reflexivity.
  - cbn [skipn map GaC3_V01_qsum GaC3_V01_opwalk]. rewrite IH.
    reflexivity. (* pnorm2 z is pdot z z by definition *)
Qed.

Lemma GaC3_V01_nth_pair_sum : forall (A : Type) (op : A -> A -> Q) (az : A),
  (forall x : A, op x az == 0) ->
  (forall x : A, op az x == 0) ->
  forall (l : list A) (d : nat),
  GaC3_V01_qsum (map (fun t => op (nth t l az) (nth ((t + d)%nat) l az)) (seq 0 (length l)))
  == GaC3_V01_opwalk A op l (skipn d l).
Proof.
  intros A op az Hopr Hopl l. induction l as [| x l' IH]; intro d.
  - rewrite (GaC3_V01_skipn_nil A d nil (Nat.le_0_l _)).
    cbn [seq map length GaC3_V01_qsum GaC3_V01_opwalk]. reflexivity.
  - assert (Estn : forall (m : nat) (mm : list A),
              nth (S m) (x :: mm) az = nth m mm az)
      by (intros m mm; reflexivity).
    cbn [length seq map GaC3_V01_qsum].
    rewrite (GaC3_V01_map_seq_S Q
              (fun t => op (nth t (x :: l') az) (nth ((t + d)%nat) (x :: l') az))
              (length l')).
    cbv beta. cbn [Nat.add].
    assert (Emap : map (fun i : nat => op (nth (S i) (x :: l') az) (nth (S (i + d)) (x :: l') az))
                     (seq 0 (length l'))
                 = map (fun t : nat => op (nth t l' az) (nth ((t + d)%nat) l' az))
                     (seq 0 (length l'))).
    { rewrite (map_ext
                 (fun i : nat => op (nth (S i) (x :: l') az) (nth (S (i + d)) (x :: l') az))
                 (fun t : nat => op (nth t l' az) (nth ((t + d)%nat) l' az))).
      - reflexivity.
      - cbv beta. intros a.
        rewrite (Estn a l'), (Estn (a + d)%nat l'). reflexivity. }
    rewrite Emap. rewrite (IH d).
    destruct d as [| d'].
    + cbn [skipn nth GaC3_V01_opwalk]. reflexivity.
    + rewrite (Estn d' l').
      destruct l' as [| y l''].
      * rewrite (GaC3_V01_skipn_nil A (S d') nil (Nat.le_0_l _)).
        cbn [skipn].
        rewrite (GaC3_V01_skipn_nil A d' nil (Nat.le_0_l _)).
        assert (En : nth d' nil az = az) by (apply nth_overflow; apply Nat.le_0_l).
        rewrite En. rewrite Hopr. cbn [GaC3_V01_opwalk]. ring.
      * cbn [skipn].
        destruct (skipn d' (y :: l'')) as [| w ws] eqn:Esk.
        -- assert (Hlen : (length (y :: l'') <= d')%nat)
              by (apply (GaC3_V01_skipn_nil_inv A d' (y :: l'') Esk)).
           assert (En : nth d' (y :: l'') az = az)
             by (apply nth_overflow; exact Hlen).
           assert (Ew : skipn d' l'' = nil).
           { apply (GaC3_V01_skipn_nil A d' l'').
             apply (Nat.le_trans (length l'') (S (length l'')) d').
             - apply Nat.le_succ_diag_r.
             - exact Hlen. }
           rewrite En. rewrite Ew. cbn [GaC3_V01_opwalk].
           rewrite Hopr. ring.
        -- assert (Hnn : skipn d' (y :: l'') <> nil) by (rewrite Esk; discriminate).
           assert (Ew : nth d' (y :: l'') az = w).
           { rewrite <- (GaC3_V01_skipn_head_nth A az d' (y :: l'') Hnn).
             rewrite Esk. cbn [nth]. reflexivity. }
           assert (Ews : ws = skipn ((S d')%nat) (y :: l''))
             by (rewrite <- (GaC3_V01_tl_skipn A d' (y :: l''));
                 rewrite Esk; reflexivity).
           rewrite Ew. rewrite Ews. reflexivity.
Qed.

(* ===================================================================== *)
(* Section 5. The two-index transpose.                                    *)
(* ===================================================================== *)

Lemma GaC3_V01_qsum_transpose : forall (f : nat -> nat -> Q) (M L : nat),
  GaC3_V01_qsum (map (fun t => GaC3_V01_qsum (map (f t) (seq 0 M))) (seq 0 L))
  == GaC3_V01_qsum (map (fun j => GaC3_V01_qsum (map (fun t => f t j) (seq 0 L))) (seq 0 M)).
Proof.
  intros f M L. revert f. induction L as [| L' IH]; intros f.
  - cbn [seq map GaC3_V01_qsum]. symmetry. apply GaC3_V01_qsum_map_0.
  - cbn [seq map GaC3_V01_qsum].
    rewrite (GaC3_V01_map_seq_S Q
              (fun t => GaC3_V01_qsum (map (f t) (seq 0 M))) L').
    cbv beta.
    assert (E1 : forall j, GaC3_V01_qsum (map (fun t => f t j) (seq 1 L'))
                           == GaC3_V01_qsum (map (fun t => f (S t) j) (seq 0 L'))).
    { intro j. rewrite (GaC3_V01_map_seq_S Q (fun t => f t j) L'). reflexivity. }
    assert (E3 : GaC3_V01_qsum
                   (map (fun j => f 0%nat j + GaC3_V01_qsum (map (fun t => f t j) (seq 1 L')))
                        (seq 0 M))
              == GaC3_V01_qsum
                   (map (fun j => f 0%nat j + GaC3_V01_qsum (map (fun t => f (S t) j) (seq 0 L')))
                        (seq 0 M))).
    { apply GaC3_V01_qsum_ext. intros j _. rewrite E1. reflexivity. }
    rewrite E3.
    rewrite (GaC3_V01_qsum_map_add (fun j => f 0%nat j)
                                   (fun j => GaC3_V01_qsum (map (fun t => f (S t) j) (seq 0 L')))
                                   M 0%nat).
    assert (E4 : GaC3_V01_qsum (map (fun j => f 0%nat j) (seq 0 M))
              == GaC3_V01_qsum (map (f 0%nat) (seq 0 M))).
    { apply GaC3_V01_qsum_ext. intros j _. reflexivity. }
    rewrite E4.
    assert (E5 : GaC3_V01_qsum (map (fun j => GaC3_V01_qsum (map (fun t => f (S t) j) (seq 0 L'))) (seq 0 M))
              == GaC3_V01_qsum (map (fun t => GaC3_V01_qsum (map (f (S t)) (seq 0 M))) (seq 0 L'))).
    { symmetry. exact (IH (fun t => f (S t))). }
    rewrite E5. reflexivity.
Qed.
