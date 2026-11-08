(* ConstructiveWorld-Main - the polymorphic exact-Q finite-sum toolkit for
   the van der Corput A-process. *)
(** * GaC3_V01_VdCSecond_a: the van der Corput toolkit leaf A.
    Mission.  Node C3-V01 sunken toolkit leaf A: the polymorphic
      exact-Q finite-sum machinery consumed by the later van der
      Corput A-process files of this node: the nat-to-Q embedding
      [GaC3_V01_qn], the seq/map list-equation bridges, the
      skipn/firstn nth calculus, the membership-to-nth bridge, and
      the Q list-summation kit (extension, append, additivity, zero
      strips, reversal, monotone-ness, constant multiple).  Purely
      polymorphic: no node carrier, L0-only dependency face.
    Dependencies.  Stdlib only ([QArith.QArith] incl. [Qabs],
      [Arith.Arith], [List]); L0-only require face.
    References.  The van der Corput A-process inequality
      (Graham-Kolesnik, van der Corput's method of exponential sums,
      A-process chapter; Iwaniec-Kowalski Ch. 8), the summation kit
      its exact-Q proof runs on; card cards_C3 C3-V01; drafts_C3 V01
      statement skeleton.
    Constructivity.  Set-carried statements; zero classical choice;
      all numerics stay in Q (decidable, exact); [coqchk] reports
      zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_V01_VdCSecond_a.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3] (-AllowG3 -GearForce 0 -TempLimit 98
      -LoadLimit 60 -CoreN 2). *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import List.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. The nat-to-Q embedding.                                     *)
(* ===================================================================== *)

Fixpoint GaC3_V01_qn (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | S n' => 1 + GaC3_V01_qn n'
  end.

Lemma GaC3_V01_qn_pos : forall n : nat, (0 <= GaC3_V01_qn n)%Q.
Proof.
  intro n. induction n as [| n' IH].
  - cbn [GaC3_V01_qn]. apply Qle_refl.
  - apply (Qle_trans 0 (0 + GaC3_V01_qn n') (1 + GaC3_V01_qn n')).
    + rewrite Qplus_0_l. exact IH.
    + apply Qplus_le_compat.
      * assert (H01 : (0 < 1)%Q) by reflexivity.
        apply Qlt_le_weak. exact H01.
      * apply Qle_refl.
Qed.

(* ===================================================================== *)
(* Section 2. Nil-list normal forms.                                      *)
(* ===================================================================== *)

Lemma GaC3_V01_nth_nil : forall (A : Type) (d0 : A) (m : nat),
  nth m (nil:list A) d0 = d0.
Proof. intros A d0 m. destruct m; reflexivity. Qed.

Lemma GaC3_V01_firstn_nil : forall (A : Type) (n : nat),
  firstn n (nil:list A) = nil.
Proof. intros A n. destruct n; reflexivity. Qed.

Lemma GaC3_V01_skipn_nil : forall (A : Type) (n : nat) (l : list A),
  (length l <= n)%nat -> skipn n l = nil.
Proof.
  intros A n. induction n as [| n' IH]; intro l.
  - destruct l as [| x l'].
    + reflexivity.
    + intros H. cbn [length] in H. inversion H.
  - destruct l as [| x l'].
    + reflexivity.
    + intros H. cbn [skipn length] in *. apply IH. apply le_S_n. exact H.
Qed.

Lemma GaC3_V01_skipn_nil_inv : forall (A : Type) (n : nat) (l : list A),
  skipn n l = nil -> (length l <= n)%nat.
Proof.
  intros A n. induction n as [| n' IH]; intros l E.
  - destruct l as [| x l'].
    + apply Nat.le_refl.
    + discriminate.
  - destruct l as [| x l'].
    + cbn [length]. apply Nat.le_0_l.
    + cbn [skipn] in E. apply le_n_S. apply (IH l' E).
Qed.

(* ===================================================================== *)
(* Section 3. Seq and map list-equation bridges.                          *)
(* ===================================================================== *)

Lemma GaC3_V01_seq_S_map : forall (A : Type) (a n : nat), seq (S a) n = map S (seq a n).
Proof.
  intros A a n. revert a. induction n as [| n' IH]; intro a.
  - reflexivity.
  - cbn [seq map]. f_equal. apply IH.
Qed.

Lemma GaC3_V01_seq_tail : forall (a n : nat), seq a (S n) = seq a n ++ ((a + n)%nat :: nil).
Proof.
  intros a n. revert a. induction n as [| n' IH]; intro a.
  - cbn [seq app]. f_equal. rewrite Nat.add_0_r. reflexivity.
  - replace (seq a (S (S n'))) with (a :: seq (S a) (S n')) by reflexivity.
    rewrite (IH (S a)). cbn [seq app]. f_equal. f_equal.
    rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma GaC3_V01_map_seq_S : forall (A : Type) (h : nat -> A) (n : nat),
  map h (seq 1 n) = map (fun i => h (S i)) (seq 0 n).
Proof.
  intros A h n.
  rewrite (GaC3_V01_seq_S_map A 0 n).
  rewrite map_map. reflexivity.
Qed.

Lemma GaC3_V01_map_seq_shift : forall (A : Type) (h : nat -> A) (a n : nat),
  map h (seq a n) = map (fun i => h ((a + i)%nat)) (seq 0 n).
Proof.
  intros A h a n. revert h a. induction n as [| n' IH]; intros h a.
  - reflexivity.
  - cbn [seq map]. rewrite Nat.add_0_r. f_equal.
    rewrite (IH h (S a)).
    rewrite (GaC3_V01_map_seq_S A (fun i => h ((a + i)%nat)) n').
    apply map_ext. intro i. f_equal. now rewrite Nat.add_succ_r.
Qed.

(* ===================================================================== *)
(* Section 4. The skipn/firstn nth calculus.                              *)
(* ===================================================================== *)

Lemma GaC3_V01_nth_skipn : forall (A : Type) (d0 : A) (n m : nat) (l : list A),
  nth m (skipn n l) d0 = nth ((n + m)%nat) l d0.
Proof.
  intros A d0 n. induction n as [| n' IH]; intros m l.
  - cbn [skipn Nat.add]. reflexivity.
  - destruct l as [| x l'].
    + rewrite (GaC3_V01_skipn_nil A (S n') nil (Nat.le_0_l _)).
      rewrite !GaC3_V01_nth_nil. reflexivity.
    + cbn [skipn]. cbn [Nat.add nth]. apply IH.
Qed.

Lemma GaC3_V01_nth_firstn : forall (A : Type) (d0 : A) (n p : nat) (l : list A),
  (p < n)%nat -> nth p (firstn n l) d0 = nth p l d0.
Proof.
  intros A d0 n. induction n as [| n' IH]; intros p l Hp.
  - inversion Hp.
  - destruct l as [| x l'].
    + rewrite (GaC3_V01_firstn_nil A (S n')). rewrite !GaC3_V01_nth_nil. reflexivity.
    + destruct p as [| p'].
      * cbn [firstn nth]. reflexivity.
      * cbn [firstn nth]. apply IH. apply le_S_n. exact Hp.
Qed.

Lemma GaC3_V01_nth_firstn_skipn : forall (A : Type) (d0 : A) (l : list A) (a n j : nat),
  (j < n)%nat -> nth j (firstn n (skipn a l)) d0 = nth ((a + j)%nat) l d0.
Proof.
  intros A d0 l a. revert l. induction a as [| a' IH]; intros l n j Hj.
  - cbn [skipn]. rewrite (GaC3_V01_nth_firstn A d0 n j l Hj). cbn [Nat.add]. reflexivity.
  - destruct l as [| x l'].
    + cbn [skipn].
      rewrite (GaC3_V01_firstn_nil A n).
      rewrite !GaC3_V01_nth_nil. reflexivity.
    + cbn [skipn]. cbn [Nat.add nth]. apply IH. exact Hj.
Qed.

Lemma GaC3_V01_firstn_S_tail : forall (A : Type) (n : nat) (l : list A),
  firstn (S n) l = firstn n l ++ match skipn n l with nil => nil | x :: _ => x :: nil end.
Proof.
  intros A n. induction n as [| n' IH]; intro l.
  - destruct l as [| x l'].
    + reflexivity.
    + cbn [firstn skipn app]. reflexivity.
  - destruct l as [| x l'].
    + reflexivity.
    + cbn [firstn skipn app]. f_equal. apply IH.
Qed.

Lemma GaC3_V01_skipn_head_nth : forall (A : Type) (d0 : A) (d : nat) (l : list A),
  skipn d l <> nil -> nth 0 (skipn d l) d0 = nth d l d0.
Proof.
  intros A d0 d. induction d as [| d' IH]; intro l.
  - intros H. cbn [skipn nth]. reflexivity.
  - destruct l as [| x l'].
    + intros H. exfalso. apply H.
      apply (GaC3_V01_skipn_nil A (S d') nil).
      apply Nat.le_0_l.
    + intros H. cbn [skipn nth] in *. apply IH. exact H.
Qed.

Lemma GaC3_V01_tl_skipn : forall (A : Type) (n : nat) (l : list A),
  tl (skipn n l) = skipn (S n) l.
Proof.
  intros A n. induction n as [| n' IH]; intro l.
  - reflexivity.
  - destruct l as [| x l'].
    + rewrite (GaC3_V01_skipn_nil A (S n') nil (Nat.le_0_l _)).
      rewrite (GaC3_V01_skipn_nil A (S (S n')) nil (Nat.le_0_l _)).
      reflexivity.
    + cbn [skipn tl]. apply IH.
Qed.

(* ===================================================================== *)
(* Section 5. Membership to nth bridge.                                   *)
(* ===================================================================== *)

Lemma GaC3_V01_In_firstn_nth : forall (A : Type) (d0 : A) (l : list A) (H : nat) (y : A),
  In y (firstn H l) -> exists j, (j < H)%nat /\ nth j l d0 = y.
Proof.
  intros A d0 l H. revert l. induction H as [| H' IH]; intros l y Hin.
  - cbn [firstn] in Hin. contradiction.
  - destruct l as [| x l'].
    + rewrite (GaC3_V01_firstn_nil A (S H')) in Hin. destruct Hin.
    + cbn [firstn] in Hin. destruct Hin as [Ey | Hin].
      * exists 0%nat. split.
        -- apply le_n_S. apply Nat.le_0_l.
        -- cbn [nth]. exact Ey.
      * destruct (IH l' y Hin) as [j [Hj Ej]].
        exists (S j). split.
        -- apply le_n_S. exact Hj.
        -- cbn [nth]. exact Ej.
Qed.

Lemma GaC3_V01_In_firstn_skipn_nth : forall (A : Type) (d0 : A) (l : list A) (p H : nat) (y : A),
  In y (firstn H (skipn p l)) -> exists j, (j < H)%nat /\ nth ((p + j)%nat) l d0 = y.
Proof.
  intros A d0 l p H y Hin.
  destruct (GaC3_V01_In_firstn_nth A d0 (skipn p l) H y Hin) as [j [Hj Ej]].
  exists j. split; [exact Hj |].
  rewrite <- (GaC3_V01_nth_skipn A d0 p j l). exact Ej.
Qed.

(* ===================================================================== *)
(* Section 6. The Q list sum and its kit.                                 *)
(* ===================================================================== *)

Fixpoint GaC3_V01_qsum (l : list Q) : Q :=
  match l with
  | nil => 0
  | x :: l' => x + GaC3_V01_qsum l'
  end.

Lemma GaC3_V01_qplus_eq_compat_l : forall x y z : Q, x == y -> z + x == z + y.
Proof. intros x y z H. rewrite H. reflexivity. Qed.

Lemma GaC3_V01_qplus_exchange : forall a b c d : Q, (a + b) + (c + d) == (a + c) + (b + d).
Proof. intros a b c d. ring. Qed.

Lemma GaC3_V01_qsum_eq : forall l1 l2 : list Q,
  l1 = l2 -> GaC3_V01_qsum l1 == GaC3_V01_qsum l2.
Proof. intros l1 l2 E. rewrite E. reflexivity. Qed.

Lemma GaC3_V01_qsum_app : forall l1 l2 : list Q,
  GaC3_V01_qsum (l1 ++ l2) == GaC3_V01_qsum l1 + GaC3_V01_qsum l2.
Proof.
  induction l1 as [| x l1 IH]; intro l2.
  - cbn [app GaC3_V01_qsum]. ring.
  - cbn [app GaC3_V01_qsum]. rewrite IH. ring.
Qed.

Lemma GaC3_V01_qsum_ext : forall (g h : nat -> Q) (n a : nat),
  (forall i, (a <= i < a + n)%nat -> g i == h i) ->
  GaC3_V01_qsum (map g (seq a n)) == GaC3_V01_qsum (map h (seq a n)).
Proof.
  intros g h n. revert g h. induction n as [| n' IH]; intros g h a Hpt.
  - reflexivity.
  - cbn [seq map GaC3_V01_qsum].
    assert (Ha : g a == h a).
    { apply Hpt. split.
      - apply Nat.le_refl.
      - rewrite Nat.add_succ_r. apply le_n_S. apply Nat.le_add_r. }
    rewrite Ha. apply GaC3_V01_qplus_eq_compat_l. apply IH.
    intros i Hi. apply Hpt. split.
    + apply (Nat.le_trans a (S a) i).
      * apply Nat.le_succ_diag_r.
      * exact (proj1 Hi).
    + rewrite Nat.add_succ_r. exact (proj2 Hi).
Qed.

Lemma GaC3_V01_qsum_map_add : forall (g h : nat -> Q) (n a : nat),
  GaC3_V01_qsum (map (fun i => g i + h i)%Q (seq a n))
  == GaC3_V01_qsum (map g (seq a n)) + GaC3_V01_qsum (map h (seq a n)).
Proof.
  intros g h n. revert g h. induction n as [| n' IH]; intros g h a.
  - cbn [seq map GaC3_V01_qsum]. ring.
  - cbn [seq map GaC3_V01_qsum]. rewrite (IH g h (S a)).
    apply GaC3_V01_qplus_exchange.
Qed.

Lemma GaC3_V01_qsum_map_0 : forall (a n : nat),
  GaC3_V01_qsum (map (fun _ : nat => 0)%Q (seq a n)) == 0.
Proof.
  intros a n. revert a. induction n as [| n' IH]; intro a.
  - reflexivity.
  - cbn [seq map GaC3_V01_qsum]. rewrite IH. ring.
Qed.

Lemma GaC3_V01_qsum_const_mul : forall (A : Type) (c : Q) (l : list A),
  GaC3_V01_qsum (map (fun _ => c) l) == GaC3_V01_qn (length l) * c.
Proof.
  intros A c l. induction l as [| x l' IH].
  - cbn [map length GaC3_V01_qn GaC3_V01_qsum]. ring.
  - cbn [map length GaC3_V01_qn GaC3_V01_qsum]. rewrite IH. ring.
Qed.

Lemma GaC3_V01_qsum_le : forall (g h : nat -> Q) (n a : nat),
  (forall i, (a <= i < a + n)%nat -> g i <= h i) ->
  GaC3_V01_qsum (map g (seq a n)) <= GaC3_V01_qsum (map h (seq a n)).
Proof.
  intros g h n. revert g h. induction n as [| n' IH]; intros g h a Hpt.
  - apply Qle_refl.
  - cbn [seq map GaC3_V01_qsum]. apply Qplus_le_compat.
    + apply Hpt. split.
      * apply Nat.le_refl.
      * rewrite Nat.add_succ_r. apply le_n_S. apply Nat.le_add_r.
    + apply IH. intros i Hi. apply Hpt. split.
      * apply (Nat.le_trans a (S a) i).
        -- apply Nat.le_succ_diag_r.
        -- exact (proj1 Hi).
      * rewrite Nat.add_succ_r. exact (proj2 Hi).
Qed.

Lemma GaC3_V01_qsum_head_zero : forall (g : nat -> Q) (c M a : nat),
  (forall i, (a <= i < a + c)%nat -> g i == 0) ->
  GaC3_V01_qsum (map g (seq a ((c + M)%nat))) == GaC3_V01_qsum (map g (seq ((a + c)%nat) M)).
Proof.
  intros g c M a Hz.
  rewrite (seq_app c M a). rewrite map_app. rewrite GaC3_V01_qsum_app.
  assert (Ehead : GaC3_V01_qsum (map g (seq a c)) == 0).
  { rewrite (GaC3_V01_qsum_ext g (fun _ => 0) c a).
    - apply GaC3_V01_qsum_map_0.
    - intros i Hi. exact (Hz i Hi). }
  rewrite Ehead. apply Qplus_0_l.
Qed.

Lemma GaC3_V01_qsum_tail_zero : forall (g : nat -> Q) (M c a : nat),
  (forall i, (a + M <= i < a + M + c)%nat -> g i == 0) ->
  GaC3_V01_qsum (map g (seq a ((M + c)%nat))) == GaC3_V01_qsum (map g (seq a M)).
Proof.
  intros g M c a Hz.
  rewrite (seq_app M c a). rewrite map_app. rewrite GaC3_V01_qsum_app.
  assert (Etail : GaC3_V01_qsum (map g (seq ((a + M)%nat) c)) == 0).
  { rewrite (GaC3_V01_qsum_ext g (fun _ => 0) c ((a + M)%nat)).
    - apply GaC3_V01_qsum_map_0.
    - intros i Hi. exact (Hz i Hi). }
  rewrite Etail. apply Qplus_0_r.
Qed.

Lemma GaC3_V01_qsum_seq_rev : forall (g : nat -> Q) (n : nat),
  GaC3_V01_qsum (map (fun j => g ((n - j)%nat)) (seq 0 n)) == GaC3_V01_qsum (map g (seq 1 n)).
Proof.
  intro g. induction n as [| n' IH].
  - reflexivity.
  - rewrite (GaC3_V01_seq_tail 1 n').
    cbn [seq map GaC3_V01_qsum].
    rewrite (GaC3_V01_map_seq_S Q (fun j => g ((S n' - j)%nat)) n').
    cbv beta.
    assert (E : map (fun i => g ((S n' - S i)%nat)) (seq 0 n')
              = map (fun i => g ((n' - i)%nat)) (seq 0 n')).
    { apply map_ext. intro i. cbn [Nat.sub]. reflexivity. }
    rewrite E. rewrite IH.
    rewrite map_app. rewrite GaC3_V01_qsum_app.
    cbn [map GaC3_V01_qsum Nat.sub Nat.add]. ring.
Qed.

Lemma GaC3_V01_nth_seq_sum : forall (A : Type) (f : A -> Q) (l : list A) (d0 : A),
  GaC3_V01_qsum (map (fun i => f (nth i l d0)) (seq 0 (length l))) == GaC3_V01_qsum (map f l).
Proof.
  intros A f l. induction l as [| x l' IH]; intro d0.
  - reflexivity.
  - cbn [length seq map GaC3_V01_qsum].
    rewrite (GaC3_V01_map_seq_S Q (fun i => f (nth i (x :: l') d0)) (length l')).
    cbv beta. cbn [nth]. rewrite (IH d0). reflexivity.
Qed.
