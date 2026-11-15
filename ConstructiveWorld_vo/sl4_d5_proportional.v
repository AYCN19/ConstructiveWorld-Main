(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 debt row D-SL4-5, proven.  *)
(* Mission      : SL4BODY ticket, dispatch row D-SL4-5 (survey volume SL4    *)
(*                section 9; the minimal startable ledger row, no upstream). *)
(*                Proven here: the subtraction helper planb4_sl4_d5_sub_eq,  *)
(*                the generic rank-one pair lemma planb4_sl4_d5_rank1_pair   *)
(*                (a zero determinant forces the second coefficient pair to  *)
(*                be a rational multiple of the first, under the base-row-   *)
(*                nonzero premise), the complete disjunctive form            *)
(*                planb4_sl4_d5_rank1_complete (the zero base row appears    *)
(*                as an explicit branch, no premise), and the skeleton       *)
(*                Section 5 face planb4_sl4_proportional_on_zero consumed   *)
(*                by name under its exact provability-limiting premise; the *)
(*                unconditional face needs the base-row nonzero account     *)
(*                too (ledger D-SL4-3 territory), disclosed, NOT claimed.   *)
(* Dependencies : planb4_sl4_skeleton (the registered Section 5 face, by     *)
(*                name) plus planb4_g1_ab_def, over the twelve-file sandbox  *)
(*                closure in skeleton-seat dependency order; sources         *)
(*                byte-identical to the package snapshots where overlapping; *)
(*                source routing stays in the seat receipt (comment law).    *)
(* References   : survey SL4 sections 2/5/9; skeleton Section 5; ledger      *)
(*                rows D-SL4-3 (premise account) and D-SL4-7 (consumer).    *)
(* Constructivity: decidable Z case analysis only; no classical principle,  *)
(*                no choice, no global assumption face; postulate-free;     *)
(*                ring only at leaf equalities, never a mission-statement   *)
(*                finisher; all items Defined; new faces are proof bridges. *)
(* Build        : coqc -native-compiler no -q -Q <sandbox root> ""           *)
(*                sl4_d5_proportional.v (Rocq 9.3.0, scripted form).         *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith.
Require Import planb4_sl4_skeleton.
Require Import planb4_g1_ab_def.

(* ================================================================== *)
(* Section 1. The subtraction helper and the generic rank-one pair    *)
(*            lemma (pure Z/Q algebra, no carrier facts).             *)
(* ================================================================== *)

(* The product form of a zero subtraction: the one-step rewrite that  *)
(* turns the determinant equation into the product equality used by  *)
(* the construction below.                                            *)
Lemma planb4_sl4_d5_sub_eq :
  forall x y : Z, (x - y)%Z = 0%Z -> x = y.
Proof.
  intros x y Hsub.
  replace y with (y + (x - y))%Z by (rewrite Hsub; ring).
  ring.
Defined.

(* The rank-one pair lemma: a zero determinant forces (c, d) to be a  *)
(* rational multiple of (a, b) as soon as (a, b) is not identically   *)
(* zero.  Case spine: the sign three-way split of a yields the scale  *)
(* as the plain fraction c over a (denominator carried in Qmake); the *)
(* a = 0 branch uses the nonzero-row premise to exclude b = 0, reads  *)
(* c = 0 off the product equality, and scales by d over b instead.    *)
Theorem planb4_sl4_d5_rank1_pair :
  forall a b c d : Z,
    (a * d - c * b)%Z = 0%Z ->
    (a <> 0%Z \/ b <> 0%Z)%Z ->
    exists l : Q,
      Qeq (inject_Z c)
          (Qmult l (inject_Z a)) /\
      Qeq (inject_Z d)
          (Qmult l (inject_Z b)).
Proof.
  intros a b c d Hdet Hnz.
  apply planb4_sl4_d5_sub_eq in Hdet.
  destruct a as [|p|p].
  - (* a = 0: b = 0 contradicts the nonzero-row premise; otherwise     *)
    (* the product equality reads c = 0 and the scale is d over b.     *)
    destruct b as [|q|q].
    + destruct Hnz as [Hc|Hc].
      * destruct (Hc eq_refl).
      * destruct (Hc eq_refl).
    + simpl in Hdet. symmetry in Hdet.
      destruct (proj1 (Z.mul_eq_0 c (Zpos q)) Hdet) as [Hc0|Hq0].
      * exists (Qmake d q). split.
        -- rewrite Hc0. cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. ring.
        -- cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r. ring.
      * discriminate Hq0.
    + simpl in Hdet. symmetry in Hdet.
      destruct (proj1 (Z.mul_eq_0 c (Zneg q)) Hdet) as [Hc0|Hq0].
      * replace (Zneg q) with (- Zpos q)%Z by reflexivity.
        exists (Qmake (- d) q). split.
        -- rewrite Hc0. cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. ring.
        -- cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r. ring.
      * discriminate Hq0.
  - (* a = Zpos p: the scale is the fraction c over p. *)
    exists (Qmake c p). split.
    + cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r. ring.
    + cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r.
      rewrite (Z.mul_comm d (Zpos p)). rewrite Hdet. ring.
  - (* a = Zneg p: the scale is -c over p; the sign fold is explicit. *)
    replace (Zneg p) with (- Zpos p)%Z in Hdet by reflexivity.
    replace (Zneg p) with (- Zpos p)%Z by reflexivity.
    rewrite Z.mul_opp_l in Hdet.
    exists (Qmake (- c) p). split.
    + cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r. ring.
    + cbv beta iota delta [inject_Z Qmult Qeq Qnum Qden]. rewrite Pos.mul_1_r.
      rewrite (Z.mul_comm d (Zpos p)). rewrite Z.mul_opp_l.
      rewrite <- Hdet. ring.
Defined.

(* ================================================================== *)
(* Section 2. The complete disjunctive rank-one fact: the zero base   *)
(*            row branch is explicit, so no premise remains.          *)
(* ================================================================== *)

(* The exact algebraic content of a zero 2x2 determinant over the     *)
(* fraction field: either the base row (a, b) is identically zero, or *)
(* the second row is a rational multiple of it.                       *)
Theorem planb4_sl4_d5_rank1_complete :
  forall a b c d : Z,
    (a * d - c * b)%Z = 0%Z ->
    ((a = 0%Z /\ b = 0%Z) \/
     exists l : Q,
       Qeq (inject_Z c)
           (Qmult l (inject_Z a)) /\
       Qeq (inject_Z d)
           (Qmult l (inject_Z b))).
Proof.
  intros a b c d Hdet.
  destruct a as [|p|p].
  - (* a = 0: only the b-side nonzero branch survives the helper. *)
    destruct b as [|q|q].
    + left. split; reflexivity.
    + right. apply (planb4_sl4_d5_rank1_pair Z0 (Zpos q) c d Hdet).
      right. intros Hc. discriminate Hc.
    + right. apply (planb4_sl4_d5_rank1_pair Z0 (Zneg q) c d Hdet).
      right. intros Hc. discriminate Hc.
  - (* a = Zpos p: the a-side nonzero branch applies directly. *)
    right. apply (planb4_sl4_d5_rank1_pair (Zpos p) b c d Hdet).
    left. intros Hc. discriminate Hc.
  - (* a = Zneg p: the a-side nonzero branch applies directly. *)
    right. apply (planb4_sl4_d5_rank1_pair (Zneg p) b c d Hdet).
    left. intros Hc. discriminate Hc.
Defined.

(* ================================================================== *)
(* Section 3. The skeleton Section 5 face consumed by name: the       *)
(*            interface disclosure of the base-row-nonzero premise.   *)
(* ================================================================== *)

(* The skeleton face conclusion holds at every n whose base row       *)
(* (planb4_g1_A n, planb4_g1_B n) is not identically zero.  The       *)
(* determinant equation is the Section 1 definition face verbatim.    *)
Theorem planb4_sl4_d5_proportional_on_zero_base_row_nz :
  forall n : nat,
    (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z ->
    planb4_sl4_delta n = 0%Z ->
    exists l : Q,
      Qeq (inject_Z (planb4_g1_A (S n)))
          (Qmult l (inject_Z (planb4_g1_A n))) /\
      Qeq (inject_Z (planb4_g1_B (S n)))
          (Qmult l (inject_Z (planb4_g1_B n))).
Proof.
  intros n Hnz H0. unfold planb4_sl4_delta in H0.
  exact (planb4_sl4_d5_rank1_pair (planb4_g1_A n) (planb4_g1_B n)
         (planb4_g1_A (S n)) (planb4_g1_B (S n)) H0 Hnz).
Defined.

(* The skeleton Section 5 statement itself, discharged modulo one     *)
(* explicit interface premise: the base-row nonzero account.  When a  *)
(* supply side lands for that account (ledger row D-SL4-3 territory), *)
(* this theorem composes it with no further algebra.                  *)
Theorem planb4_sl4_d5_skeleton_face_via_base_row_nz :
  (forall n : nat, (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z) ->
  planb4_sl4_proportional_on_zero.
Proof.
  intro Hrow.
  exact (fun n H0 =>
           planb4_sl4_d5_proportional_on_zero_base_row_nz n (Hrow n) H0).
Defined.

(* ================================================================== *)
(* Section 4. Assumption audit (kernel verdicts, printed at build).   *)
(* ================================================================== *)

Print Assumptions planb4_sl4_d5_sub_eq.
Print Assumptions planb4_sl4_d5_rank1_pair.
Print Assumptions planb4_sl4_d5_rank1_complete.
Print Assumptions planb4_sl4_d5_proportional_on_zero_base_row_nz.
Print Assumptions planb4_sl4_d5_skeleton_face_via_base_row_nz.

(* ================= end of the D-SL4-5 proportional half =========== *)
