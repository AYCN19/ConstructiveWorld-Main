(* ========================================================================= *)
(* Mission.     SLWAVE3-hexitB1 - L6 exit-debt carrier migration piece       *)
(*   (hexit slot route B-1, carrier rebinding; accessible survey tier).      *)
(*   Statement faces (born, verbatim from the slot draft s.1.1-1.2):         *)
(*   l6_env_L - lower-envelope carrier L(a,b) := |a + b*xLm| - |b|*em;       *)
(*   l6_hexit_at_env_lower - the consumption-verbatim exit face at it;       *)
(*   l6_tail_bound_face - the explicit tail-bound premise slot;              *)
(*   l6_exit_from_tail_bound - PROVEN bridge discharging the exit face from  *)
(*     the tail-bound face (witness K := m0 uniform in (a,b));               *)
(*   l6_l2dv_orientation - PROVEN twin-orientation agreement at the l2_dv    *)
(*     carrier (the bridge lemma the fourslots header assigns to supply).    *)
(* Dependencies. S02_CauchyComplete (QleT'/QeqT, their Qle bridges);         *)
(*   LW0MLicBridge (lw0m_xL, lw0m_e); planb4_l2_dv_cast, planb3_g1_g2_design *)
(*   (the l2_dv carrier the orientation bridge binds; the draft's            *)
(*   zero-consumption-require rule governs the draft faces only); stdlib     *)
(*   QArith, ZArith, Arith, Lia, Morphisms/Setoid (the Qabs morphism).       *)
(* References.   Born faces follow the exit-debt slot draft; the carrier     *)
(*   mirrors the tree upper envelope sl12_env_U                              *)
(*   (sl2_rint_recast.v:338-341; +/- is the only textual difference);        *)
(*   consumption anchors planb4_l4_fourslots.v:122-129 (orientation note at  *)
(*   its header lines 36-44), planb4_l3_limbs_discharge.v:45-49 (the twin    *)
(*   symmetric form l2_dv b (-a)), planb3_g1_g2_design.v:132-138.            *)
(* Constructivity. Every statement is Set-carried (QleT', QeqT, sigT); both  *)
(*   bridges are transparent (Defined) with real derivation chains;          *)
(*   postulate-free (tail audit Closed on all; zero admission primitives,    *)
(*   zero checker weakening; section Context discharged at End).             *)
(* Build.        coqc -q -native-compiler no -Q <world> ""                   *)
(*               l6_carrier_migration.v (Rocq 9.3.0; single guard-wrapped    *)
(*               lane; <world> carries the dependency closure).              *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Morphisms Setoid.
Require Import S02_CauchyComplete.
Require Import LW0MLicBridge.
Require Import planb4_l2_dv_cast.
Require Import planb3_g1_g2_design.

(* ================================================================== *)
(* Orientation ledger (the draft's orientation note, after the        *)
(* fourslots header lines 36-44 idiom).  The consumption-verbatim     *)
(* orientation is l6_env_L (- a) b throughout this piece.  The l3     *)
(* limbs twin stores the carrier-symmetric form l2_dv b (- a)         *)
(* (planb4_l3_limbs_discharge.v:45-49); at the l2_dv carrier the two  *)
(* faces agree pointwise (the carrier is the absolute value of a      *)
(* sum) and the bridge lemma belongs to the supply side - discharged  *)
(* as l6_l2dv_orientation below.  At the l6_env_L carrier the         *)
(* pointwise agreement FAILS (the error term Qabs (inject_Z b) * em   *)
(* breaks the a/b symmetry), so no symmetric twin is cast here and no *)
(* carrier-L bridge lemma is claimed - the orientation is registered, *)
(* not discharged.  Out of scope here (kept for their own lines): the *)
(* abstract-anchor route faces (the breakthrough tier) and the        *)
(* triangle-consistency registration face at the same carrier (the    *)
(* shared missing piece).                                             *)
(* ================================================================== *)

(* ================================================================== *)
(* Section 1. The lower-envelope carrier and the exit face at it      *)
(*            (born faces, honestly unproven - the honest interface). *)
(*            The carrier is the pointwise mirror of the tree upper   *)
(*            envelope: the +/- sign is the only textual difference,  *)
(*            and the mirror sits pointwise below the true-pi mirror  *)
(*            carrier, which is the direction the exit face needs.    *)
(* ================================================================== *)

Section L6_EXIT.

(* xLm := the xL-bridge midpoint slot (consumption form lw0m_xL m0);   *)
(* em := the envelope error slot (consumption form lw0m_e m0).         *)
Context (xLm em : Q).

(* the lower-envelope carrier. *)
Definition l6_env_L (a b : Z) : Q :=
  Qabs (inject_Z a + inject_Z b * xLm)%Q - Qabs (inject_Z b) * em.

(* the exit face at the lower-envelope carrier: the consumption-       *)
(* verbatim shape of the tree hexit slot face with the carrier         *)
(* swapped to l6_env_L.  Discharge topology: the reverse-triangle      *)
(* inequality plus the tree tail bound give the witness K := m0        *)
(* uniformly in (a,b); the discharge is constructed in Section 2.      *)
Definition l6_hexit_at_env_lower : Set :=
  forall (a b : Z), (1 <= b)%Z ->
    sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      S02_CauchyComplete.QleT' (l6_env_L (- a)%Z b)
        (Qabs (inject_Z b * lw0m_xL k - inject_Z a))).

End L6_EXIT.

(* ================================================================== *)
(* Section 2. The tail-bound transfer topology and its discharge       *)
(*            bridge.  The tree already carries the tail instance      *)
(*            lw0m_tail_bounded_pi (PROVEN); the supply side consumes  *)
(*            it and does not re-prove it.  The premise slot below is  *)
(*            kept explicit and unnamed-instance-free (the tree        *)
(*            instance is consumed at construction time, not bound     *)
(*            here).  The discharge bridge is the supply side's        *)
(*            ten-line Q-arithmetic chain: reverse triangle plus the   *)
(*            tail bound, K := m0 uniformly in (a,b).                  *)
(* ================================================================== *)

Definition l6_tail_bound_face (m0 : nat) : Set :=
  forall k : nat, (m0 <= k)%nat ->
    S02_CauchyComplete.QleT' (Qabs (lw0m_xL k - lw0m_xL m0)) (lw0m_e m0).

(* the discharge bridge (the draft's assembly-topology face, now       *)
(* constructed): the exit face at the carrier slots xLm := lw0m_xL m0, *)
(* em := lw0m_e m0 follows from the tail-bound face.  The explicit     *)
(* full-parameterization form is chosen (the section-eliminated exit   *)
(* face applied to the two slots); the two forms are semantically      *)
(* isomorphic per the draft's notation note.                           *)
Theorem l6_exit_from_tail_bound :
  forall (m0 : nat),
  l6_tail_bound_face m0 ->
  l6_hexit_at_env_lower (lw0m_xL m0) (lw0m_e m0).
Proof.
  intros m0 Htb a b Hb.
  exists m0. intros k Hk.
  unfold l6_env_L.
  apply Qle_to_QleT'.
  pose proof (Htb k Hk) as Htk.
  apply QleT'_to_Qle in Htk.
  (* the increment carries the tail bound through the multiplicative   *)
  (* monotonicity step.                                                *)
  assert (HabsD : Qabs (inject_Z b * (lw0m_xL k - lw0m_xL m0))
                  == Qabs (inject_Z b)
                     * Qabs (lw0m_xL k - lw0m_xL m0))
    by apply Qabs_Qmult.
  assert (Hu : Qle (Qabs (inject_Z b * (lw0m_xL k - lw0m_xL m0)))
                   (Qabs (inject_Z b) * lw0m_e m0)).
  { rewrite HabsD.
    rewrite (Qmult_comm (Qabs (inject_Z b))
                        (Qabs (lw0m_xL k - lw0m_xL m0))).
    rewrite (Qmult_comm (Qabs (inject_Z b)) (lw0m_e m0)).
    apply (Qmult_le_compat_r _ _ _).
    - exact Htk.
    - apply Qabs_nonneg. }
  (* the split identity: the exit-slot right side is the carrier slot  *)
  (* plus the increment.  The ring tactic over Qeq is shadowed in this *)
  (* import environment, so the auxiliary algebra fact is rearranged   *)
  (* on field lemmas instead (inline scaffolding, no statement face).  *)
  assert (Hsplit : forall (x y z t : Q),
           (x * z - t == (Qopp t + x * y) + x * (z - y))%Q).
  { intros x y z t. unfold Qminus.
    rewrite (Qmult_plus_distr_r x z (Qopp y)).
    rewrite <- (Qplus_assoc (Qopp t) (x * y)
                            (x * z + x * (Qopp y))).
    rewrite (Qplus_comm (x * z) (x * (Qopp y))).
    rewrite (Qplus_assoc (x * y) (x * (Qopp y)) (x * z)).
    rewrite <- (Qmult_plus_distr_r x y (Qopp y)).
    rewrite (Qplus_opp_r y).
    rewrite (Qmult_0_r x).
    rewrite (Qplus_0_l (x * z)).
    rewrite (Qplus_comm (Qopp t) (x * z)).
    reflexivity. }
  assert (Hid : (inject_Z b * lw0m_xL k - inject_Z a
                 == (inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                    + inject_Z b * (lw0m_xL k - lw0m_xL m0))%Q).
  { pose proof (Hsplit (inject_Z b) (lw0m_xL m0) (lw0m_xL k)
                       (inject_Z a)) as Hq.
    assert (HAmA : inject_Z (- a)%Z == Qopp (inject_Z a)%Q)
      by (unfold inject_Z, Qopp; cbn; reflexivity).
    rewrite <- HAmA in Hq.
    exact Hq. }
  assert (Hid2 : Qabs (inject_Z b * lw0m_xL k - inject_Z a)
                 == Qabs ((inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                          + inject_Z b * (lw0m_xL k - lw0m_xL m0))).
  { rewrite Hid. reflexivity. }
  apply (Qle_trans _ (Qabs (inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                      - Qabs (inject_Z b * (lw0m_xL k - lw0m_xL m0)))).
  - (* subtracting the smaller increment weakens the claim. *)
    apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qopp_le_compat. exact Hu.
  - (* the reverse triangle: carrier slot minus increment is at most   *)
    (* the exit-slot right side.                                       *)
    apply (Qle_trans _ (Qabs ((inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                              + inject_Z b * (lw0m_xL k - lw0m_xL m0)))).
    + pose proof (Qabs_triangle_reverse
                    (inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                    (- (inject_Z b * (lw0m_xL k - lw0m_xL m0)))) as Hr.
      rewrite (Qabs_opp (inject_Z b * (lw0m_xL k - lw0m_xL m0))) in Hr.
      assert (Hplus : ((inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                       - (- (inject_Z b * (lw0m_xL k - lw0m_xL m0)))
                       == (inject_Z (- a)%Z + inject_Z b * lw0m_xL m0)
                          + inject_Z b * (lw0m_xL k - lw0m_xL m0))%Q).
      { unfold Qminus. rewrite Qopp_involutive. reflexivity. }
      rewrite Hplus in Hr.
      exact Hr.
    + rewrite <- Hid2. apply Qle_refl.
Defined.

(* ================================================================== *)
(* Section 3. The orientation bridge at the l2_dv carrier (the        *)
(*            supply-side obligation registered in the fourslots      *)
(*            header note: the carrier is the absolute value of a     *)
(*            sum, so the consumption-verbatim orientation l2_dv      *)
(*            (-a) b and the twin symmetric form l2_dv b (-a) agree   *)
(*            pointwise; the agreement is discharged here).           *)
(* ================================================================== *)

Lemma l6_l2dv_orientation : forall (a b : Z),
  S02_CauchyComplete.QeqT (l2_dv (- a)%Z b) (l2_dv b (- a)%Z).
Proof.
  intros a b. unfold l2_dv, planb3_dv.
  apply qeq_imp_qeqT. apply (Qabs_wd _ _). apply Qplus_comm.
Defined.

(* ================================================================== *)
(* Section 4. Assumption audit (per-statement, tail).                 *)
(* ================================================================== *)

Print Assumptions l6_env_L.
Print Assumptions l6_hexit_at_env_lower.
Print Assumptions l6_tail_bound_face.
Print Assumptions l6_exit_from_tail_bound.
Print Assumptions l6_l2dv_orientation.
