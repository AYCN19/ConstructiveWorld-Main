(* vacuity_face_a.v - gate8 vacuity sentinel probe, face (a).
   Sentinel contract.  COMPILE-MUST-FAIL PROBE.  This file must never
     compile.  It is a best-effort contradiction attempt against the
     corrected premise interface of the compiled top piece
     piu1932_uncond_zz; its rejection by the kernel is the standing
     evidence that the premise interface is non-vacuous.  If this file
     ever compiles, the premise interface has become jointly
     unsatisfiable - RED (run_vacuity_sentinel.sh exits 1 and gate8
     fails).  Do not repair this file into compiling; a needed change
     to the interface must be re-audited through a fresh refutation
     attempt instead.
   Mission.  Attempt to refute the corrected premise interface of the
     compiled top piece piu1932_uncond_zz at face (a): the corrected
     Htri joint with the corrected Hexit, for an arbitrary residual
     carrier dv.  The corrected Htri (second residual slot
     dv (- p) (Z.of_nat q), the second-slot transposition surgery) at
     (a,b,p,q) = (1,-3,3,1) only forces
     dv 1 (-3) + 3 * dv (-3) 1 >= 8, while the corrected Hexit (first
     slot dv (- a) b) at (a,b) = (3,1) bounds dv (-3) 1 <= 7/15 through
     the lp_odd chain (sc_lp_odd_chain, sc_lp_odd_le_s2); the atom
     dv 1 (-3) is unbounded above, so the written-form contradiction
     (8 <= 4 * dv 1 (-3) <= 28/15) is no longer derivable.  The
     written-form closing readout is kept verbatim as the final step so
     the compiler verdict lands exactly there (expected verdict: the
     contradiction is NOT derivable - direct evidence that the
     corrected interface is non-vacuous).
   Dependencies.  S02_CauchyComplete, S10_KVQuantTrig, LW0MLicBridge,
     piu_mu_criterion, piu1932_uncond_zz (world closure, read-only,
     resolved from the compiled vo tree).
   References.  piu_mu_criterion.v:169-172 (corrected Htri verbatim);
     piu1932_uncond_zz.v:65-68 and :84-86 (corrected premise slots);
     the superseded written-shape predecessor of this probe (same
     face).
   Constructivity.  Set-carried statements only (piu_mu_QleT, sigT,
     QleT'); no Axiom, no Admitted, no Abort; the examined files are
     consumed compiled (read-only), never modified.
   Build.  bash scripts/gates/vacuity_sentinel/run_vacuity_sentinel.sh
     (Rocq 9.3.0; the script compiles the tracked Live-tree companion
     sources into a temporary probe world and points -Q at that world
     plus the compiled vo tree). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Qring.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Lqa.
Require Import S02_CauchyComplete.
Require Import S10_KVQuantTrig.
Require Import LW0MLicBridge.
Require Import piu_mu_criterion.
Require Import piu1932_uncond_zz.

(* ==== The verbatim corrected forms (piu1932_uncond_zz.v:65-68 and
       :84-86 at the corrected slots; dv is the abstract residual
       carrier). ==== *)

Definition vac_a_Htri_written (dv : Z -> Z -> Q) : Set :=
  forall (a b p : Z) (q : nat), (1 <= q)%nat ->
     piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
       (inject_Z (Z.of_nat q) * dv a b
         + inject_Z (Z.abs b) * dv (- p)%Z (Z.of_nat q)).

Definition vac_a_Hexit_written (dv : Z -> Z -> Q) : Set :=
  forall a b : Z, (1 <= b)%Z ->
     sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       S02_CauchyComplete.QleT' (dv (- a)%Z b)
         (Qabs (inject_Z b * lw0m_xL k - inject_Z a))).

(* ==== Machine bite: the two transcribed corrected forms type-check
       against the actual premise slots of the compiled top piece
       (corrected :65-68 / :84-86), i.e. the attempt targets the real
       corrected interface, not a strawman. ==== *)

Check (fun (A B : nat -> Z) (dv : Z -> Z -> Q)
         Hp
         (Ht : vac_a_Htri_written dv)
         Hc He Hg
         (He2 : vac_a_Hexit_written dv) =>
       piu1932_uncond_zz A B dv Hp Ht Hc He Hg He2).

(* ==== Computational ground faces. ==== *)

Example vac_a_lp_odd_0 : lp_odd 0 = (2 # 3)%Q.
Proof. reflexivity. Qed.

Example vac_a_lp_four : lp_four = (4 # 1)%Q.
Proof. reflexivity. Qed.

(* ==== Face (a), corrected form: the refutation attempt. ==== *)

Theorem vac_a_face_empty :
  forall dv : Z -> Z -> Q,
  vac_a_Htri_written dv ->
  vac_a_Hexit_written dv ->
  Empty_set.
Proof.
  intros dv Htri Hexit.
  (* Corrected Htri(1,-3,3,1):
     (8#1) <= (1#1)*dv 1 (-3) + (3#1)*dv (-3) 1. *)
  assert (Hq1 : (1 <= 1)%nat) by lia.
  destruct (Htri 1%Z (-3)%Z 3%Z 1%nat Hq1) as [Hlo].
  assert (E8 : inject_Z (Z.abs (1 * Z.of_nat 1 + (-3) * 3)) = (8 # 1)%Q)
    by reflexivity.
  assert (E1 : inject_Z (Z.of_nat 1) = (1 # 1)%Q) by reflexivity.
  assert (E3 : inject_Z (Z.abs (-3)) = (3 # 1)%Q) by reflexivity.
  rewrite E8, E1, E3 in Hlo.
  assert (Eo1 : Z.of_nat 1 = 1%Z) by reflexivity.
  rewrite Eo1 in Hlo.
  (* fold the Z.opp 3 form of the corrected second slot into the
     numeral form; the two residual atoms are now
     w1 := dv 1 (-3) and w2 := dv (-3) 1. *)
  assert (Ev : dv (- (3))%Z 1%Z = dv (-3)%Z 1%Z) by reflexivity.
  rewrite Ev in Hlo.
  (* Corrected Hexit(3,1): dv (-3) 1 <= |lw0m_xL K - 3| at some K. *)
  assert (Hb : (1 <= 1)%Z) by lia.
  destruct (Hexit 3%Z 1%Z Hb) as [K HK].
  specialize (HK K (Nat.le_refl K)).
  apply QleT'_to_Qle in HK.
  assert (Ei1 : inject_Z 1 = (1 # 1)%Q) by reflexivity.
  assert (Ei3 : inject_Z 3 = (3 # 1)%Q) by reflexivity.
  rewrite Ei1, Ei3 in HK.
  (* HK : dv (-3) 1 <= Qabs ((1#1) * lw0m_xL K - (3#1)). *)
  assert (Ex : (inject_Z 1 * lw0m_xL K - inject_Z 3
                == (4 # 1) * lp_odd K - (3 # 1))%Q).
  { unfold lw0m_xL. rewrite vac_a_lp_four. ring. }
  assert (HKx : dv (-3)%Z 1%Z <= Qabs ((4 # 1) * lp_odd K - (3 # 1))%Q).
  { apply (Qle_trans _ (Qabs (inject_Z 1 * lw0m_xL K - inject_Z 3))).
    - exact HK.
    - apply (qeq_imp_qle _ _).
      apply (Qabs_wd _ _). exact Ex. }
  (* lp_odd bounds: lp_odd 0 = 2/3 <= lp_odd K (sc_lp_odd_chain) and
     lp_odd K <= 13/15 (sc_lp_odd_le_s2), so |4*lp_odd K - 3| <= 7/15. *)
  assert (Hlo2 : Qle ((2 # 3)) (lp_odd K)).
  { pose proof (sc_lp_odd_chain 0 K (Nat.le_0_l K)) as Hc.
    rewrite vac_a_lp_odd_0 in Hc. exact Hc. }
  assert (Hhi : Qle (lp_odd K) ((13 # 15)%Q)) by exact (sc_lp_odd_le_s2 K).
  assert (Habs : Qabs ((4 # 1) * lp_odd K - (3 # 1))%Q <= (7 # 15)%Q).
  { apply (proj2 (Qabs_Qle_condition ((4 # 1) * lp_odd K - (3 # 1))%Q
                                     (7 # 15)%Q)).
    split; lra. }
  assert (Hkl : dv (-3)%Z 1%Z <= (7 # 15)%Q).
  { apply (Qle_trans _ (Qabs ((4 # 1) * lp_odd K - (3 # 1))%Q)).
    - exact HKx.
    - exact Habs. }
  (* Written-form closing step, kept verbatim: 8 <= 4 * dv 1 (-3) <=
     28/15.  Under the corrected form the two atoms are distinct and
     dv 1 (-3) carries no upper bound, so this linear readout no
     longer closes; the attempt ends here. *)
  assert (Hfin : False) by lra.
  exact (False_rect Empty_set Hfin).
Qed.

Print Assumptions vac_a_face_empty.
