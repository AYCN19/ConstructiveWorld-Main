(* vacuity_face_c.v - gate8 vacuity sentinel probe, face (c), the
   design-face refutation lane.
   Sentinel contract.  COMPILE-MUST-FAIL PROBE.  This file must never
     compile.  It attempts to refute the two corrected design faces at
     their written-form counterinstance shapes; the rejection of both
     attempts by the kernel is the standing evidence that the examined
     obligations resist their recorded counterinstances.  If this file
     ever compiles, the examined premise interface has become jointly
     unsatisfiable - RED (run_vacuity_sentinel.sh exits 1 and gate8
     fails).  Do not repair this file into compiling; a needed change
     must be re-audited through a fresh refutation attempt instead.
   Mission.  Attempt to refute the two corrected design faces at their
     written-form counterinstance shapes: the anchor-parametric
     triangle obligation at xpi = 22/7 (sub-face (c).1) and the
     exit-mirror obligation at the constant sequence xL = 3
     (sub-face (c).2); both examined faces are born unproven design
     debts, not interface premises, and the verdicts below are read
     with that scope.
   (c).1: the anchor-parametric design obligation planb3_g2_htri_face
     (planb3_g1_g2_design.v:138-142, corrected second slot
     planb3_dv_anchor (- p) (Z.of_nat q)) at the rational anchor
     xpi = 22/7.  At the counterinstance shape (a,b,p,q) = (-22,7,7,22)
     the corrected instance reads
     LHS = |(-22)*22 + 7*7| = 435 while
     RHS = 22*|-22 + 7*(22/7)| + 7*|-7 + 22*(22/7)| = 0 + 7*(435/7) = 435,
     i.e. the honest triangle identity in its equality case - TRUE, so
     the written-form refutation (which read RHS = 0 from the
     transposed slot) no longer goes through.  The written-form closing
     step is kept verbatim so the compiler verdict lands exactly there.
   (c).2: the exit-mirror design face l2_dv_hexit_face
     (planb4_l2_dv_cast.v:89-93, corrected first slot l2_dv (- a) b) at
     the constant sequence xL = fun _ => 3 with (a,b) = (3,1): the
     instance forces QleT' (l2_dv (-3) 1) (Qabs (1*3 - 3)); at the
     x = 1 carrier l2_dv (-3) 1 = |-3+1| = 2 (the carrier |a+b| is
     transposition-invariant), so the instance is the false QleT' 2 0.
   The examined files are consumed through their named Definitions
   (tracked Live-tree sources compiled into the temporary probe world
   by the sentinel script); no transcription is involved for this
   face.  Design faces are born unproven statements (registered debts),
   not interface premises; the verdicts below are read with that
   scope.
   Dependencies.  S02_CauchyComplete, piu_mu_criterion (world closure,
     resolved from the compiled vo tree); planb3_g1_calib,
     planb3_g1_g2_design, planb4_l2_dv_cast (tracked Live-tree
     sources, compiled into the temporary probe world by the sentinel
     script).
   References.  planb3_g1_g2_design.v:138-142 (corrected design
     obligation 2); planb4_l2_dv_cast.v:89-93 (corrected exit-mirror
     face); the superseded written-shape predecessor of this probe
     (same face).
   Constructivity.  Set-carried statements only (piu_mu_QleT, sigT,
     QleT'); no Axiom, no Admitted, no Abort.
   Build.  bash scripts/gates/vacuity_sentinel/run_vacuity_sentinel.sh
     (Rocq 9.3.0; the script compiles the tracked Live-tree companion
     sources into a temporary probe world and points -Q at that world
     plus the compiled vo tree). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Qring.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Lqa.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import planb3_g1_calib.
Require Import planb3_g1_g2_design.
Require Import planb4_l2_dv_cast.

(* ==== Documented exported shapes of the two examined corrected
       faces. ==== *)

Check planb3_g2_htri_face.
Check l2_dv_hexit_face.

(* ==== (c).1: planb3_g2_htri_face at xpi = 22/7, corrected form. ==== *)

Theorem vac_c_g2_htri_22_7_empty :
  planb3_g2_htri_face (22 # 7)%Q -> Empty_set.
Proof.
  intros Hf.
  assert (Hq : (1 <= 22)%nat) by lia.
  destruct (Hf (-22)%Z 7%Z 7%Z 22%nat Hq) as [Hbad].
  (* Corrected second slot: planb3_dv_anchor (-7) 22 = |-7 + 22*(22/7)|
     = 435/7, so the instance reads 435 <= 22*0 + 7*(435/7) = 435 -
     the triangle identity at equality, TRUE.  The written-form
     closing step is kept so the verdict lands exactly here. *)
  assert (Hfin : False).
  { unfold Qle in Hbad.
    vm_compute in Hbad.
    exact (Hbad eq_refl). }
  exact (False_rect Empty_set Hfin).
Qed.

(* ==== (c).2: l2_dv_hexit_face at the constant sequence xL = 3,
       corrected form. ==== *)

Theorem vac_c_l2_hexit_xL3_empty :
  l2_dv_hexit_face -> Empty_set.
Proof.
  intros Hf.
  assert (Hb : (1 <= 1)%Z) by lia.
  destruct (Hf (fun _ : nat => (3 # 1)%Q) 3%Z 1%Z Hb) as [K HK].
  specialize (HK K (Nat.le_refl K)).
  apply QleT'_to_Qle in HK.
  (* Corrected first slot l2_dv (-3) 1 = |-3+1| = 2 (the x = 1 carrier
     is transposition-invariant); RHS |1*3 - 3| = 0. *)
  assert (Hfin : False).
  { unfold Qle in HK.
    vm_compute in HK.
    exact (HK eq_refl). }
  exact (False_rect Empty_set Hfin).
Qed.

Print Assumptions vac_c_g2_htri_22_7_empty.
Print Assumptions vac_c_l2_hexit_xL3_empty.
