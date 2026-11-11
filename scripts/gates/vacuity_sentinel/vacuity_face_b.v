(* vacuity_face_b.v - gate8 vacuity sentinel probe, face (b).
   Sentinel contract.  COMPILE-MUST-FAIL PROBE.  This file must never
     compile.  It is a best-effort contradiction attempt against the
     corrected five-premise consumption face planb_b_mubound_zerotouch;
     its rejection by the kernel is the standing evidence that the
     corrected premise interface is non-vacuous.  If this file ever
     compiles, the premise interface has become jointly unsatisfiable
     - RED (run_vacuity_sentinel.sh exits 1 and gate8 fails).  Do not
     repair this file into compiling; a needed change to the interface
     must be re-audited through a fresh refutation attempt instead.
   Mission.  Attempt to refute the corrected five-premise consumption
     face planb_b_mubound_zerotouch
     (planb1_hcage_zerotouch_prescription.v:290-297) at face (b): the
     corrected-form Htri (second residual slot dval (- p) (Z.of_nat q))
     joint with planb_b_hval_direct (:258-260) at the calibration pair
     planb3_g1_A / planb3_g1_B.  The corrected Htri instance
     (a,b,p,q) = (22544,-7176,7176,22544) reads
     456736960 <= 22544 * dval 22544 (-7176)
                  + 7176 * dval (-7176) 22544,
     while planb_b_hval_direct at n = 1 gives
     dval 22544 (-7176) * 4 <= 1; the second atom
     dval (-7176) 22544 is unbounded above under these two premises,
     so the written-form contradiction
     (456736960 <= 29720 * w and 4 * w <= 1) is no longer derivable.
     The written-form closing readout is kept verbatim as the final
     step so the compiler verdict lands exactly there (expected
     verdict: the contradiction is NOT derivable).
   Dependencies.  S02_CauchyComplete, piu_mu_criterion (world closure,
     resolved from the compiled vo tree); planb3_g1_calib and
     planb1_hcage_zerotouch_prescription (tracked Live-tree sources,
     compiled into the temporary probe world by the sentinel script).
   References.  planb1_hcage_zerotouch_prescription.v:290-297 (the
     five-premise zero-touch face, corrected slot :295);
     piu_mu_criterion.v:169-172 (corrected Htri verbatim); the
     superseded written-shape predecessor of this probe (same face).
   Constructivity.  Set-carried statements only (piu_mu_QleT, sigT);
     no Axiom, no Admitted, no Abort; the examined files are consumed
     compiled (read-only), never modified.
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
Require Import planb1_hcage_zerotouch_prescription.

(* ==== The verbatim corrected form (examined file
       planb1_hcage_zerotouch_prescription.v:292-295, corrected second
       slot). ==== *)

Definition vac_b_Htri_written (dval : Z -> Z -> Q) : Set :=
  forall (a b p : Z) (q : nat), (1 <= q)%nat ->
    piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
      ((inject_Z (Z.of_nat q) * dval a b
        + inject_Z (Z.abs b) * dval (- p)%Z (Z.of_nat q))%Q).

(* ==== Machine bite: the transcribed corrected form type-checks
       against the actual premise slot of the compiled consumption face
       planb_b_mubound_zerotouch (:290-297, corrected). ==== *)

Check (fun (A B : nat -> Z) (dval : Z -> Z -> Q)
         (Hp : forall a b : Z, piu_mu_QleT 0 (dval a b))
         (Hc : planb_b_hcoef17 A B)
         (Hv : planb_b_hval_direct A B dval)
         (Ht : vac_b_Htri_written dval)
         (He : planb_b_hesc17 A B dval) =>
       planb_b_mubound_zerotouch A B dval Hp Hc Hv Ht He).

(* ==== Arithmetic ground faces (documentary pins). ==== *)

Example vac_b_A1 : planb3_g1_A 1 = 22544%Z.
Proof. reflexivity. Qed.

Example vac_b_B1 : planb3_g1_B 1 = (-7176)%Z.
Proof. reflexivity. Qed.

Example vac_b_sum : 22544 + 7176 = 29720.
Proof. reflexivity. Qed.

Example vac_b_456736960 :
  inject_Z (Z.abs (22544 * 22544 + (-7176) * 7176)) = (456736960 # 1)%Q.
Proof. reflexivity. Qed.

(* ==== Face (b), corrected form: the refutation attempt. ==== *)

Theorem vac_b_face_empty :
  forall dval : Z -> Z -> Q,
  vac_b_Htri_written dval ->
  planb_b_hval_direct planb3_g1_A planb3_g1_B dval ->
  Empty_set.
Proof.
  intros dval Htri Hv.
  assert (Hq : (1 <= 22544)%nat) by (apply (proj1 (Nat.leb_le 1 22544)); vm_compute; reflexivity).
  destruct (Htri (planb3_g1_A 1%nat) (planb3_g1_B 1%nat) 7176%Z 22544%nat Hq) as [Hle].
  assert (EA : planb3_g1_A 1 = 22544%Z) by reflexivity.
  assert (EB : planb3_g1_B 1 = (-7176)%Z) by reflexivity.
  rewrite EA, EB in Hle.
  assert (Eq : Z.of_nat 22544 = 22544%Z) by reflexivity.
  rewrite Eq in Hle.
  assert (EL : inject_Z (Z.abs (22544 * 22544 + (-7176) * 7176))
               = (456736960 # 1)%Q) by reflexivity.
  assert (EI : inject_Z 22544 = (22544 # 1)%Q) by reflexivity.
  assert (EAbB : inject_Z (Z.abs (-7176)) = (7176 # 1)%Q) by reflexivity.
  rewrite EL, EI, EAbB in Hle.
  (* fold the Z.opp 7176 form of the corrected second slot into the
     numeral form; the two residual atoms are
     w1 := dval 22544 (-7176) and w2 := dval (-7176) 22544. *)
  assert (Ev : dval (- (7176))%Z 22544%Z = dval (-7176)%Z 22544%Z)
    by reflexivity.
  rewrite Ev in Hle.
  (* Hle : (456736960#1) <= (22544#1) * w1 + (7176#1) * w2. *)
  destruct (Hv 1%nat) as [Hv1].
  rewrite EA, EB in Hv1.
  assert (EE : piu_mu_epos (2 * 1) = (4 # 1)%Q) by reflexivity.
  rewrite EE in Hv1.
  (* Hv1 : w1 * (4#1) <= (1#1); the atom w2 carries no upper bound
     under these two corrected premises, so the written-form readout
     456736960 * 4 <= 29720 no longer closes; the attempt ends here. *)
  assert (Hfin : False) by lra.
  exact (False_rect Empty_set Hfin).
Qed.

Print Assumptions vac_b_face_empty.
