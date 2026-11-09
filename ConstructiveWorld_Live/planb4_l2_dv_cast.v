(* ConstructiveWorld-Main - unif L2 piece: the concrete dv cast module. *)

(** * planb4_l2_dv_cast: the concrete dv : Z -> Z -> Q casting.

    Mission.  The L2 work-order deliverable (01 work order, section 1,
    lane L2): the concrete informative casting of the e_carrier.v:617
    section slot [dv : Z -> Z -> Q], with limb 1 (pointwise
    nonnegativity, CLOSED proof) and limb 2 (triangle consistency,
    CLOSED proof) re-exported through the cast name, and limb 3 (the
    exit mirror) registered as the honest Set-typed statement face over
    the abstract xL slot - mirroring planb3_g2_hexit_face
    (planb3_g1_g2_design.v:148-152); born statement, honestly
    unproven, debt registered (the cage_constants HCDRAFT precedent).
    Born provenance.  The carrier and limbs 1-2 are re-exports of born
    faces: planb3_dv (planb3_g1_g2_design.v:45), planb3_dv_hp (:65-68),
    planb3_dv_htri (:74-103) - no new mathematics claimed here.
    Debts registered (comments only).  (i) The limb-3 concrete binding
    to the lw0m_xL consumption slot (piu1932_uncond_zz.v:83-86;
    LW0MLicBridge.v:20) is the L3 assembly: LW0MLicBridge carries no
    in-tree .vo at cast time, and the general-anchor identity is the
    ZZ2020 dual-pairing debt (planb3_g1_g2_design.v:132-137).  (ii) The
    Hval/Hcage slots are the registered G2 debts (planb3_g1_g2_design
    .v:127-130; top theorem piu1932_uncond_zz.v:81-82) - outside the
    L2 acceptance face, not touched.
    Constructivity.  Every new statement is Set-carried (piu_mu_QleT,
    sigT, QleT'); the closed limbs inherit the born proofs, audited
    Closed under the global context in planb3_g1_g2_design.v:198-202
    and re-audited below; postulate-free throughout.
    Build.  coqc -q -native-compiler no -Q <Live> "" planb4_l2_dv_cast.v
    (Rocq 9.3.0, single lane wrapped in cpu_guard_v3; E952: coqc only,
    no interactive feed). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import planb3_g1_g2_design.

(* ================================================================== *)
(* Section 1. The cast: the concrete carrier under its L2 name.       *)
(* ================================================================== *)

(* l2_dv := planb3_dv - the x = 1 anchored residual |a + b| (Qabs     *)
(* construction, total, informative), the concretization of the       *)
(* e_carrier.v:617 slot under the L2 name.                            *)
Definition l2_dv : Z -> Z -> Q := planb3_dv.

(* ================================================================== *)
(* Section 2. Limb 1 (Hp): pointwise nonnegativity - CLOSED proof.    *)
(* ================================================================== *)

(* The work-order limb-1 acceptance face: piu_mu_QleT 0 (l2_dv a b)   *)
(* for all a b, discharged by the born carrier proof (piu_mu_QleT_i   *)
(* + Qabs_nonneg, the ec_epos_pos precedent).                         *)
Lemma l2_dv_hp : forall a b : Z, piu_mu_QleT 0 (l2_dv a b).
Proof. intros a b. exact (planb3_dv_hp a b). Qed.

(* ================================================================== *)
(* Section 3. Limb 2 (Htri): triangle consistency - CLOSED proof.     *)
(* ================================================================== *)

(* The consumption shape verbatim as at piu1932_uncond_zz.v:65-69 /   *)
(* piu_mu_criterion.v:169-172 / piu_zz_e_carrier.v:622-625, at the    *)
(* cast name; discharged by the born carrier proof (the exact         *)
(* triangle identity a*q + b*p = q*(a+b) + (-b)*(q + (-p)), then      *)
(* Qabs_triangle + Qabs_Qmult, closing by Qle_refl).                  *)
Lemma l2_dv_htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * l2_dv a b
      + inject_Z (Z.abs b) * l2_dv (Z.of_nat q) (- p)%Z)%Q).
Proof. intros a b p q Hq. exact (planb3_dv_htri a b p q Hq). Qed.

(* ================================================================== *)
(* Section 4. Limb 3 (Hexit): the honest consumption face (born       *)
(*            statement, honestly unproven - the G2/L3 debt).         *)
(* ================================================================== *)

(* The exit-mirror consumption face over the abstract xL slot,        *)
(* mirroring planb3_g2_hexit_face (planb3_g1_g2_design.v:148-152) at  *)
(* the cast name.  NOT claimed: the concrete binding to lw0m_xL       *)
(* (LW0MLicBridge.v:20; top-theorem shape piu1932_uncond_zz.v:83-86)  *)
(* is the L3 assembly, and the general-anchor identity is the ZZ2020  *)
(* dual-pairing debt (planb3_g1_g2_design.v:132-137).                 *)
Definition l2_dv_hexit_face : Set :=
  forall (xL : nat -> Q) (a b : Z), (1 <= b)%Z ->
    sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      S02_CauchyComplete.QleT' (l2_dv b (- a)%Z)
        (Qabs (inject_Z b * xL k - inject_Z a))).

(* ================================================================== *)
(* Section 5. Assumption audit (the closed limbs; the face is a       *)
(*            statement, not a claim).                                *)
(* ================================================================== *)

Print Assumptions l2_dv.
Print Assumptions l2_dv_hp.
Print Assumptions l2_dv_htri.
