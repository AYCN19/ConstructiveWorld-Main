(* ConstructiveWorld-Main - planB wave-1 piece 3b: the G2 dv residual-mirror design face and the G1 slot registration. *)

(** * planb3_g1_g2_design: G2 dv residual mirror (design) and G1 slot registration.

    Mission.  (a) The informative concretization of the e_carrier.v:617
      section variable [dv : Z -> Z -> Q]: the x = 1 anchored
      dual-pairing residual [dv a b := |a + b|] (Qabs construction);
      the triangle identity [a*q + b*p = q*(a+b) - b*(q-p)] makes Hp
      AND Htri provable by construction at this anchor (the
      [piu_zz_ec_epos_pos] precedent, e_carrier.v:234).  (b) The
      anchor-parametric design obligations ([dv_anchor], the
      Hval/Htri/Hexit faces over the rational anchor slot [xpi]) are
      Set-typed statement faces awaiting supply - not claimed (the
      ZZ2020 main-lemma instantiation is the registered G2 debt).
      (c) The Hcoef@17 consumption face is registered with its honest
      n=5 A-side tension (the A-channel supply is the N2c chain debt).
    Dependencies.  planb3_g1_calib (sandbox-local); piu_mu_criterion
      (mu faces + Qinv_nonneg); S02_CauchyComplete (QleT'); stdlib
      QArith.QArith, QArith.Qabs, ZArith, Arith, Lia, Qpower.
    References.  e_carrier.v:613-650 (the dv slot and premise
      shapes), :234-240 (Qabs precedent); piu_mu_criterion.v:169-172
      (Htri shape verbatim).
    Constructivity.  The born proofs (dv_hp, dv_htri, qabs_inj_nat)
      are Set-carried and close under the global context; the design
      obligations are Set-typed statement faces (the cage_constants
      HCDRAFT precedent - born statements, honestly unproven, debts
      registered); postulate-free and admission-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb3_g1_g2_design.v
      (Rocq 9.3.0, single lane under cpu_guard_v3; coqchk with -bytecode-compiler yes). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import planb3_g1_calib.

(* ================================================================== *)
(* Section 1. The informative carrier: the x = 1 anchored residual    *)
(*            (the e_carrier.v:617 slot concretized).                 *)
(* ================================================================== *)

(* dv a b := |a + b| - the dual-pairing residual at the x = 1 anchor. *)
(* Qabs construction, total, informative (Q : Set).                   *)
Definition planb3_dv (a b : Z) : Q := Qabs (inject_Z a + inject_Z b)%Q.

(* |inject_Z q| = inject_Z q (needed for the triangle readout). *)
Lemma planb3_qabs_inj_nat : forall q : nat,
  Qabs (inject_Z (Z.of_nat q)) == inject_Z (Z.of_nat q).
Proof.
  intros q. unfold Qabs, inject_Z, Qeq. cbn.
  destruct (Z.le_gt_cases 0 (Z.of_nat q)) as [H | H].
  - rewrite Z.abs_eq by lia. lia.
  - exfalso. lia.
Qed.

(* the Z-cast bridge: inject_Z of a Z.abs IS the Qabs of the inject_Z  *)
(* (both reduce to Qmake (Z.abs x) 1). *)
Lemma planb3_inj_zabs_qabs : forall x : Z,
  inject_Z (Z.abs x) == Qabs (inject_Z x).
Proof. intros x. unfold Qabs, inject_Z. reflexivity. Qed.

(* Hp DISCHARGED at the carrier (the one-line Qabs construction, the   *)
(* ec_epos_pos precedent e_carrier.v:234).                             *)
Lemma planb3_dv_hp : forall a b : Z, piu_mu_QleT 0 (planb3_dv a b).
Proof.
  intros a b. apply piu_mu_QleT_i. unfold planb3_dv. apply Qabs_nonneg.
Qed.

(* Htri DISCHARGED at the carrier: the exact triangle identity        *)
(* a*q + b*p = q*(a+b) + (-b)*(q + (-p)) gives                        *)
(* |aq + bp| <= q*|a+b| + |b|*|q-p| (the piu_mu_criterion.v:169-172   *)
(* Htri shape verbatim, proven at the concrete carrier).              *)
Lemma planb3_dv_htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * planb3_dv a b
      + inject_Z (Z.abs b) * planb3_dv (Z.of_nat q) (- p)%Z)%Q).
Proof.
  intros a b p q Hq. apply piu_mu_QleT_i. unfold planb3_dv.
  rewrite (planb3_inj_zabs_qabs (a * Z.of_nat q + b * p)).
  assert (Habsb : (Qabs (inject_Z (- b)) == inject_Z (Z.abs b))%Q).
  { unfold Qabs, inject_Z, Qeq. cbn. rewrite Z.abs_opp. lia. }
  assert (Hid : inject_Z (a * Z.of_nat q + b * p)
                == (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b)
                    + inject_Z (- b)
                      * (inject_Z (Z.of_nat q) + inject_Z (- p)))%Q).
  { unfold inject_Z, Qplus, Qminus, Qmult, Qeq. cbn. ring. }
  rewrite Hid.
  pose proof (Qabs_triangle (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b))
              (inject_Z (- b)
               * (inject_Z (Z.of_nat q) + inject_Z (- p)))) as Htri0.
  apply (Qle_trans _
    (Qabs (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b))
     + Qabs (inject_Z (- b)
             * (inject_Z (Z.of_nat q) + inject_Z (- p))))%Q).
  - exact Htri0.
  - rewrite (Qabs_Qmult (inject_Z (Z.of_nat q)) (inject_Z a + inject_Z b)).
    rewrite (planb3_qabs_inj_nat q).
    rewrite (Qabs_Qmult (inject_Z (- b))
              (inject_Z (Z.of_nat q) + inject_Z (- p))).
    rewrite Habsb.
    apply Qle_refl.
Qed.

(* ================================================================== *)
(* Section 2. The anchor-parametric design obligations (born          *)
(*            statements, honestly unproven - the G2 debts).          *)
(* ================================================================== *)

Section G2_DESIGN.

(* xpi: the rational anchor slot of the residual pairing (the general *)
(* x != 1 carrier). xL: the point-sequence slot (the lw0m_xL          *)
(* abstraction, kept abstract to preserve the one-way layering).      *)
Variable xpi : Q.
Variable xL : nat -> Q.

(* the anchor-parametric carrier: dv_x a b := |a + b * xpi|. *)
Definition planb3_dv_anchor (a b : Z) : Q :=
  Qabs (inject_Z a + inject_Z b * xpi)%Q.

(* DESIGN OBLIGATION 1 (the value slot at tau = 2 over the calibration *)
(* pair): dval(A n, B n) * 2^(2n) <= 1. Awaiting supply: the anchor    *)
(* choice and the decay estimate (the Rhat_n decay face is machine-    *)
(* verified n = 1..40 in the kb41m package; the Coq-side transfer is   *)
(* open). NOT claimed here.                                            *)
Definition planb3_g2_hval_face : Set :=
  forall n : nat,
    piu_mu_QleT (planb3_dv_anchor (planb3_g1_A n) (planb3_g1_B n)
                 * piu_mu_epos (2 * n)) (1 # 1)%Q.

(* DESIGN OBLIGATION 2 (the ZZ2020 main-lemma instantiation, the       *)
(* HIGH-RISK G2 debt): the triangular mirror consistency at the        *)
(* anchor carrier. The x = 1 instance is PROVEN above (planb3_dv_htri) *)
(* - exactly the special case xpi = 1 of this face; the general        *)
(* anchor requires the ZZ2020 dual-pairing identity and consumes the   *)
(* padic_clearing B1-B3 integer core (cited, not required here).       *)
Definition planb3_g2_htri_face : Set :=
  forall (a b p : Z) (q : nat), (1 <= q)%nat ->
    piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
      ((inject_Z (Z.of_nat q) * planb3_dv_anchor a b
        + inject_Z (Z.abs b) * planb3_dv_anchor (Z.of_nat q) (- p)%Z)%Q).

(* DESIGN OBLIGATION 3 (the exit mirror): dval(b, -a) is eventually    *)
(* bounded by |b * xL(k) - a| (the e_carrier.v:647-650 Hexit shape at  *)
(* the anchor carrier, xL abstract). Awaiting supply: the transfer     *)
(* from the xL convergence face. NOT claimed here.                     *)
Definition planb3_g2_hexit_face : Set :=
  forall a b : Z, (1 <= b)%Z ->
    sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      S02_CauchyComplete.QleT' (planb3_dv_anchor b (- a)%Z)
        (Qabs (inject_Z b * xL k - inject_Z a))).

End G2_DESIGN.

(* the x = 1 instance consistency: at xpi = 1 the anchor carrier       *)
(* coincides with the proven carrier (pointwise Qeq face).             *)
Lemma planb3_g2_anchor_one : forall a b : Z,
  planb3_dv_anchor (1 # 1)%Q a b == planb3_dv a b.
Proof.
  intros a b. unfold planb3_dv_anchor, planb3_dv.
  rewrite Qmult_1_r. apply Qeq_refl.
Qed.

(* ================================================================== *)
(* Section 3. The G1 Hcoef@17 consumption-slot registration (born     *)
(*            statement, honestly unproven - the N2c chain debt).     *)
(* ================================================================== *)

(* The Hcoef@17 face over the calibration pair (the e_carrier.v:627-  *)
(* 630 Hcoef isomorph at sigma = 17, A/B := the calibration tables).  *)
(* NOT claimed: the n=5 A-side tension face in planb3_g1_calib.v      *)
(* (2^85 < |A 5|) certifies that the calibration A-channel does not   *)
(* yet supply this slot; the supply is the N2c chain-product debt     *)
(* (sigma_decay.v:94-97 consumption face + KB41m 5.5 s2/A0 margin).   *)
Definition planb3_g1_hcoef17_face : Set :=
  forall n : nat,
    piu_mu_and2
      (piu_mu_ZleT (Z.abs (planb3_g1_A n)) (2 ^ Z.of_nat (17 * n))%Z)
      (piu_mu_ZleT (Z.abs (planb3_g1_B n)) (2 ^ Z.of_nat (17 * n))%Z).

(* The pipeline continuation registry (comments only, per the one-way  *)
(* layering): G1 next segments = (i) zzm slice-2/3 Pade pipeline       *)
(* (pdivmod/pshift/Laurent extraction, single-source generator law),   *)
(* (ii) the list-Q -> nat->Z lift with Q->Z typing, (iii) the          *)
(* L_n = lcm(1..4n)/Phi_n assembly + 2^(-floor(5n/2)+1) normalization  *)
(* feeding A(n)/B(n) as the general-n formula face; consumers: G4      *)
(* (Hcoef sharpening + B side), G3 (limb-2 nonvanishing at the same    *)
(* witness), G2 (the dv mirror above). Dependence line: G1 -> G2 ->    *)
(* (Hp, Htri, Hexit, G3); G4/G6 -> Hcoef; construction order G6 -> G5  *)
(* first, G3 the mathematical main attack.                             *)

(* ================================================================== *)
(* Section 4. Assumption audit (the born proofs only; the design      *)
(*            obligations are statement faces, not claims).           *)
(* ================================================================== *)

Print Assumptions planb3_qabs_inj_nat.
Print Assumptions planb3_inj_zabs_qabs.
Print Assumptions planb3_dv_hp.
Print Assumptions planb3_dv_htri.
Print Assumptions planb3_g2_anchor_one.
