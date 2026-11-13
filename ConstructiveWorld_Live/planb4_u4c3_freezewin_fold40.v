(* ConstructiveWorld-Main - U4-C3: the mandated k = 40 fold anchors,     *)
(* the single vm_compute census folds of the work order.                  *)

(** * planb4_u4c3_freezewin_fold40: the k = 40 fold anchors.
    Mission.  The work-order face shape, one vm_compute fold per
      census: [planb4_g1_awin_40], [planb4_g1_bwin_40],
      [planb4_g1_symwin_40] (each a single kernel fold of the
      Fixpoint census over the declared window n = 1..40) and
      [planb4_g1_allb_nz_40] (transferred from [bwin_40] and the
      frozen-table nonzero census via the mono Lemma, no
      recomputation of the B pipeline).  The pointwise belt
      (planb4_u4c3_freezewin_s1 and the s2n9..s2n14 micro segments)
      covers the same window bite by bite; this file is the fold
      shape of record.
    Dependencies.  planb4_u4c3_freezewin_cert (the census
      Fixpoints, the mono Lemma, the calib census Example).
    References.  ZZ2020 Prop 1; planb3_g1_calib A/B tables
      n = 1..40; the fold-lane ETA is machine-condition dependent
      (deep single kernel evaluations run duty-cycled under memory
      pressure; observed 12-25 min per single point on this host).
    Constructivity.  vm_compute folds and one Lemma application;
      admission-free and postulate-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_fold40.v
      (Rocq 9.3.0, single lane under cpu_guard_v3; heavy fold shot,
      long patience window, no parallel lane). *)

From Stdlib Require Import ZArith.
Require Import planb3_g1_calib.
Require Import planb4_u4c3_freezewin_cert.

(* heavy fold 1: the full A-channel table bite census, one fold. *)
Example planb4_g1_awin_40 : planb4_g1_awin 40%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* heavy fold 2: the full B-channel twin census, one fold. *)
Example planb4_g1_bwin_40 : planb4_g1_bwin 40%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* heavy fold 3: the full pole-symmetry census, one fold. *)
Example planb4_g1_symwin_40 : planb4_g1_symwin 40%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* the assembled-B nonzero census at k = 40: transfer from the
   table bite fold plus the frozen nonzero census (the mono Lemma;
   the B pipeline is not recomputed). *)
Example planb4_g1_allb_nz_40 : planb4_g1_allb_nz 40%nat = true.
Proof. apply planb4_g1_allb_nz_mono.
  - exact planb4_g1_bwin_40.
  - exact planb4_u4c3_calib_allb_nz_40.
Qed.

Print Assumptions planb4_g1_awin_40.
Print Assumptions planb4_g1_bwin_40.
Print Assumptions planb4_g1_symwin_40.
Print Assumptions planb4_g1_allb_nz_40.
