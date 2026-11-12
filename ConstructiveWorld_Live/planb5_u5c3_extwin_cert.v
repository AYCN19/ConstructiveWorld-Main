(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-5 U5-C3: the extension-window     *)
(* {44,56,64} A/B cross-certificate face (rebuilt-source regime).        *)
(* ===================================================================== *)

(** * planb5_u5c3_extwin_cert: extension-window cross bites.

    Mission.  The per-point cross certificates of the general-n A/B
      assembly at n = 44, 56, 64, in the litdef cross-multiplication
      form (main-session ruling item 3-b): the comparison
      face is [Qeq_bool (exp * L * sign * r_snapshot) (anchor)] with
      the pipeline's internal r/s channel values carried as Z
      literals (the snapshot kb41m_rs_snapshot_20261112.json, md5
      cb63015370a8714d9292313126e181e1).  The expected values remain
      the rebuilt single-source anchors (below); the snapshot is a
      pipeline-internal value, not an expected-value source - the
      face computes to false exactly when the snapshot is wrong, so
      it still bites the anchor fail-loud.  This shape avoids the
      giant-term reduction of [planb4_abqA n] (machine-level freeze:
      small-term compiles pass, n >= 8 giant-term reductions hang,
      three seats affected, main-session ruling).  Provenance (honest
      registration): rebuilt per main-session dispatch; the original package source
      kb41m_asm_rb.json (md5 097fda87c872c75bacbc63c5239940bd) is LOST
      (double zero-hit: git history of both repos + attn-wide find;
      main-session ruling item 3); the values come from the
      KB41m Lemma 3(9) recurrence pipeline (the same recurrence whose
      n = 1..40 window is frozen in planb3_g1_calib) cross-validated
      40/40 against planb3_g1_A/planb3_g1_B in the same production
      run; the new anchor md5 is 212a0c2643cf8a66e3635f3014587c59,
      re-verified at emit time, and the snapshot run re-verified the
      anchors plus the n = 1 frozen-table round trip.  Honest
      contraction (main-session ruling, round 6): the n = 56 / 64
      rebuilt values were falsified by an independent 460-digit
      Machin-pi recomputation (machine-run, ESCALATE_evidence_r5,
      re-run by this seat): independent log2|ahat + bhat*pi| = +665.30
      (n = 56) and +801.50 (n = 64) against the KB41m receipt line 93
      reference exponents -159.68 / -178.90 - two conflicting witness
      values, neither declared here.  The n = 44 face is the only
      doubly-verified point (Machin -125.3355 vs receipt -125.34,
      delta 0.0045) and is retained.  The points 45..55, 56, 57..64
      and 65..1347 therefore carry no claim anywhere - the honest
      window of this face is n = 44 alone until a correct value
      source for 56 / 64 is adjudicated (registered debt: Coq-side
      exact-rational Machin, original-archive recovery, or
      coordination-channel petition).  Domain
      honesty: the calib domain table excludes all three points
      (their claims are carried by these cross bites, not by the
      1..40 tables).

    Dependencies.  planb4_g1_ab_def (planb4_ab_exp/planb4_ab_L/
      planb4_ab_sign, the small-term channel definitions);
      planb3_g1_calib (planb3_g1_dom).  Expected literals: emitted
      from the rebuilt source artifact via the registered emitter
      (single-anchor law, md5 re-verified at emit time); the emitted
      file carries no invented digit.  Snapshot literals: from
      kb41m_rs_snapshot_20261112.json (pipeline-internal, fail-loud
      against the anchors).

    References.  KB41m beta0 pre-survey receipt supplement 6 (the
      44/56/64 single-point extension; |Rhat|_hi exponents -125.34 /
      -159.68 / -178.90); born_ledger_planB_wave1 piece-3 gates; the
      ZZ2020 Prop 1 assembly (2^(-5n/2+2) L_n I_n in Z + Z pi).

    Constructivity.  Informative claims over Z/Q; each face closes
      by one vm_compute step over small-integer arithmetic (no
      giant-term reduction); admission-free; zero Prop statement
      face beyond the informative Qeq_bool booleans.

    Build.  coqc -native-compiler no -q -Q . "" planb5_u5c3_extwin_cert.v
      (Rocq 9.3.0, serial single lane under cpu_guard_v3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.

(* ================================================================ *)
(* Section 1. The extension-window face (n = 44): one Qeq_bool       *)
(* cross-multiplication face per channel: the in-tree exp/L/sign     *)
(* definitions times the pipeline's internal r/s channel snapshot    *)
(* (Z literals from kb41m_rs_snapshot_20261112, md5                  *)
(* cb63015370a8714d9292313126e181e1) must equal the rebuilt          *)
(* single-source anchor.  n = 44 is the only doubly-verified point   *)
(* (independent Machin -125.3355 vs receipt -125.34, delta 0.0045).  *)
(* The n = 56 / 64 faces are RETRACTED (honest contraction, round 6  *)
(* ruling): their rebuilt values conflict with the independent       *)
(* Machin recomputation by +825 / +980 bits, and neither candidate   *)
(* value is declared here.  Small-integer arithmetic only; the       *)
(* giant-term reduction form is banned (per main-session ruling).  The       *)
(* snapshot is not an expected-value source: a wrong snapshot        *)
(* computes to false and the compile fails loud.                     *)
(* ================================================================ *)

Example planb5_ext_A_44 :
  Qeq_bool (planb4_ab_exp 44 * inject_Z (planb4_ab_L 44)
            * inject_Z (planb4_ab_sign 44)
            * inject_Z (-17545533289124070670616905700395653654224401868563345277693392653649161786724860692729299608637207202891087053923615584730299882208355256477907838466973275771625400436763336653552173956280971742799586287067888949341715991881393443180963029609086976)%Z
            / inject_Z (15346144494172535825501455131028779402768044548349646823875)%Z)
           (inject_Z 22609249443517065326730524672222971139740359111382579347265754575004671993461901853384416766782692596045207624429359081530101354062646361128499523029089709989146125764883782483690897799478899760050131649331224952015159296%Z) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_ext_B_44 :
  Qeq_bool (planb4_ab_exp 44 * inject_Z (planb4_ab_L 44)
            * inject_Z (planb4_ab_sign 44)
            * inject_Z (363929631081981549690549204999197006408907739587470555424302824807952638390580207065288770564572814236656934867553306533048280084435564378965911740685104282013134304224213533276784813932544)%Z
            / inject_Z 1%Z)
           (inject_Z (-7196747617066849641395044252287707900357657332554179848655982765193550893378537337014724660256508088907095948818919585133102098127620044242316061925741402104447482293400828526919868824079369324017839893248043059298848000)%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* n = 56 / 64: retracted by the round-6 honest contraction - the    *)
(* rebuilt anchors conflict with the independent Machin recomputation *)
(* by +825 / +980 bits; two conflicting witnesses, no claim here.    *)

(* ================================================================ *)
(* Section 2. Domain honesty.  The extension points sit outside the  *)
(* frozen 1..40 calib domain.  The n = 44 claim is carried by        *)
(* Section 1's cross bites against the doubly-verified anchor; the   *)
(* points 45..55, 56, 57..64 and 65..1347 carry NO claim anywhere -  *)
(* 45..55 were never computed (the KB41m 43-point window), 56/64     *)
(* were retracted by the round-6 honest contraction (two conflicting *)
(* witness values, both undeclared).  The pipeline computes          *)
(* everywhere, but this face asserts only at n = 44.                 *)
(* ================================================================ *)

Example planb5_ext_dom_44 : planb3_g1_dom 44 = false.
Proof. reflexivity. Qed.

Example planb5_ext_dom_56 : planb3_g1_dom 56 = false.
Proof. reflexivity. Qed.

Example planb5_ext_dom_64 : planb3_g1_dom 64 = false.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* Section 3. Assumption audit (5 faces).                            *)
(* ================================================================ *)

Print Assumptions planb5_ext_A_44.
Print Assumptions planb5_ext_B_44.
Print Assumptions planb5_ext_dom_44.
Print Assumptions planb5_ext_dom_56.
Print Assumptions planb5_ext_dom_64.
