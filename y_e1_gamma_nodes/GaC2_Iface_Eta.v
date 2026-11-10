(* ConstructiveWorld-Main - the eta block interface slice of the C2 segment. *)
(** * GaC2_Iface_Eta: the eta block interface slice.

    Mission.  Cross-segment trans-supply face of the eta (alternating
      continuation) block of segment C2.  Whitelist row of
      gamma_module_spec.md section 2.3: GaC2_Iface_Eta = C2.06..C2.10
      (five nodes).  An interface module carries ONLY the finalized
      statement faces of its block with Require Export trans-supply plus
      the named-item index comments: zero proof bodies, zero definition
      bodies; every definition and theorem statement lives in its node
      file, this slice only re-exports names.  Cross-segment consumers
      Require Import this slice; within-segment consumers go through
      node stems directly.  Rows are instantiated one by one as their
      node statement faces are cast and pass acceptance; a row whose
      statements are not yet in the tree is not written here.  The
      registered cross-segment consumers of this slice are the C3 Z03
      and Z09 supply faces (drafts_C3.md, the Z03 and Z09 headers).

    Dependencies.  Two node statement faces, both cast and accepted,
      held via [Require Export] (the only Export site a gamma file may
      hold; same-segment stems only; Stdlib: none required directly):
      [GaC2_06_AltMonoFace] (node C2.06; acceptance record
      accept/C2.06.json, verdict PASS) and [GaC2_09_DenomZeroSet_a]
      (node C2.09 machine piece; acceptance record accept/C2.09.json,
      verdict PASS; re-exported at leaf level because the consolidating
      stem GaC2_09_DenomZeroSet is not yet cast, and the row moves up
      to the stem when it lands).  The remaining whitelist rows are
      open, not omitted: C2.07 [GaC2_07_DirichletTestAbel], C2.08
      [GaC2_08_EtaZetaRelation], C2.10 [GaC2_10_EtaContinuation], and
      the C2.09 companion pieces [GaC2_09_DenomZeroSet_b] /
      [GaC2_09_DenomZeroSet] have no module in the tree yet, so
      exporting them now would re-export names with no statement face
      behind them; each row is appended as soon as its faces pass.

    References.  gamma_module_spec.md section 2.3 (whitelist and the
      production-timing rule: interface slices are end-of-wave joint
      certification deliverables and only accepted statement faces are
      exported); drafts_C2.md section 5 item 3.  Wave-end obligations
      registered here: when C2.10 lands, its analytic carrier form is
      checked against the C1-15 local expansion form (drafts_C2.md
      C2.10 obligation row), and the end-of-wave joint re-run of the
      acceptance covers all five rows of this slice.

    Constructivity.  This file adds no statements, hence zero assumed
      constants and no computational content; Print Assumptions of
      every trans-supplied item is inherited Closed from the node
      files; [coqchk] reports no module-owned assumed entries for
      either exported module.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_Iface_Eta.v] compiles cleanly (exit 0)
      through the dependency-closure build (50_toolkit/build_deposit.py);
      acceptance runs use 50_toolkit/accept_node.py and write
      accept/<node>.json. *)

(* ---- C2.06: GaC2_06_AltMonoFace -- the monotone modulus face of the     *)
(*      alternating Dirichlet block.  15 named items (3 Definitions,       *)
(*      12 Lemmas; Section AltMonoFace discharge with premises sig,        *)
(*      sig0, 0 < sig0, sig0 <= sig, and positivity of the embedded        *)
(*      naturals):                                                         *)
(*        Definitions (3): r_npow, r_npow0, r_npow_at (consumption         *)
(*          alias of r_npow0 registered for the C2.07 consumer)            *)
(*        Statements (4): r_npow_anti, r_npow_tozero, r_npow0_tendsto      *)
(*          (explicit sigT convergence modulus, witness M0 = 2, bound is   *)
(*          the sig0 slice at 2), r_npow_diff_nonneg                       *)
(*        Node helpers (8): mn_exp_le (section-external), mn_sig_pos,      *)
(*          mn_natreal_le, mn_log_nonneg, mn_slice_exp_gen, mn_slice_exp,  *)
(*          mn_slice_exp0, mn_rnpow_irrel                                  *)
Require Export GaC2_06_AltMonoFace.

(* ---- C2.09: GaC2_09_DenomZeroSet_a -- machine cluster of the            *)
(*      denominator zero set of the eta quotient 1 - 2^(1-s).  18 named    *)
(*      items (18 Lemmas, no Section):                                     *)
(*        Real-order cancellation kit (10): d09_rplus_zero_l_pt,           *)
(*          d09_rmult_zero_l_pt, d09_rmult_opp_opp, d09_rmult_opp_l_pt,    *)
(*          d09_lt_zero_opp_rev, d09_lt_zero_opp, d09_mult_pos_gen,        *)
(*          d09_mult_cancel_pos, d09_sq_zero, d09_two_zero_cancel          *)
(*        Pair helpers (8): d09_cRe_scale, d09_cIm_scale, d09_norm_wd,     *)
(*          d09_norm_one, d09_c_eq_shift, d09_c_opp_zero,                  *)
(*          d09_rone_minus_rone, d09_cIm_plus_opp                          *)
(*      The carrier block of the node (the logarithm constant, the         *)
(*      2^(1-s) power carrier, the denominator faces, and the zero set     *)
(*      statements proper: denom_zero_real_dir, denom_zero_imag_char,      *)
(*      denom_first_order, zero_set_membership per drafts_C2.md C2.09)     *)
(*      is cast in the companion pieces GaC2_09_DenomZeroSet_b and         *)
(*      GaC2_09_DenomZeroSet (per the leaf header); those pieces are not   *)
(*      in the tree yet and join this slice when cast and accepted.        *)
Require Export GaC2_09_DenomZeroSet_a.
