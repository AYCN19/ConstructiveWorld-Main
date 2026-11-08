(* ConstructiveWorld-Main - the Dirichlet-series block interface slice of the
   C2 segment for cross-segment consumers. *)
(** * GaC2_Iface_DS: the DS-block interface slice.
    Mission.  Cross-segment trans-supply face of the Dirichlet-series
      block.  Whitelist row gamma_module_spec.md section 2.3:
      GaC2_Iface_DS = C2.01..C2.05 (five nodes).  An interface module
      carries ONLY the Require of the segment's finalized statement
      faces with Require Export trans-supply plus the named-item index
      comments: zero proof bodies, zero definition bodies; every
      definition and theorem statement lives in its node file, this
      slice only re-exports names.  Cross-segment consumers Require
      Import this slice; within-segment consumers go through node
      stems directly.
    Dependencies.  The five node stems [GaC2_01_DirichletPartialSum],
      [GaC2_02_AbsConvTailBound], [GaC2_03_FiniteEulerProduct],
      [GaC2_04_EulerTailError], and [GaC2_05_EulerLimitAsm] of this
      development, held via [Require Export] (the only Export site a
      gamma file may hold; same-segment stems only; Stdlib: none
      required directly).
    References.  gamma_module_spec.md section 2.3 whitelist.
      Trans-supply scope: the exported stems re-export their own
      top-level namespaces (C2.01: 23 named items; C2.02 stem: 3;
      C2.03 stem: 25; C2.04: 9; C2.05: 6).  The C2.02 leaf faces (_a:
      47, _b: 24, _c: 19 named items), the certificate faces
      (C2.01_cert, C2.02_cert, C2.03_FiniteEulerProduct_cert) and the
      C2.03 companion leaves (_a/_b/_c_eq_shim/_d/_e/_f) load
      transitively but are NOT re-exported, because no existing
      cross-segment consumer position names them (LINT-3
      consumer-position discipline: export only on a real consumer
      position); further rows are added on demand.
    Constructivity.  This file adds no statements, hence zero assumed
      constants and no computational content; Print Assumptions of
      every trans-supplied item is inherited Closed from the node
      files; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_Iface_DS.v] compiles cleanly (exit 0), wrapped
      by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3
      -GearForce 0 -CoreN 2). *)

(* ---- C2.01: GaC2_01_DirichletPartialSum -- the finite Dirichlet          *)
(*      partial-sum carrier of the zeta series. 23 named items.             *)
(*      Consumer face (Section DirichletPartialSum discharge; Section       *)
(*      premise Hnpos : forall n, NatLe 1 n -> 0 < nat_real n):             *)
(*        c_powq / c_zeta_part / c_tail / c_powq_plus_law /                 *)
(*        c_powq_norm_sq / c_tail_zero_le / c_zeta_part_tail_eq  (7 items)  *)
(*      Node-internal global helpers (16 items):                            *)
(*        c_of_real / nat_real / NatLe_one_S / NatLe_1_zero_empty /         *)
(*        cRe_wd / c_scale_wd / c_exp_wd / c_norm_sq_via_conj /             *)
(*        c_plus_conj_real / c_scale_plus / c_mult_distrib_l /              *)
(*        cRe_mult_wd / c_plus_zero_r / c_powq_arg_face /                   *)
(*        c_inv_wit / c_inv_wit_correct                                     *)
Require Export GaC2_01_DirichletPartialSum.

(* ---- C2.02: GaC2_02_AbsConvTailBound -- absolute convergence with        *)
(*      an explicit tail bound, Cauchy condensation route. 3 named items,   *)
(*      Section AbsConvMain discharge (premises Hnpos / sig / Hsig1 /       *)
(*      Hlnmono / Hln2pos / Hnormtri; slot L-C2.02-C under Hnormtri is the  *)
(*      open supply face):                                                  *)
(*        condensation_tail_bound / zeta_part_cauchy_bound /                *)
(*        tail_bound_uniform                                                *)
(*      Leaf faces _a/_b/_c and the certificate face load transitively      *)
(*      (see header: not re-exported).                                      *)
Require Export GaC2_02_AbsConvTailBound.

(* ---- C2.03: GaC2_03_FiniteEulerProduct -- the finite Euler product       *)
(*      main identity, prime-table form.  25 named items, Section           *)
(*      FiniteEulerProduct discharge (premise Hnpos):                       *)
(*        dpow / R_N (2 Definitions)                                        *)
(*        eblock / eprod / prodf_pow (3 Fixpoints)                          *)
(*        dpow_dfun / dpow_mult_law / dpow_one / eblock_S / eprod_cons /    *)
(*        cxsum_add / cxsum_range_eq / cxsum_split_le / prodf_pow_cons /    *)
(*        prodf_pow_ge1 / prime_list_fresh / dsum_step_fresh /              *)
(*        dsum_pow_split / eprod_eq_dsum / prodf_pow_fold /                 *)
(*        prodf_pow_eq_hl_lcm / fin_euler_prod_eq_dsum /                    *)
(*        c_zeta_part_cxsum / zeta_part_add_R_N / zeta_part_sub_dsum        *)
(*      (20 Lemmas; M1 = fin_euler_prod_eq_dsum, M2 = prodf_pow_eq_hl_lcm;  *)
(*      the peel faces live in GaC2_03_f and load transitively; the         *)
(*      numeric certificate face GaC2_03_FiniteEulerProduct_cert loads      *)
(*      transitively, not re-exported).                                     *)
Require Export GaC2_03_FiniteEulerProduct.

(* ---- C2.04: GaC2_04_EulerTailError -- the partial-product error          *)
(*      estimate.  9 named items, Section                                   *)
(*      EulerTailError discharge (premises Hnpos / sig / Hsig1; zero new    *)
(*      GAPASUME slots -- the real-part carrier, Hnormtri-free):            *)
(*        g2_hlnmono / g2_hln2pos (2 L0-slot castings, Section-external)    *)
(*        r_stail (1 Fixpoint)                                              *)
(*        r_npow_pos / r_stail_le_rtail / cRe_R_le_stail /                  *)
(*        smooth_tail_condensation / euler_tail_error_bound /               *)
(*        zeta_part_add_R_N_stem (6 Lemmas)                                 *)
Require Export GaC2_04_EulerTailError.

(* ---- C2.05: GaC2_05_EulerLimitAsm -- the Euler limit assembly,           *)
(*      honest finite face.  6 named items,                                 *)
(*      Section EulerLimitAsm discharge (premises Hnpos / sig / Hsig1):     *)
(*        r_zeta_seq (1 Definition)                                         *)
(*        cRe_cxsum_dpow_tsum / r_zeta_seq_eq_cRe / r_zeta_diff_eq /        *)
(*        prod_zeta_diff / prod_zeta_diff_real (5 Lemmas)                   *)
(*      The lim main theorem is the open supply face (the                   *)
(*      m1sig-vanishing analysis face); the Cauchy difference clause        *)
(*      (r_zeta_diff_eq) and the difference identity (prod_zeta_diff)      *)
(*      are the re-exported consumption carriers for its completion.        *)
Require Export GaC2_05_EulerLimitAsm.
