(* ConstructiveWorld-Main - the real-line slice interface of the C1 segment. *)
(** * GaC1_Iface_Real: the C1 real-line slice interface.
    Mission.  The C1 real-line slice interface for cross-segment
      consumers: re-exports the six C1.1/C1.2 node stems.  Interface
      form only: [Require Export] plus a named-item index; zero
      proofs, zero definitions.  Named items (index):
      RB carriers [GaC1_RB01_RealLeB] ([real_le_b], the Bishop-form
      order), [GaC1_RB02_RealLeToLeB] ([real_le_to_le_b], one-way
      bridge), [GaC1_RB03_LogLeLinearB] ([real_log_le_linear_B]);
      C1-01 [GaC1_01_LogMono]: [gaC1_01_log_lt_mono],
      [gaC1_01_log_le_mono], [gaC1_01_log_le_linear_B];
      C1-02 [GaC1_02_LogPowBridge]: [g2_ipow]/[real_ipow]/
      [real_ipow_pos], [gaC1_02_log_ipow], [gaC1_02_log_exp],
      [gaC1_02_log_le_x]; C1-03 [GaC1_03_LogTelescope]:
      [g3_prod]/[sumR], [gaC1_03_log_prod], [gaC1_03_telescope],
      [gaC1_03_sumR_nonneg], craft le_b family;
      C1-04 [GaC1_04_QRealBridge]: [gaC1_04_const_margin],
      [gaC1_04_qltT_pointwise_transfer], [gaC1_04_qlt_const_lt],
      [gaC1_04_const_lt_qlt_down]; C1-05 [GaC1_05_RealPowRoot]:
      [kroot], [gaC1_05_kroot_pos], [gaC1_05_log_kroot],
      [gaC1_05_exp_inj], [gaC1_05_log_wd], [gaC1_05_log_inj],
      [gaC1_05_log_eq_transfer], [sqrtR], [gaC1_05_sqrt_sq],
      [gaC1_05_sqrt_unique]; C1-06 [GaC1_06_RealPowOrder]:
      [gaC1_06_kroot_le_mono], [gaC1_06_kroot_le_one_plus], Or-form
      craft family.
    Dependencies.  Stdlib: none required directly.  Requires, via
      [Require Export], [GaC1_RB01_RealLeB],
      [GaC1_RB02_RealLeToLeB], [GaC1_RB03_LogLeLinearB],
      [GaC1_01_LogMono], [GaC1_02_LogPowBridge],
      [GaC1_03_LogTelescope], [GaC1_04_QRealBridge],
      [GaC1_05_RealPowRoot], and [GaC1_06_RealPowOrder] of this
      development.
    References.  This development, the C1 segment modules re-exported
      here verbatim under their original names; consumers import this
      single slice instead of the underlying module list.
    Constructivity.  Interface only; zero assumed constants; nothing
      is defined here; closed under the global context transitively;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_Iface_Real.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

Require Export GaC1_RB01_RealLeB.
Require Export GaC1_RB02_RealLeToLeB.
Require Export GaC1_RB03_LogLeLinearB.
Require Export GaC1_01_LogMono.
Require Export GaC1_02_LogPowBridge.
Require Export GaC1_03_LogTelescope.
Require Export GaC1_04_QRealBridge.
Require Export GaC1_05_RealPowRoot.
Require Export GaC1_06_RealPowOrder.
