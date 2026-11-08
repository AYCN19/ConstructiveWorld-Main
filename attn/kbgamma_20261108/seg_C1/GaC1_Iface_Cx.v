(* ConstructiveWorld-Main - the complex-plane slice interface of the C1
   segment for cross-segment consumers. *)

(** * GaC1_Iface_Cx: the C1 complex-plane slice interface.

    Mission.  The C1 complex-plane slice interface for cross-segment
      consumers: re-exports the pair-carrier files under their
      original names, the shared Pythagorean block, and the four C1.4
      node stems.  Named items (index):
      RB carrier [GaC1_RB01_RealLeB] ([real_le_b], the Bishop-form
      order, consumed in the statement faces of C1-15/C1-16);
      C1-07..13 [CxRealPairCore] / [CxRealPairExpLog] (original
      names); [G1_PYTH]: [real_pyth_cos_sq_sin_sq],
      [real_sq_sin_pi_half_one], [real_sin_pi_half_one],
      [g1_plus_zero_l]; C1-14 [GaC1_14_SeriesCauchy]:
      [cxsum]/[cdiff]/[cxseries_cauchy]/[cxs_pointwise_cauchyQ],
      [gaC1_14_pointwise_to_cauchy],
      [gaC1_14_cauchy_to_pointwise_slack],
      [gaC1_14_norm_sq_pair_lt], Q-level helper family;
      C1-15 [GaC1_15_PowSeriesConv]: [rsum]/[rdif],
      [gaC1_15_tail_closed], [gaC1_15_cauchy], craft le_b/lt family;
      C1-16 [GaC1_16_CExpNorm]: [gaC1_16_norm_sq_exp],
      [gaC1_16_strip]; C1-17 [GaC1_17_TwoPiPeriod]:
      [pi_R]/[two_pi_R], [gaC1_17_sin_pi], [gaC1_17_cos_pi],
      [gaC1_17_sin_two_pi], [gaC1_17_cos_two_pi],
      [gaC1_17_sin_period], [gaC1_17_cos_period],
      [gaC1_17_two_pi_eq_geom].

    Dependencies.  Stdlib: none required directly.  Requires, via
      [Require Export], [GaC1_RB01_RealLeB], [CxRealPairCore],
      [CxRealPairExpLog], [G1_PYTH], [GaC1_14_SeriesCauchy],
      [GaC1_15_PowSeriesConv], [GaC1_16_CExpNorm], and
      [GaC1_17_TwoPiPeriod] of this development.

    References.  This development, the C1 segment modules re-exported
      here verbatim under their original names; consumers import this
      single slice instead of the underlying module list.

    Constructivity.  Interface only: zero proofs and zero definitions
      here; nothing is carried beyond the re-exported modules; closed
      under the global context transitively; [coqchk] reports zero
      assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_Iface_Cx.v] compiles cleanly (exit 0), wrapped
      by [cpu_guard v3]. *)

Require Export GaC1_RB01_RealLeB.
Require Export CxRealPairCore.
Require Export CxRealPairExpLog.
Require Export G1_PYTH.
Require Export GaC1_14_SeriesCauchy.
Require Export GaC1_15_PowSeriesConv.
Require Export GaC1_16_CExpNorm.
Require Export GaC1_17_TwoPiPeriod.
