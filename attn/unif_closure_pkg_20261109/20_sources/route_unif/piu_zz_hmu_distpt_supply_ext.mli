
type __ = Obj.t

type empty_set = |

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val max : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

val gmin : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1

module Nat :
 sig
  val pred : nat -> nat

  val leb : nat -> nat -> bool

  val max : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val size_nat : positive -> nat

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val inject_Z : z -> q

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qred : q -> q

val qabs : q -> q

val qmin : q -> q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

type qseq = nat -> q

val qlt_bool : q -> q -> bool

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

val qltT_0_1 : qltT

val qltT_0_2 : qltT

val qltT_0_3 : qltT

val qleT'_refl : q -> qleT'

val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT'

val qltT_leT' : q -> q -> qltT -> qleT'

val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT

val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT'

val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT

val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT

val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_mult_ltT_compat :
  q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT

val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT

val qeq_leT' : q -> q -> qleT'

type qeqT = bool id

val qeq_imp_qeqT : q -> q -> qeqT

val qabs_nonnegT : q -> qleT'

val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT

val qltT_div_pos : q -> q -> qltT -> qltT -> qltT

val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT

val qltT_eq_compat_r : q -> q -> q -> qltT -> qltT

val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

val real_plus : real -> real -> real

val real_opp : real -> real

val real_zero : real

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

val real_lt_trans : real -> real -> real -> real_lt -> real_lt -> real_lt

val sum_abs_prefix : qseq -> nat -> q

val cauchy_bounded : qseq -> cauchy -> q

val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT

val real_mult : real -> real -> real

val real_const : q -> real

val q_arch_inv : q -> (nat, __) sigT

val real_eq_refl : real -> real_eq

val real_eq_sym : real -> real -> real_eq -> real_eq

val real_eq_trans : real -> real -> real -> real_eq -> real_eq -> real_eq

val real_one : real

val real_eq_of_zero_diff : real -> real -> real_eq

val real_plus_comm : real -> real -> real_eq

val real_plus_assoc : real -> real -> real -> real_eq

val real_plus_zero : real -> real_eq

val real_plus_opp : real -> real_eq

val real_mult_comm : real -> real -> real_eq

val real_mult_assoc : real -> real -> real -> real_eq

val real_mult_one : real -> real_eq

val real_mult_zero : real -> real_eq

val real_distrib : real -> real -> real -> real_eq

val real_le_refl : real -> real_le

val real_lt_eq_lt : real -> real -> real -> real_lt -> real_eq -> real_lt

val real_eq_lt_lt : real -> real -> real -> real_eq -> real_lt -> real_lt

val real_le_trans : real -> real -> real -> real_le -> real_le -> real_le

val real_lt_le_trans : real -> real -> real -> real_lt -> real_le -> real_lt

val real_le_lt_trans : real -> real -> real -> real_le -> real_lt -> real_lt

val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le

val real_lt_plus_compat :
  real -> real -> real -> real -> real_lt -> real_lt -> real_lt

val q_pow : q -> nat -> q

val q_fact : nat -> q

val exp_partial : nat -> q -> q

val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT

val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT

val exp_partial_cauchy : q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT

val exp_series : nat -> q -> q

val exp_partial_cauchy_bounded :
  q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q -> qleT'
  -> qltT) sigT

val exp_series_arch : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val cauchy_real_exp : real -> real

val cauchy_real_exp_zero : real_eq

val sum_upto : nat -> (nat -> q) -> q

val exp_partial_tail_small : q -> q -> qleT' -> qleT' -> (nat, __) sigT

val cauchy_real_exp_pos : real -> real_lt

val real_abs : real -> real

val real_metric : real -> real -> real

val real_inv_pos : real -> real_lt -> real

val real_inv_pos_correct : real -> real_lt -> real_eq

val real_inv_pos_pos : real -> real_lt -> real_lt

module RealSetoid :
 sig
  val real_eq_le : real -> real -> real_eq -> real_le

  val real_lt_le_iff_req : real -> real -> (real_lt, real_eq) or0 -> real_le

  val real_eq_plus_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_opp_compat : real -> real -> real_eq -> real_eq

  val real_eq_mult_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_abs_compat : real -> real -> real_eq -> real_eq

  val real_lt_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_lt -> real_lt

  val real_le_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_le -> real_le

  val real_le_id_l : real -> real -> real -> real_eq -> real_le -> real_le

  val real_le_id_r : real -> real -> real -> real_eq -> real_le -> real_le
 end

val exp_trunc_arch_seq :
  (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
  qleT') -> qltT -> (nat, nat -> __ -> qltT) sigT

val cauchy_real_exp_plus : real -> real -> real_eq

val cauchy_real_exp_gt_one : real -> real_lt -> real_lt

val real_lt_opp_plus : real -> real -> real_lt -> real_lt

val real_mult_pos_compat : real -> real -> real_lt -> real_lt -> real_lt

val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt

val real_lt_zero_minus : real -> real -> real_lt -> real_lt

val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq

val real_mult_minus_factor : real -> real -> real_eq

val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt

val real_arch : real -> (nat, (__, real_lt) and0) sigT

val cauchy_real_exp_gt_const : nat -> real_lt

val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt

val real_inv_unique : real -> real -> real -> real_eq -> real_eq -> real_eq

val exp_neg_recip : real -> real_lt -> real_eq

val real_const_pos : q -> qltT -> real_lt

val real_inv_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val q_eps16_posT : q -> qltT

val log_testA_eps : real -> q -> q -> q -> bool

val log_testB_eps : real -> q -> q -> q -> bool

val log_m_eps : q -> q -> q

val log_d4_eps : q -> q

val log_K1_eps : q -> q -> q -> nat

val log_K2_eps : real -> q -> q -> q -> nat

val log_q_eps : q -> q -> q -> q

val log_r_eps : real -> q -> q -> q -> q

val log_testA_eps_true_lt : real -> q -> q -> q -> real_lt

val log_testB_eps_true_gt : real -> q -> q -> q -> real_lt

val log_scan :
  real -> q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod

val log_scan_spec :
  real -> q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt,
  (real_lt, qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0

val exp_lower_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT

val exp_upper_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT

val log_lower : real -> real_lt -> q

val log_upper : real -> real_lt -> q

val q_pow_arch : q -> q -> (nat, __) sigT

val real_const_lt : q -> q -> real_lt

val real_lt_pt_lt : real -> real -> real_lt -> (nat, __) sigT

val exp_const_lt : q -> q -> real_lt

val approx_span_pt :
  real -> q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> (nat,
  __) sigT

val real_abs_lift : q -> real -> q -> q -> nat -> real_lt

val approx_def_test : real -> q -> q -> nat -> real_lt

val approx_root :
  real -> real_lt -> q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT

val log_eps : nat -> q

val log_seq : real -> real_lt -> nat -> q

val approx_root_pt_bound : real -> real_lt -> nat -> (nat, __) sigT

val exp_pos_shape :
  real -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT

val log_seq_cauchy : real -> real_lt -> cauchy

val cw_log : real -> real_lt -> real

val exp_series_arch_shape : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val cw_log_exp_right : real -> real_lt -> real_eq

val real_lt_not_eq : real -> real -> real_lt -> real_eq not

val real_weak_trich : real -> real -> real_lt not -> real_lt not -> real_eq

val log_inv_one_thm : real_lt -> real_eq

val log_inv_mult_thm :
  real -> real -> real_lt -> real_lt -> real_lt -> real_eq

val real_mult_lt_compat :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_mult_lt_compat_l :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_inv_pos_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_lt_plus_translate : real -> real -> real -> real_lt -> real_lt

val real_lt_plus_compat_le_lt :
  real -> real -> real -> real -> real_le -> real_lt -> real_lt

val real_lt_plus_compat_lt_le :
  real -> real -> real -> real -> real_lt -> real_le -> real_lt

val real_log_lt_mono :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_le_plus_compat :
  real -> real -> real -> real -> real_le -> real_le -> real_le

val real_inv_pos_ext :
  real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_le_mult_compat :
  real -> real -> real -> real_lt -> real_le -> real_le

val real_le_mult_compat_weak :
  real -> real -> real -> real_le -> real_le -> real_le

val real_lt_mult_compat :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_lt_zero_one : real_lt

val real_plus_positive : real -> real -> real_lt -> real_lt -> real_lt

val real_mult_positive : real -> real -> real_lt -> real_lt -> real_lt

val real_min : real -> real -> real

val real_abs_zero_req : real_eq

val real_abs_mult_req : real -> real -> real_eq

val real_abs_pos_req : real -> real_lt -> real_eq

val real_abs_triangle_le_eps : real -> real -> real -> real_lt -> real_le

val real_min_pos : real -> real -> real_lt -> real_lt -> real_lt

val real_opp_plus : real -> real -> real_eq

val real_log : real -> real_lt -> real

val real_log_mult : real -> real -> real_lt -> real_lt -> real_eq

val real_log_one : real_lt -> real_eq

module RealInterfaceEnhancedMod :
 sig
  val real_exp_ge_linear_eps : real -> real -> real_lt -> real_le

  val real_log_le_linear_eps : real -> real -> real_lt -> real_lt -> real_le
 end

val real_opp_mult : real -> real -> real_eq

val real_opp_opp : real -> real_eq

val real_eq_mult_cancel_r :
  real -> real -> real -> real_lt -> real_eq -> real_eq

val real_inv_inv : real -> real_lt -> real_lt -> real_eq

val real_exp_neg_opp_log : real -> real_lt -> real_eq

val real_log_inv_one_inv : real -> real_lt -> real_lt -> real_eq

val real_log_wd : real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_succ_minus_one : real -> real_eq

val real_log_one_plus_le_eps : real -> real -> real_lt -> real_lt -> real_le

val real_log_div : real -> real -> real_lt -> real_lt -> real_eq

val real_succ_mult_inv : real -> real -> real_lt -> real_eq

val real_log_plus_diff :
  real -> real -> real_lt -> real_lt -> real_lt -> real_eq

val real_abs_lt_lower : real -> real -> real_lt -> real_lt

val real_two_pos_local : real_lt

val real_inv_minus_one_opp_noHt : real -> real_lt -> real_eq

val real_t_plus_inv_minus_one : real -> real_lt -> real_eq

val real_t_minus_log_bound : real -> real -> real_lt -> real_lt -> real_le

val real_quad_div_le_two_eps :
  real -> real -> real -> real_lt -> real_lt -> real_lt -> real_le

val real_min_lt_l : real -> real -> real -> real_lt -> real_lt

val real_min_lt_r : real -> real -> real -> real_lt -> real_lt

val real_half_x_mult_inv : real -> real_lt -> real_eq

val real_half_lt_one_plus_t : real -> real_lt -> real_lt

val real_t_abs_lt_half : real -> real -> real_lt -> real_lt -> real_lt

val real_abs_le_quad_ll :
  real -> real -> real -> real -> real -> real_lt -> real_lt -> real_lt ->
  real_lt -> real_lt -> real_le

val real_abs_le_quad_le :
  real -> real -> real -> real -> real -> real_lt -> real_eq -> real_lt ->
  real_lt -> real_lt -> real_le

val real_abs_le_quad_ee :
  real -> real -> real -> real -> real -> real_eq -> real_eq -> real_lt ->
  real_lt -> real_lt -> real_le

val real_abs_le_quad_el :
  real -> real -> real -> real -> real -> real_eq -> real_lt -> real_lt ->
  real_lt -> real_lt -> real_le

val real_abs_le_quad_eps :
  real -> real -> real -> real -> real -> real_le -> real_le -> real_lt ->
  real_lt -> real_lt -> real_le

val real_quad_t_le_h_eps :
  real -> real -> real -> real -> real_lt -> real_lt -> real_lt -> real_lt ->
  real_le

val real_abs_eq_compat : real -> real -> real_eq -> real_eq

val real_inv_proj : real -> real_lt -> (nat, __) sigT

val real_exp_le_inv_one_minus : real -> real_lt -> real_lt -> real_le

val sin_term : nat -> q -> q

val cos_term : nat -> q -> q

val sin_partial : nat -> q -> q

val cos_partial : nat -> q -> q

val sc_sin_partial_cauchy_bounded :
  q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q -> qleT'
  -> qltT) sigT

val sc_cos_partial_cauchy_bounded :
  q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q -> qleT'
  -> qltT) sigT

val cauchy_real_sin : real -> real

val cauchy_real_cos : real -> real

val lp_a : nat -> q

val lp_pair : nat -> q

val lp_odd : nat -> q

val lp_four : q

val cauchy_real_pi_leibniz : real

val real_pi_leibniz_gt_three : real_lt

val real_cos_three_halves_pos : real_lt

val real_cos_five_thirds_neg : real_lt

val real_sin_eq_compat : real -> real -> real_eq -> real_eq

val real_cos_eq_compat : real -> real -> real_eq -> real_eq

val real_cos_strict_decr :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val cos_partial_cauchy : q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT

val cos_K1_eps : q -> q -> nat

val cos_testA_eps : q -> q -> bool

val cos_testB_eps : q -> q -> bool

val cos_testA_eps_true_lt : q -> q -> real_lt

val cos_testB_eps_true_gt : q -> q -> real_lt

val cos_scan : q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod

val cos_scan_spec :
  q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt, (real_lt,
  qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0

val approx_span_pt_cos :
  q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> real_lt ->
  real_lt -> (nat, __) sigT

val cos_abs_lift : q -> q -> q -> nat -> real_lt

val approx_def_test_cos : q -> q -> nat -> real_lt

val approx_root_cos : q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT

val cos_zero_seq : nat -> q

val cos_root_pt_bound : nat -> (nat, __) sigT

val cos_seq_cauchy : q -> qltT -> (nat, nat -> nat -> __ -> __ -> qltT) sigT

val cos_seq_cauchyT :
  q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

val cos_pi_half : real

val real_cos_pi_half_zero : real_eq

val real_pi_geom : real

val cos_eq_zero_diag_bound : real -> real_eq -> q -> (nat, __) sigT

val real_lt_lower_pt : q -> real -> real_lt -> (nat, __) sigT

val real_lt_upper_pt : q -> real -> real_lt -> (nat, __) sigT

val real_pi_leibniz_lt_ten_thirds : real_lt

val cos_pi_half_unique_widened :
  real -> real_lt -> real_lt -> real_eq -> real_eq

val real_half_const_three : real_eq

val real_half_const_ten_thirds : real_eq

val real_half_pos : real_lt

val real_half_pi_leibniz_comm : real_eq

val real_pi_leibniz_half_lower : real_lt

val real_pi_leibniz_half_upper : real_lt

val real_two_half_one : real_eq

val real_double_half_cancel : real -> real_eq

val sc_add_sin_err_bound :
  q -> q -> qleT' -> qltT -> (nat, q -> q -> nat -> natLe -> qleT' -> qleT' ->
  qltT) sigT

val rs_add_sin : real -> real -> real_eq

val sc_add_cos_err_bound :
  q -> q -> qleT' -> qltT -> (nat, q -> q -> nat -> natLe -> qleT' -> qleT' ->
  qltT) sigT

val rs_add_cos : real -> real -> real_eq

val arctan_term : nat -> q -> q

val arctan_partial : nat -> q -> q

val cauchy_real_arctan : real -> (nat -> qleT') -> real

val real_sin_eq_cos_cos_double_zero : real -> real_eq -> real_eq

val real_two_mult_plus : real -> real_eq

val real_sin_eq_cos_cos_two_zero : real -> real_eq -> real_eq

val atan1_pt_bound : nat -> qleT'

val arctan_one_real : real

val real_const_half_four : real_eq

val real_half_four_mult : real -> real_eq

val channel_cos_double_zero : real_eq -> real_eq

val channel_w_eq_two_theta : real_eq -> real_eq

val channel_n5 : real_eq -> real_eq -> real_eq

val channel_w_lower : real_lt

val channel_w_upper_two : real_lt

val channel_w_eq_cos_pi_half : real_eq -> real_eq -> real_eq

val channel_two_w_eq_pi : real_eq

val channel_f1 : real_eq -> real_eq -> real_eq

val a3_h4_value_bridge : real_eq

val real_const_pos_f1 : q -> real_lt

val b3r_one_sq_real_pos : real -> real_lt

val b3rr_qdecay : q -> q -> (nat, __) sigT

val b3rr_dom_lt1 : real -> q -> (nat -> qleT') -> qleT' -> nat -> qleT'

val b3rr_C2 : q -> q

val b3rr_dom_r1 : real -> q -> (nat -> qleT') -> nat -> qleT'

type cw_unit = nat -> qleT'

val real_E : real -> cw_unit -> real

val real_E_one : real

val real_E_one_unfold : real_eq

val real_eq_minus_zero : real -> real -> real_eq -> real_eq

val b5b_const_one_mult : real -> real_eq

val b5b_hsc_main : real_eq -> real_eq

val b5b_arch2 : (q, (qleT', nat -> qleT') and0) sigT

val b5b_ap_uniform : q -> (nat, (q, (qltT, __) and0) sigT) sigT

val b5b_unit_const : q -> cw_unit

val b5a_QltT_eq_r : q -> q -> q -> qltT -> qltT

val b5a_q_half_lt_one_plus_sq_T : q -> qltT

val b5a_one_plus_sq_pos : real -> real_lt

val b5a_E : real -> (nat -> qleT') -> real

val b5a_S : real -> real

val b5a_sin_wd_exact : real -> real -> real_eq

val b5a_atan_d : real -> real

val b5a_comp_err_sin :
  real -> (nat -> qleT') -> real -> (nat -> qleT') -> real

val b5a_comp_err_cos :
  real -> (nat -> qleT') -> real -> (nat -> qleT') -> real

val b5c_const_unit : q -> nat -> qleT'

val b5c_unit_zero : nat -> qleT'

val b5c_S_pos : real -> real_lt

val b5c_J : real -> (nat -> qleT') -> real

val b5c_sin_zero : real_eq

val b5c_E_zero_at_zero : (nat -> qleT') -> real_eq

val b5c_J_zero_at_zero : (nat -> qleT') -> real_eq

val b5c_d_proj_le_one : real -> (nat, __) sigT

val b5i_An : real -> nat -> q

val b5i_Ahn : real -> real -> nat -> q

val b5i_vn : real -> real -> nat -> q

val b5i_addcol_sin : real -> real -> (nat -> qleT') -> nat -> q

val b5i_h_le_enk : real -> real -> q -> real_lt -> qltT -> (nat, __) sigT

val b5i_h_le_const : real -> q -> real_lt -> qltT -> (nat, __) sigT

val b5i_abs_le_pointwise :
  real -> real -> real_le -> real -> real_lt -> (nat, __) sigT

val b5i_one_plus_eps2_pos : real -> q -> real_lt -> qltT -> real_lt

val b5i_h_inv_quarter : real -> real -> real_lt -> real_lt -> (nat, __) sigT

val b5i_rs_addcol :
  real -> (nat -> qleT') -> real -> (nat -> qleT') -> q -> qltT -> (nat, nat
  -> natLe -> qltT) sigT

val b4_abs_le_forall_eps_eq :
  real -> real -> (real -> real_lt -> real_le) -> real_eq

val b5b_E_close_q : q -> (nat, (q, (qltT, __) and0) sigT) sigT

val b5b_ep_xg_pos : q -> real_lt

val b5b_ep_xg_lt_one : q -> real_lt

val b5b_endpoint :
  (real -> cw_unit -> real_lt -> real_lt -> real_eq) -> real_eq

val b5b_hsc_theorem :
  (real -> cw_unit -> real_lt -> real_lt -> real_eq) -> real_eq

val b5n_h_pts :
  real -> real -> q -> q -> real_lt -> qltT -> qltT -> real_lt -> real_lt ->
  real_lt -> (nat, nat -> natLe -> (qleT', (qleT', qleT') and0) and0) sigT

val b5n_eps_proj_lt : real -> real_lt -> (q, (qltT, (nat, __) sigT) and0) sigT

val b5c_inv_pos_cert_eq : real -> real_lt -> real_lt -> real_eq

val b5d_addcol_cos : real -> real -> (nat -> qleT') -> nat -> q

val b5d_rs_addcol_cos :
  real -> (nat -> qleT') -> real -> (nat -> qleT') -> q -> qltT -> (nat, nat
  -> natLe -> qltT) sigT

val b5e_E_err : real -> (nat -> qleT') -> real -> (nat -> qleT') -> real

val b5e_E_dec_proj :
  real -> (nat -> qleT') -> real -> (nat -> qleT') -> (nat, __) sigT

val b5f_g : real -> real

val b5f_v : real -> real -> real

val b5f_g_S : real -> real_eq

val b5f_S_xh_eq : real -> real -> real_eq

val b5f_S_err_decomp : real -> real -> real_eq

val b5f_u : real -> real

val b5f_Du : real -> real -> real

val b5f_LogErr : real -> real -> real

val b5f_u_Du_eq : real -> real -> real_eq

val b5f_u_plus_Du_pos : real -> real -> real_lt

val b5f_Du_act_delta :
  q -> real -> (nat -> qleT') -> real -> real -> real_lt -> real_lt -> real_lt
  -> real_lt

val b5j_kL : q

val b5j_kL_posT : qltT

val b5j_Sx_abs_pos : real -> real_lt

val b5j_Kvq : q -> q

val b5j_real_const_mult_eq : q -> q -> real_eq

val b5j_real_le_m_pts :
  real -> real -> real -> real_le -> real_lt -> (nat, __) sigT

val b5j_v_abs_bd :
  q -> real -> (nat -> qleT') -> real -> real -> real_lt -> (real -> real_lt
  -> real_le) -> real_lt -> real_le

val b5j_lin_shape_eq : real -> real_eq

val b5j_v_act_lt :
  q -> real -> (nat -> qleT') -> real -> real -> real_lt -> (real -> real_lt
  -> real_le) -> real_lt -> real_lt -> real_lt

val b5j_real_const_req : q -> q -> real_eq

val b5j_qinv_kvq_req : q -> real_eq

val b5j_mult_plus_distr_eq : real -> real -> real -> real_eq

val b5j_fourth_threefourth_sum : real -> real_eq

val b5j_eps0_kvq_req : q -> real -> real -> real_eq

val b5j_eps0_shv_req : q -> real -> real -> real -> real_lt -> real_eq

val b5k_S_gt_one_cert : real -> real_lt -> real_lt

val b5k_S_ge_one_cert : real -> real_lt -> (nat, __) sigT

val b5k_S_ge_one_pos : real -> real_lt -> (nat, __) sigT

val b5a_S_ge_one : real -> real_lt -> (nat, __) sigT

val b5l_k_posT : q -> qltT

val b5l_eq_abs_tri :
  real -> real -> real -> q -> real_eq -> qltT -> (nat, __) sigT

val b5m_rS : real -> real -> real

val b5m_S_pos_pt : real -> (q, (qltT, (nat, __) sigT) and0) sigT

val b5m_J_dec_proj :
  real -> real -> (nat -> qleT') -> (nat -> qleT') -> (nat, __) sigT

val b5m_S_wd : real -> real -> real_eq -> real_eq

val b5p2_E_eq_J_S : real -> cw_unit -> real_eq

val b5p2_E_zero_of_J_zero : real -> cw_unit -> real_eq -> real_eq

val b5p2_arctan_wd : real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq

val b5p2_E_wd : real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq

val b5p2_S_wd : real -> real -> real_eq -> real_eq

val b5p2_J_wd : real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq

val b5d1_b3rr_atan_deriv_lin :
  q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
  real_lt -> (nat -> qleT') -> real -> real_lt -> real_le) and0) sigT

val b5dD_atan_deriv_b5a_r_exp :
  q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
  real_lt -> (nat -> qleT') -> real -> real_lt -> real_le) and0) sigT

val b5dD_vdh_pts_r_exp :
  q -> real -> (nat -> qleT') -> real -> real_lt -> q -> q -> qltT -> qltT ->
  (real, (real_lt, real -> real_lt -> (nat -> qleT') -> real -> real_lt ->
  (nat, __) sigT) and0) sigT

val b5dM_real_const_pos : q -> qltT -> real_lt

val b5dM_b5i_one_plus_eps2_pos : real -> q -> real_lt -> qltT -> real_lt

val b5dM_b5n_eps_proj_lt :
  real -> real_lt -> (q, (qltT, (nat, __) sigT) and0) sigT

val b5dM_b5c_d_proj_le_one : real -> (nat, __) sigT

val b5dI_inv_leaf_witness_eq : real -> q -> real_lt -> qltT -> real_eq

val b5dI_real_mult_positive_exp :
  real -> real -> real_lt -> real_lt -> real_lt

val b5dI_sin_atan_diff_closed_r_exp :
  q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
  real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
  real -> real_lt -> real_le) and0) sigT

val b5dI_cos_atan_diff_closed_r_exp :
  q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
  real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
  real -> real_lt -> real_le) and0) sigT

val b5dI_E_diff_closed_r_exp :
  q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
  real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
  real -> real_lt -> real_le) and0) sigT

val b5dJ_two_pos_exp : real_lt

val b5dJ_log_diff_dx_exp :
  real -> real_lt -> real -> real_lt -> (real, (real_lt, real -> real_lt ->
  real_lt -> real -> real_lt -> real_le) and0) sigT

val b5dJ_LogErr_delta_exp :
  real -> real -> real_lt -> (real, (real_lt, real -> real -> real_lt ->
  real_lt -> real_le) and0) sigT

val b5d3_exp_arch4_C : q

val b5d3_exp_arch4_C_ge1 : qleT'

val b5d3_exp_arch4_C_all : nat -> qleT'

val b5dK_real_mult_positive_exp :
  real -> real -> real_lt -> real_lt -> real_lt

val b5dK_real_abs_plus_one_pos_exp : real -> real_lt

val b5dK_real_abs_scaling_le_exp :
  real -> real -> real -> real -> real_lt -> real_lt -> real_le

val b5dK_exp_minus_one_linear_closed_exp :
  real -> real_lt -> (real, (real_eq, (real_lt, real -> real_lt -> real ->
  real_lt -> real_le) and0) and0) sigT

val b5dK_gdiff_pts_r_exp :
  q -> real -> (nat -> qleT') -> real -> real_lt -> q -> q -> qltT -> qltT ->
  (real, (real_lt, real -> real_lt -> real -> real_lt -> (nat, __) sigT) and0)
  sigT

val b5dK_exp_part_bound_closed_r_exp :
  q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
  real_lt -> real -> real_lt -> real_le) and0) sigT

val b5d4_const0_eq_zero : real_eq

val b5d4_S_const0_eq_one : real_eq

val b5dE_const1_eq_one : real_eq

val b5dE_q_pos : q -> real_lt

val b5dE_half_pos_real : real_lt

val b5dE_log_ub_one : q -> real_lt

val b5dE_S_lt_exp_half : q -> real_lt

val b5dE_exp_half_le_two : real_le

val b5dE_S_ub_tail_q : q -> (nat, __) sigT

val b5dH_E_eq_b5aE : real -> cw_unit -> real_eq

val b5dH_J_zero0 : real_eq

val b5dH_E_zero_of_J_zero : real -> cw_unit -> real_eq -> real_eq

val b5dH_real_const_qeq : q -> q -> real_eq

val b5dH_plus_const_eq : q -> q -> real_eq

val b5dL_tkq : q -> nat -> nat -> q

val b5dL_qdiv : q -> nat -> q

val b5dL_Qnsum : (nat -> q) -> nat -> q

val b5dL_tkC : q -> nat -> nat -> cw_unit

val b5dL_abs_const : q -> real_eq

val b5dL_mult_const : q -> q -> real_eq

val b5dL_bk : q -> nat -> q -> nat -> q

val b5dL_epsQ1 : nat -> q -> q

val b5dL_J_grid_premise :
  q -> nat -> (nat -> q) -> (nat -> q) -> (nat -> __ -> cw_unit -> cw_unit ->
  real_le) -> cw_unit -> cw_unit -> real_le

val b5dL_eps_real_lower : real -> real_lt -> (q, (qltT, real_le) and0) sigT

val b5dL_J_zero_on_grid_premise :
  q -> nat -> q -> (nat -> __ -> cw_unit -> cw_unit -> real_le) -> cw_unit ->
  real_le

val b5dL_E_rational_zero_premise :
  q -> (q -> __ -> (nat, (natLe, nat -> __ -> cw_unit -> cw_unit -> real_le)
  and0) sigT) -> cw_unit -> real_eq

val b5dP_S_diff_closed_r_M_exp_tail :
  q -> real -> (nat -> qleT') -> q -> nat -> real -> real_lt -> (real,
  (real_lt, real -> real_lt -> real -> real_lt -> real_le) and0) sigT

val b5dQ_min_lb : real -> real -> real -> real_lt -> real_lt -> real_lt

val b5dQ_Hq32T : qltT

val b5dQ_chain3 : q -> q

val b5dQ_chain4 : q -> q

val b5dQ_vB : q -> q -> q

val b5dQ_margin_lemma : q -> qltT

val b5dQ_vSC : q -> q -> q

val b5dQ_vE : q -> q -> q

val b5dQ_lb_E : q -> real -> (nat -> qleT') -> q -> real_lt

val b5dQ_Hq14T : qltT

val b5dQ_Hq1T : qltT

val b5dQ_S_tk0_eq_one : q -> nat -> real_eq

val b5dQ_S_lb_tail_k0 : q -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_k0 : q -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_restate : (nat -> q) -> (nat, __) sigT -> (nat, __) sigT

val b5dQ_S_lb_tail_kS : q -> nat -> nat -> (nat, __) sigT

val b5dQ_S_ub_tail_kS : q -> nat -> nat -> (nat, __) sigT

val b5dQ_tkq_Hxr : q -> nat -> nat -> nat -> qleT'

val b5dQ_xph_unit : q -> nat -> nat -> cw_unit

val b5dQ_rhs_bk : q -> nat -> nat -> q -> real_eq

val b5dQ_J_tk_succ_bridge : q -> nat -> nat -> cw_unit -> cw_unit -> real_eq

val b5dQ_J_cert_wd : q -> cw_unit -> cw_unit -> real_eq

val b5dQ_step_inst :
  q -> nat -> nat -> (nat -> qleT') -> cw_unit -> cw_unit -> cw_unit -> real
  -> real_le -> real_le

val b5dQ_lbSdiff_cE : q -> q -> q

val b5dQ_lbSdiff_cG : q -> q -> q

val b5dQ_lbSdiff_cS : q -> q -> q

val b5dQ_lbSdiff_val : q -> q -> q

val b5dQ_lb_Sdiff : q -> real -> (nat -> qleT') -> q -> nat -> real_lt

val b5dQ_tau : q -> q

val b5dQ_kS : q -> q

val b5dQ_m4 : q -> q -> q

val b5dQ_delta0 : q -> q -> q

val b5dQ_p4g_leaf_E : q -> real -> (nat -> qleT') -> q -> real_lt

val b5dQ_p4g_leaf_S : q -> real -> (nat -> qleT') -> q -> nat -> real_lt

val b5dQ_p4g_J_tail_lb_var :
  q -> q -> nat -> nat -> (nat -> qleT') -> nat -> nat -> (real, (real_lt,
  (real -> real_lt -> (nat -> qleT') -> real -> real_lt -> real_le, real_lt)
  and0) and0) sigT

val b5dQ_Hstep :
  q -> q -> nat -> nat -> (nat -> qleT') -> nat -> nat -> cw_unit -> cw_unit
  -> real_le

val b5dQ_Hmod :
  q -> q -> (nat, (natLe, nat -> __ -> cw_unit -> cw_unit -> real_le) and0)
  sigT

val b5dQ_E_rational_zero : q -> cw_unit -> real_eq

val b5dS_E_pair_close : q -> (nat, (q, (qltT, __) and0) sigT) sigT

val b5dS_E_zero_on_unit : real -> cw_unit -> real_lt -> real_lt -> real_eq

type qltT' = bool id

val qlt_to_QltT' : q -> q -> qltT'

val lw0m_xL : nat -> q

val lw0m_metric_congr : real -> real -> real -> real_eq -> real_eq

val lw2_channel_f1_closed : real_eq

val leibsep_metric_pi_transport :
  q -> q -> qltT -> (nat, nat -> natLe -> qltT) sigT

val lw1m_height : q -> nat

type lw1m_dist_pt = (nat, nat -> natLe -> qltT') sigT

val piu1932_ck_alpha : q -> nat -> q -> q

type piu_mu_QleT =
| Piu_mu_QleT_i

type piu_mu_ZleT =
| Piu_mu_ZleT_i

type ('s1, 's2) piu_mu_and2 =
| Piu_mu_and2_i of 's1 * 's2

type ('s1, 's2, 's3) piu_mu_and3 =
| Piu_mu_and3_i of 's1 * 's2 * 's3

val piu_mu_mult_le_r_inv : q -> q -> q -> piu_mu_QleT

val piu_zz_c0_criterion : q

val piu_zz_mu_kappa : q

val piu_zz_mu_qpow_inject : nat -> q -> q -> qleT' -> qleT'

val piu_zz_realcert_of_distpt : q -> q -> q -> qltT -> lw1m_dist_pt -> real_lt

val piu_zz_Hmu_rateslot_of_distpt :
  q -> (q, (qltT, lw1m_dist_pt) and0) sigT -> real_lt

val piu_zz_ec_mu_cond :
  (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
  -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT, piu_mu_ZleT)
  piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT, piu_mu_ZleT,
  piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z -> __ -> (nat,
  nat -> __ -> qleT') sigT) -> q -> real_lt

type piu_zz_n2b_hcoef17_A = nat -> qleT'

val piu_zz_s2_w1 : q

val piu_zz_s2_w2 : q

val piu_zz_s2_w3 : q

val piu_zz_s2_regime_splice :
  (nat -> q) -> (nat -> qleT' -> qleT' -> qleT') -> (nat -> qleT' -> qleT' ->
  qleT') -> (nat -> qleT' -> qleT') -> nat -> qleT' -> qleT'

val piu_zz_s2_head_maxform :
  (nat -> q) -> (nat -> qleT' -> qleT' -> qleT') -> (nat -> qleT' -> qleT' ->
  qleT') -> (nat -> qleT' -> qleT') -> (nat -> qleT' -> qleT' -> qleT') -> nat
  -> (qleT', qleT') sum

type piu_zz_s2_head_combined_face =
  (piu_zz_n2b_hcoef17_A, (nat -> qleT' -> qleT' -> qleT', nat -> qleT' ->
  qleT' -> qleT', nat -> qleT' -> qleT') piu_mu_and3) piu_mu_and2

val piu_zz_ec_nescD : nat -> nat

val piu_zz_ec_escwin_limb1_Q : nat -> piu_mu_QleT

val piu_zz_ec_escwin_limb3_Q : nat -> piu_mu_QleT

type piu_zz_ec_HescD_face =
  (nat, (piu_mu_QleT, piu_mu_ZleT, piu_mu_QleT) piu_mu_and3) sigT

val piu_zz_ec_HescD_of_window :
  (nat -> z) -> (nat -> z) -> z -> nat -> piu_mu_ZleT -> piu_zz_ec_HescD_face

val piu_zz_hmu_kappa_c0 : qeqT

val piu_zz_hmu_c0_inv : qeqT

val piu_zz_hmu_qpow_inject_alpha8 : q -> q -> qleT' -> qleT'

val piu_zz_hmu_qpow_inject_tau2 : q -> q -> qleT' -> qleT'

val piu_zz_hmu_distpt_of_realcert :
  q -> q -> real_lt -> (q, (qltT, lw1m_dist_pt) and0) sigT

val piu_zz_hmu_distpt_supply :
  (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
  -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT, piu_mu_ZleT)
  piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT, piu_mu_ZleT,
  piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z -> __ -> (nat,
  nat -> __ -> qleT') sigT) -> q -> (q, (qltT, lw1m_dist_pt) and0) sigT

val piu_zz_hmu_realcert_of_chain :
  (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
  -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT, piu_mu_ZleT)
  piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT, piu_mu_ZleT,
  piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z -> __ -> (nat,
  nat -> __ -> qleT') sigT) -> q -> real_lt

val piu_zz_hmu_n5_hescd_contract :
  (nat -> z) -> (nat -> z) -> z -> nat -> piu_mu_ZleT -> piu_zz_ec_HescD_face

val piu_zz_hmu_n4_maxform_of_combined :
  (nat -> z) -> (nat -> z) -> (nat -> q) -> piu_zz_s2_head_combined_face ->
  (nat -> qleT' -> qleT' -> qleT') -> nat -> (qleT', qleT') sum
