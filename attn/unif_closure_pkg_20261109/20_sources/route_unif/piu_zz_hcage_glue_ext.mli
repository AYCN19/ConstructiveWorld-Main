
type bool =
| True
| False

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val sub : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val eq_dec : nat -> nat -> sumbool
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val max : z -> z -> z

  val of_nat : nat -> z
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val le_lt_dec : nat -> nat -> sumbool

type q = { qnum : z; qden : positive }

val inject_Z : z -> q

val qmult : q -> q -> q

val qinv : q -> q

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

type 'a id =
| Id_refl

type qltT = bool id

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

type ('s1, 's2) piu_mu_and2 =
| Piu_mu_and2_i of 's1 * 's2

type piu_zz_c7_Casm_admissible = qleT'

val piu_zz_c7_tail_base_1348 : qleT'

val piu_zz_c7_tail_prev_violation_1347 : qltT

type piu_zz_ec_hcage_all_face = nat -> qleT'

type piu_zz_ec_hcage_N0_face = (qleT', qltT) piu_mu_and2

val piu_zz_hcg_casm_anchor : q -> piu_zz_c7_Casm_admissible -> qleT'

val piu_zz_hcg_A : q

val piu_zz_hcg_ushape_dn : q -> piu_zz_c7_Casm_admissible -> nat -> qleT'

val piu_zz_hcg_ushape_up : q -> piu_zz_c7_Casm_admissible -> nat -> qleT'

val piu_zz_hcg_casm_ushape : q -> piu_zz_c7_Casm_admissible -> nat -> qleT'

val piu_zz_hcg_hcage_all_glue :
  (nat -> q) -> q -> (nat -> qleT') -> piu_zz_c7_Casm_admissible ->
  piu_zz_ec_hcage_all_face

val piu_zz_hcg_hcage_head_glue :
  (nat -> q) -> q -> (nat -> qleT') -> piu_zz_c7_Casm_admissible -> nat ->
  qleT'

val piu_zz_hcg_hcage_tail_glue :
  (nat -> q) -> q -> (nat -> qleT') -> piu_zz_c7_Casm_admissible -> nat ->
  qleT'

val piu_zz_hcg_tail_absorb : nat -> qleT'

val piu_zz_hcg_hcage_n0_of_bank : piu_zz_ec_hcage_N0_face
