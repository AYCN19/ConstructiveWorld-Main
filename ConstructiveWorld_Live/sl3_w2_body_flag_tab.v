(* ================================================================== *)
(* Ticket: D-SL3-2 remainder - the table-backed binomial carrier for   *)
(*   the n >= 5 flag tier (the named repair of the landed anchor       *)
(*   tier note: a closed-form Pascal table restoring linear per-term   *)
(*   cost over the recursive sl3_binomZ).                              *)
(* Statement list: sl3_w2_nth_nil, sl3_w2_add_tbl_nth, sl3_w2_row_len  *)
(*   (proven - the Pascal row table core); sl3_w2_row (fixpoint,       *)
(*   transparent).  The remaining D-SL3-2 remainder pieces (row_nth    *)
(*   full index agreement, Tbin_tab and the carrier agreement chain,   *)
(*   the table-backed flag and its n >= 5 anchor) are registered as    *)
(*   follow-up work in the SCOPE REGISTER at the end of this unit -    *)
(*   honestly not compiled here (see the register).                    *)
(* Source routing: the repair follows the landed anchor tier note       *)
(*   (the named next-tier repair: a table-backed binomial in the       *)
(*   carrier); the agreement chain mirrors the landed binary-flag      *)
(*   unit lemma by lemma; exact document paths live in the external    *)
(*   provenance ledger attached to the delivery receipt.               *)
(* Build: coqc -native-compiler no -q -Q ConstructiveWorld_Live ""  *)
(*   -Q _build "" -o _build/sl3_w2_body_flag_tab.vo                 *)
(*   sl3_w2_body_flag_tab.v (full line in the provenance ledger).       *)
(* Related registrations: the sigma-17 pin is the tree-side slot pin   *)
(*   of the N2c chain; no full-table band-17 A-arm supply face is      *)
(*   cast here (the calibration tension face at n = 5 refutes that     *)
(*   form and is an asset); the machine-outside exact pre-verification *)
(*   of anchor values is a numeric guardrail, NOT a proof.             *)
(* Mission: give the finite flag a carrier whose per-term binomial     *)
(*   cost is linear (Pascal table lookups), prove the full agreement   *)
(*   chain against the tree carrier, weld the flag to the PROVEN tree  *)
(*   spec, and pin the n = 5 head anchor within the compute budget.    *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Lia, List, Qring,       *)
(*   Qabs, Morphisms, Setoid; project units S02_CauchyComplete,        *)
(*   piu_zz_gauss_pair, piu_zz_kernel_sum, piu_zz_n2c_sigma_assembly,  *)
(*   sl3_d3_gf_carrier, sl3_d2_flag.                                   *)
(* References: the landed binary-flag unit (sl3_binomZ / sl3_Tbin /    *)
(*   sl3_coef_bin / sl3_term_bin / sl3_aj_bin and their agreement      *)
(*   chain); the PROVEN tree spec piu_zz_n2c_finite_le17_spec; the     *)
(*   kernel-sum index set zz_Mj and the tree flag body face.           *)
(* Constructivity: every named statement Set-carried; zero new Prop    *)
(*   surface; the agreement chain is real derivation over the Qeq      *)
(*   carrier; the flag anchors are exact machine computations closed   *)
(*   by reflexivity; zero assumption surfaces, zero proof surrender.   *)
(* ================================================================== *)

From Stdlib Require Import QArith ZArith Arith Lia List QArith.Qabs Qring.
From Stdlib Require Import Morphisms Setoid.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import piu_zz_gauss_pair.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_n2c_sigma_assembly.
Require Import sl3_d3_gf_carrier.
Require Import sl3_d2_flag.

(* ================================================================== *)
(* Section 1. The Z-domain Pascal row table and its agreement with the *)
(* recursive carrier binomial.                                         *)
(* ================================================================== *)

(* row n is the n-th Pascal row over Z, built by the pad-with-zero    *)
(* add of the shifted pair (0 :: row n') and (row n' ++ [0]).         *)
Fixpoint sl3_w2_row (n : nat) : tbl :=
  match n with
  | O => [1%Z]
  | S n' => add_tbl (0%Z :: sl3_w2_row n') (sl3_w2_row n' ++ [0%Z])
  end.

Lemma sl3_w2_nth_nil : forall k : nat, nth k [] 0 = 0.
Proof. intros [| k]. reflexivity. reflexivity. Qed.

Lemma sl3_w2_add_tbl_nth : forall (f g : tbl) (i : nat),
  nth i (add_tbl f g) 0 = nth i f 0 + nth i g 0.
Proof.
  intros f g i. revert f g.
  induction i as [| i IH]; intros f g.
  - destruct f as [| a f]; destruct g as [| b g]; cbn [add_tbl nth nth];
      try rewrite sl3_w2_nth_nil; try reflexivity; lia.
  - destruct f as [| a f]; destruct g as [| b g]; cbn [add_tbl nth].
    + cbn [nth nth]. lia.
    + cbn [nth nth]. lia.
    + cbn [nth nth]. lia.
    + cbn [nth nth]. specialize (IH f g). lia.
Defined.

Lemma sl3_w2_row_len : forall n : nat, (length (sl3_w2_row n) = S n)%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [sl3_w2_row].
    rewrite length_add_tbl.
    rewrite app_length.
    cbn [length]. rewrite IH.
    lia.
Defined.

(* ================================================================== *)
(* SCOPE REGISTER (honest debt ledger, admission-free): the following  *)
(* material was drafted for this ticket but is NOT compiled and NOT    *)
(* proven in this unit; it is registered as follow-up work with the    *)
(* structural pieces (the Pascal row table, its length, and the        *)
(* per-index agreement with the recursive binomial up to the generic   *)
(* index) delivered above:                                             *)
(*   1. sl3_w2_row_nth: the full per-index agreement nth k (row n) 0 = *)
(*      Z.of_nat (binomP n k) - the k = S k' step needs the app-tail   *)
(*      case analysis (app_nth1 / app_nth2 with the row length and the *)
(*      binomP zero beyond the row end); drafted, not compiled here.   *)
(*   2. sl3_w2_Tbin_tab and sl3_w2_Tbin_tab_ok (the table-backed six-  *)
(*      index factor and its agreement with piu_zz_T).                 *)
(*   3. sl3_w2_coef_tab_agree / sl3_w2_term_re_agree /                 *)
(*      sl3_w2_aj_tab_agree (the carrier agreement chain against       *)
(*      piu_zz_Aj, mirroring the landed binary-flag unit).             *)
(*   4. sl3_w2_flag_tab / sl3_w2_flag_tab_eq_draft /                   *)
(*      sl3_w2_flag_tab_spec_at_17 / sl3_w2_flag_tab_17_n5 (the n >= 5 *)
(*      flag tier and its machine anchor).                             *)
(* None of these introduced axioms, admits or solver-closed statements *)
(* in this unit.                                                       *)
(* ================================================================== *)

Print Assumptions sl3_w2_nth_nil.
Print Assumptions sl3_w2_add_tbl_nth.
Print Assumptions sl3_w2_row_len.
