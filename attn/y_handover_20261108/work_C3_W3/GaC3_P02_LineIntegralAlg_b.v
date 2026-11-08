(* ===================================================================== *)
(* GaC3_P02_LineIntegralAlg_b.v                                           *)
(*                                                                       *)
(* Mission: node C3-P02 (segment C3 wave W2) leaf slice - the orientation *)
(*   reversal law of the line integral (drafts P02 skeleton              *)
(*   line_integral_reverse): the reversed path (order reversed AND each  *)
(*   segment re-oriented), the reversal identity of both path-sum        *)
(*   components, and the Cx-level reverse law.  Split from the P02 stem  *)
(*   under the wave-internal leafing axis of the module spec section on  *)
(*   the 400-line budget (the stem held the path carrier, seeds, concat   *)
(*   and linear laws; this leaf consumes the stem by Require - no        *)
(*   mutual Require).                                                    *)
(* Dependencies: GaC3_P02_LineIntegralAlg (stem: path sums, concat, Cx    *)
(*   bridges), GaC3_P01_LineIntegralDef (Cx bridges over the rational    *)
(*   embedding), CxRealPairCore (born), S01_BaseRing, S02_CauchyComplete *)
(*   (real_eq_of_zero_diff).  Stdlib: QArith, List.                      *)
(* References: AFP Perron_Prerequisites (Eberl 2026-06-17) - reversal    *)
(*   is not a separate AFP item (path algebra implicit in HOL-Analysis); *)
(*   from-zero at the step carrier.  Card: cards_C3 C3-P02 incl.         *)
(*   20261103 AFP comparison record; drafts_C3 P02 statement skeleton.   *)
(* Constructivity: Set-carried statements; zero Axiom, zero Parameter,   *)
(*   zero classical choice; all numerics stay in Q (decidable, exact);   *)
(*   ring goals never receive reducible constant applications - the      *)
(*   arithmetic step faces are discharged by pure-Q helper lemmas and    *)
(*   apply (session craft note of 20261103).                             *)
(* Build: coqc -native-compiler no -q (sandbox -Q paths), cpu_guard v3    *)
(*   wrapper (-AllowG3 -GearForce 0 -TempLimit 98 -LoadLimit 60 -CoreN 2). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P02_LineIntegralAlg.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 7. Orientation reversal (the reverse law).                     *)
(* ===================================================================== *)

Definition GaC3_P02_rev_seg (s : GaC3_P02_pseg) : GaC3_P02_pseg := (snd s, fst s).

Lemma GaC3_P02_contrib_rev_R : forall (s : GaC3_P02_pseg) (v : Q * Q),
  fst (GaC3_P02_seg_contrib (GaC3_P02_rev_seg s) v)
  == - fst (GaC3_P02_seg_contrib s v).
Proof.
  intros [[x0 y0] [x1 y1]] [vr vi].
  cbn [GaC3_P02_rev_seg GaC3_P02_seg_dz GaC3_P02_seg_contrib fst snd].
  ring.
Qed.

Lemma GaC3_P02_contrib_rev_I : forall (s : GaC3_P02_pseg) (v : Q * Q),
  snd (GaC3_P02_seg_contrib (GaC3_P02_rev_seg s) v)
  == - snd (GaC3_P02_seg_contrib s v).
Proof.
  intros [[x0 y0] [x1 y1]] [vr vi].
  cbn [GaC3_P02_rev_seg GaC3_P02_seg_dz GaC3_P02_seg_contrib fst snd].
  ring.
Qed.

(* Reversal arithmetic helpers (pure Q; applied as helpers so that no     *)
(* reducible constant application ever enters a ring goal). *)
Lemma GaC3_P02_qplus_0_r : forall a : Q, a + 0 == a.
Proof. intros a. ring. Qed.

Lemma GaC3_P02_qneg_swap : forall a b : Q, - a + (- b) == - (b + a).
Proof. intros a b. ring. Qed.

(* Reversal of the real-component path sum (zip-matched data; the path    *)
(* map is kept in unfolded form map rev_seg (rev ps)). *)
Theorem GaC3_P02_path_sumR_rev : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q)),
  GaC3_P02_plen_ok ps vs ->
  GaC3_P02_path_sumR (map GaC3_P02_rev_seg (rev ps)) (rev vs)
  == - GaC3_P02_path_sumR ps vs.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs Hlen.
  - destruct vs as [| v vs'].
    + cbn [rev map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
  - destruct vs as [| v vs'].
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
    + assert (Heq : length ps' = length vs')
        by (pose proof (GaC3_P02_plen_ok_true _ _ Hlen) as Hlen0;
            cbn [length] in Hlen0; injection Hlen0 as Heq0; exact Heq0).
      cbn [rev map]. rewrite map_app. cbn [map].
      rewrite GaC3_P02_path_concat_R
        by (apply GaC3_P02_plen_ok_of_eq; rewrite length_map, !length_rev; exact Heq).
      rewrite (IH vs' (GaC3_P02_plen_ok_of_eq _ _ Heq)).
      rewrite GaC3_P02_path_sumR_cons.
      rewrite GaC3_P02_path_sumR_cons.
      rewrite GaC3_P02_contrib_rev_R.
      change (GaC3_P02_path_sumR [] []) with 0%Q.
      rewrite GaC3_P02_qplus_0_r.
      apply GaC3_P02_qneg_swap.
Qed.

(* Reversal of the imaginary-component path sum. *)
Theorem GaC3_P02_path_sumI_rev : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q)),
  GaC3_P02_plen_ok ps vs ->
  GaC3_P02_path_sumI (map GaC3_P02_rev_seg (rev ps)) (rev vs)
  == - GaC3_P02_path_sumI ps vs.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs Hlen.
  - destruct vs as [| v vs'].
    + cbn [rev map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
  - destruct vs as [| v vs'].
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
    + assert (Heq : length ps' = length vs')
        by (pose proof (GaC3_P02_plen_ok_true _ _ Hlen) as Hlen0;
            cbn [length] in Hlen0; injection Hlen0 as Heq0; exact Heq0).
      cbn [rev map]. rewrite map_app. cbn [map].
      rewrite GaC3_P02_path_concat_I
        by (apply GaC3_P02_plen_ok_of_eq; rewrite length_map, !length_rev; exact Heq).
      rewrite (IH vs' (GaC3_P02_plen_ok_of_eq _ _ Heq)).
      rewrite GaC3_P02_path_sumI_cons.
      rewrite GaC3_P02_path_sumI_cons.
      rewrite GaC3_P02_contrib_rev_I.
      change (GaC3_P02_path_sumI [] []) with 0%Q.
      rewrite GaC3_P02_qplus_0_r.
      apply GaC3_P02_qneg_swap.
Qed.

(* The reversed path: reverse order AND re-orient each segment. *)
Definition GaC3_P02_path_reverse (ps : GaC3_P02_cpath) : GaC3_P02_cpath :=
  map GaC3_P02_rev_seg (rev ps).

(* The reverse law at Cx level: the integral over the reversed path is    *)
(* the negation (drafts P02 skeleton line_integral_reverse). *)
Theorem GaC3_P02_line_integral_reverse : forall (ps : GaC3_P02_cpath)
  (vs : list (Q * Q)),
  GaC3_P02_plen_ok ps vs ->
  c_eq (GaC3_P02_line_integral (GaC3_P02_path_reverse ps) (rev vs))
       (c_opp (GaC3_P02_line_integral ps vs)).
Proof.
  intros ps vs Hlen. unfold GaC3_P02_line_integral, GaC3_P02_path_reverse.
  apply (c_eq_trans _ (c_of_Q (- GaC3_P02_path_sumR ps vs) (- GaC3_P02_path_sumI ps vs))).
  - apply GaC3_P01_cofQ_eq;
      [ exact (GaC3_P02_path_sumR_rev ps vs Hlen)
      | exact (GaC3_P02_path_sumI_rev ps vs Hlen) ].
  - exact (GaC3_P02_coppoQ (GaC3_P02_path_sumR ps vs) (GaC3_P02_path_sumI ps vs)).
Qed.
