(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 wave-2 survey band faces.   *)
(* Mission      : SL4-W2-SURVEY-BAND (survey SL4 sections 5/9; debt rows     *)
(*                D-SL4-2 wiring complement and D-SL4-7 wiring segment): pin *)
(*                the validity band of the window-slot twins and discharge   *)
(*                the born face planb4_sl4_frozen_delta_vacuity of           *)
(*                planb4_sl4_delta_anchor by name.  The twin on the total    *)
(*                carrier holds over the whole frozen-valid band            *)
(*                1 <= q <= 2^77 (39-case dispatch over the landed anchors); *)
(*                the frozen channels read 0 at window index n >= 40.        *)
(* Statements   : planb4_sl4_w2_nlo_pos / _nlo_le_39 / _delta_nz_table /     *)
(*                _abdef_twin_table_band / _frozen_default_A/B /             *)
(*                _frozen_delta_zero_hi / _frozen_delta_vacuity (of the      *)
(*                born face).                                                *)
(* Dependencies : planb3_g1_calib; planb1_hcage_zerotouch_prescription       *)
(*                (planb_b_nlo); planb4_sl4_delta_anchor.  Byte-exact        *)
(*                origin/main blobs; source routing in the seat receipt.     *)
(* References   : survey SL4 sections 1/5/9; planb4_sl4_delta_anchor;        *)
(*                planb5_hesc18_assembly consumers.                          *)
(* Constructivity: decidable nat/Z reasoning (log2/div2 monotone lemmas,    *)
(*                a 39-case dispatch, exact table defaults); Z-carried       *)
(*                propositions only; postulate-free (no Parameter, no        *)
(*                Conjecture, no Abort); every item Defined; ring only at    *)
(*                leaf equalities.                                           *)
(* Build        : coqc -native-compiler no -q -Q <closure root> ""           *)
(*                sl4_w2_survey_band.v (Rocq 9.3.0, scripted form; explicit  *)
(*                -o products outside the source root).                      *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import planb3_g1_calib.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb4_sl4_delta_anchor.

(* ================================================================== *)
(* Section 1. Window-index basics: the window index is positive and   *)
(*            stays within the certified table window on the whole    *)
(*            frozen-valid band q <= 2^77 (the mirror of the in-tree  *)
(*            outer bound planb4_sl4_nlo_ge_40 at 2^79).              *)
(* ================================================================== *)

Lemma planb4_sl4_w2_nlo_pos : forall q : nat, (1 <= q)%nat ->
  (1 <= planb_b_nlo q)%nat.
Proof.
  intros q Hq. unfold planb_b_nlo.
  assert (Hpos : (0 <= Nat.log2 q)%nat) by (apply Nat.le_0_l).
  assert (Hd : (1 <= Nat.div2 (Nat.log2 q + 2))%nat).
  { apply Nat.div2_le_mono. lia. }
  destruct (Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 q + 2))) (2 * q)%nat); lia.
Defined.

Lemma planb4_sl4_w2_nlo_le_39 : forall q : nat, (q <= 2 ^ 77)%nat ->
  (planb_b_nlo q <= 39)%nat.
Proof.
  intros q Hq. destruct q as [|q'].
  - unfold planb_b_nlo. vm_compute. lia.
  - unfold planb_b_nlo.
    assert (Hl : (Nat.log2 (S q') <= 77)%nat).
    { destruct (Nat.le_gt_cases (Nat.log2 (S q')) 77) as [Hle | Hgt];
        [ exact Hle | exfalso ].
      assert (Hlt : (Nat.log2 (S q') < 78)%nat) by lia.
      apply Nat.log2_lt_pow2 in Hlt; [ lia | lia ]. }
    assert (Hd : (Nat.div2 (Nat.log2 (S q') + 2) <= 39)%nat).
    { apply Nat.div2_le_mono. lia. }
    destruct (Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 (S q') + 2)))
                      (2 * S q')%nat); lia.
Defined.

(* ================================================================== *)
(* Section 2. The dodge determinant is nonzero at every certified     *)
(*            window index: a 39-case dispatch over the landed        *)
(*            per-index anchors, and the resulting table-domain band  *)
(*            face of the total-carrier window twin.                  *)
(* ================================================================== *)

Lemma planb4_sl4_w2_delta_nz_table : forall n : nat,
  (1 <= n)%nat -> (n <= 39)%nat -> planb4_sl4_delta n <> 0%Z.
Proof.
  intros n H1 H2.
  destruct n as [|k0]. { lia. }
  destruct k0 as [|k1]. { exact planb4_sl4_delta_nz_1. }
  destruct k1 as [|k2]. { exact planb4_sl4_delta_nz_2. }
  destruct k2 as [|k3]. { exact planb4_sl4_delta_nz_3. }
  destruct k3 as [|k4]. { exact planb4_sl4_delta_nz_4. }
  destruct k4 as [|k5]. { exact planb4_sl4_delta_nz_5. }
  destruct k5 as [|k6]. { exact planb4_sl4_delta_nz_6. }
  destruct k6 as [|k7]. { exact planb4_sl4_delta_nz_7. }
  destruct k7 as [|k8]. { exact planb4_sl4_delta_nz_8. }
  destruct k8 as [|k9]. { exact planb4_sl4_delta_nz_9. }
  destruct k9 as [|k10]. { exact planb4_sl4_delta_nz_10. }
  destruct k10 as [|k11]. { exact planb4_sl4_delta_nz_11. }
  destruct k11 as [|k12]. { exact planb4_sl4_delta_nz_12. }
  destruct k12 as [|k13]. { exact planb4_sl4_delta_nz_13. }
  destruct k13 as [|k14]. { exact planb4_sl4_delta_nz_14. }
  destruct k14 as [|k15]. { exact planb4_sl4_delta_nz_15. }
  destruct k15 as [|k16]. { exact planb4_sl4_delta_nz_16. }
  destruct k16 as [|k17]. { exact planb4_sl4_delta_nz_17. }
  destruct k17 as [|k18]. { exact planb4_sl4_delta_nz_18. }
  destruct k18 as [|k19]. { exact planb4_sl4_delta_nz_19. }
  destruct k19 as [|k20]. { exact planb4_sl4_delta_nz_20. }
  destruct k20 as [|k21]. { exact planb4_sl4_delta_nz_21. }
  destruct k21 as [|k22]. { exact planb4_sl4_delta_nz_22. }
  destruct k22 as [|k23]. { exact planb4_sl4_delta_nz_23. }
  destruct k23 as [|k24]. { exact planb4_sl4_delta_nz_24. }
  destruct k24 as [|k25]. { exact planb4_sl4_delta_nz_25. }
  destruct k25 as [|k26]. { exact planb4_sl4_delta_nz_26. }
  destruct k26 as [|k27]. { exact planb4_sl4_delta_nz_27. }
  destruct k27 as [|k28]. { exact planb4_sl4_delta_nz_28. }
  destruct k28 as [|k29]. { exact planb4_sl4_delta_nz_29. }
  destruct k29 as [|k30]. { exact planb4_sl4_delta_nz_30. }
  destruct k30 as [|k31]. { exact planb4_sl4_delta_nz_31. }
  destruct k31 as [|k32]. { exact planb4_sl4_delta_nz_32. }
  destruct k32 as [|k33]. { exact planb4_sl4_delta_nz_33. }
  destruct k33 as [|k34]. { exact planb4_sl4_delta_nz_34. }
  destruct k34 as [|k35]. { exact planb4_sl4_delta_nz_35. }
  destruct k35 as [|k36]. { exact planb4_sl4_delta_nz_36. }
  destruct k36 as [|k37]. { exact planb4_sl4_delta_nz_37. }
  destruct k37 as [|k38]. { exact planb4_sl4_delta_nz_38. }
  destruct k38 as [|k39]. { exact planb4_sl4_delta_nz_39. }
  lia.
Defined.

Theorem planb4_sl4_w2_abdef_twin_table_band :
  forall q : nat, (1 <= q)%nat -> (q <= 2 ^ 77)%nat ->
    planb4_sl4_delta (planb_b_nlo q) <> 0%Z.
Proof.
  intros q H1 H2. apply planb4_sl4_w2_delta_nz_table.
  - apply planb4_sl4_w2_nlo_pos. exact H1.
  - apply planb4_sl4_w2_nlo_le_39. exact H2.
Defined.

(* ================================================================== *)
(* Section 3. The frozen-carrier default: both channels read 0 past   *)
(*            the table edge, so the frozen twin premise reads 0 at   *)
(*            every window index n >= 40; this discharges the born    *)
(*            vacuity face of planb4_sl4_delta_anchor by name.        *)
(* ================================================================== *)

Lemma planb4_sl4_w2_frozen_default_A : forall n : nat, (41 <= n)%nat ->
  planb3_g1_A n = 0%Z.
Proof.
  intros n Hn.
  destruct n as [|w0]. { lia. }
  destruct w0 as [|w1]. { lia. }
  destruct w1 as [|w2]. { lia. }
  destruct w2 as [|w3]. { lia. }
  destruct w3 as [|w4]. { lia. }
  destruct w4 as [|w5]. { lia. }
  destruct w5 as [|w6]. { lia. }
  destruct w6 as [|w7]. { lia. }
  destruct w7 as [|w8]. { lia. }
  destruct w8 as [|w9]. { lia. }
  destruct w9 as [|w10]. { lia. }
  destruct w10 as [|w11]. { lia. }
  destruct w11 as [|w12]. { lia. }
  destruct w12 as [|w13]. { lia. }
  destruct w13 as [|w14]. { lia. }
  destruct w14 as [|w15]. { lia. }
  destruct w15 as [|w16]. { lia. }
  destruct w16 as [|w17]. { lia. }
  destruct w17 as [|w18]. { lia. }
  destruct w18 as [|w19]. { lia. }
  destruct w19 as [|w20]. { lia. }
  destruct w20 as [|w21]. { lia. }
  destruct w21 as [|w22]. { lia. }
  destruct w22 as [|w23]. { lia. }
  destruct w23 as [|w24]. { lia. }
  destruct w24 as [|w25]. { lia. }
  destruct w25 as [|w26]. { lia. }
  destruct w26 as [|w27]. { lia. }
  destruct w27 as [|w28]. { lia. }
  destruct w28 as [|w29]. { lia. }
  destruct w29 as [|w30]. { lia. }
  destruct w30 as [|w31]. { lia. }
  destruct w31 as [|w32]. { lia. }
  destruct w32 as [|w33]. { lia. }
  destruct w33 as [|w34]. { lia. }
  destruct w34 as [|w35]. { lia. }
  destruct w35 as [|w36]. { lia. }
  destruct w36 as [|w37]. { lia. }
  destruct w37 as [|w38]. { lia. }
  destruct w38 as [|w39]. { lia. }
  destruct w39 as [|w40]. { lia. }
  vm_compute. reflexivity.
Defined.

Lemma planb4_sl4_w2_frozen_default_B : forall n : nat, (41 <= n)%nat ->
  planb3_g1_B n = 0%Z.
Proof.
  intros n Hn.
  destruct n as [|v0]. { lia. }
  destruct v0 as [|v1]. { lia. }
  destruct v1 as [|v2]. { lia. }
  destruct v2 as [|v3]. { lia. }
  destruct v3 as [|v4]. { lia. }
  destruct v4 as [|v5]. { lia. }
  destruct v5 as [|v6]. { lia. }
  destruct v6 as [|v7]. { lia. }
  destruct v7 as [|v8]. { lia. }
  destruct v8 as [|v9]. { lia. }
  destruct v9 as [|v10]. { lia. }
  destruct v10 as [|v11]. { lia. }
  destruct v11 as [|v12]. { lia. }
  destruct v12 as [|v13]. { lia. }
  destruct v13 as [|v14]. { lia. }
  destruct v14 as [|v15]. { lia. }
  destruct v15 as [|v16]. { lia. }
  destruct v16 as [|v17]. { lia. }
  destruct v17 as [|v18]. { lia. }
  destruct v18 as [|v19]. { lia. }
  destruct v19 as [|v20]. { lia. }
  destruct v20 as [|v21]. { lia. }
  destruct v21 as [|v22]. { lia. }
  destruct v22 as [|v23]. { lia. }
  destruct v23 as [|v24]. { lia. }
  destruct v24 as [|v25]. { lia. }
  destruct v25 as [|v26]. { lia. }
  destruct v26 as [|v27]. { lia. }
  destruct v27 as [|v28]. { lia. }
  destruct v28 as [|v29]. { lia. }
  destruct v29 as [|v30]. { lia. }
  destruct v30 as [|v31]. { lia. }
  destruct v31 as [|v32]. { lia. }
  destruct v32 as [|v33]. { lia. }
  destruct v33 as [|v34]. { lia. }
  destruct v34 as [|v35]. { lia. }
  destruct v35 as [|v36]. { lia. }
  destruct v36 as [|v37]. { lia. }
  destruct v37 as [|v38]. { lia. }
  destruct v38 as [|v39]. { lia. }
  destruct v39 as [|v40]. { lia. }
  vm_compute. reflexivity.
Defined.

Lemma planb4_sl4_w2_frozen_delta_zero_hi : forall n : nat, (40 <= n)%nat ->
  (planb3_g1_A n * planb3_g1_B (S n)
   - planb3_g1_A (S n) * planb3_g1_B n)%Z = 0%Z.
Proof.
  intros n Hn.
  destruct (Nat.eq_dec n 40%nat) as [H40 | Hge].
  - subst n.
    rewrite (planb4_sl4_w2_frozen_default_B 41%nat) by lia.
    rewrite (planb4_sl4_w2_frozen_default_A 41%nat) by lia.
    ring.
  - assert (H41 : (41 <= n)%nat) by lia.
    rewrite (planb4_sl4_w2_frozen_default_A n) by lia.
    rewrite (planb4_sl4_w2_frozen_default_A (S n)) by lia.
    rewrite (planb4_sl4_w2_frozen_default_B (S n)) by lia.
    ring.
Defined.

Theorem planb4_sl4_w2_frozen_delta_vacuity : planb4_sl4_frozen_delta_vacuity.
Proof.
  unfold planb4_sl4_frozen_delta_vacuity. intros q Hq.
  exact (planb4_sl4_w2_frozen_delta_zero_hi (planb_b_nlo q)
           (planb4_sl4_nlo_ge_40 q Hq)).
Defined.

(* ================================================================== *)
(* Section 4. Assumption audit (kernel verdicts, printed at build).   *)
(* ================================================================== *)

Print Assumptions planb4_sl4_w2_nlo_pos.
Print Assumptions planb4_sl4_w2_nlo_le_39.
Print Assumptions planb4_sl4_w2_delta_nz_table.
Print Assumptions planb4_sl4_w2_abdef_twin_table_band.
Print Assumptions planb4_sl4_w2_frozen_default_A.
Print Assumptions planb4_sl4_w2_frozen_default_B.
Print Assumptions planb4_sl4_w2_frozen_delta_zero_hi.
Print Assumptions planb4_sl4_w2_frozen_delta_vacuity.

(* ==================== end of the wave-2 band faces ================ *)
