(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 debt row D-SL4-4, the      *)
(* forall-n reduction skeleton: machine-verified glue, open accounts.       *)
(* Mission      : Dispatch row D-SL4-4 (survey volume SL4, section 9): the  *)
(*                forall-n face planb4_sl4_denom_bound (skeleton Section 4) *)
(*                needs two per-n accounts missing in tree - B-side growth  *)
(*                (debt row D-SL4-3) and a gcd upper bound over the N2c     *)
(*                chain (planb3_g1_g2_design.v:170-180).  The complete      *)
(*                forall-n face is NOT claimed here; what lands is the      *)
(*                machine-checked reduction: for n >= 3, growth 2^(6(n-1))  *)
(*                plus gcd bound 2^((7n-11)/2) yield the bound 2^((5n-1)/2);*)
(*                thin bridges lift this to the named faces (n >= 3).       *)
(* Statements   : planb4_sl4_d4_denom_transfer;                            *)
(*                planb4_sl4_d4_denom_bound_via_accounts;                   *)
(*                planb4_sl4_d4_skeleton_face_3up (gcd premise stays a      *)
(*                premise of the bridges - no new born face).               *)
(* Dependencies : planb4_sl4_skeleton; planb4_g1_ab_def; Stdlib QArith,     *)
(*                ZArith, Lia (auxiliary steps only).  Source routing: in   *)
(*                the delivery receipt per the comment law.                 *)
(* References   : survey volume SL4 sections 2/3/9 (row D-SL4-4); skeleton  *)
(*                Sections 3/4/7; planb3_g1_g2_design.v:170-180 (N2c       *)
(*                Hcoef@17); sl4_d4_denom_anchors.v (table domain).         *)
(* Constructivity: decidable Z arithmetic; the transfer bridge is a        *)
(*                Z-level derivation (divisibility, exact division, power  *)
(*                monotonicity), transparently defined; no classical       *)
(*                principle, no choice, postulate-free; no Parameter, no   *)
(*                Conjecture, no Abort; lia never finishes a named result. *)
(* Build        : coqc -native-compiler no -q -Q <sandbox root> ""          *)
(*                sl4_d4_denom_skeleton.v  (Rocq 9.3.0, scripted form).    *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Lia.
Require Import planb4_g1_ab_def.
Require Import planb4_sl4_skeleton.

(* ================================================================== *)
(* Section 1. The per-n transfer bridge (machine-verified glue).       *)
(* ================================================================== *)

(* Reduction form: on the n >= 3 slice, the reduced-denominator bound    *)
(* follows from the two per-n accounts.  The growth premise is the       *)
(* Section 3 skeleton face instantiated at n; the gcd premise is the     *)
(* open half - priced against the N2c chain registration, see the        *)
(* ledger below.                                                        *)
(* Arithmetic spine: the gcd g of |A n| and |B n| divides |B n|, so      *)
(* d_n = |B n| / g is an exact division; for positive g the target       *)
(* 2^((5n-1)/2) <= d_n is equivalent to 2^((5n-1)/2) * g <= |B n|, and   *)
(* that chain closes by 2^((5n-1)/2) * g <= 2^((5n-1)/2) *               *)
(* 2^((7n-11)/2) = 2^((5n-1)/2 + (7n-11)/2) <= 2^(6(n-1)) <= |B n|.      *)
(* The exponent bookkeeping (both threshold halves nonnegative, their    *)
(* sum at most 6n-6) is discharged by an explicit div/mod decomposition, *)
(* linear arithmetic confined to auxiliary steps.  The n = 1..2 slice,   *)
(* where this gcd pin form degenerates, is covered table-domain-wise by  *)
(* sl4_d4_denom_anchors.v (n = 1..40 anchors).                           *)
Theorem planb4_sl4_d4_denom_transfer :
  forall n : nat, (3 <= n)%nat ->
    (2 ^ Z.of_nat ((6 * (n - 1))%nat) <= Z.abs (planb4_g1_B n))%Z ->
    (Z.gcd (Z.abs (planb4_g1_A n)) (Z.abs (planb4_g1_B n))
       <= 2 ^ ((Z.of_nat n * 7 - 11) / 2))%Z ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) <= planb4_sl4_denom_reduced n)%Z.
Proof.
  intros n Hn3 Hgrow Hgcd.
  unfold planb4_sl4_denom_reduced.
  set (a := (Z.abs (planb4_g1_A n))%Z).
  set (b := (Z.abs (planb4_g1_B n))%Z).
  (* exponent bookkeeping: both threshold halves are nonnegative; their    *)
  (* sum is at most the growth exponent Z.of_nat (6*(n-1)); all closed by  *)
  (* linear arithmetic over the explicit div/mod decompositions.           *)
  assert (Hz3 : (3 <= Z.of_nat n)%Z) by lia.
  assert (Hd1 : (Z.of_nat n * 5 - 1)%Z
                = (2 * ((Z.of_nat n * 5 - 1) / 2)
                   + (Z.of_nat n * 5 - 1) mod 2)%Z)
    by (apply Z.div_mod; lia).
  assert (Hd2 : (Z.of_nat n * 7 - 11)%Z
                = (2 * ((Z.of_nat n * 7 - 11) / 2)
                   + (Z.of_nat n * 7 - 11) mod 2)%Z)
    by (apply Z.div_mod; lia).
  assert (Hm1 : (0 <= (Z.of_nat n * 5 - 1) mod 2 < 2)%Z)
    by (apply Z.mod_pos_bound; lia).
  assert (Hm2 : (0 <= (Z.of_nat n * 7 - 11) mod 2 < 2)%Z)
    by (apply Z.mod_pos_bound; lia).
  assert (He1 : (0 <= (Z.of_nat n * 5 - 1) / 2)%Z) by lia.
  assert (He2 : (0 <= (Z.of_nat n * 7 - 11) / 2)%Z) by lia.
  assert (He3 : (0 <= Z.of_nat ((6 * (n - 1))%nat))%Z) by lia.
  assert (Hsum : ((Z.of_nat n * 5 - 1) / 2 + (Z.of_nat n * 7 - 11) / 2
                  <= Z.of_nat ((6 * (n - 1))%nat))%Z) by lia.
  (* the gcd g divides |B n|, hence is nonzero as soon as |B n| is;        *)
  (* |B n| is positive off the growth account since 6(n-1) > 0 here, and   *)
  (* Z.gcd is nonnegative, so g is positive.                              *)
  set (g := (Z.gcd a b)%Z).
  assert (Hgdiv : (g | b)%Z) by apply Z.gcd_divide_r.
  assert (Hb0 : (0 < b)%Z).
  { apply (Z.lt_le_trans _ (2 ^ Z.of_nat ((6 * (n - 1))%nat))).
    - apply Z.pow_pos_nonneg; [lia | exact He3].
    - exact Hgrow. }
  assert (Hgne : g <> 0%Z).
  { intro Hgz.
    rewrite Hgz in Hgdiv.
    assert (Hbz : b = 0%Z) by (apply Z.divide_0_l; exact Hgdiv).
    lia. }
  assert (Hgnn : (0 <= g)%Z) by (unfold g; apply Z.gcd_nonneg).
  assert (Hg0 : (0 < g)%Z) by lia.
  (* exact division face *)
  assert (Hbmod : (b mod g)%Z = 0%Z)
    by (apply (proj2 (Z.mod_divide b g Hgne)); exact Hgdiv).
  assert (Hbmul : b = (g * (b / g))%Z)
    by (apply (proj2 (Z.div_exact b g Hgne)); exact Hbmod).
  (* main chain: multiply the target by the positive g and cascade down   *)
  (* to the growth account through the power monotonicity.               *)
  assert (Hp1 : (0 < 2 ^ ((Z.of_nat n * 5 - 1) / 2))%Z)
    by (apply Z.pow_pos_nonneg; [lia | exact He1]).
  assert (Hkey : (2 ^ ((Z.of_nat n * 5 - 1) / 2) * g <= b)%Z).
  { eapply Z.le_trans.
    - apply Z.mul_le_mono_pos_l.
      + exact Hp1.
      + exact Hgcd.
    - eapply Z.le_trans.
      + rewrite <- (Z.pow_add_r 2 ((Z.of_nat n * 5 - 1) / 2)
                     ((Z.of_nat n * 7 - 11) / 2) He1 He2).
        apply Z.pow_le_mono_r; [lia | exact Hsum].
      + exact Hgrow. }
  rewrite Hbmul in Hkey.
  rewrite (Z.mul_comm g (b / g)) in Hkey.
  exact (proj2 (Z.mul_le_mono_pos_r (2 ^ ((Z.of_nat n * 5 - 1) / 2))
                 (b / g) g Hg0) Hkey).
Defined.

(* ================================================================== *)
(* Section 2. Named-face bridges: the accounts to the born faces on    *)
(*            the n >= 3 slice.                                        *)
(* ================================================================== *)

(* The accounts to the raw per-n bound.  The growth premise is the born  *)
(* Section 3 face; the gcd premise stays hypothetical - the open account.*)
Theorem planb4_sl4_d4_denom_bound_via_accounts :
  planb4_sl4_bgrowth ->
  (forall n : nat, (3 <= n)%nat ->
    (Z.gcd (Z.abs (planb4_g1_A n)) (Z.abs (planb4_g1_B n))
       <= 2 ^ ((Z.of_nat n * 7 - 11) / 2))%Z) ->
  forall n : nat, (3 <= n)%nat ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) <= planb4_sl4_denom_reduced n)%Z.
Proof.
  intros Hgrow Hgcd n Hn3.
  apply planb4_sl4_d4_denom_transfer;
    [ exact Hn3 | apply (Hgrow n); lia | apply Hgcd; exact Hn3 ].
Defined.

(* The same two accounts to the per-n body of the born Section 4 face    *)
(* (the face planb4_sl4_denom_bound is a Prop definition, so the bridge  *)
(* states its applied body verbatim over the n >= 3 slice).              *)
Theorem planb4_sl4_d4_skeleton_face_3up :
  planb4_sl4_bgrowth ->
  (forall n : nat, (3 <= n)%nat ->
    (Z.gcd (Z.abs (planb4_g1_A n)) (Z.abs (planb4_g1_B n))
       <= 2 ^ ((Z.of_nat n * 7 - 11) / 2))%Z) ->
  forall n : nat, (3 <= n)%nat -> (1 <= n)%nat ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) <= planb4_sl4_denom_reduced n)%Z.
Proof.
  intros Hgrow Hgcd n Hn3 Hle1.
  apply planb4_sl4_d4_denom_transfer;
    [ exact Hn3 | apply (Hgrow n); lia | apply Hgcd; exact Hn3 ].
Defined.

(* ================================================================== *)
(* Section 3. Assumption audit.                                        *)
(* ================================================================== *)

Print Assumptions planb4_sl4_d4_denom_transfer.
Print Assumptions planb4_sl4_d4_denom_bound_via_accounts.
Print Assumptions planb4_sl4_d4_skeleton_face_3up.

(* ================================================================== *)
(* Section 4. Pending-debt ledger (comments only; nothing here is      *)
(*            claimed, proven, or priced beyond the survey row).       *)
(* ================================================================== *)

(* D-SL4-4 residual, first half: the B-side growth account is debt row   *)
(* D-SL4-3 (planb4_sl4_bgrowth, skeleton Section 3; the Laurent product  *)
(* structure general-n face).  Until it lands, the growth premise above  *)
(* stays hypothetical.                                                  *)

(* D-SL4-4 residual, second half: the gcd upper-bound account            *)
(* gcd(|A n|, |B n|) <= 2^((7n-11)/2) for n >= 3.  This is the open half *)
(* owned by the G4/N2c chain (planb3_g1_g2_design.v:170-180              *)
(* registration; the upstream list is the M1:329 criterion (i) row).     *)
(* No lemma of this shape exists in tree today.                          *)

(* Complete forall-n face: open.  The reduction is machine-verified in   *)
(* Section 1; the n = 1..2 slice (where the gcd pin form degenerates)    *)
(* is table-certified by sl4_d4_denom_anchors.v for the table domain     *)
(* and needs no symbol-level account.  Confluence with the nonzero       *)
(* witness face is debt row D-SL4-7 territory.                           *)

(* Review condition: any gcd upper-bound lemma landing in tree forces a  *)
(* re-estimate of debt row D-SL4-4, per the survey ledger row.           *)

(* ================= end of reduction skeleton and ledger ============ *)
