(* sl2_anchor_carrier.v - SL2 supply faces: the (B) Hval-direct live    *)
(* consumption shape, the pi-anchored decay carrier and its discharge   *)
(* lemmas, and head-side machine anchors over the frozen tables.        *)
(* Mission. Slot-draft SL12 section 2 statement faces: the live        *)
(*  consumption face (verbatim (B) Hval-direct isomorph); the anchor-  *)
(*  parametric decay carrier and the joint assembly-topology face; the *)
(*  Hp and Htri discharge lemmas at the anchor carrier; the band-end   *)
(*  bridge (decay at crho <= 1/4 discharges Hval-direct); the pinned   *)
(*  pi-bracket anchor with window faces; 40 vm_compute head anchors    *)
(*  (pass 40/40, worst margin 5.9e-12); the forall-n decay face is NOT *)
(*  claimed.                                                           *)
(* Dependencies. Slot-draft section 0 block verbatim: Stdlib QArith,   *)
(*  Qabs, ZArith, Arith, Lia, Qpower; S02_CauchyComplete,              *)
(*  piu_mu_criterion, piu_zz_e_carrier, planb4_g1_witness,             *)
(*  planb4_l2_dv_cast, planb3_g1_g2_design, planb1_hcage,              *)
(*  planb3_g1_calib.                                                   *)
(* References. [1] slot draft SL12 section 2. [2] planb1:386-389 the   *)
(*  (B) Hval-direct face (zero-touch semantics). [3] CARRIER-SWAP      *)
(*  ANNOTATION (interface-change obligation): the fourslots hcage-slot *)
(*  face (planb4_l4_hcage_slot, x = 1 l2_dv carrier, (13/400)^n) is    *)
(*  NOT re-cast here and must not be discharged; the live consumption  *)
(*  position is the (B) Hval-direct face only; the slot's carrier swap *)
(*  belongs to the landing step with the migration ledger (this        *)
(*  sandbox ticket does not touch the tree; machine support:           *)
(*  sl2_rint_recast.v pins the x = 1 cage refutation 40/40). [4]       *)
(*  design.v:74-103 x = 1 Hp/Htri precedents. Provenance ledger kept   *)
(*  with the seat receipt, not in this file. Constructivity:           *)
(*  postulate-free, all faces Set-carried, zero new Prop statements,   *)
(*  lemmas Defined transparent, anchors vm_compute-closed pins.        *)
(*  Build: coqc -native-compiler no -q (Rocq 9.3.0, E952 script form). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_e_carrier.
Require Import planb4_g1_witness.
Require Import planb4_l2_dv_cast.
Require Import planb3_g1_g2_design.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb3_g1_calib.

(* ==== Section 1: the shared SL1-object face (draft 1.1 statement-  *)
(* ==== only local copy) and the live consumption face (draft 2.1). ==== *)

(* SL1 main face, verbatim slot-draft 1.1. Statement-only local copy  *)
(* so the parallel SL1/SL2 lanes stay file-disjoint (zero inter-lane  *)
(* file dependency); the in-tree supply instance is the SL1 seat      *)
(* deliverable and unifies at landing. *)
Definition sl12_lzn_pow_bound_face (b : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_LZn n)))
      (Qpower b (Z.of_nat n)).

(* SL2 live consumption shape, verbatim slot-draft 2.1: the (B)       *)
(* Hval-direct isomorph (zero-touch semantics, planb1:382-389); this  *)
(* is the face the SL2 supply ticket discharges at the pi-anchored    *)
(* carrier. *)
Definition sl12_hval_direct_face (dval : Z -> Z -> Q) (A B : nat -> Z) : Set :=
  forall n : nat,
    piu_mu_QleT (dval (A n) (B n) * piu_mu_epos (2 * n)) (1 # 1)%Q.

(* ==== Section 2: the anchor-parametric decay carrier (draft 2.2). ==== *)

Section SL12_DECAY.

Context (xpi : Q).
Variable A B : nat -> Z.

(* the anchor carrier: dv_x a b := |a + b * xpi|. *)
Definition sl12_dval_pi (a b : Z) : Q :=
  Qabs (inject_Z a + inject_Z b * xpi)%Q.

(* the decay supply face at the anchor carrier. *)
Definition sl12_I_decay_face (crho : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (sl12_dval_pi (A n) (B n))
      (Qpower crho (Z.of_nat n)).

(* the two-sub-certificate assembly-topology face (draft 2.2): the    *)
(* SL1 shared object plus the approximation-quality factor jointly    *)
(* yield the decay face. Registered topology only - the quality       *)
(* factor is a separate third item and is NOT supplied here.          *)
Definition sl12_I_decay_from_LZn_face (b crho : Q) : Set :=
  sl12_lzn_pow_bound_face b ->
  sl12_I_decay_face crho.

End SL12_DECAY.

(* ==== Section 3: carrier discharge lemmas.                            ==== *)

(* power monotonicity on the nonneg domain (the one helper the band-  *)
(* end bridge needs; plain mult-compat induction). *)
Lemma sl12_Qpower_le_mono_nonneg :
  forall (x y : Q) (n : nat),
  (0 <= x)%Q -> x <= y ->
  Qpower x (Z.of_nat n) <= Qpower y (Z.of_nat n).
Proof.
  intros x y n Hx0 Hxy.
  assert (Hy0 : (0 <= y)%Q).
  { apply (Qle_trans 0 x y); [exact Hx0 | exact Hxy]. }
  induction n as [|k IHk].
  - cbn. apply Qle_refl.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    destruct (Qeq_bool x 0) eqn:Hb.
    + apply Qeq_bool_eq in Hb.
      rewrite Hb, (Qpower_0 (Z.of_nat k + 1) ltac:(lia)).
      apply Qpower_0_le. exact Hy0.
    + apply Qeq_bool_neq in Hb.
      assert (Hx0s : (0 < x)%Q).
      { destruct (Qlt_le_dec 0 x) as [Hlt | Hle].
        - exact Hlt.
        - exfalso. apply Hb. apply Qle_antisym; [exact Hle | exact Hx0]. }
      assert (Hy0s : (0 < y)%Q).
      { apply (Qlt_le_trans 0 x y); [exact Hx0s | exact Hxy]. }
      assert (Hxq0 : ~ (x == 0)) by (intro Hc; exact (Hb Hc)).
      assert (Hyq0 : ~ (y == 0)).
      { intro Hc. rewrite Hc in Hy0s. unfold Qlt in Hy0s. cbn in Hy0s. lia. }
      rewrite !Qpower_plus by assumption.
      apply (Qle_trans _ (Qpower y (Z.of_nat k) * x)%Q).
      * apply Qmult_le_compat_r; [exact IHk | exact Hx0].
      * rewrite (Qmult_comm (Qpower y (Z.of_nat k)) x).
        rewrite (Qmult_comm (Qpower y (Z.of_nat k)) y).
        apply Qmult_le_compat_r; [exact Hxy |].
        apply Qpower_0_le. exact Hy0.
Defined.

(* Hp discharged at the anchor carrier (the Qabs construction; the    *)
(* x = 1 precedent planb3_dv_hp transfers verbatim). *)
Lemma sl12_dval_pi_hp :
  forall (xpi : Q) (a b : Z), piu_mu_QleT 0 (sl12_dval_pi xpi a b).
Proof.
  intros xpi a b. apply piu_mu_QleT_i. unfold sl12_dval_pi. apply Qabs_nonneg.
Defined.

(* Htri discharged at the anchor carrier: the exact triangle identity *)
(* a*q + b*p = q*(a + b*xpi) + (-b)*(-p + q*xpi) (the xpi terms       *)
(* cancel); the x = 1 precedent planb3_dv_htri transfers verbatim.    *)
Lemma sl12_dval_pi_htri :
  forall (xpi : Q) (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * sl12_dval_pi xpi a b
      + inject_Z (Z.abs b) * sl12_dval_pi xpi (- p)%Z (Z.of_nat q))%Q).
Proof.
  intros xpi0 a b p q Hq. destruct xpi0 as [nx dx].
  apply piu_mu_QleT_i. unfold sl12_dval_pi.
  rewrite (planb3_inj_zabs_qabs (a * Z.of_nat q + b * p)).
  assert (Habsb : (Qabs (inject_Z (- b)) == inject_Z (Z.abs b))%Q).
  { unfold Qabs, inject_Z, Qeq. cbn. rewrite Z.abs_opp. lia. }
  assert (Hid : inject_Z (a * Z.of_nat q + b * p)
                == (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b * (nx # dx)%Q)
                    + inject_Z (- b)
                      * (inject_Z (- p) + inject_Z (Z.of_nat q) * (nx # dx)%Q))%Q).
  { unfold inject_Z, Qplus, Qminus, Qmult, Qeq. cbn.
    rewrite (Pos2Z.inj_mul dx dx).
    ring. }
  rewrite Hid.
  pose proof (Qabs_triangle (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b * (nx # dx)%Q))
              (inject_Z (- b)
               * (inject_Z (- p) + inject_Z (Z.of_nat q) * (nx # dx)%Q))) as Htri0.
  apply (Qle_trans _
    (Qabs (inject_Z (Z.of_nat q) * (inject_Z a + inject_Z b * (nx # dx)%Q))
     + Qabs (inject_Z (- b)
             * (inject_Z (- p) + inject_Z (Z.of_nat q) * (nx # dx)%Q)))%Q).
  - exact Htri0.
  - rewrite (Qabs_Qmult (inject_Z (Z.of_nat q)) (inject_Z a + inject_Z b * (nx # dx)%Q)).
    rewrite (planb3_qabs_inj_nat q).
    rewrite (Qabs_Qmult (inject_Z (- b))
              (inject_Z (- p) + inject_Z (Z.of_nat q) * (nx # dx)%Q)).
    rewrite Habsb.
    apply Qle_refl.
Defined.

(* carrier consistency: at xpi = 1 the anchor carrier coincides with  *)
(* the x = 1 dv carrier (the planb3_g2_anchor_one isomorph, QeqT      *)
(* form - Set-carried). *)
Lemma sl12_dval_pi_one_consistency : forall a b : Z,
  S02_CauchyComplete.QeqT (sl12_dval_pi (1 # 1)%Q a b) (planb3_dv a b).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold sl12_dval_pi, planb3_dv.
  rewrite Qmult_1_r. apply Qeq_refl.
Defined.

(* the base identity the band-end assembly needs (1/4 * 4 == 1). *)
Lemma sl12_quarter_times_four : ((1 # 4)%Q * (4 # 1)%Q) == (1 # 1)%Q.
Proof. unfold Qeq, Qmult, Qnum, Qden. cbn. lia. Qed.

(* the band-end discharge bridge: decay at crho inside (0, 1/4]       *)
(* discharges the (B) Hval-direct face at the anchor carrier (the     *)
(* slot-draft 2.2 band line cast as a proven lemma; positivity of     *)
(* crho is derived from the decay face at n = 1 and the Qabs          *)
(* construction; epos(2n) = 4^n splits via the piu_zz_ec_inject_pow   *)
(* bridge). *)
Lemma sl12_decay_hval_direct :
  forall (xpi : Q) (A B : nat -> Z) (crho : Q),
  S02_CauchyComplete.QleT' crho (1 # 4)%Q ->
  sl12_I_decay_face xpi A B crho ->
  sl12_hval_direct_face (sl12_dval_pi xpi) A B.
Proof.
  intros xpi A B crho Hband Hdecay n.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hband) as HB.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hdecay n)) as HDn.
  assert (Hpos : (0 <= crho)%Q).
  { assert (H0 : (0 <= sl12_dval_pi xpi (A 1%nat) (B 1%nat))%Q).
    { unfold sl12_dval_pi. apply Qabs_nonneg. }
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hdecay 1%nat)) as H1.
    exact (Qle_trans _ _ _ H0 H1). }
  pose proof (sl12_Qpower_le_mono_nonneg crho (1 # 4)%Q n Hpos HB) as Hmono.
  apply piu_mu_QleT_i. unfold piu_mu_epos.
  rewrite <- (qeqT_imp_qeq _ _ (piu_zz_ec_inject_pow 2 (2 * n)%nat ltac:(lia))).
  assert (Hs2 : (Z.of_nat (2 * n) = Z.of_nat n + Z.of_nat n)%Z) by lia.
  rewrite Hs2, (Qpower_plus (inject_Z 2) (Z.of_nat n) (Z.of_nat n)
    ltac:(intro Hc0; exfalso; unfold inject_Z, Qeq in Hc0; cbn in Hc0; lia)).
  apply (Qle_trans _
    (Qpower crho (Z.of_nat n)
     * (Qpower (inject_Z 2) (Z.of_nat n) * Qpower (inject_Z 2) (Z.of_nat n)))%Q).
  - apply Qmult_le_compat_r; [exact HDn |].
    apply Qmult_le_0_compat;
      [apply Qlt_le_weak; apply (piu_zz_ec_pow_pos (inject_Z 2) n
         ltac:(unfold inject_Z, Qlt; cbn; lia))
      | apply Qlt_le_weak; apply (piu_zz_ec_pow_pos (inject_Z 2) n
         ltac:(unfold inject_Z, Qlt; cbn; lia))].
  - rewrite <- (Qmult_power (inject_Z 2) (inject_Z 2) (Z.of_nat n)).
    replace ((inject_Z 2) * (inject_Z 2))%Q with ((4 # 1)%Q) by reflexivity.
    apply (Qle_trans _
      (Qpower (1 # 4)%Q (Z.of_nat n) * Qpower (4 # 1)%Q (Z.of_nat n))%Q).
    + apply Qmult_le_compat_r; [exact Hmono |].
      apply Qpower_0_le. unfold Qle. cbn. lia.
    + rewrite <- (Qmult_power (1 # 4)%Q (4 # 1)%Q (Z.of_nat n)).
      rewrite sl12_quarter_times_four.
      assert (Hqone : Qpower (1 # 1)%Q (Z.of_nat n) == (1 # 1)%Q).
      { change (Qpower (inject_Z 1%Z) (Z.of_nat n) == inject_Z 1%Z).
        rewrite (qeqT_imp_qeq _ _ (piu_zz_ec_inject_pow 1 n%nat ltac:(lia))).
        rewrite (Z.pow_1_l (Z.of_nat n) ltac:(lia)). reflexivity. }
      rewrite Hqone. apply Qle_refl.
Defined.

(* ==== Section 4: the pinned pi-bracket anchor point.                  ==== *)

(* The anchor is the midpoint of the exact rational Machin window     *)
(* [LB, UB] with                                                      *)
(*   LB = 16*S_182(atan(1/5)) - 4*S_50(atan(1/239)),                  *)
(*   UB = 16*S_181(atan(1/5)) - 4*S_49(atan(1/239)),                  *)
(* window width ~1.4e-237, produced by the seat's exact-arithmetic    *)
(* script (stdlib fractions only, rerunnable). The identification of  *)
(* this window with a pi-bracket rests on Machin's formula with the   *)
(* alternating-series error bound (literature); the Coq side pins     *)
(* only the rational window-membership faces below - no real number,  *)
(* no classical principle, and the bracket semantics is routed, not   *)
(* claimed. *)
Definition sl12_xpi_lb : Q := (215326759435765629896379065815873445445452340634586750589067009029981314994213375039067684329829994228708281666570484275123462941313946508626604567638859820897351857211037837352397971001600768124992577765672484110521885855176064759254954250715259731715894537266860990682069052532039898309594394354199511463801077124649283376002219648768042291760917747383126030547649929639957143450712502173396213325017730852165511543042737539045082495469934659598989345192925268743155244205737023938530777875549493175046071838933085905528824351587988550104432314278633760865485838880614801256739028449874924297285675695069322555157099622229723564689132 # 68540636288323031691785297633823801932352698239272980775438498767148487888766253627993104277037882550098539663304411276490450218326067026054482944568922340137189648377804013974686112498404448028235033331097727320770287222758952353622495059667282231585514526378694698704811119479722248167354540080124116920364732511478283078090522653770441214149570352591988573462362823568487476857586534178840783084452444258197592431191488661870666929722988171736054594482190269260331080917152416225516505344919679030414003149595350631467072367344742978638324013775407066524815183290376393763277685507776424106256285551097562347422353923320770263671875)%Q.
Definition sl12_xpi_ub : Q := (491987193029214741812442744738740283091587325975529191215923864912062507751378487824263407864168764013521830283046905291173093066831757540770411180323972473179105417430067692296252980063297499042708041382119118595084825677340479804536089888898082756932110625910163289146870795062900967567431910119334806159093489968758830714202364473330442441932140524288661471943593415556604975249427125550371050958527080273946570899764976805285017916305310329649258740183350899420404266587642842118819744585198395246294949991828528198252019259156280466440306672401170092492882710963394991874898725476326819469342194051527438855544487366869579700277514424 # 156604387417011995730658719445665975607116739045020477394952899523131551067768686939383764376347235565767147364304451060976440276840130983810324811068856519639056396199541723289921817280854419032832533556225331291588783058048564695650821612130193134015847010451096795388700638232048581502698347356670787304326155431526040308144349780240854903737504324416279172189745073802222926623288016753182574822680322738900187090483560954188574627708272294309406979656687614816774866922746526688709132072286279435851130956321440936801225627803962547311988239634601081878558723389183599526087386955587884854938611478569754353884491138160228729248046875)%Q.
Definition sl12_xpi_pi_bracket : Q := (12299679825730368545311068618468507077289683149388229780398096622801562693784462195606585196604219100338045757076172632279327326670793938519260279508099311829477635435751692307406324501582437476067701034552977964877120641933511995113402244488779210029323188755487224438711118113127587610264069576444800224150559287828031241787840950195270202397989447877744039394751073509939558186141913487702920687650757405427605228672134315549959802565685447966092669445674428380693938684483487798681655088829611240404590209653705002483006228632982252815761472516969545683359742188392236429729329090496738018759404966333120372530870435846561766122772884786 # 3915109685425299893266467986141649390177918476125511934873822488078288776694217173484594109408680889144178684107611276524411006921003274595258120276721412990976409904988543082248045432021360475820813338905633282289719576451214117391270540303254828350396175261277419884717515955801214537567458683916769682608153885788151007703608744506021372593437608110406979304743626845055573165582200418829564370567008068472504677262089023854714365692706807357735174491417190370419371673068663167217728301807156985896278273908036023420030640695099063682799705990865027046963968084729589988152184673889697121373465286964243858847112278454005718231201171875)%Q.

(* window membership faces (pure rational statements, vm_compute). *)
Example sl12_xpi_above_lb : piu_mu_QltT sl12_xpi_lb sl12_xpi_pi_bracket.
Proof. apply piu_mu_QltT_i. unfold Qlt. cbn. lia. Defined.

Example sl12_xpi_below_ub : piu_mu_QltT sl12_xpi_pi_bracket sl12_xpi_ub.
Proof. apply piu_mu_QltT_i. unfold Qlt. cbn. lia. Defined.

(* ==== Section 5: head-side machine anchors over the frozen tables.    ==== *)

(* The (B) Hval-direct shape at the anchor carrier, n = 1..40: pass   *)
(* set 40/40, exact margins (worst 5.9e-12 at n = 40, best-margin     *)
(* index n = 5 at 2.84e-1); first-hand exact-arithmetic reproduction  *)
(* of the survey table row. Domain honesty: the frozen tables answer  *)
(* 0 outside n = 1..40 (planb3_g1_out_of_dom) - these anchors are the *)
(* head band only; the forall-n decay face is NOT claimed (the SL2-b  *)
(* breakthrough item of the survey). *)
Example sl12_hval_head_1 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 1%nat) (planb3_g1_B 1%nat)
               * piu_mu_epos (2%nat * 1%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_2 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 2%nat) (planb3_g1_B 2%nat)
               * piu_mu_epos (2%nat * 2%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_3 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 3%nat) (planb3_g1_B 3%nat)
               * piu_mu_epos (2%nat * 3%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_4 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 4%nat) (planb3_g1_B 4%nat)
               * piu_mu_epos (2%nat * 4%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_5 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 5%nat) (planb3_g1_B 5%nat)
               * piu_mu_epos (2%nat * 5%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_6 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 6%nat) (planb3_g1_B 6%nat)
               * piu_mu_epos (2%nat * 6%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_7 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 7%nat) (planb3_g1_B 7%nat)
               * piu_mu_epos (2%nat * 7%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_8 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 8%nat) (planb3_g1_B 8%nat)
               * piu_mu_epos (2%nat * 8%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_9 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 9%nat) (planb3_g1_B 9%nat)
               * piu_mu_epos (2%nat * 9%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_10 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 10%nat) (planb3_g1_B 10%nat)
               * piu_mu_epos (2%nat * 10%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_11 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 11%nat) (planb3_g1_B 11%nat)
               * piu_mu_epos (2%nat * 11%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_12 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 12%nat) (planb3_g1_B 12%nat)
               * piu_mu_epos (2%nat * 12%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_13 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 13%nat) (planb3_g1_B 13%nat)
               * piu_mu_epos (2%nat * 13%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_14 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 14%nat) (planb3_g1_B 14%nat)
               * piu_mu_epos (2%nat * 14%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_15 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 15%nat) (planb3_g1_B 15%nat)
               * piu_mu_epos (2%nat * 15%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_16 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 16%nat) (planb3_g1_B 16%nat)
               * piu_mu_epos (2%nat * 16%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_17 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 17%nat) (planb3_g1_B 17%nat)
               * piu_mu_epos (2%nat * 17%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_18 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 18%nat) (planb3_g1_B 18%nat)
               * piu_mu_epos (2%nat * 18%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_19 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 19%nat) (planb3_g1_B 19%nat)
               * piu_mu_epos (2%nat * 19%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_20 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 20%nat) (planb3_g1_B 20%nat)
               * piu_mu_epos (2%nat * 20%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_21 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 21%nat) (planb3_g1_B 21%nat)
               * piu_mu_epos (2%nat * 21%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_22 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 22%nat) (planb3_g1_B 22%nat)
               * piu_mu_epos (2%nat * 22%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_23 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 23%nat) (planb3_g1_B 23%nat)
               * piu_mu_epos (2%nat * 23%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_24 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 24%nat) (planb3_g1_B 24%nat)
               * piu_mu_epos (2%nat * 24%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_25 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 25%nat) (planb3_g1_B 25%nat)
               * piu_mu_epos (2%nat * 25%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_26 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 26%nat) (planb3_g1_B 26%nat)
               * piu_mu_epos (2%nat * 26%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_27 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 27%nat) (planb3_g1_B 27%nat)
               * piu_mu_epos (2%nat * 27%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_28 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 28%nat) (planb3_g1_B 28%nat)
               * piu_mu_epos (2%nat * 28%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_29 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 29%nat) (planb3_g1_B 29%nat)
               * piu_mu_epos (2%nat * 29%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_30 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 30%nat) (planb3_g1_B 30%nat)
               * piu_mu_epos (2%nat * 30%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_31 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 31%nat) (planb3_g1_B 31%nat)
               * piu_mu_epos (2%nat * 31%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_32 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 32%nat) (planb3_g1_B 32%nat)
               * piu_mu_epos (2%nat * 32%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_33 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 33%nat) (planb3_g1_B 33%nat)
               * piu_mu_epos (2%nat * 33%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_34 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 34%nat) (planb3_g1_B 34%nat)
               * piu_mu_epos (2%nat * 34%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_35 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 35%nat) (planb3_g1_B 35%nat)
               * piu_mu_epos (2%nat * 35%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_36 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 36%nat) (planb3_g1_B 36%nat)
               * piu_mu_epos (2%nat * 36%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_37 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 37%nat) (planb3_g1_B 37%nat)
               * piu_mu_epos (2%nat * 37%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_38 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 38%nat) (planb3_g1_B 38%nat)
               * piu_mu_epos (2%nat * 38%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_39 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 39%nat) (planb3_g1_B 39%nat)
               * piu_mu_epos (2%nat * 39%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

Example sl12_hval_head_40 :
  piu_mu_QleT (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 40%nat) (planb3_g1_B 40%nat)
               * piu_mu_epos (2%nat * 40%nat)) (1 # 1)%Q.
Proof. apply piu_mu_QleT_i. unfold Qle, sl12_dval_pi, piu_mu_epos. cbn. lia. Defined.

(* ==== Section 6: assumption audit. ==== *)

Print Assumptions sl12_lzn_pow_bound_face.
Print Assumptions sl12_hval_direct_face.
Print Assumptions sl12_dval_pi.
Print Assumptions sl12_I_decay_face.
Print Assumptions sl12_I_decay_from_LZn_face.
Print Assumptions sl12_Qpower_le_mono_nonneg.
Print Assumptions sl12_dval_pi_hp.
Print Assumptions sl12_dval_pi_htri.
Print Assumptions sl12_dval_pi_one_consistency.
Print Assumptions sl12_quarter_times_four.
Print Assumptions sl12_decay_hval_direct.
Print Assumptions sl12_xpi_lb.
Print Assumptions sl12_xpi_ub.
Print Assumptions sl12_xpi_pi_bracket.
Print Assumptions sl12_xpi_above_lb.
Print Assumptions sl12_xpi_below_ub.
Print Assumptions sl12_hval_head_1.
Print Assumptions sl12_hval_head_2.
Print Assumptions sl12_hval_head_3.
Print Assumptions sl12_hval_head_4.
Print Assumptions sl12_hval_head_5.
Print Assumptions sl12_hval_head_6.
Print Assumptions sl12_hval_head_7.
Print Assumptions sl12_hval_head_8.
Print Assumptions sl12_hval_head_9.
Print Assumptions sl12_hval_head_10.
Print Assumptions sl12_hval_head_11.
Print Assumptions sl12_hval_head_12.
Print Assumptions sl12_hval_head_13.
Print Assumptions sl12_hval_head_14.
Print Assumptions sl12_hval_head_15.
Print Assumptions sl12_hval_head_16.
Print Assumptions sl12_hval_head_17.
Print Assumptions sl12_hval_head_18.
Print Assumptions sl12_hval_head_19.
Print Assumptions sl12_hval_head_20.
Print Assumptions sl12_hval_head_21.
Print Assumptions sl12_hval_head_22.
Print Assumptions sl12_hval_head_23.
Print Assumptions sl12_hval_head_24.
Print Assumptions sl12_hval_head_25.
Print Assumptions sl12_hval_head_26.
Print Assumptions sl12_hval_head_27.
Print Assumptions sl12_hval_head_28.
Print Assumptions sl12_hval_head_29.
Print Assumptions sl12_hval_head_30.
Print Assumptions sl12_hval_head_31.
Print Assumptions sl12_hval_head_32.
Print Assumptions sl12_hval_head_33.
Print Assumptions sl12_hval_head_34.
Print Assumptions sl12_hval_head_35.
Print Assumptions sl12_hval_head_36.
Print Assumptions sl12_hval_head_37.
Print Assumptions sl12_hval_head_38.
Print Assumptions sl12_hval_head_39.
Print Assumptions sl12_hval_head_40.
