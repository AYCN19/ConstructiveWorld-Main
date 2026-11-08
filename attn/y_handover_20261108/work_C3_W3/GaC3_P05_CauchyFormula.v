(* ConstructiveWorld-Main - discrete Cauchy integral formula faces on the C3 path-step carriers. *)

(** * GaC3_P05_CauchyFormula: step-carrier faces of the Cauchy integral formula.

    Mission.  Node C3-P05 (segment C3): the step-carrier faces of the
    Cauchy integral formula node over the P02 path carrier.  (1) The
    primitive-certificate telescope: value data whose per-segment
    contribution equals the forward difference of a primitive-value list
    makes the closed-loop path sum vanish in both components - the
    discrete path-independence face of the draft P04/P05
    primitive-existence corollary [GaC3_P05_loop_cancel],
    [GaC3_P05_loop_cancel_cx].  (2) The affine instance: endpoint-sum data
    (twice the midpoint data) against the square primitive on the P04
    rectangle boundary - the Cauchy-zero face beyond constant data
    [GaC3_P05_rect_endsum_loop_zero].  (3) The Cauchy kernel: the exact
    complex inverse on Q pairs with its multiplicative identity, at the
    pair level and at the Cx level.  Not cast here, reasons on record: the
    circle-parametrised formula face (the parametrisation z0 + r*exp(i*t)
    consumes the 2pi-periodicity reduction, the Z02-recorded C1.4 residue
    the tree does not yet carry) and the native derivative-bound faces
    (the base carrier has no complex-differentiability machinery; gap
    registered at P04); the estimate faces continue in
    [GaC3_P05_CauchyFormula_b].

    Dependencies.  [GaC3_P02_LineIntegralAlg] (path carrier, path sums,
    [seg_contrib]), [GaC3_P01_LineIntegralDef] (Cx bridges over the
    rational embedding), [CxRealPairCore] (base module), [S01_BaseRing],
    [S02_CauchyComplete]; Stdlib [QArith], [List].

    References.  AFP PNT_with_Remainder PNT_Complex_Analysis_Lemmas
    ([Schwarz_Lemma1] :310, [Schwarz_Lemma2] :342,
    [Borel_Caratheodory1/2/3] :375/:484/:497, statement-shape anchors for
    the analytic-layer continuation) and Zeta_Zerofree [deriv_zeta_bound]
    :355-358 (the B/r + 1/|s-1|^2 consumption shape; its step-carrier
    analogues are cast in the _b leaf); drafts_C3 P05 statement skeleton
    (the [holo_on_disk] / [HasDerivativeAt] / [circle_seg] faces are the
    deferrals recorded above); cards_C3 C3-P05.

    Constructivity.  Set-carried statements; the data-validation
    predicates are carried by the S01/S02 boolean-reflection canon ([Id
    (Qeq_bool ...) true], the S02 [QleT'] :99 shape) with native bridges;
    zero assumed constants, zero abandoned proofs, zero classical choice;
    all numerics stay in Q (decidable, exact).

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_P05_CauchyFormula.v] compiles cleanly (exit 0) from the work
    directory (sandbox pair), single compile lane under the cpu_guard v3
    wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P04_CauchyRect.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. Q-pair algebra and the Set-carried pair equality.           *)
(* ===================================================================== *)

(* Complex product of two Q pairs (both components). *)
Definition GaC3_P05_qmul (u v : Q * Q) : Q * Q :=
  (fst u * fst v - snd u * snd v, fst u * snd v + snd u * fst v).

(* Componentwise difference of two Q pairs. *)
Definition GaC3_P05_vsub (u v : Q * Q) : Q * Q :=
  (fst u - fst v, snd u - snd v).

(* Set-carried pair equality: the S02 QleT' :99 boolean-reflection canon  *)
(* applied componentwise - Qeq_bool is the decidable Q equality check, so *)
(* the bearer is data, and the native Qeq faces are recovered by bridges. *)
Definition GaC3_P05_veq (u v : Q * Q) : Set :=
  And (Id (Qeq_bool (fst u) (fst v)) true)
      (Id (Qeq_bool (snd u) (snd v)) true).

(* Bridge (elim): the S01 Id carrier reflects into native equality. *)
Lemma GaC3_P05_id_eq : forall (A : Set) (x y : A), Id x y -> x = y.
Proof.
  intros A x y p.
  exact (match p in (Id _ y') return x = y' with id_refl => eq_refl end).
Qed.

(* Bridge (intro): native equality into the S01 Id carrier. *)
Lemma GaC3_P05_eq_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y E. destruct E. apply id_refl.
Qed.

(* Mathematical Q equality reflects into the boolean check. *)
Lemma GaC3_P05_qeq_to_qeqb : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq_bool, Qeq in *. rewrite H. apply Z.eqb_refl.
Qed.

(* Bridge (intro) for the pair bearer. *)
Lemma GaC3_P05_veq_intro : forall u v : Q * Q,
  fst u == fst v -> snd u == snd v -> GaC3_P05_veq u v.
Proof.
  intros [a b] [c d] Ha Hb. unfold GaC3_P05_veq. split.
  - apply GaC3_P05_eq_id. apply GaC3_P05_qeq_to_qeqb. exact Ha.
  - apply GaC3_P05_eq_id. apply GaC3_P05_qeq_to_qeqb. exact Hb.
Qed.

(* Bridge (elim) for the pair bearer. *)
Lemma GaC3_P05_veq_elim : forall u v : Q * Q,
  GaC3_P05_veq u v -> fst u == fst v /\ snd u == snd v.
Proof.
  intros [a b] [c d] H. unfold GaC3_P05_veq in H.
  destruct H as [H1 H2]. split.
  - apply Qeq_bool_eq. apply GaC3_P05_id_eq. exact H1.
  - apply Qeq_bool_eq. apply GaC3_P05_id_eq. exact H2.
Qed.

Lemma GaC3_P05_veq_refl : forall u : Q * Q, GaC3_P05_veq u u.
Proof. intro u. apply GaC3_P05_veq_intro; apply Qeq_refl. Qed.

(* Qeq transitivity in rewrite-free form. *)
Lemma GaC3_P05_qeq_trans2 : forall x y z : Q, x == y -> y == z -> x == z.
Proof.
  intros x y z H1 H2. rewrite H1. exact H2.
Qed.

(* ===================================================================== *)
(* Section 2. The primitive-certificate telescope (path independence).    *)
(* ===================================================================== *)

(* The certificate: for every segment of ps (zipped with value data vs)   *)
(* the segment contribution equals the forward difference of the          *)
(* primitive values fs.  The recursive bearer bites on every segment:     *)
(* any zip mismatch collapses to Empty_set, so a well-formed certificate  *)
(* forces the three lists to run in lockstep (no length premise needed).  *)
Fixpoint GaC3_P05_prim_ok (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (fs : list (Q * Q)) : Set :=
  match ps with
  | nil => Id (Nat.eqb 0 0) true
  | p :: ps' =>
      match vs, fs with
      | v :: vs', f0 :: f1 :: fs' =>
          And (GaC3_P05_veq (GaC3_P02_seg_contrib p v) (GaC3_P05_vsub f1 f0))
              (GaC3_P05_prim_ok ps' vs' (f1 :: fs'))
      | _, _ => Empty_set
      end
  end.

(* The primitive value at the walk's start. *)
Definition GaC3_P05_prim_head (fs : list (Q * Q)) : Q * Q :=
  match fs with
  | nil => (0, 0)
  | f :: _ => f
  end.

(* The primitive value at the walk's end: consume one value per segment. *)
Fixpoint GaC3_P05_prim_tail (ps : GaC3_P02_cpath) (fs : list (Q * Q)) : Q * Q :=
  match ps, fs with
  | _ :: ps', _ :: f1 :: fs' => GaC3_P05_prim_tail ps' (f1 :: fs')
  | _, f :: _ => f
  | _, nil => (0, 0)
  end.

(* Telescope, real component: the prefix sum plus the start value equals  *)
(* the end value - the discrete fundamental theorem at the step carrier.  *)
Lemma GaC3_P05_sumR_prim : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (fs : list (Q * Q)),
  GaC3_P05_prim_ok ps vs fs ->
  GaC3_P02_path_sumR ps vs + fst (GaC3_P05_prim_head fs)
  == fst (GaC3_P05_prim_tail ps fs).
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs fs H.
  - destruct fs as [| f fs'].
    + cbn [GaC3_P02_path_sumR GaC3_P05_prim_head GaC3_P05_prim_tail fst snd].
      ring.
    + cbn [GaC3_P02_path_sumR GaC3_P05_prim_head GaC3_P05_prim_tail].
      ring.
  - destruct vs as [| v vs'].
    + cbn [GaC3_P05_prim_ok] in H. destruct H.
    + destruct fs as [| f0 fs'].
      * cbn [GaC3_P05_prim_ok] in H. destruct H.
      * destruct fs' as [| f1 fs''].
        -- cbn [GaC3_P05_prim_ok] in H. destruct H.
        -- cbn [GaC3_P05_prim_ok] in H. destruct H as [Hcert Hrest].
           cbn [GaC3_P02_path_sumR GaC3_P05_prim_head GaC3_P05_prim_tail].
           pose proof (IH vs' (f1 :: fs'') Hrest) as IH2.
           cbn [GaC3_P05_prim_head] in IH2.
           destruct (GaC3_P05_veq_elim _ _ Hcert) as [Hc1 Hc2].
           cbn [GaC3_P05_vsub fst snd] in Hc1.
           rewrite Hc1. rewrite <- IH2. ring.
Qed.

(* Telescope, imaginary component: mirror of the real one. *)
Lemma GaC3_P05_sumI_prim : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (fs : list (Q * Q)),
  GaC3_P05_prim_ok ps vs fs ->
  GaC3_P02_path_sumI ps vs + snd (GaC3_P05_prim_head fs)
  == snd (GaC3_P05_prim_tail ps fs).
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs fs H.
  - destruct fs as [| f fs'].
    + cbn [GaC3_P02_path_sumI GaC3_P05_prim_head GaC3_P05_prim_tail fst snd].
      ring.
    + cbn [GaC3_P02_path_sumI GaC3_P05_prim_head GaC3_P05_prim_tail].
      ring.
  - destruct vs as [| v vs'].
    + cbn [GaC3_P05_prim_ok] in H. destruct H.
    + destruct fs as [| f0 fs'].
      * cbn [GaC3_P05_prim_ok] in H. destruct H.
      * destruct fs' as [| f1 fs''].
        -- cbn [GaC3_P05_prim_ok] in H. destruct H.
        -- cbn [GaC3_P05_prim_ok] in H. destruct H as [Hcert Hrest].
           cbn [GaC3_P02_path_sumI GaC3_P05_prim_head GaC3_P05_prim_tail].
           pose proof (IH vs' (f1 :: fs'') Hrest) as IH2.
           cbn [GaC3_P05_prim_head] in IH2.
           destruct (GaC3_P05_veq_elim _ _ Hcert) as [Hc1 Hc2].
           cbn [GaC3_P05_vsub fst snd] in Hc2.
           rewrite Hc2. rewrite <- IH2. ring.
Qed.

(* Loop cancellation: a certificate whose start and end primitive values  *)
(* coincide kills both components of the closed-loop sum - the discrete   *)
(* face of Cauchy's theorem behind the integral formula. *)
Theorem GaC3_P05_loop_cancel : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (fs : list (Q * Q)),
  GaC3_P05_prim_ok ps vs fs ->
  GaC3_P05_veq (GaC3_P05_prim_tail ps fs) (GaC3_P05_prim_head fs) ->
  GaC3_P02_path_sumR ps vs == 0 /\ GaC3_P02_path_sumI ps vs == 0.
Proof.
  intros ps vs fs Hcert Hclose.
  destruct (GaC3_P05_veq_elim _ _ Hclose) as [Hc1 Hc2].
  pose proof (GaC3_P05_sumR_prim ps vs fs Hcert) as HR.
  pose proof (GaC3_P05_sumI_prim ps vs fs Hcert) as HI.
  rewrite Hc1 in HR. rewrite Hc2 in HI.
  split.
  - apply (GaC3_P05_qeq_trans2 _
             (GaC3_P02_path_sumR ps vs + fst (GaC3_P05_prim_head fs)
              + (- fst (GaC3_P05_prim_head fs)))).
    + ring.
    + rewrite HR. ring.
  - apply (GaC3_P05_qeq_trans2 _
             (GaC3_P02_path_sumI ps vs + snd (GaC3_P05_prim_head fs)
              + (- snd (GaC3_P05_prim_head fs)))).
    + ring.
    + rewrite HI. ring.
Qed.

(* The Cx-level face: the line integral over a certified closed loop is   *)
(* zero in the base complex carrier. *)
Theorem GaC3_P05_loop_cancel_cx : forall (ps : GaC3_P02_cpath)
  (vs : list (Q * Q)) (fs : list (Q * Q)),
  GaC3_P05_prim_ok ps vs fs ->
  GaC3_P05_veq (GaC3_P05_prim_tail ps fs) (GaC3_P05_prim_head fs) ->
  c_eq (GaC3_P02_line_integral ps vs) (c_of_Q 0 0).
Proof.
  intros ps vs fs Hcert Hclose.
  destruct (GaC3_P05_loop_cancel ps vs fs Hcert Hclose) as [HR HI].
  unfold GaC3_P02_line_integral. apply GaC3_P01_cofQ_eq; assumption.
Qed.

(* ===================================================================== *)
(* Section 3. The affine instance: endpoint-sum data against z^2.         *)
(* ===================================================================== *)

(* The endpoint sum of a segment: z0 + z1, i.e. twice the midpoint - the  *)
(* degree-one sample data of the affine face, division-free. *)
Definition GaC3_P05_endsum (s : GaC3_P02_pseg) : Q * Q :=
  (fst (fst s) + fst (snd s), snd (fst s) + snd (snd s)).

(* The square primitive z^2 on Q pairs (division-free). *)
Definition GaC3_P05_sq (z : Q * Q) : Q * Q :=
  (fst z * fst z - snd z * snd z, 2 * (fst z * snd z)).

(* Per-segment certificate: the endpoint-sum contribution equals the      *)
(* forward difference of z^2 - the identity (z1 - z0) * (z0 + z1) =       *)
(* z1^2 - z0^2 componentwise, pure Q algebra. *)
Lemma GaC3_P05_endsum_cert : forall s : GaC3_P02_pseg,
  GaC3_P05_veq (GaC3_P02_seg_contrib s (GaC3_P05_endsum s))
               (GaC3_P05_vsub (GaC3_P05_sq (snd s)) (GaC3_P05_sq (fst s))).
Proof.
  intros [[x0 y0] [x1 y1]].
  apply GaC3_P05_veq_intro;
    cbn [GaC3_P02_seg_contrib GaC3_P02_seg_dz GaC3_P05_endsum GaC3_P05_sq
         GaC3_P05_vsub fst snd]; ring.
Qed.

(* The primitive values of z^2 along the vertex walk of ps, starting at   *)
(* z0: one value per vertex. *)
Fixpoint GaC3_P05_sqvals (z0 : Q * Q) (ps : GaC3_P02_cpath) : list (Q * Q) :=
  match ps with
  | nil => GaC3_P05_sq z0 :: nil
  | p :: ps' => GaC3_P05_sq z0 :: GaC3_P05_sqvals (snd p) ps'
  end.

(* The certificate holds on the P04 rectangle: the boundary is a          *)
(* contiguous walk starting at (c, -T), so the square-value list threads  *)
(* through the four segments definitionally - the affine (degree-one)     *)
(* integrand data integrates to zero around the rectangle at the step     *)
(* carrier. *)
Theorem GaC3_P05_rect_endsum_loop_zero : forall c b T : Q,
  c_eq (GaC3_P02_line_integral (GaC3_P04_rect_boundary c b T)
        (map GaC3_P05_endsum (GaC3_P04_rect_boundary c b T))) (c_of_Q 0 0).
Proof.
  intros c b T.
  assert (Hcert : GaC3_P05_prim_ok (GaC3_P04_rect_boundary c b T)
            (map GaC3_P05_endsum (GaC3_P04_rect_boundary c b T))
            (GaC3_P05_sqvals (c, - T) (GaC3_P04_rect_boundary c b T))).
  { cbn [GaC3_P04_rect_boundary map GaC3_P05_sqvals GaC3_P05_prim_ok].
    split; [ apply GaC3_P05_endsum_cert
           | split; [ apply GaC3_P05_endsum_cert
                    | split; [ apply GaC3_P05_endsum_cert
                             | split; [ apply GaC3_P05_endsum_cert
                                      | exact (@id_refl bool (Nat.eqb 0 0)) ] ] ] ]. }
  assert (Hcl : GaC3_P05_veq (GaC3_P05_prim_tail (GaC3_P04_rect_boundary c b T)
                (GaC3_P05_sqvals (c, - T) (GaC3_P04_rect_boundary c b T)))
                (GaC3_P05_prim_head (GaC3_P05_sqvals (c, - T)
                  (GaC3_P04_rect_boundary c b T)))).
  { cbn [GaC3_P04_rect_boundary GaC3_P05_sqvals GaC3_P05_prim_tail
         GaC3_P05_prim_head].
    apply GaC3_P05_veq_refl. }
  exact (GaC3_P05_loop_cancel_cx _ _ _ Hcert Hcl).
Qed.

(* ===================================================================== *)
(* Section 4. The Cauchy kernel: the exact complex inverse on Q pairs.    *)
(* ===================================================================== *)

(* The Cauchy kernel 1/(a + i b) at Q precision: (a - i b)/(a^2 + b^2).   *)
(* Qinv is total, so the definition carries no premise; the positivity of *)
(* the squared norm is the premise of the identity below. *)
Definition GaC3_P05_cinv (a b : Q) : Q * Q :=
  (a * / (a * a + b * b), - (b * / (a * a + b * b))).

(* The kernel identity: (a + i b) multiplied by its inverse is 1 - the    *)
(* pair-level face. *)
Lemma GaC3_P05_cinv_mult : forall a b : Q,
  QltT 0 (a * a + b * b) ->
  GaC3_P05_veq (GaC3_P05_qmul (a, b) (GaC3_P05_cinv a b)) (1, 0).
Proof.
  intros a b Hd.
  assert (Hne0 : ~ (a * a + b * b == 0)).
  { intro Hzz. apply (Qlt_not_eq 0 (a * a + b * b)).
    - apply QltT_to_Qlt. exact Hd.
    - apply Qeq_sym. exact Hzz. }
  apply GaC3_P05_veq_intro;
    cbn [GaC3_P05_qmul GaC3_P05_cinv fst snd].
  - rewrite <- (Qmult_inv_r (a * a + b * b) Hne0). ring.
  - ring.
Qed.

(* The kernel identity at the Cx level: the rational-embedded product of  *)
(* the point (a, b) with its inverse is the unit - consuming the P01      *)
(* product bridge. *)
Lemma GaC3_P05_cinv_cx : forall a b : Q,
  QltT 0 (a * a + b * b) ->
  c_eq (c_mult (c_of_Q a b)
          (c_of_Q (fst (GaC3_P05_cinv a b)) (snd (GaC3_P05_cinv a b))))
       (c_of_Q 1 0).
Proof.
  intros a b Hd.
  apply (c_eq_trans _
    (c_of_Q (a * fst (GaC3_P05_cinv a b) - b * snd (GaC3_P05_cinv a b))
            (a * snd (GaC3_P05_cinv a b) + b * fst (GaC3_P05_cinv a b)))).
  - exact (GaC3_P01_cmuloQ a b (fst (GaC3_P05_cinv a b)) (snd (GaC3_P05_cinv a b))).
  - apply GaC3_P01_cofQ_eq.
    + destruct (GaC3_P05_veq_elim _ _ (GaC3_P05_cinv_mult a b Hd)) as [H1 H2].
      cbn [GaC3_P05_qmul fst snd] in H1. exact H1.
    + destruct (GaC3_P05_veq_elim _ _ (GaC3_P05_cinv_mult a b Hd)) as [H1 H2].
      cbn [GaC3_P05_qmul fst snd] in H2. exact H2.
Qed.
