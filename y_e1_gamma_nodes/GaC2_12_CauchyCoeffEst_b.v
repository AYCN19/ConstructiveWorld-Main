(* ConstructiveWorld-Main - the Cauchy-coefficient algebra kit: the
   pure algebra faces and the cancellation lemma of the quotient
   machine. *)

(** * GaC2_12_CauchyCoeffEst_b: the Cauchy-coefficient algebra kit.

    Mission.  Node C2-12 machine cluster, piece b.  Casts the pure
      algebra faces consumed by the difference-quotient machine:
      [gaC12_shift_eq] (the punctured-disk shift identity
      (z0+w)-z0 = w), [gaC12_scale_plus] and [gaC12_scale_one] (the
      complex-scale distributivity and unit faces), [gaC12_conj_wd]
      (conjugate well-definedness along [c_eq]), and
      [gaC12_quot_ringC] (the two-term recombination ring face
      folding the first-order term into the conjugate-carried
      remainder).  Also casts the cancellation lemma
      [gaC12_cauchy_cancel]: with [s] positive and [K*s = 1], the
      five-factor product (s*T2)*((K*K)*s) equals [T2] - the
      account by which the squared-modulus chain of the quotient
      estimate collapses onto [T2] itself.  Set-carried throughout;
      zero Sections.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog] (the Setoid compatibility and order
      faces), [CxRealPairCore], [CxRealPairExpLog],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], and the machine cluster
      [GaC2_11_MaxModulusDisk_a] (the [mm_*] algebra kit: the unit
      face [mm_mult_one_l] is consumed by [gaC12_cauchy_cancel]).

    References.  drafts_C2.md C2.12 card (the difference-quotient
      route: g = (f - f(z0))/(z - z0) is disk-expandable with
      g(z0) = f'(z0), and the circle bound 2M/R is pushed through
      C2-11) and the GaC2_12 seat forensics registered in SOP
      section 2 (C2-11 L14 packs only a0/a1/Tmaj; the
      difference-quotient expandability needs second-order data,
      which the Tmaj quadratic face supplies).  Ahlfors Ch.2 the
      classical quotient argument (statement architecture only; no
      proof object transcribed).

    Constructivity.  All statements are Set-sorted; the ring faces
      are coordinate-level polynomial identities proven by
      [real_eq_of_zero_diff] plus [ring] at the rational-point
      level, the same style as the [mm_*] cluster; the order faces
      propagate through monotone faces only; no Section wrappers, no
      premise slots, zero assumed constants, zero admitted goals;
      every proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_b.v] from the flat
      build directory; acceptance via 50_toolkit/accept_node.py
      (six-chain gate), thermal-guard wrapped. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_12_CauchyCoeffEst_a.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(* Section 1. The pure algebra faces.                                    *)
(* ===================================================================== *)

Lemma gaC12_shift_eq : forall z0 w : Cx,
  c_eq (c_plus (c_plus z0 w) (c_opp z0)) w.
Proof.
  intros [zr zi] [wr wi].
  destruct zr as [zrq zrqc]. destruct zi as [ziq ziqc].
  destruct wr as [wrq wrqc]. destruct wi as [wiq wiqc].
  unfold c_eq; split; apply real_eq_of_zero_diff; intro n;
    cbn [projT1 real_plus real_opp real_zero c_plus c_opp cRe cIm fst snd]; ring.
Qed.

Lemma gaC12_scale_plus : forall (k : Real) (z w : Cx),
  c_eq (c_scale k (c_plus z w)) (c_plus (c_scale k z) (c_scale k w)).
Proof.
  intros k [zr zi] [wr wi].
  destruct k as [kq kqc].
  destruct zr as [zrq zrqc]. destruct zi as [ziq ziqc].
  destruct wr as [wrq wrqc]. destruct wi as [wiq wiqc].
  unfold c_eq; split; apply real_eq_of_zero_diff; intro n;
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_scale c_plus cRe cIm fst snd]; ring.
Qed.

Lemma gaC12_scale_one : forall z : Cx, c_eq (c_scale real_one z) z.
Proof.
  intros [zr zi].
  destruct zr as [zrq zrqc]. destruct zi as [ziq ziqc].
  unfold c_eq; split; apply real_eq_of_zero_diff; intro n;
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_scale cRe cIm fst snd]; ring.
Qed.

Lemma gaC12_conj_wd : forall z w : Cx, c_eq z w -> c_eq (c_conj z) (c_conj w).
Proof.
  intros z w H. unfold c_eq in H. destruct H as [Hr Hi].
  unfold c_eq; split.
  - exact Hr.
  - exact (RealSetoid.real_eq_opp_compat _ _ Hi).
Qed.

(* The two-term recombination: (X - a1*d) * conj(d) equals
   X * conj(d) - |d|^2 * a1, the algebra that folds the first-order
   term of the quotient into the remainder. *)
Lemma gaC12_quot_ringC : forall (X a1 d : Cx),
  c_eq (c_plus (c_mult X (c_conj d)) (c_scale (c_norm_sq d) (c_opp a1)))
       (c_mult (c_plus X (c_opp (c_mult a1 d))) (c_conj d)).
Proof.
  intros [xr xi] [ar ai] [dr di].
  destruct xr as [xrq xrqc]. destruct xi as [xiq xiqc].
  destruct ar as [arq arqc]. destruct ai as [aiq aiqc].
  destruct dr as [drq drqc]. destruct di as [diq diqc].
  unfold c_eq; split; apply real_eq_of_zero_diff; intro n;
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_plus c_opp c_mult c_scale c_conj c_norm_sq cRe cIm fst snd]; ring.
Qed.

(* ===================================================================== *)
(* Section 2. The cancellation lemma.                                    *)
(* ===================================================================== *)

Lemma gaC12_cauchy_cancel : forall (s K T2 : Real)
    (Hs : real_lt real_zero s) (Hinv : real_eq (real_mult K s) real_one),
  real_eq (real_mult (real_mult s T2) (real_mult (real_mult K K) s)) T2.
Proof.
  intros s K T2 Hs Hinv.
  assert (HSK : real_eq (real_mult s K) real_one)
    by exact (real_eq_trans _ _ _ (real_mult_comm s K) Hinv).
  apply (real_eq_trans
           (real_mult (real_mult s T2) (real_mult (real_mult K K) s))
           (real_mult T2 (real_mult (real_mult s K) (real_mult K s)))
           T2).
  - apply (real_eq_trans
             (real_mult (real_mult s T2) (real_mult (real_mult K K) s))
             (real_mult (real_mult T2 s) (real_mult (real_mult K K) s))).
    + apply RealSetoid.real_eq_mult_compat.
      * exact (real_mult_comm s T2).
      * apply real_eq_refl.
    + apply (real_eq_trans
               (real_mult (real_mult T2 s) (real_mult (real_mult K K) s))
               (real_mult T2 (real_mult s (real_mult (real_mult K K) s)))).
      * exact (real_eq_sym _ _ (real_mult_assoc T2 s (real_mult (real_mult K K) s))).
      * apply (real_eq_trans
                 (real_mult T2 (real_mult s (real_mult (real_mult K K) s)))
                 (real_mult T2 (real_mult s (real_mult K (real_mult K s))))).
        -- apply RealSetoid.real_eq_mult_compat.
           ++ apply real_eq_refl.
           ++ apply RealSetoid.real_eq_mult_compat.
              ** apply real_eq_refl.
              ** exact (real_eq_sym _ _ (real_mult_assoc K K s)).
        -- apply RealSetoid.real_eq_mult_compat.
           ++ apply real_eq_refl.
           ++ exact (real_mult_assoc s K (real_mult K s)).
  - apply (real_eq_trans
             (real_mult T2 (real_mult (real_mult s K) (real_mult K s)))
             (real_mult T2 real_one)).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (real_eq_trans _ _ _
                  (RealSetoid.real_eq_mult_compat
                     (real_mult s K) (real_mult K s) real_one real_one HSK Hinv)
                  (mm_mult_one_l real_one)).
    + exact (real_eq_trans _ _ _ (real_mult_comm T2 real_one)
                (mm_mult_one_l T2)).
Qed.
