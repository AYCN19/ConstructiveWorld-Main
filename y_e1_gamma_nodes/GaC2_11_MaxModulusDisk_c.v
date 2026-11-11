(* ConstructiveWorld-Main - the alignment and first-order increment cluster of the
   maximum-modulus disk node. *)

(** * GaC2_11_MaxModulusDisk_c: alignment and the first-order increment algebra.

    Mission.  Node C2-11 (segment C2, slot W2), machine piece.  The alignment face of the
      first-order increment ([mm_align_kappa]: the direction-aligned complex scaling
      collapses to the real gain applied to the base value), the quarter-reciprocal identity
      ([mm_inv_quarter]), the squared product algebra ([mm_ABAB], [mm_le_comm]), the order
      transports ([mm_le_lt_trans], [mm_le_lt_trans_alt]), the expanded square
      ([mm_sq_plus]), the remainder recombination ([mm_c_recombine]), and the first-order
      norm identity ([mm_first_order_norm]: the squared modulus of u plus a real-scaled
      copy of u in the expanded closed form).  All identities are pointwise algebra or
      order transports.
    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete] (order kit, [real_eq_of_zero_diff] ring route,
      ring laws), [S03_QExp] ([real_inv_pos] and its faces), [S07_RealSetoidExpLog]
      ([real_mult_positive], [RealSetoid.real_eq_mult_compat], [RealSetoid.real_eq_le]),
      [CxRealPairCore] + [CxRealPairExpLog] (pair carrier, [c_scale]), [GaC1_Iface_Cx]
      (complex slice), [GaC1_Iface_Real] (C1-04 rational bridge, C1-05 square root faces),
      and the machine faces [GaC2_11_MaxModulusDisk_a] and [GaC2_11_MaxModulusDisk_b] of
      this node.
    References.  drafts_C2.md C2.11 statement sketch (the squared modulus carrier and the
      explicit first-order increment algebra); Ahlfors Ch.2, the first-order growth
      direction argument mirrored at the squared-carrier level.
    Constructivity.  Every named construction is carried by [Set]; the order predicates are
      the Set-sorted [real_lt] / [real_le]; zero assumed constants; every proof closes under
      the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> "" -Q <build dir> ""
      GaC2_11_MaxModulusDisk_c.v] from the flat build directory, thermal guard wrapper. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* The aligned increment: z scaled twice against its own conjugate
   product lands as t*s*|z|^2 applied to u. *)
Lemma mm_align_kappa : forall (z u : Cx) (t s : Real),
  c_eq (c_mult z (c_scale t (c_scale s (c_mult (c_conj z) u))))
       (c_scale (real_mult t (real_mult s (c_norm_sq z))) u).
Proof.
  intros z u t s.
  apply (c_eq_trans (c_mult z (c_scale t (c_scale s (c_mult (c_conj z) u))))
           (c_scale t (c_mult z (c_scale s (c_mult (c_conj z) u))))
           (c_scale (real_mult t (real_mult s (c_norm_sq z))) u)).
  - exact (mm_c_mult_scale z t (c_scale s (c_mult (c_conj z) u))).
  - apply (c_eq_trans
             (c_scale t (c_mult z (c_scale s (c_mult (c_conj z) u))))
             (c_scale t (c_scale s (c_mult z (c_mult (c_conj z) u))))
             (c_scale (real_mult t (real_mult s (c_norm_sq z))) u)).
    + apply mm_c_scale_wd.
      exact (mm_c_mult_scale z s (c_mult (c_conj z) u)).
    + apply (c_eq_trans
               (c_scale t (c_scale s (c_mult z (c_mult (c_conj z) u))))
               (c_scale (real_mult t s) (c_mult z (c_mult (c_conj z) u)))
               (c_scale (real_mult t (real_mult s (c_norm_sq z))) u)).
      * exact (mm_c_scale_scale t s (c_mult z (c_mult (c_conj z) u))).
      * apply (c_eq_trans
                 (c_scale (real_mult t s) (c_mult z (c_mult (c_conj z) u)))
                 (c_scale (real_mult (real_mult t s) (c_norm_sq z)) u)
                 (c_scale (real_mult t (real_mult s (c_norm_sq z))) u)).
        -- apply (c_eq_trans (c_scale (real_mult t s) (c_mult z (c_mult (c_conj z) u)))
                   (c_scale (real_mult t s) (c_scale (c_norm_sq z) u))
                   (c_scale (real_mult (real_mult t s) (c_norm_sq z)) u)).
           ++ apply mm_c_scale_wd.
              apply (c_eq_trans (c_mult z (c_mult (c_conj z) u))
                         (c_mult (c_mult z (c_conj z)) u)
                         (c_scale (c_norm_sq z) u)).
              ** exact (c_mult_assoc z (c_conj z) u).
              ** apply (c_eq_trans (c_mult (c_mult z (c_conj z)) u)
                           (c_mult (c_scale (c_norm_sq z) c_one) u)
                           (c_scale (c_norm_sq z) u)).
                 --- apply c_mult_congr.
                     +++ exact (mm_sq_embed z).
                     +++ apply c_eq_refl.
                 --- exact (mm_c_scale_one_mult (c_norm_sq z) u).
           ++ exact (mm_c_scale_scale (real_mult t s) (c_norm_sq z) u).
        -- apply mm_c_eq_scale_wd.
           apply real_eq_sym. exact (real_mult_assoc t s (c_norm_sq z)).
  Qed.


Lemma mm_inv_quarter : forall (a b : Real) (Hc : real_lt real_zero
                              (real_mult (real_const (4#1)%Q) (real_mult a b))),
  real_eq (real_mult (real_mult a b)
             (real_inv_pos (real_mult (real_const (4#1)%Q) (real_mult a b)) Hc))
          (real_const (1#4)%Q).
Proof.
  intros a b Hc.
  assert (the_const_one_face : real_eq (real_mult (real_const (1#4)%Q) (real_const (4#1)%Q))
                                 real_one).
  { apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const]. ring. }
  set (H := real_mult (real_const (4#1)%Q) (real_mult a b)).
  set (X := real_mult (real_mult a b) (real_inv_pos H Hc)).
  assert (Hface : real_eq (real_mult X H) (real_mult (real_const (1#4)%Q) H)).
  { assert (H1 : real_eq (real_mult X H) (real_mult a b)).
    { exact (real_eq_trans (real_mult X H)
               (real_mult (real_mult a b) real_one)
               (real_mult a b)
               (real_eq_trans (real_mult X H)
                  (real_mult (real_mult a b) (real_mult (real_inv_pos H Hc) H))
                  (real_mult (real_mult a b) real_one)
                  (real_eq_sym _ _
                     (real_mult_assoc (real_mult a b) (real_inv_pos H Hc) H))
                  (RealSetoid.real_eq_mult_compat (real_mult a b)
                     (real_mult (real_inv_pos H Hc) H) (real_mult a b) real_one
                     (real_eq_refl (real_mult a b))
                     (real_eq_trans (real_mult (real_inv_pos H Hc) H) real_one real_one
                        (mm_inv_mul_one H Hc) (real_eq_refl real_one))))
               (real_mult_one (real_mult a b))). }
    assert (H2 : real_eq (real_mult (real_const (1#4)%Q) H) (real_mult a b)).
    { exact (real_eq_trans (real_mult (real_const (1#4)%Q) H)
               (real_mult (real_mult (real_const (1#4)%Q) (real_const (4#1)%Q))
                  (real_mult a b))
               (real_mult a b)
               (real_mult_assoc (real_const (1#4)%Q) (real_const (4#1)%Q)
                  (real_mult a b))
               (real_eq_trans (real_mult (real_mult (real_const (1#4)%Q) (real_const (4#1)%Q))
                                 (real_mult a b))
                  (real_mult real_one (real_mult a b))
                  (real_mult a b)
                  (RealSetoid.real_eq_mult_compat
                     (real_mult (real_const (1#4)%Q) (real_const (4#1)%Q))
                     (real_mult a b) real_one (real_mult a b)
                     the_const_one_face (real_eq_refl (real_mult a b)))
                  (mm_mult_one_l (real_mult a b)))). }
    exact (real_eq_trans (real_mult X H) (real_mult a b)
             (real_mult (real_const (1#4)%Q) H) H1 (real_eq_sym _ _ H2)). }
  apply (mm_mult_cancel_eq X (real_const (1#4)%Q) H Hc Hface).
Qed.



Lemma mm_ABAB : forall A B : Real,
  real_eq (real_mult (real_mult A A) (real_mult B B))
          (real_mult (real_mult A B) (real_mult A B)).
Proof.
  intros A B.
  apply (real_eq_sym _ _).
  apply (real_eq_trans (real_mult (real_mult A B) (real_mult A B))
           (real_mult A (real_mult B (real_mult A B)))
           (real_mult (real_mult A A) (real_mult B B))).
  - apply real_eq_sym. exact (real_mult_assoc A B (real_mult A B)).
  - apply (real_eq_trans (real_mult A (real_mult B (real_mult A B)))
             (real_mult A (real_mult A (real_mult B B)))
             (real_mult (real_mult A A) (real_mult B B))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply (real_eq_trans (real_mult B (real_mult A B))
                 (real_mult (real_mult A B) B)
                 (real_mult A (real_mult B B))).
        -- apply real_mult_comm.
        -- apply real_eq_sym.
           exact (real_mult_assoc A B B).
    + exact (real_mult_assoc A A (real_mult B B)).
Qed.

Lemma mm_le_comm : forall x y : Real, real_le (real_mult x y) (real_mult y x).
Proof.
  intros x y. apply RealSetoid.real_eq_le. apply real_mult_comm.
Qed.

(* a < b gives a <= b through the Set-sorted order sum. *)
Lemma mm_le_lt_trans_alt : forall (a b c : Real),
  real_lt a b -> real_le b c -> real_lt a c.
Proof.
  intros a b c Hlt Hle. exact (real_lt_le_trans a b c Hlt Hle).
Qed.

Lemma mm_le_lt_trans : forall (a b c : Real),
  real_le a b -> real_lt b c -> real_lt a c.
Proof.
  intros a b c Hle Hlt. destruct Hle as [Hlt2 | Heq].
  - exact (real_lt_trans a b c Hlt2 Hlt).
  - exact (real_eq_lt_lt a b c Heq Hlt).
Qed.

(* (a + b)^2 == a^2 + 2ab + b^2, expanded two-term nesting. *)
Lemma mm_sq_plus : forall a b : Real,
  real_eq (real_mult (real_plus a b) (real_plus a b))
          (real_plus (real_mult a a)
             (real_plus (real_mult (real_const (2#1)%Q) (real_mult a b))
                        (real_mult b b))).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  destruct a as [u Hu]. destruct b as [v Hv].
  cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const]. ring.
Qed.

(* (a + b) + (c + (d - b) - a) == c + d, the remainder recombination. *)
Lemma mm_c_recombine : forall (a0 aw fz : Cx),
  c_eq (c_plus (c_plus a0 aw)
               (c_plus (c_plus fz (c_opp a0)) (c_opp aw))) fz.
Proof.
  intros [a b] [p q] [u v].
  destruct a as [ua Ha]. destruct b as [ub Hb].
  destruct p as [uc Hc]. destruct q as [ud Hd].
  destruct u as [ue He]. destruct v as [uf Hf].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_opp real_zero
         c_plus c_opp cRe cIm fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_opp real_zero
         c_plus c_opp cRe cIm fst snd]. ring.
Qed.

(* The squared modulus of u plus a real-scaled copy of u:
   |u + t*u|^2 == (1 + t)^2 * |u|^2, stated in the expanded form
   |u|^2 + 2*t*|u|^2 + t^2*|u|^2 consumed by the growth statement. *)
Lemma mm_first_order_norm : forall (u : Cx) (k : Real) (m : Real),
  real_eq (c_norm_sq u) m ->
  real_eq (c_norm_sq (c_plus u (c_scale k u)))
          (real_plus m
             (real_plus (real_mult (real_const (2#1)) (real_mult k m))
                        (real_mult (real_mult k k) m))).
Proof.
  intros u k m Hm.
  assert (Hmid : real_eq
           (c_norm_sq (c_plus u (c_scale k u)))
           (real_plus (c_norm_sq u)
              (real_plus (c_norm_sq (c_scale k u))
                 (real_mult (real_const (2#1))
                    (cRe (c_mult (c_conj u) (c_scale k u))))))).
  { apply real_eq_of_zero_diff. intro n.
    destruct u as [p q]. destruct k as [ra Ha].
    destruct p as [uc Hc]. destruct q as [ud Hd].
    cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const
         c_plus c_scale c_conj c_mult cRe cIm c_norm_sq fst snd]. ring. }
  assert (Hre : real_eq (cRe (c_mult (c_conj u) (c_scale k u)))
                     (real_mult k (cRe (c_mult (c_conj u) u)))).
  { apply (real_eq_trans
             (cRe (c_mult (c_conj u) (c_scale k u)))
             (cRe (c_scale k (c_mult (c_conj u) u)))
             (real_mult k (cRe (c_mult (c_conj u) u)))).
    - destruct (mm_c_mult_scale (c_conj u) k u) as [Hrce _].
      exact Hrce.
    - exact (mm_re_scale k (c_mult (c_conj u) u)). }
  assert (Hrest : real_eq
           (real_plus (c_norm_sq u)
              (real_plus (c_norm_sq (c_scale k u))
                 (real_mult (real_const (2#1))
                    (cRe (c_mult (c_conj u) (c_scale k u))))))
           (real_plus m
              (real_plus (real_mult (real_const (2#1)) (real_mult k m))
                 (real_mult (real_mult k k) m)))).
  { apply RealSetoid.real_eq_plus_compat.
    - exact Hm.
    - apply (real_eq_trans
               (real_plus (c_norm_sq (c_scale k u))
                  (real_mult (real_const (2#1))
                     (cRe (c_mult (c_conj u) (c_scale k u)))))
               (real_plus (real_mult (real_mult k k) m)
                  (real_mult (real_const (2#1)) (real_mult k m)))
               (real_plus (real_mult (real_const (2#1)) (real_mult k m))
                  (real_mult (real_mult k k) m))).
      + apply RealSetoid.real_eq_plus_compat.
        * apply (real_eq_trans (c_norm_sq (c_scale k u))
                   (real_mult (real_mult k k) (c_norm_sq u))
                   (real_mult (real_mult k k) m)).
          -- exact (mm_norm_scale k u).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ apply real_eq_refl.
             ++ exact Hm.
        * assert (Hre2 : real_eq (cRe (c_mult (c_conj u) (c_scale k u)))
                             (real_mult k m)).
          -- exact (real_eq_trans (cRe (c_mult (c_conj u) (c_scale k u)))
                     (real_mult k (cRe (c_mult (c_conj u) u)))
                     (real_mult k m) Hre
                     (RealSetoid.real_eq_mult_compat k
                        (cRe (c_mult (c_conj u) u)) k m
                        (real_eq_refl k)
                        (real_eq_trans (cRe (c_mult (c_conj u) u))
                           (c_norm_sq u) m (mm_re_conj_self u) Hm))).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ apply real_eq_refl.
             ++ exact Hre2.
      + apply real_plus_comm. }
  exact (real_eq_trans _ _ _ Hmid Hrest).
Qed.
