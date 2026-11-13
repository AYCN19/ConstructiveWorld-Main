(* ==========================================================================)
   UpReqBanachProd.v — 有限和算子的代数律与指数乘积展开
   使命: bsum 定义族（bsum_ext/bsum_plus/bsum_scal/bsum_mult_l）、bplus_swap4、bpow_comm_r、esp_as_bsum（指数部分和实现）、bsum_prod 与 esp_prod_square（部分和乘积重排）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp；Stdlib QArith、Lia
   对标: 有限求和的线性/换序律与指数级数 Cauchy 乘积（二项展开预备）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* ① bsum：Banach 层部分和（对齐库内 sum_upto：                 *)
(*   bsum n f = Σ_{k=0}^{n-1} f k，bsum (S m) f = bsum m f + f m）*)
(* ============================================================ *)

Fixpoint bsum (B : BanachAlg) (n : nat) (f : nat -> (@BA B)) : (@BA B) :=
  match n with
  | 0%nat => @bzero B
  | Datatypes.S m => @bplus B (bsum B m f) (f m)
  end.

(* ============================================================ *)
(* ② bae 面和式引擎                                             *)
(* ============================================================ *)

(* 左乘拉出：Σ (c·g i) == c·Σ g（bdistrib_l，无乘法交换需求） *)
Lemma bsum_mult_l : forall (B : BanachAlg) (n : nat) (c : (@BA B))
                            (g : nat -> (@BA B)),
  @bae B (bsum B n (fun i : nat => @bmult B c (g i)))
         (@bmult B c (bsum B n g)).
Proof.
  intros B n c g. induction n as [| m IH].
  - (* bsum 0 = bzero；bmult c bzero = bzero *)
    apply (@bae_sym B). exact (@bmult_zero B c).
  - change (bsum B (Datatypes.S m) (fun i : nat => @bmult B c (g i)))
      with (@bplus B (bsum B m (fun i : nat => @bmult B c (g i)))
                     (@bmult B c (g m))).
    eapply bae_trans.
    + (* IH 逐项替换首加项：bplus X (c·g m) → bplus (c·Σm g) (c·g m) *)
      apply (@bplus_wd_l B). exact IH.
    + (* c·(Σm + g m) 分配回去（bsum (S m) g 定义形转换吸收） *)
      apply (@bae_sym B). exact (@bdistrib_l B c (bsum B m g) (g m)).
Qed.

(* 逐项 bae ⟹ 和 bae *)
Lemma bsum_ext : forall (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)),
  (forall k : nat, (k < n)%nat -> @bae B (f k) (g k)) ->
  @bae B (bsum B n f) (bsum B n g).
Proof.
  intros B n f g. induction n as [| m IH]; intros H.
  - apply (@bae_refl B).
  - change (bsum B (Datatypes.S m) f) with (@bplus B (bsum B m f) (f m)).
    change (bsum B (Datatypes.S m) g) with (@bplus B (bsum B m g) (g m)).
    apply (@bplus_wd B).
    + apply IH. intros k Hk. apply H. lia.
    + apply H. lia.
Qed.

(* 四元 AC 重排：(a+b)+(c+d) = (a+c)+(b+d)（加法交换群引擎件） *)
Lemma bplus_swap4 : forall (B : BanachAlg) (a b c d : (@BA B)),
  @bae B (@bplus B (@bplus B a b) (@bplus B c d))
         (@bplus B (@bplus B a c) (@bplus B b d)).
Proof.
  intros B a b c d.
  apply (@bae_trans B _ _ _
    (@bae_sym B _ _ (@bplus_assoc B a b (@bplus B c d)))
    (@bae_trans B _ _ _
      (@bplus_wd_r B (@bplus B b (@bplus B c d))
                     (@bplus B (@bplus B b c) d) a
        (@bplus_assoc B b c d))
      (@bae_trans B _ _ _
        (@bplus_wd_r B (@bplus B (@bplus B b c) d)
                       (@bplus B (@bplus B c b) d) a
          (@bplus_wd_l B (@bplus B b c) (@bplus B c b) d
             (@bplus_comm B b c)))
        (@bae_trans B _ _ _
          (@bplus_wd_r B (@bplus B (@bplus B c b) d)
                         (@bplus B c (@bplus B b d)) a
            (@bae_sym B _ _ (@bplus_assoc B c b d)))
          (@bplus_assoc B a c (@bplus B b d)))))).
Qed.

(* 和的线性：Σ(f+g) = Σf + Σg *)
Lemma bsum_plus : forall (B : BanachAlg) (n : nat) (f g : nat -> (@BA B)),
  @bae B (bsum B n (fun k : nat => @bplus B (f k) (g k)))
         (@bplus B (bsum B n f) (bsum B n g)).
Proof.
  intros B n f g. induction n as [| m IH].
  - apply (@bae_sym B). apply (@bplus_zero_l B).
  - change (bsum B (Datatypes.S m) (fun k : nat => @bplus B (f k) (g k)))
      with (@bplus B (bsum B m (fun k : nat => @bplus B (f k) (g k)))
                     (@bplus B (f m) (g m))).
    change (@bplus B (bsum B (Datatypes.S m) f) (bsum B (Datatypes.S m) g))
      with (@bplus B (@bplus B (bsum B m f) (f m))
                     (@bplus B (bsum B m g) (g m))).
    apply (@bae_trans B _
      (@bplus B (@bplus B (bsum B m f) (bsum B m g))
                (@bplus B (f m) (g m))) _).
    + apply (@bplus_wd_l B). exact IH.
    + exact (bplus_swap4 B (bsum B m f) (bsum B m g) (f m) (g m)).
Qed.

(* 右标量拉出：Σ (f k · sc) == (Σ f) · sc（sc = bcoef 面，经分配） *)
Lemma bsum_scal : forall (B : BanachAlg) (n : nat) (c : Q) (f : nat -> (@BA B)),
  @bae B (bsum B n (fun k : nat => @bmult B (f k) (@bcoef B c)))
         (@bmult B (bsum B n f) (@bcoef B c)).
Proof.
  intros B n c f. induction n as [| m IH].
  - (* bsum 0 双侧 = bzero；bmult bzero sc 经 bcoef_comm 换位后用 bmult_zero *)
    apply (@bae_sym B).
    apply (@bae_trans B _ (@bmult B (@bcoef B c) (@bzero B)) _).
    + exact (@bcoef_comm B c (@bzero B)).
    + exact (@bmult_zero B (@bcoef B c)).
  - change (bsum B (Datatypes.S m)
              (fun k : nat => @bmult B (f k) (@bcoef B c)))
      with (@bplus B (bsum B m (fun k : nat => @bmult B (f k) (@bcoef B c)))
                     (@bmult B (f m) (@bcoef B c))).
    eapply bae_trans.
    + apply (@bplus_wd_l B). exact IH.
    + apply (@bae_sym B).
      exact (@bdistrib_r B (bsum B m f) (f m) (@bcoef B c)).
Qed.

(* ============================================================ *)
(* ③ comm 清项引擎：ab=ba ⟹ a^n·b = b·a^n                      *)
(* （交付① bpow_add 归纳步的前置；bplus_middle_swap 同族放大）  *)
(* ============================================================ *)

Lemma bpow_comm_r : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall n : nat,
    @bae B (@bmult B (bpow B a n) b) (@bmult B b (bpow B a n)).
Proof.
  intros B a b hab n. induction n as [| m IH].
  - (* bone·b = b·bone = b *)
    apply (@bae_trans B _ b _).
    + exact (@bmult_one_l B b).
    + apply (@bae_sym B). exact (@bmult_one_r B b).
  - change (bpow B a (Datatypes.S m)) with (@bmult B (bpow B a m) a).
    (* 五步链：((a^m)·a)·b = (a^m)·(a·b) = (a^m)·(b·a)
              = ((a^m)·b)·a = (b·(a^m))·a = b·((a^m)·a) *)
    apply (@bae_trans B _ (@bmult B (bpow B a m) (@bmult B a b)) _).
    + apply (@bae_sym B). exact (@bmult_assoc B (bpow B a m) a b).
    + apply (@bae_trans B _ (@bmult B (bpow B a m) (@bmult B b a)) _).
      * apply (@bmult_wd B (bpow B a m) (@bmult B a b)
                           (bpow B a m) (@bmult B b a)).
        -- apply (@bae_refl B).
        -- exact hab.
      * apply (@bae_trans B _
                 (@bmult B (@bmult B (bpow B a m) b) a) _).
        -- exact (@bmult_assoc B (bpow B a m) b a).
        -- apply (@bae_trans B _
                     (@bmult B b (@bmult B (bpow B a m) a)) _).
           ++ apply (@bae_trans B _
                        (@bmult B (@bmult B b (bpow B a m)) a) _).
           ** apply (@bmult_wd B (@bmult B (bpow B a m) b) a
                                 (@bmult B b (bpow B a m)) a IH).
              apply (@bae_refl B).
           ** apply (@bae_sym B).
              exact (@bmult_assoc B b (bpow B a m) a).
           ++ (* b·((a^m)·a) ≡ b·(bpow a (S m))：定义形自反闭合 *)
              apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* ④ esp 展开为和式：esp n a = Σ_{k≤n} a^k/k!                   *)
(* ============================================================ *)

Lemma esp_as_bsum : forall (B : BanachAlg) (a : (@BA B)) (n : nat),
  @bae B (exp_series_partial B a n)
         (bsum B (Datatypes.S n)
            (fun k : nat => @bmult B (bpow B a k)
                                    (@bcoef B (/ q_fact k)))).
Proof.
  intros B a n. induction n as [| m IH].
  - (* 基例：bone = bzero + bone·bcoef(1)（q_fact 0 = 1 定义形） *)
    assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
    change (exp_series_partial B a 0%nat) with (@bone B).
    change (bsum B (Datatypes.S 0%nat)
              (fun k : nat => @bmult B (bpow B a k)
                                      (@bcoef B (/ q_fact k))))
      with (@bplus B (@bzero B)
              (@bmult B (@bone B) (@bcoef B (/ q_fact 0%nat)))).
    rewrite Hq0.
    apply (@bae_sym B).
    eapply bae_trans.
    + apply (@bplus_wd_r B (@bmult B (@bone B) (@bcoef B 1%Q)) (@bone B)).
      eapply bae_trans.
      * exact (@bmult_one_l B (@bcoef B 1%Q)).
      * exact (@bcoef_one B).
    + exact (@bplus_zero_l B (@bone B)).
  - change (exp_series_partial B a (Datatypes.S m))
      with (@bplus B (exp_series_partial B a m)
               (@bmult B (bpow B a (Datatypes.S m))
                         (@bcoef B (/ q_fact (Datatypes.S m))))).
    change (bsum B (Datatypes.S (Datatypes.S m))
              (fun k : nat => @bmult B (bpow B a k)
                                      (@bcoef B (/ q_fact k))))
      with (@bplus B (bsum B (Datatypes.S m)
                        (fun k : nat => @bmult B (bpow B a k)
                                                (@bcoef B (/ q_fact k))))
                     (@bmult B (bpow B a (Datatypes.S m))
                               (@bcoef B (/ q_fact (Datatypes.S m))))).
    apply (@bplus_wd B).
    + exact IH.
    + apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* ⑤ 柯西乘积部分和恒等形（交付②）                             *)
(* ============================================================ *)

(* 乘积双和（方块）：(Σ_{j≤m} f j)·(Σ_{i≤n} g i) = Σ_{j≤m} Σ_{i≤n} f j·g i
   —— ExpPlusStage2 sum_upto_prod 降层移植：纯 bdistrib_r+assoc，
      无乘法交换需求（f j·g i 序全程不动）。 *)
Lemma bsum_prod : forall (B : BanachAlg) (m n : nat)
                         (f g : nat -> (@BA B)),
  @bae B (@bmult B (bsum B (Datatypes.S m) f) (bsum B (Datatypes.S n) g))
         (bsum B (Datatypes.S m)
            (fun j : nat => bsum B (Datatypes.S n)
               (fun i : nat => @bmult B (f j) (g i)))).
Proof.
  intros B m n f g. induction m as [| m' IH].
  - (* 基例 m=0：双侧 bzero 消 + 左乘拉出 *)
    change (bsum B (Datatypes.S 0%nat) f)
      with (@bplus B (@bzero B) (f 0%nat)).
    change (bsum B (Datatypes.S 0%nat)
              (fun j : nat => bsum B (Datatypes.S n)
                 (fun i : nat => @bmult B (f j) (g i))))
      with (@bplus B (@bzero B)
              (bsum B (Datatypes.S n)
                 (fun i : nat => @bmult B (f 0%nat) (g i)))).
    apply (@bae_trans B _
      (@bmult B (f 0%nat) (bsum B (Datatypes.S n) g)) _).
    + apply (@bmult_wd B (@bplus B (@bzero B) (f 0%nat))
                         (bsum B (Datatypes.S n) g) (f 0%nat)
                         (bsum B (Datatypes.S n) g)).
      * exact (bplus_zero_l B (f 0%nat)).
      * apply (@bae_refl B).
    + (* bmult (f 0) Σg == bplus bzero W，W = Σ (f 0·g i) *)
      apply (@bae_sym B).
      apply (@bae_trans B
        (@bplus B (@bzero B)
           (bsum B (Datatypes.S n)
              (fun i : nat => @bmult B (f 0%nat) (g i))))
        (bsum B (Datatypes.S n)
           (fun i : nat => @bmult B (f 0%nat) (g i)))
        (@bmult B (f 0%nat) (bsum B (Datatypes.S n) g))).
      * apply (@bplus_zero_l B).
      * exact (bsum_mult_l B (Datatypes.S n) (f 0%nat) g).
  - (* 归纳步：右分配拆出 S m' 项 + IH + 左乘拉出 *)
    apply (@bae_trans B
      (@bmult B (bsum B (Datatypes.S (Datatypes.S m')) f)
                (bsum B (Datatypes.S n) g))
      (@bplus B (@bmult B (bsum B (Datatypes.S m') f)
                          (bsum B (Datatypes.S n) g))
                (@bmult B (f (Datatypes.S m'))
                         (bsum B (Datatypes.S n) g)))
      (bsum B (Datatypes.S (Datatypes.S m'))
         (fun j : nat => bsum B (Datatypes.S n)
            (fun i : nat => @bmult B (f j) (g i))))).
    + exact (@bdistrib_r B (bsum B (Datatypes.S m') f)
                          (f (Datatypes.S m'))
                          (bsum B (Datatypes.S n) g)).
    + apply (@bplus_wd B).
      * exact IH.
      * apply (@bae_sym B).
        exact (bsum_mult_l B (Datatypes.S n) (f (Datatypes.S m')) g).
Qed.

(* 交付②主件：esp n a · esp n b = Σ_{j≤n} Σ_{i≤n} (a^j/j!)·(b^i/i!)
   —— ExpPlusStage2 exp_prod_double 降层移植
   （esp_as_bsum ×2 + bsum_prod 组装）。 *)
Lemma esp_prod_square : forall (B : BanachAlg) (a b : (@BA B)) (n : nat),
  @bae B (@bmult B (exp_series_partial B a n)
                   (exp_series_partial B b n))
         (bsum B (Datatypes.S n)
            (fun j : nat => bsum B (Datatypes.S n)
               (fun i : nat =>
                  @bmult B (@bmult B (bpow B a j)
                                    (@bcoef B (/ q_fact j)))
                           (@bmult B (bpow B b i)
                                    (@bcoef B (/ q_fact i)))))).
Proof.
  intros B a b n.
  apply (@bae_trans B _
    (@bmult B (bsum B (Datatypes.S n)
                 (fun k : nat => @bmult B (bpow B a k)
                                         (@bcoef B (/ q_fact k))))
              (bsum B (Datatypes.S n)
                 (fun k : nat => @bmult B (bpow B b k)
                                         (@bcoef B (/ q_fact k))))) _).
  - apply (@bmult_wd B).
    + exact (esp_as_bsum B a n).
    + exact (esp_as_bsum B b n).
  - exact (bsum_prod B n n
             (fun k : nat => @bmult B (bpow B a k) (@bcoef B (/ q_fact k)))
             (fun k : nat => @bmult B (bpow B b k) (@bcoef B (/ q_fact k)))).
Qed.

(* ============================================================ *)
(* ⑥ 和式换元三件（交付① bpow_add Pascal 组装前备；            *)
(*    对齐 ExpPlusStage2 sum_upto_rot/shift_pred/shift_pred2）  *)
(* ============================================================ *)

(* rot：Σ_{k≤n} f k = f 0 + Σ_{k≤n-1} f (S k)（首项提出） *)
Lemma bsum_rot : forall (B : BanachAlg) (n : nat) (f : nat -> (@BA B)),
  @bae B (bsum B (Datatypes.S n) f)
         (@bplus B (f 0%nat)
                     (bsum B n (fun k : nat => f (Datatypes.S k)))).
Proof.
  intros B n f. induction n as [| m IH].
  - change (bsum B (Datatypes.S 0%nat) f)
      with (@bplus B (@bzero B) (f 0%nat)).
    change (bsum B 0%nat (fun k : nat => f (Datatypes.S k)))
      with (@bzero B).
    apply (@bplus_comm B (@bzero B) (f 0%nat)).
  - change (bsum B (Datatypes.S (Datatypes.S m)) f)
      with (@bplus B (bsum B (Datatypes.S m) f) (f (Datatypes.S m))).
    change (@bplus B (f 0%nat)
              (bsum B (Datatypes.S m) (fun k : nat => f (Datatypes.S k))))
      with (@bplus B (f 0%nat)
              (@bplus B (bsum B m (fun k : nat => f (Datatypes.S k)))
                       (f (Datatypes.S m)))).
    apply (@bae_trans B _
      (@bplus B (@bplus B (f 0%nat)
                          (bsum B m (fun k : nat => f (Datatypes.S k))))
                (f (Datatypes.S m))) _).
    + apply (@bplus_wd_l B). exact IH.
    + apply (@bae_sym B).
      apply (@bplus_assoc B (f 0%nat)
               (bsum B m (fun k : nat => f (Datatypes.S k)))
               (f (Datatypes.S m))).
Qed.

(* 换元 j=k+1：Σ_{j≤n+1} f (j−1) = f 0 + Σ_{k≤n} f k *)
Lemma bsum_shift_pred : forall (B : BanachAlg) (n : nat) (f : nat -> (@BA B)),
  @bae B (bsum B (Datatypes.S (Datatypes.S n))
              (fun j : nat => f (Nat.sub j 1)))
         (@bplus B (f 0%nat) (bsum B (Datatypes.S n) f)).
Proof.
  intros B n f.
  (* G := fun j => f (j−1)；G 0 ≡ f 0、G (S k) ≡ f k 均定义形 *)
  set (G := fun j : nat => f (Nat.sub j 1)).
  induction n as [| m IH].
  - change (bsum B (Datatypes.S (Datatypes.S 0%nat)) G)
      with (@bplus B (@bplus B (@bzero B) (f 0%nat)) (f 0%nat)).
    change (bsum B (Datatypes.S 0%nat) f)
      with (@bplus B (@bzero B) (f 0%nat)).
    (* (0+X)+X = X+(0+X)（中转 X+X） *)
    apply (@bae_trans B _ (@bplus B (f 0%nat) (f 0%nat)) _).
    + eapply bae_trans.
      * apply (@bae_sym B).
        exact (@bplus_assoc B (@bzero B) (f 0%nat) (f 0%nat)).
      * exact (bplus_zero_l B (@bplus B (f 0%nat) (f 0%nat))).
    + apply (@bplus_wd_r B (f 0%nat) (@bplus B (@bzero B) (f 0%nat))).
      apply (@bae_sym B). exact (bplus_zero_l B (f 0%nat)).
  - change (bsum B (Datatypes.S (Datatypes.S (Datatypes.S m))) G)
      with (@bplus B (bsum B (Datatypes.S (Datatypes.S m)) G)
                     (G (Datatypes.S (Datatypes.S m)))).
    apply (@bae_trans B _
      (@bplus B (@bplus B (f 0%nat) (bsum B (Datatypes.S m) f))
                (G (Datatypes.S (Datatypes.S m)))) _).
    + apply (@bplus_wd_l B). exact IH.
    + (* 重结合（对称）后尾项 (S (S m)−1) ≡ S m 定义形闭合 *)
      apply (@bae_sym B).
      apply (@bplus_assoc B (f 0%nat) (bsum B (Datatypes.S m) f)
               (G (Datatypes.S (Datatypes.S m)))).
Qed.

(* 换元 j=k+1（原序）：Σ_{k≤n} f k + f 0 = Σ_{j≤n+1} f (j−1) *)
Lemma bsum_shift_pred2 : forall (B : BanachAlg) (n : nat) (f : nat -> (@BA B)),
  @bae B (@bplus B (bsum B (Datatypes.S n) f) (f 0%nat))
         (bsum B (Datatypes.S (Datatypes.S n))
            (fun j : nat => f (Nat.sub j 1))).
Proof.
  intros B n f.
  apply (@bae_trans B _
    (@bplus B (f 0%nat) (bsum B (Datatypes.S n) f)) _).
  - apply (@bplus_comm B (bsum B (Datatypes.S n) f) (f 0%nat)).
  - apply (@bae_sym B). exact (bsum_shift_pred B n f).
Qed.

(* ============================================================ *)
(* 遗留登记（对称遗留，不落承认件）：                           *)
(*   第二部分：交付① bpow_add（ab=ba 下二项式恒等：q_choose/     *)
(*     Pascal 系数层 + bsum 换元/配对 + bpow_comm_r 清项）；    *)
(*   第三部分：三角转置（exp_cauchy_swap 降层）→ e^(a+b) 主链；   *)
(*   尾界对接：esp_diff_le_tail/exp_series_cauchy 已绿          *)
(*     （UpReqBanachExp），带尾估计为收敛收尾件。               *)
(* ============================================================ *)

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bplus_swap4.
