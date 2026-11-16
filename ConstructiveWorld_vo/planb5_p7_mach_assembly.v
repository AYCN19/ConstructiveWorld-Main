(* * planb5_p7_mach_assembly: the P7 exit assembly root (three-lemma
      face aggregation; the table-domain clearing piece is carried in
      the require closure as the sibling root planb5_p7_hval_table).

    Mission.  Aggregate the three P7 deliverable statement faces, each
    transcribed verbatim from its upstream canonical cast (the
    proper-name table below), zero new math:

      1. p7_assembly_bridge_amplify  <- mach_edge_bridge_amplify
         (cast_bridge.v:284; strong cross-index bridge
         |mdot k - xL j| <= w k + 4*pie_mag(2j+2); canonical sources:
         mach_edge_one = mach_fold_chain.v:280, both own moduli
         atan_tail_bound S11_TP3B5.v:301 / pie_tail4, limit elimination
         via decidable Q order; M1:438 prescription item 1)
      2. p7_assembly_modulus_k_of_b <- mach_modulus_k_of_b
         (cast_modulus.v:640; family-one modulus function
         k(b) = mu k. w_k(b) <= c0/(4*max(|b|,1)^11) with
         c0 = 1/71663616, delivered with budget face and minimality
         face; M1:438 prescription item 2)
      3. p7_assembly_parity_interleave <- parity_interleave_mdot
         (cast_parity.v:145; family-three 3a parity-interleave
         instance bundle; canonical anchors chong1_run1.log L54-L62;
         M1:438 prescription item 3)
      4. planb5_p7_hval_table (separate root, required below): the
         table-domain Hval clearing at the canonical 1d depths - rows
         n=1..20 certified Coq-side, rows 21..40 registered
         evaluation-budget debt with the full canonical k0 table
         carried (see that file's header).

    Zero new math: every face in this file is a byte-level
    transcription of its upstream cast statement; each proof is
    exact-forwarding to the upstream derivation chain (the derivation
    substance lives in the three casts and their four-gate accounts;
    this root is the aggregation interface).  The upstream canonical
    names remain importable unchanged (signature stability, red-line
    law 6).

    Dependencies.  S01_BaseRing (NatLe, And as the Set-level product),
    S02_CauchyComplete (QltT / QleT' / QeqT Id-bool carriers),
    S03_QExp (q_pow), S11_TP3B5 (arctan_partial, atan_mag),
    LW0MLicBridge (lw0m_xL), PiEnvelope (pie_mag), cast_bridge,
    cast_modulus, cast_parity, planb5_p7_hval_table (which carries
    planb3_g1_calib for the A/B tables).

    References.  mach_edge_one = mach_fold_chain.v:280; atan_tail_bound
    = S11_TP3B5.v:301; lw0m_xL = LW0MLicBridge.v:20; pie_mag =
    PiEnvelope.v:88; M1:438 prescription (P7 bridge-level assembly);
    numerical anchors chong1_run1.log L15-L79; exploration-volume
    section-two statement faces (via each cast's provenance header).

    Constructivity.  Zero axioms, zero admitted goals; every face is
    Set-carried (QleT'/QltT/QeqT Id-bool carriers, sigT, And as the
    Set-level product).  The restated lemmas are transparent
    (Defined): each proof term is the upstream witness itself.  No
    large-constant evaluation is performed in this file.

    Build.  coqc -native-compiler no -q -Q . ""
      planb5_p7_mach_assembly.v  (world directory, after
      planb5_p7_hval_table; Rocq 9.3.0; guard-wrapped single lane). *)

Require Import S01_BaseRing S02_CauchyComplete S03_QExp S11_TP3B5
               LW0MLicBridge PiEnvelope.
Require Import cast_bridge cast_modulus cast_parity planb5_p7_hval_table.
From Stdlib Require Import QArith.QArith QArith.Qabs.

(* Deliverable 1 (M1:438 item 1).  Face verbatim from
   cast_bridge.v:284-286 (mach_edge_bridge_amplify). *)
Theorem p7_assembly_bridge_amplify : forall (k j : nat),
  QleT' (Qabs (mach_mdot k - lw0m_xL j))
        (mach_own_modulus k + 4 * pie_mag (2 * j + 2)).
Proof.
  intros k j. exact (mach_edge_bridge_amplify k j).
Defined.

(* Deliverable 2 (M1:438 item 2).  Face verbatim from
   cast_modulus.v:640-644 (mach_modulus_k_of_b). *)
Definition p7_assembly_modulus_k_of_b (b : Q) :
  sigT (fun k : nat => And
    (QleT' (mach_own_modulus k) (mach_modulus_target b))
    (forall m : nat, NatLe (Datatypes.S m) k ->
      QltT (mach_modulus_target b) (mach_own_modulus m)))
  := mach_modulus_k_of_b b.

(* Deliverable 3 (M1:438 item 3).  Face verbatim from
   cast_parity.v:145-153 (parity_interleave_mdot). *)
Theorem p7_assembly_parity_interleave :
  And (QltT (mach_mdot 40) (mach_mdot 0 - mach_own_modulus 40))
  (And (QltT (mach_mdot 1 + mach_own_modulus 40) (mach_mdot 40))
  (And (And (QltT (mach_mdot 2) (mach_mdot 0))
            (QltT (mach_mdot 1) (mach_mdot 3)))
  (And (QltT (mach_mdot 1) (mach_mdot 0))
       (QeqT (mach_mdot 0 - mach_mdot 1)
             (16 * atan_mag 1 (1 # 5)%Q
              - 4 * atan_mag 1 (1 # 239)%Q))))).
Proof.
  exact parity_interleave_mdot.
Defined.

Print Assumptions p7_assembly_bridge_amplify.
Print Assumptions p7_assembly_modulus_k_of_b.
Print Assumptions p7_assembly_parity_interleave.
