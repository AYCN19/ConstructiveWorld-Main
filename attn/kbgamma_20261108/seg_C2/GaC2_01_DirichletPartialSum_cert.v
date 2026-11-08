(* ConstructiveWorld-Main - certificate face of node C2.01. *)
(** * GaC2_01_DirichletPartialSum_cert: certificate face of node C2.01.
    Mission.  NO-COMPUTABLE-FACE DECLARATION: this node is pure
      definition/finite-algebra (term, partial sum, tail, exp addition
      law, squared-modulus formula, tail difference identity).  It
      carries no numeric constant, no sample band, and no N_0 table,
      so there is no vm_compute acceptance witness to certify: the
      certificate face of this node is this declaration itself.
    Dependencies.  None: this cert file requires no module of this
      development (direction: the proof face may consume this face by
      name).
    References.  The proof face [GaC2_01_DirichletPartialSum], whose
      statement faces this declaration covers.
    Constructivity.  No statements and no definitions are added here;
      the face is pure declaration; [coqchk] reports zero assumed
      constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_01_DirichletPartialSum_cert.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3]. *)
