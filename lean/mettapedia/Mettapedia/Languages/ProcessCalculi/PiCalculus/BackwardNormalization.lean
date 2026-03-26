import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

/-!
# Backward Normalization Helpers for π→ρ

Small normalization lemmas for backward/reflection proofs:
- explicit flattened bag shape for key admin sources
- canonical COMM-shape permutations
- SC bridges from encoded sources to COMM-ready shapes
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Positive normalization example: a bag is already in component form. -/
theorem parComponents_bag_example (elems : List Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
      (.collection .hashBag elems none) = elems := by
  rfl

/-- Negative normalization example: a non-bag stays as a singleton component list. -/
theorem parComponents_nonbag_example (p : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
      (.apply "PDrop" [p]) = [.apply "PDrop" [p]] := by
  rfl

/-- Alternative encoded-source COMM decomposition through `canInteract`:
proves existence of a core COMM step without committing to a fixed
permutation-normalized redex/target shape. -/
theorem comm_exists_from_encoded_source_via_canInteract
    (x y z : Name) (P : Process) (n v : String) (rest : List Pattern) :
    let inp : Pattern := rhoInput (.fvar x) y (encode P n v)
    let out : Pattern := rhoOutput (.fvar x) (rhoDrop (.fvar z))
    let src : Pattern := .collection .hashBag (inp :: out :: rest) none
    ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  intro inp out src
  have hcan :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract
        (.collection .hashBag (inp :: out :: rest) none) (.fvar x) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract
    constructor
    · refine ⟨Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v), ?_⟩
      simp [inp, rhoInput]
    · refine ⟨rhoDrop (.fvar z), ?_⟩
      simp [out, rhoOutput, rhoDrop]
  simpa [src] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.reduces_of_canInteract
      (elems := inp :: out :: rest) (x := .fvar x) hcan)

/-- General COMM existence from `parComponents` membership: if a source has
both a matching input and output at top-level parallel components, it can
perform a COMM step. -/
theorem comm_exists_from_parComponents_src
    {src : Pattern} {x body q : Pattern}
    (hmemIn :
      Pattern.apply "PInput" [x, .lambda none body] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src)
    (hmemOut :
      Pattern.apply "POutput" [x, q] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src) :
    ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  rcases Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponentsSpec src with
    hpc | ⟨elems, hsrc, hpc⟩
  · have hmemIn' :
        Pattern.apply "PInput" [x, .lambda none body] ∈ [src] := by
        simpa [hpc] using hmemIn
    have hmemOut' :
        Pattern.apply "POutput" [x, q] ∈ [src] := by
        simpa [hpc] using hmemOut
    have hinEq : Pattern.apply "PInput" [x, .lambda none body] = src := by
      simpa using hmemIn'
    have houtEq : Pattern.apply "POutput" [x, q] = src := by
      simpa using hmemOut'
    have hneq :
        Pattern.apply "PInput" [x, .lambda none body] ≠
          Pattern.apply "POutput" [x, q] := by
      intro h
      injection h with hname _hargs
      have hname' : ("PInput" : String) ≠ "POutput" := by decide
      exact hname' hname
    have : False := by
      apply hneq
      calc
        Pattern.apply "PInput" [x, .lambda none body] = src := hinEq
        _ = Pattern.apply "POutput" [x, q] := by
          simp [houtEq]
    exact this.elim
  · have hmemIn' :
        Pattern.apply "PInput" [x, .lambda none body] ∈ elems := by
        simpa [hpc] using hmemIn
    have hmemOut' :
        Pattern.apply "POutput" [x, q] ∈ elems := by
        simpa [hpc] using hmemOut
    have hcan :
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract
          (.collection .hashBag elems none) x := by
      unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract
      exact ⟨⟨body, hmemIn'⟩, ⟨q, hmemOut'⟩⟩
    simpa [hsrc] using
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.reduces_of_canInteract
        (elems := elems) (x := x) hcan)

/-- Every source is SC-equivalent to the bag built from its top-level
parallel components. -/
theorem sc_to_parComponents_bag (src : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      src
      (.collection .hashBag
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src) none) := by
  rcases Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponentsSpec src with
    hsingle | ⟨elems, hbag, hpc⟩
  · rw [hsingle]
    exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_singleton src)
  · subst hbag
    simpa [hpc] using
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl
        (.collection .hashBag elems none))

/-- Any parallel-component witness of a matching input/output channel yields
a COMM step on the original source (via `canInteract` + SC transport). -/
theorem comm_exists_from_parComponents
    {src : Pattern} {x body q : Pattern}
    (hin :
      .apply "PInput" [x, .lambda none body] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src)
    (hout :
      .apply "POutput" [x, q] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src) :
    ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  let bag : Pattern :=
    .collection .hashBag
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src) none
  have hsc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src bag :=
    sc_to_parComponents_bag src
  have hcan :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract bag x := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.canInteract
    exact ⟨⟨body, by simpa using hin⟩, ⟨q, by simpa using hout⟩⟩
  rcases Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.reduces_of_canInteract
      (elems := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src)
      (x := x) hcan with ⟨tgt, hred⟩
  exact ⟨tgt,
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
      hsc (Classical.choice hred)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)⟩⟩

/-- Canonical ν-listener source bag used for COMM decomposition. -/
def nuListenerSource (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda none listenerBody])

/-- Canonical ν-listener COMM-redex shape. -/
def nuListenerPreComm (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [rhoOutput (.fvar v) (.fvar n),
     .apply "PInput" [.fvar v, .lambda none listenerBody],
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none

/-- Canonical ν-listener COMM target. -/
def nuListenerTarget (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none

/-- Flattened source shape for the ν-listener administrative step. -/
theorem nu_listener_source_eq_bag
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    nuListenerSource x P n v listenerBody =
      .collection .hashBag
        [rhoOutput (.fvar v) (.fvar n),
         rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
         .apply "PInput" [.fvar v, .lambda none listenerBody]] none := by
  simp [nuListenerSource, encode, rhoPar, rhoInput, rhoOutput]

/-- Permutation from flattened ν source to COMM-ready shape. -/
theorem nu_listener_comm_shape_perm
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    ([rhoOutput (.fvar v) (.fvar n),
      rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
      .apply "PInput" [.fvar v, .lambda none listenerBody]] : List Pattern).Perm
    [rhoOutput (.fvar v) (.fvar n),
     .apply "PInput" [.fvar v, .lambda none listenerBody],
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] := by
  refine List.Perm.cons _ ?_
  simpa using (List.Perm.swap
    (rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v))
    (.apply "PInput" [.fvar v, .lambda none listenerBody])
    ([] : List Pattern)).symm

/-- SC bridge: ν-listener source into COMM-ready shape. -/
theorem nu_listener_source_sc_comm_shape
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nuListenerSource x P n v listenerBody)
      (nuListenerPreComm x P n v listenerBody) := by
  calc
    nuListenerSource x P n v listenerBody =
        .collection .hashBag
          [rhoOutput (.fvar v) (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
           .apply "PInput" [.fvar v, .lambda none listenerBody]] none := by
            simpa using nu_listener_source_eq_bag x P n v listenerBody
    _ ≡ nuListenerPreComm x P n v listenerBody := by
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm _ _
                (nu_listener_comm_shape_perm x P n v listenerBody)

/-- Candidate COMM reduction on the canonical ν-listener COMM-redex shape. -/
def nu_listener_preComm_reduces
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nuListenerPreComm x P n v listenerBody)
      (nuListenerTarget x P n v listenerBody) := by
  simpa [nuListenerPreComm, nuListenerTarget] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.comm
      (n := (.fvar v))
      (q := (.fvar n))
      (p := listenerBody)
      (rest := [rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)]))

/-- COMM decomposition endpoint for ν-listener sources:
SC normalization + candidate COMM step to canonical target. -/
theorem nu_listener_comm_decompose
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nuListenerSource x P n v listenerBody)
      (nuListenerPreComm x P n v listenerBody) ∧
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nuListenerPreComm x P n v listenerBody)
      (nuListenerTarget x P n v listenerBody)) := by
  exact ⟨nu_listener_source_sc_comm_shape x P n v listenerBody,
    ⟨nu_listener_preComm_reduces x P n v listenerBody⟩⟩

/-- Canonical name-server listener source bag used for COMM decomposition. -/
def nameServerListenerSource (x z v s : String) (listenerBody : Pattern) : Pattern :=
  rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda none listenerBody])

/-- Canonical name-server listener COMM-redex shape. -/
def nameServerListenerPreComm (x z v s : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
     .apply "PInput" [.fvar z, .lambda none listenerBody],
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] none

/-- Canonical name-server listener COMM target. -/
def nameServerListenerTarget (x z v s : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] none

/-- Flattened source shape for the name-server listener administrative step. -/
theorem nameServer_listener_source_eq_bag
    (x z v s : String) (listenerBody : Pattern) :
    nameServerListenerSource x z v s listenerBody =
      .collection .hashBag
        [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
         dropOperation x,
         rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
         .apply "PInput" [.fvar z, .lambda none listenerBody]] none := by
  simp [nameServerListenerSource, nameServer, rhoPar, rhoReplicate, dropOperation, rhoOutput]

/-- Permutation from flattened seed-listener source to COMM-ready shape. -/
theorem nameServer_listener_comm_shape_perm
    (x z v s : String) (listenerBody : Pattern) :
    ([rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
      dropOperation x,
      rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
      .apply "PInput" [.fvar z, .lambda none listenerBody]] : List Pattern).Perm
    [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
     .apply "PInput" [.fvar z, .lambda none listenerBody],
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] := by
  simpa using
    (show (([rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x] ++
        [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]), .apply "PInput" [.fvar z, .lambda none listenerBody]]) : List Pattern).Perm
        (([rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]), .apply "PInput" [.fvar z, .lambda none listenerBody]] ++
          [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x]) : List Pattern) from
      List.perm_append_comm)

/-- SC bridge: name-server listener source into COMM-ready shape. -/
theorem nameServer_listener_source_sc_comm_shape
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nameServerListenerSource x z v s listenerBody)
      (nameServerListenerPreComm x z v s listenerBody) := by
  calc
    nameServerListenerSource x z v s listenerBody =
        .collection .hashBag
          [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x,
           rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
           .apply "PInput" [.fvar z, .lambda none listenerBody]] none := by
            simpa using nameServer_listener_source_eq_bag x z v s listenerBody
    _ ≡ nameServerListenerPreComm x z v s listenerBody := by
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm _ _
                (nameServer_listener_comm_shape_perm x z v s listenerBody)

/-- Candidate COMM reduction on the canonical name-server listener COMM-redex shape. -/
def nameServer_listener_preComm_reduces
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nameServerListenerPreComm x z v s listenerBody)
      (nameServerListenerTarget x z v s listenerBody) := by
  simpa [nameServerListenerPreComm, nameServerListenerTarget] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.comm
      (n := (.fvar z))
      (q := (.apply "PDrop" [.fvar s]))
      (p := listenerBody)
      (rest := [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x]))

/-- COMM decomposition endpoint for name-server listener sources:
SC normalization + candidate COMM step to canonical target. -/
theorem nameServer_listener_comm_decompose
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nameServerListenerSource x z v s listenerBody)
      (nameServerListenerPreComm x z v s listenerBody) ∧
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nameServerListenerPreComm x z v s listenerBody)
      (nameServerListenerTarget x z v s listenerBody)) := by
  exact ⟨nameServer_listener_source_sc_comm_shape x z v s listenerBody,
    ⟨nameServer_listener_preComm_reduces x z v s listenerBody⟩⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization
