import Mettapedia.Languages.Megalodon.SignatureEmbedding
import Mathlib.Logic.Equiv.Basic

/-!
# Constructed round trips for selected Megalodon libraries

Global names and base-carrier addresses can be changed by bijections while
primitive slots retain their declared positions. The target environment is
constructed by mapping every declaration, definition and known proposition.
Both exact lookup embeddings and their inverse are then proved, rather than
supplied as extra compatibility assumptions.

This gives inverse maps on types, terms and proof syntax, including open
binders, and exact preservation and reflection of bounded proof checking.
It does not identify different axiom packages or establish the truth of an
imported assumption. Syntax export and source parsing remain separate from
this selected-signature equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SignatureEquivalence

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.SignatureEmbedding

/-- A bijective change of names and carrier addresses. Primitive slots are
part of the selected source theory and are kept in their declared order. -/
structure LibraryRenaming where
  names : Name ≃ Name
  carriers : Nat ≃ Nat

namespace LibraryRenaming

def symm (relabel : LibraryRenaming) : LibraryRenaming :=
  ⟨relabel.names.symm, relabel.carriers.symm⟩

def toMap (relabel : LibraryRenaming) : SignatureMap where
  name := relabel.names
  primitive := id
  base := relabel.carriers
  name_injective := relabel.names.injective
  primitive_injective := Function.injective_id
  base_injective := relabel.carriers.injective

/-- The complete finite target signature, including definition bodies and
the propositions at known-proof addresses. -/
def mapEnvironment (relabel : LibraryRenaming) (source : Environment) : Environment where
  primitives := source.primitives.map (mapTp relabel.toMap)
  terms := source.terms.map (mapTermDecl relabel.toMap)
  known := source.known.map (mapKnownDecl relabel.toMap)

@[simp] theorem symm_symm (relabel : LibraryRenaming) :
    relabel.symm.symm = relabel := by
  cases relabel
  rfl

@[simp] theorem mapTp_roundtrip (relabel : LibraryRenaming) (type : Tp) :
    mapTp relabel.symm.toMap (mapTp relabel.toMap type) = type := by
  induction type <;> simp only [mapTp, *]
  simp [toMap, symm]

@[simp] theorem mapTm_roundtrip (relabel : LibraryRenaming) (term : Tm) :
    mapTm relabel.symm.toMap (mapTm relabel.toMap term) = term := by
  induction term <;> simp only [mapTm, mapTp_roundtrip, *] <;> simp [toMap, symm]

@[simp] theorem mapPf_roundtrip (relabel : LibraryRenaming) (proof : Pf) :
    mapPf relabel.symm.toMap (mapPf relabel.toMap proof) = proof := by
  induction proof <;> simp only [mapPf, mapTp_roundtrip, mapTm_roundtrip, *] <;>
    simp [toMap, symm]

@[simp] theorem mapTermDecl_roundtrip (relabel : LibraryRenaming) (decl : TermDecl) :
    mapTermDecl relabel.symm.toMap (mapTermDecl relabel.toMap decl) = decl := by
  cases decl with
  | mk name type definition =>
      cases definition <;> simp only [mapTermDecl, mapTp_roundtrip, Option.map_none,
        Option.map_some, mapTm_roundtrip] <;> simp [toMap, symm]

@[simp] theorem mapKnownDecl_roundtrip (relabel : LibraryRenaming) (decl : KnownDecl) :
    mapKnownDecl relabel.symm.toMap (mapKnownDecl relabel.toMap decl) = decl := by
  cases decl
  simp only [mapKnownDecl, mapTm_roundtrip]
  simp [toMap, symm]

@[simp] theorem mapEnvironment_roundtrip (relabel : LibraryRenaming) (source : Environment) :
    relabel.symm.mapEnvironment (relabel.mapEnvironment source) = source := by
  cases source
  simp [mapEnvironment, List.map_map, Function.comp_def]

/-- Exact lookup agreement follows from the actual mapped declarations,
including the absence of names not present in the source. -/
def embedding (relabel : LibraryRenaming) (source : Environment) :
    Embedding source (relabel.mapEnvironment source) where
  map := relabel.toMap
  lookupPrimitive_commutes := by
    intro index
    simp [mapEnvironment, toMap]
  lookupTerm_commutes := by
    intro name
    exact lookupTermList?_map relabel.toMap source.terms name
  lookupKnown_commutes := by
    intro name
    exact lookupKnownList?_map relabel.toMap source.known name

def inverseEmbedding (relabel : LibraryRenaming) (source : Environment) :
    Embedding (relabel.mapEnvironment source) source := by
  simpa using relabel.symm.embedding (relabel.mapEnvironment source)

def typesEquiv (relabel : LibraryRenaming) : Tp ≃ Tp where
  toFun := mapTp relabel.toMap
  invFun := mapTp relabel.symm.toMap
  left_inv := mapTp_roundtrip relabel
  right_inv := by
    intro type
    simpa using mapTp_roundtrip relabel.symm type

def termsEquiv (relabel : LibraryRenaming) : Tm ≃ Tm where
  toFun := mapTm relabel.toMap
  invFun := mapTm relabel.symm.toMap
  left_inv := mapTm_roundtrip relabel
  right_inv := by
    intro term
    simpa using mapTm_roundtrip relabel.symm term

def proofsEquiv (relabel : LibraryRenaming) : Pf ≃ Pf where
  toFun := mapPf relabel.toMap
  invFun := mapPf relabel.symm.toMap
  left_inv := mapPf_roundtrip relabel
  right_inv := by
    intro proof
    simpa using mapPf_roundtrip relabel.symm proof

theorem substitute_commutes (relabel : LibraryRenaming) (replacement body : Tm) :
    relabel.termsEquiv (Tm.instantiate replacement body) =
      Tm.instantiate (relabel.termsEquiv replacement) (relabel.termsEquiv body) :=
  mapTm_instantiate relabel.toMap replacement body

theorem typeSubstitute_commutes (relabel : LibraryRenaming) (replacement : Tp) (body : Tm) :
    relabel.termsEquiv (Tm.typeInstantiate replacement body) =
      Tm.typeInstantiate (relabel.typesEquiv replacement) (relabel.termsEquiv body) :=
  mapTm_typeInstantiate relabel.toMap replacement body

theorem checkProof_iff (relabel : LibraryRenaming) (source : Environment)
    (fuel depth : Nat) (terms : List Tp) (hypotheses : List Tm)
    (proof : Pf) (proposition : Tm) :
    checkProof (relabel.mapEnvironment source) fuel depth
        (terms.map (mapTp relabel.toMap)) (hypotheses.map (mapTm relabel.toMap))
        (mapPf relabel.toMap proof) (mapTm relabel.toMap proposition) =
      checkProof source fuel depth terms hypotheses proof proposition :=
  (relabel.embedding source).checkProof_map fuel depth terms hypotheses proof proposition

/-- Every target certificate has a source certificate with exactly the same
verdict; this quantifies over target syntax, not only a chosen forward image. -/
theorem checkProof_inverse (relabel : LibraryRenaming) (source : Environment)
    (fuel depth : Nat) (terms : List Tp) (hypotheses : List Tm)
    (proof : Pf) (proposition : Tm) :
    checkProof source fuel depth
        (terms.map (mapTp relabel.symm.toMap))
        (hypotheses.map (mapTm relabel.symm.toMap))
        (mapPf relabel.symm.toMap proof) (mapTm relabel.symm.toMap proposition) =
      checkProof (relabel.mapEnvironment source) fuel depth terms hypotheses proof proposition := by
  simpa using relabel.symm.checkProof_iff (relabel.mapEnvironment source)
    fuel depth terms hypotheses proof proposition

/-- A dependent consumer can receive the transported certificate itself,
including its premise structure. The inverse recovers the original proof;
the equivalence does not replace evidence by a successful-checking bit. -/
def qualifiedProofs (relabel : LibraryRenaming) (source : Environment)
    (fuel depth : Nat) (terms : List Tp) (hypotheses : List Tm) (proposition : Tm) :
    {proof : Pf // checkProof source fuel depth terms hypotheses proof proposition = true} ≃
      {proof : Pf // checkProof (relabel.mapEnvironment source) fuel depth
        (terms.map (mapTp relabel.toMap)) (hypotheses.map (mapTm relabel.toMap))
        proof (mapTm relabel.toMap proposition) = true} where
  toFun proof := ⟨mapPf relabel.toMap proof.1, by
    rw [checkProof_iff]
    exact proof.2⟩
  invFun proof := ⟨mapPf relabel.symm.toMap proof.1, by
    have reverse := relabel.checkProof_inverse source fuel depth
      (terms.map (mapTp relabel.toMap)) (hypotheses.map (mapTm relabel.toMap))
      proof.1 (mapTm relabel.toMap proposition)
    simp only [List.map_map, Function.comp_def, mapTp_roundtrip, mapTm_roundtrip] at reverse
    simpa only [List.map_id'] using reverse.trans proof.2⟩
  left_inv proof := Subtype.ext (mapPf_roundtrip relabel proof.1)
  right_inv proof := Subtype.ext (by
    simpa using mapPf_roundtrip relabel.symm proof.1)

@[simp] theorem qualifiedProofs_value (relabel : LibraryRenaming) (source : Environment)
    (fuel depth : Nat) (terms : List Tp) (hypotheses : List Tm) (proposition : Tm)
    (proof : {proof : Pf //
      checkProof source fuel depth terms hypotheses proof proposition = true}) :
    (qualifiedProofs relabel source fuel depth terms hypotheses proposition proof).1 =
      mapPf relabel.toMap proof.1 := rfl

end LibraryRenaming

namespace Examples

/-- Both a used declaration name and a used carrier address change. -/
def swapNamesAndCarriers : LibraryRenaming :=
  ⟨Equiv.swap "p" "prime-p", Equiv.swap 0 1⟩

theorem source_carrier_moves :
    mapTp swapNamesAndCarriers.toMap (.base 0) = .base 1 := by
  simp [swapNamesAndCarriers, LibraryRenaming.toMap, mapTp]

theorem source_name_moves :
    mapTm swapNamesAndCarriers.toMap (.named "p") = .named "prime-p" := by
  simp [swapNamesAndCarriers, LibraryRenaming.toMap, mapTm]

theorem transported_accepts :
    checkProof (swapNamesAndCarriers.mapEnvironment Canary.sourceEnvironment) 16 0 [] []
      (mapPf swapNamesAndCarriers.toMap Canary.proof)
      (mapTm swapNamesAndCarriers.toMap Canary.goal) = true := by
  simpa using (swapNamesAndCarriers.checkProof_iff Canary.sourceEnvironment
    16 0 [] [] Canary.proof Canary.goal).trans Canary.source_accepts

/-- Importing the old proof while changing its carrier addresses is refused:
the symbol spelling alone is not a signature translation. -/
theorem unchanged_proof_refused :
    checkProof (swapNamesAndCarriers.mapEnvironment Canary.sourceEnvironment) 16 0 [] []
      Canary.proof (mapTm swapNamesAndCarriers.toMap Canary.goal) = false := by
  simp [swapNamesAndCarriers, LibraryRenaming.mapEnvironment, LibraryRenaming.toMap,
    Canary.sourceEnvironment, Canary.proof, Canary.goal, Canary.domain,
    Canary.namedAtom, Canary.primitiveAtom, Canary.predicateType,
    mapTp, mapTm, mapTermDecl, checkProof, checkNormalizedProof, inferProof,
    inferTerm, MathdataKernel.normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?, Tp.plainWellFormed]

end Examples

end Mettapedia.Languages.Megalodon.SignatureEquivalence
