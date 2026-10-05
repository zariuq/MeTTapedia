import Mettapedia.Languages.MM0.Presentation.AdmissionCorrespondence
import Mettapedia.Languages.MM0.Kernel.SpecificationChecking

/-!
# Resolved MM0 specifications and proof declarations as data

Specification entries retain declaration kinds, complete payloads and order.
An absent expected definition body is distinct from a supplied body. Proof
declarations retain the auxiliary flag and the actual admission witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification

open Kernel ComputationalContext ComputationalTyping ComputationalDefinitions
open ComputationalProof ComputationalDeclaration ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeEntry : SpecificationEntry → Term
  | .sort index info => .list [.sym "MM0:SpecSort", natural index, encodeSort info]
  | .term index declaration => .list [.sym "MM0:SpecTerm", natural index, encodeDeclaration declaration]
  | .definition index declaration body =>
      .list [.sym "MM0:SpecDefinition", natural index, encodeDeclaration declaration, encodeBodyResult body]
  | .axiomDecl index declaration => .list [.sym "MM0:SpecAxiom", natural index, encodeTheorem declaration]
  | .theoremDecl index declaration => .list [.sym "MM0:SpecTheorem", natural index, encodeTheorem declaration]

def encodeEntries (entries : List SpecificationEntry) : Term := .list (entries.map encodeEntry)

def encodeProofDeclaration (declaration : ProofDeclaration) : Term :=
  .list [.sym "MM0:ProofDeclaration", boolean declaration.isLocal, encodeAdmission declaration.admission]

def encodeProofDeclarations (declarations : List ProofDeclaration) : Term :=
  .list (declarations.map encodeProofDeclaration)

def encodeState (state : SpecificationAdmission.State) : Term :=
  .list [.sym "MM0:SpecificationState", encodeTheory state.theory, encodeEntries state.pending]

def encodeStateResult (state : Option SpecificationAdmission.State) : Term :=
  encodeLookupResult (state.map encodeState)

def encodePendingResult (pending : Option (List SpecificationEntry)) : Term :=
  encodeLookupResult (pending.map encodeEntries)

theorem encodeBodyResult_injective : Function.Injective encodeBodyResult := by
  intro left right same
  have same := encodeLookupResult_injective same
  cases left <;> cases right <;> simp_all [encodeBody_injective.eq_iff]

theorem encodeEntry_injective : Function.Injective encodeEntry := by
  intro left right same
  cases left <;> cases right <;>
    simp_all [encodeEntry, natural_injective.eq_iff, encodeSort_injective.eq_iff,
      encodeDeclaration_injective.eq_iff, encodeBodyResult_injective.eq_iff,
      encodeTheorem_injective.eq_iff]

theorem encodeEntries_injective : Function.Injective encodeEntries := by
  intro left right same
  exact List.map_injective_iff.mpr encodeEntry_injective (Term.list.inj same)

theorem encodeState_injective : Function.Injective encodeState := by
  intro left right same
  simp only [encodeState, Term.list.injEq, List.cons.injEq, true_and, and_true] at same
  have theories := encodeTheory_injective same.1
  have pending := encodeEntries_injective same.2
  cases left; cases right
  simp_all

theorem encodeStateResult_injective : Function.Injective encodeStateResult := by
  intro left right same
  have same := encodeLookupResult_injective same
  cases left <;> cases right <;> simp_all [encodeState_injective.eq_iff]

theorem axiom_and_proved_specification_kinds_are_distinct (index : Nat) (declaration : TheoremDecl) :
    encodeEntry (.axiomDecl index declaration) ≠ encodeEntry (.theoremDecl index declaration) := by
  simp [encodeEntry]

theorem omitted_body_is_not_an_empty_definition (index : Nat) (declaration : TermDecl)
    (body : Definition.Body) :
    encodeEntry (.definition index declaration none) ≠
      encodeEntry (.definition index declaration (some body)) := by
  simp [encodeEntry, encodeBodyResult, encodeLookupResult]

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
