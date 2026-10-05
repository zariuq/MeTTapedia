import Mettapedia.Languages.MM0.Presentation.DefinitionAdmissionCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalTableData

/-!
# MM0 sequential theory admission as data

The four namespaces retain their complete ordered stores. Admission commands
distinguish assumptions from proved declarations and retain the exact supplied
proof. Storage is updated only by the authored admission program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalDefinitions
open ComputationalProof ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeTheory (theory : Theory) : Term :=
  .list [.sym "MM0:Theory", encodeSorts theory.sorts, encodeTable theory.terms,
    encodeDefinitions theory.definitions, encodeTheorems theory.theorems]

def encodeAdmission : Admission → Term
  | .sort index info => .list [.sym "MM0:AdmitSort", natural index, encodeSort info]
  | .term index declaration => .list [.sym "MM0:AdmitTerm", natural index, encodeDeclaration declaration]
  | .definition index declaration body =>
      .list [.sym "MM0:AdmitDefinition", natural index, encodeDeclaration declaration, encodeBody body]
  | .axiomDecl index declaration => .list [.sym "MM0:AdmitAxiom", natural index, encodeTheorem declaration]
  | .theoremDecl index declaration dummies proof =>
      .list [.sym "MM0:AdmitTheorem", natural index, encodeTheorem declaration,
        encodeNaturals dummies, encodeProof proof]

def encodeAdmissions (admissions : List Admission) : Term := .list (admissions.map encodeAdmission)

def encodeTheoryResult (theory : Option Theory) : Term := encodeLookupResult (theory.map encodeTheory)

theorem encodeTheorem_injective : Function.Injective encodeTheorem := by
  intro left right same
  simp only [encodeTheorem, Term.list.injEq, List.cons.injEq, true_and, and_true] at same
  have contexts := encodeContext_injective same.1
  have hypotheses := ComputationalConversion.encodeExpressions_injective same.2.1
  have conclusions := encode_injective same.2.2
  cases left; cases right
  simp_all

theorem encodeTheory_injective : Function.Injective encodeTheory := by
  intro left right same
  simp only [encodeTheory, Term.list.injEq, List.cons.injEq, true_and, and_true] at same
  have sorts := encodeNaturalTable_injective encodeSort encodeSort_injective same.1
  have terms := encodeNaturalTable_injective encodeDeclaration encodeDeclaration_injective same.2.1
  have definitions := encodeNaturalTable_injective encodeBody encodeBody_injective same.2.2.1
  have theorems := encodeNaturalTable_injective encodeTheorem encodeTheorem_injective same.2.2.2
  cases left; cases right
  simp_all

theorem encodeTheoryResult_injective : Function.Injective encodeTheoryResult := by
  intro left right same
  have same := encodeLookupResult_injective same
  cases left <;> cases right <;> simp_all [encodeTheory_injective.eq_iff]

theorem axiom_and_theorem_commands_are_distinct (index : Nat) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) :
    encodeAdmission (.axiomDecl index declaration) ≠
      encodeAdmission (.theoremDecl index declaration dummies proof) := by
  simp [encodeAdmission]

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
