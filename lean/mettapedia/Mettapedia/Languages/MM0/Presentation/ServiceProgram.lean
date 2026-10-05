import Mettapedia.Languages.MM0.Presentation.SpecificationProgram
import Mettapedia.Languages.MM0.Presentation.CalculusProgramContract
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramInsertion

/-!
# One MM0 checking and admission program

Joining the existing components preserves their actual dispatch and every
source outcome, including failure and exhaustion. The admission additions do
not claim names called by certificate checking; the certificate additions do
not claim names called by admission. No guest computation is copied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Service

open Kernel
open ComputationalProof ComputationalDeclaration ComputationalDefinitionAdmission
open ComputationalFreeVariables ComputationalAdmission ComputationalSpecification
open ComputationalCalculus
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def admissionAdditions : Program :=
  declarationEquations ++ (naturalDifferenceEquations ++ freeVariablesEquations) ++
    bodyEquations ++ admissionEquations ++ specificationEquations

def program : Program := specificationProgram ++ calculusEquations

theorem specification_decomposition :
    specificationProgram = proofProgram ++ admissionAdditions := by
  simp [specificationProgram, admissionProgram, bodyProgram, bodyBase,
    declarationProgram, admissionAdditions, List.append_assoc]

theorem admission_disjoint :
    ∀ equation ∈ admissionAdditions, equation.head ∉ calculusProgram.calledHeads := by
  have checked : admissionAdditions.all
      (fun equation => !calculusProgram.calledHeads.contains equation.head) = true := by
    decide +kernel
  intro equation member
  have excluded := List.all_eq_true.mp checked equation member
  simpa using excluded

theorem calculus_disjoint :
    ∀ equation ∈ calculusEquations, equation.head ∉ specificationProgram.calledHeads := by
  have checked : calculusEquations.all
      (fun equation => !specificationProgram.calledHeads.contains equation.head) = true := by
    decide +kernel
  intro equation member
  have excluded := List.all_eq_true.mp checked equation member
  simpa using excluded

theorem calculus_outcomes (fuel : Nat) (head : String)
    (used : head ∈ calculusProgram.calledHeads) (arguments : List Term) :
    apply program dataEqualityHost fuel head arguments =
      apply calculusProgram dataEqualityHost fuel head arguments := by
  rw [program, specification_decomposition]
  exact apply_insert_eq proofProgram calculusEquations admissionAdditions dataEqualityHost
    admission_disjoint fuel head used arguments

theorem specification_outcomes (fuel : Nat) (head : String)
    (used : head ∈ specificationProgram.calledHeads) (arguments : List Term) :
    apply program dataEqualityHost fuel head arguments =
      apply specificationProgram dataEqualityHost fuel head arguments :=
  apply_append_eq specificationProgram calculusEquations dataEqualityHost calculus_disjoint
    fuel head used arguments

theorem calculus_returns (head : String) (used : head ∈ calculusProgram.calledHeads)
    (arguments : List Term) (result : Term) :
    Applies program dataEqualityHost head arguments result ↔
      Applies calculusProgram dataEqualityHost head arguments result := by
  unfold Applies
  simp only [calculus_outcomes _ _ used]

end Mettapedia.Languages.MM0.Presentation.Service
