import Mettapedia.GSLT.LanguageDef.TheoryGraph
import Mettapedia.Logic.HOL.TypeDerivedSignatureExamples
import Mettapedia.Logic.HOL.WitnessedSaturation

/-!
# Extensional HOL consequence under type-derived interpretations

The existing finite-derivation closure and the type-derived signature category
form a consequence institution. Its theories enter the existing theory graph;
this is a proof-theoretic object, not the full-domain or Henkin model semantics.
No completeness, model-expansion, or reverse proof-transport law is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HOLTypeDerivedConsequence

open CategoryTheory
open Mettapedia.Logic.HOL
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe u

/-- Finite extensional HOL derivability, with its existing cut theorem. -/
def derivationClosure (S : TypeDerivedSignature.{u}) :
    ClosureOperator (Set (ClosedFormula S.2.Const)) where
  toFun := ClosedTheorySet.provableClosure
  monotone' := by
    intro T U subset φ proof
    exact ClosedTheorySet.provable_mono (fun {_} member => subset member) proof
  le_closure' := ClosedTheorySet.subset_provableClosure
  idempotent' := by
    intro T
    ext φ
    exact ⟨ClosedTheorySet.provable_of_provableClosure, ClosedTheorySet.provable_of_mem⟩

/-- Consequence-only HOL with base sorts interpreted by arbitrary simple types. -/
def institution : PiInstitution TypeDerivedSignature.{u} where
  sentence := TypeDerivedSignature.sentence
  consequence := derivationClosure
  translation f _ := by
    rintro _ ⟨φ, proof, rfl⟩
    exact TypeDerivedSignature.provable_map f proof

theorem empty_consequence_iff {S : TypeDerivedSignature.{u}}
    (φ : ClosedFormula S.2.Const) :
    φ ∈ institution.theorems S ↔ ExtDerivation.Theorem S.2.Const φ := by
  constructor
  · rintro ⟨premises, admitted, proof⟩
    exact proof.mono (fun {_} member => (admitted _ member).elim)
  · intro proof
    refine ⟨[], ?_, proof⟩
    intro ψ member
    cases member

/-- The existing theory graph hosts these closed theories as its usual fibre. -/
def toTheoryGraph : PiInstitution.TheoryObject institution ⥤ TheoryGraph.Object :=
  TheoryGraph.fibre ⟨Cat.of TypeDerivedSignature, institution⟩

/-- A signature interpretation whose translated axioms are target-provable
induces the existing notion of closed-theory morphism. -/
def theoryHom {S T : TypeDerivedSignature.{u}} (f : S ⟶ T)
    (sourceAxioms : ClosedTheorySet S.2.Const) (targetAxioms : ClosedTheorySet T.2.Const)
    (admitted : ∀ φ ∈ sourceAxioms,
      ClosedTheorySet.Provable targetAxioms (TypeDerivedSignature.sentence.map f φ)) :
    PiInstitution.TheoryHom
      (PiInstitution.generatedTheory institution S sourceAxioms)
      (PiInstitution.generatedTheory institution T targetAxioms) where
  mapSignature := f
  preserves := by
    intro φ proof
    have translated := TypeDerivedSignature.provable_map f proof
    apply ClosedTheorySet.provable_of_provableClosure
    apply ClosedTheorySet.provable_mono (T := Set.image (TypeDerivedSignature.sentence.map f) sourceAxioms)
      (U := ClosedTheorySet.provableClosure targetAxioms) ?_ translated
    rintro _ ⟨ψ, member, rfl⟩
    exact admitted ψ member

namespace Examples

open TypeDerivedSignatureExamples

/-- The actual two-step interpretation is a theory-graph arrow, not just a
pair of compatible functions without a consumer. -/
def betaTheoryHom :
    PiInstitution.TheoryHom
      (PiInstitution.generatedTheory institution source ∅)
      (PiInstitution.generatedTheory institution target ∅) :=
  theoryHom (first ≫ second) ∅ ∅ (by intro φ member; cases member)

theorem beta_theorem_transported :
    targetBeta ∈ (PiInstitution.generatedTheory institution target ∅).theory.1 := by
  rw [← composed_sentence]
  apply betaTheoryHom.preserves
  change ClosedTheorySet.Provable ∅ sourceBeta
  refine ⟨[], ?_, sourceBeta_provable⟩
  intro φ member
  cases member

/-- The same substantive interpretation in the total, heterogeneous theory graph. -/
def betaGraphHom :
    toTheoryGraph.obj (PiInstitution.generatedTheory institution source ∅) ⟶
      toTheoryGraph.obj (PiInstitution.generatedTheory institution target ∅) :=
  toTheoryGraph.map betaTheoryHom

/-- The consequence institution records the existing countermodel boundary:
the sort-collapse arrow creates a theorem that cannot be reflected. -/
theorem collapse_not_reflecting_consequence :
    TypeDerivedSignature.sentence.map collapse TypeSubstitutionExample.sourceClaim ∈
        institution.theorems oneSort ∧
      TypeSubstitutionExample.sourceClaim ∉ institution.theorems twoSorts := by
  exact ⟨(empty_consequence_iff (S := oneSort) _).mpr collapse_not_reflecting.1,
    fun proof => collapse_not_reflecting.2 ((empty_consequence_iff (S := twoSorts) _).mp proof)⟩

end Examples

#print axioms institution
#print axioms theoryHom
#print axioms Examples.beta_theorem_transported
#print axioms Examples.betaGraphHom
#print axioms Examples.collapse_not_reflecting_consequence

end Mettapedia.GSLT.LanguageDef.HOLTypeDerivedConsequence
