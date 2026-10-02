import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyDeclaration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies

/-!
# Formation controls for inductive declaration admission

An undeclared field type can be structurally free of the recursive family,
and its constructor can have the right positive telescope shape. Neither
property makes that field type formed. The finite counterexample below uses
the shared declaration and indexed-family interfaces, not a separate typing
relation. Natural numbers and indexed vectors provide the positive control
with actual constructor and eliminator declarations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.InductiveDeclarationFormation

open Presentation Declaration IndexedFamily

private def familyName : DeclName := `FormationTree
private def constructorName : DeclName := `FormationNode
private def missingName : DeclName := `MissingType

private def constructorType : Tower.Tm 0 :=
  .pi (.const missingName) (.const familyName)

/-- A fresh datatype and a positive constructor whose field type is absent. -/
def missingFieldSignature : Signature Tower.Head :=
  Signature.ofList
    [(familyName, ⟨sortTm (.const 0), none⟩),
     (constructorName, ⟨constructorType, none⟩)]

theorem missingFieldSignature_fresh
    {name : DeclName} {entry : Entry Tower.Head}
    (_lookup : missingFieldSignature.entries name = some entry) :
    Tower.rules.constantType name = none := rfl

/-- The rejected constructor really passes the structural positivity test. -/
def missingFieldConstructor_positive :
    ConstructorType familyName 0 constructorType :=
  .field (.free (.const (by decide)))
    (.result ⟨[], rfl, by simp, rfl⟩)

theorem missingFieldSignature_notFormed :
    ¬ missingFieldSignature.Formed Tower.rules := by
  apply Signature.notFormedOfMissingPiDomain
    (name := constructorName) (missingName := missingName)
    (codomain := .const familyName)
  · simp [missingFieldSignature, Signature.ofList, Signature.insert,
      Signature.typeOf?, constructorName, familyName, constructorType]
  · simp [extendRules, combinedType, LevelTower.rules, missingFieldSignature,
      Signature.ofList, Signature.insert, Signature.typeOf?, Signature.empty,
      missingName, constructorName, familyName]

/-- In particular, generation extracts real formation evidence for a vector
constructor's first field; this is not inferred from positivity alone. -/
theorem vectorConstructorDomain_formed :
    ∃ level : Tower.Head, Tower.rules.isUniverse level ∧
      Presentation.HasType
        (extendRules Tower.rules NativeNaturalVectorFamilies.rawSignature)
        (.nil : Tower.Ctx 0)
        (sortTm NativeNaturalVectorFamilies.elementLevel) (.head level) := by
  exact NativeNaturalVectorFamilies.rawSignature_formed.piDomainFormation
    NativeNaturalVectorFamilies.typeOf_vcons

#print axioms Signature.Formed.piDomainFormation
#print axioms Signature.notFormedOfMissingPiDomain
#print axioms missingFieldConstructor_positive
#print axioms missingFieldSignature_notFormed
#print axioms vectorConstructorDomain_formed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.InductiveDeclarationFormation
