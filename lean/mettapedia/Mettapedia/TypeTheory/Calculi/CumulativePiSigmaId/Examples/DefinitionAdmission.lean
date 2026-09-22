import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationComputation

/-!
# Formation and unfolding controls for definition admission

A raw identity clause can be typed over an undeclared domain: raw typing
does not assert context or type formation. Declaration formation rejects that
package. A transparent universe alias supplies the positive control, and its
actual unfolding preserves a displayed type above its declaration universe.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DefinitionAdmission

open Presentation Declaration

private def missingName : DeclName := `DefinitionAdmission.MissingType
private def identityName : DeclName := `DefinitionAdmission.missingIdentity
private def identityType : Tower.Tm 0 := .pi (.const missingName) (.const missingName)

def missingIdentitySignature : Signature Tower.Head :=
  Signature.empty.insert identityName ⟨identityType, some (.lam (.var 0))⟩

/-- Raw endpoint typing alone does not earn declaration formation. -/
theorem missingIdentity_body_rawTyped :
    HasType (extendRules Tower.rules missingIdentitySignature)
      (.nil : Tower.Ctx 0) (.lam (.var 0)) identityType := by
  apply HasType.lamIntro
  simpa [identityType, Ctx.lookup_snoc_zero, rename] using
    (HasType.var (R := extendRules Tower.rules missingIdentitySignature)
      (Γ := .snoc (.nil : Tower.Ctx 0) (.const missingName)) 0)

theorem missingIdentitySignature_notFormed :
    ¬ missingIdentitySignature.Formed Tower.rules := by
  apply Signature.notFormedOfMissingPiDomain
    (name := identityName) (missingName := missingName) (codomain := .const missingName)
  · simp [missingIdentitySignature, identityType]
  · simp [extendRules, combinedType, Tower.rules, missingIdentitySignature,
      Signature.typeOf?, Signature.insert, Signature.empty, identityName, missingName]

private def aliasName : DeclName := `DefinitionAdmission.UniverseAlias
private def body : Tower.Tm 0 := sortTm Tower.zero
private def declaredType : Tower.Tm 0 := sortTm (.succ Tower.zero)

/-- A transparent, nonempty declaration; unfolding changes a constant to a sort. -/
def transparentSignature : Signature Tower.Head :=
  Signature.empty.insert aliasName ⟨declaredType, some body⟩

theorem transparentSignature_formed : transparentSignature.Formed Tower.rules where
  fresh := by
    intro name entry lookup
    rfl
  types := by
    intro name type lookup
    by_cases same : name = aliasName
    · subst name
      have equality : type = declaredType := by simpa [transparentSignature] using lookup.symm
      subst type
      exact ⟨.sort (.succ (.succ Tower.zero)), .sort _, .headType (.sort _)⟩
    · simp [transparentSignature, Signature.typeOf?, Signature.insert, Signature.empty,
        same] at lookup
  values := by
    intro name type value typeLookup valueLookup
    by_cases same : name = aliasName
    · subst name
      have typeEquality : type = declaredType := by
        simpa [transparentSignature] using typeLookup.symm
      have valueEquality : value = body := by
        simpa [transparentSignature] using valueLookup.symm
      subst type
      subst value
      exact .headType (.sort _)
    · simp [transparentSignature, Signature.typeOf?, Signature.insert, Signature.empty,
        same] at typeLookup
  noSelfDelta := by
    intro name value lookup
    by_cases same : name = aliasName
    · subst name
      have equality : value = body := by simpa [transparentSignature] using lookup.symm
      subst value
      intro impossible
      cases impossible
    · simp [transparentSignature, Signature.valueOf?, Signature.insert, Signature.empty,
        same] at lookup

/-- The body is checked once at U1. Constant generation retains and replays
the genuine lift to U2 after unfolding in any ambient context. -/
theorem unfolded_at_larger_displayed_universe (context : Tower.Ctx n) :
    HasType (extendRules Tower.rules transparentSignature) context
      (liftClosed body) (sortTm (.const 2)) := by
  apply ComputationAuthority.Signature.Formed.deltaPreserves transparentSignature_formed
    (name := aliasName)
  · simp [transparentSignature]
  · apply HasType.cumul
      (u := .sort (.succ Tower.zero))
    · apply HasType.const (name := aliasName) (type := declaredType)
      exact combinedType_of_signature Tower.rules transparentSignature rfl
        (show transparentSignature.typeOf? aliasName = some declaredType by
          simp [transparentSignature])
    · intro valuation
      simp [Tower.zero, LevelExpr.eval]

#print axioms missingIdentity_body_rawTyped
#print axioms missingIdentitySignature_notFormed
#print axioms transparentSignature_formed
#print axioms unfolded_at_larger_displayed_universe

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DefinitionAdmission
