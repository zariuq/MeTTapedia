import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-! # Concrete instances and controls for DeclarationSignature -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration

/-! ## Executable boundary witnesses -/

namespace Examples

def opaqueTypeName : DeclName := `CumulativeTower.DeclarationExample.A

def opaqueType : Entry Tower.Head where
  type := .head (.sort Tower.zero)

def oneOpaqueType : Signature Tower.Head :=
  Signature.empty.insert opaqueTypeName opaqueType

theorem oneOpaqueType_wellFormed :
    oneOpaqueType.WellFormed Tower.rules where
  fresh := by
    intro name entry lookup
    rfl
  types := by
    intro name type lookup
    have nameEquality : name = opaqueTypeName := by
      by_contra different
      simp [oneOpaqueType, Signature.typeOf?, Signature.insert,
        Signature.empty, different] at lookup
    subst name
    have typeEquality : type = (.head (.sort Tower.zero) : Tm Tower.Head 0) := by
      simpa [oneOpaqueType, opaqueType] using lookup.symm
    subst type
    exact ⟨.sort (.succ Tower.zero), .sort (.succ Tower.zero),
      .headType (.sort Tower.zero)⟩
  values := by
    intro name type value typeLookup valueLookup
    by_cases equal : name = opaqueTypeName
    · subst name
      simp [oneOpaqueType, Signature.valueOf?, Signature.insert, opaqueType,
        Signature.empty] at valueLookup
    · simp [oneOpaqueType, Signature.valueOf?, Signature.insert, opaqueType,
        Signature.empty, equal] at valueLookup
  noSelfDelta := by
    intro name value lookup
    by_cases equal : name = opaqueTypeName
    · subst name
      simp [oneOpaqueType, Signature.valueOf?, Signature.insert, opaqueType,
        Signature.empty] at lookup
    · simp [oneOpaqueType, Signature.valueOf?, Signature.insert, opaqueType,
        Signature.empty, equal] at lookup
  declaredPreserves := by
    intro n context left right type step typing
    exact step.elim

example : oneOpaqueType.typeOf? opaqueTypeName =
    some (.head (.sort Tower.zero)) := by
  simp [oneOpaqueType, opaqueType]

example : HasType (extendRules Tower.rules oneOpaqueType)
    (.nil : Ctx Tower.Head 0) (.const opaqueTypeName)
    (.head (.sort Tower.zero)) := by
  refine HasType.const (R := extendRules Tower.rules oneOpaqueType)
    (name := opaqueTypeName)
    (type := (.head (.sort Tower.zero) : Tm Tower.Head 0)) ?_
  change combinedType Tower.rules oneOpaqueType opaqueTypeName =
    some (.head (.sort Tower.zero))
  exact (by
    apply combinedType_of_signature
    · rfl
    · simp [oneOpaqueType, opaqueType])

/-- An undeclared name remains unavailable; signature extension is fail-closed. -/
theorem absent_constant_is_not_declared
    (different : DeclName) (notEqual : different ≠ opaqueTypeName) :
    oneOpaqueType.typeOf? different = none := by
  simp [oneOpaqueType, Signature.typeOf?, Signature.insert, Signature.empty,
    notEqual]

end Examples



end Declaration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
