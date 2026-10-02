import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-! # Concrete instances and controls for FormationSensitiveRegularity -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

/-! ## Declaration-formation controls -/

namespace Examples

def declaredName : DeclName := `FormationSensitiveExample.declared

def missingName : DeclName := `FormationSensitiveExample.missing

/-- One opaque declaration with the already formed cumulative ground type. -/
def formedDeclarationRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = declaredName then some (.head .legacyGround) else none }

/-- Positive: the declaration's actual type-formation proof licenses its use
in the complete candidate judgment. -/
theorem formed_declaration_judgment :
    Judgment formedDeclarationRules (.nil : Tower.Ctx 0)
      (.const declaredName) (.head .legacyGround) := by
  refine ⟨.nil, ?_⟩
  exact Typing.const (R := formedDeclarationRules) (Γ := .nil)
    (name := declaredName) (type := .head .legacyGround) (u := .sort Tower.zero) rfl
    (.headType LevelTower.HeadTyping.legacyGround) (LevelTower.IsUniverse.sort Tower.zero)

/-- The contrasting raw signature names an absent constant as the declared
type. Its universe rules and computation are otherwise unchanged. -/
def danglingDeclarationRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = declaredName then some (.const missingName) else none }

/-- Raw constant typing consults only the declared type lookup. -/
theorem raw_accepts_dangling_declaration :
    HasType danglingDeclarationRules (.nil : Tower.Ctx 0)
      (.const declaredName) (.const missingName) := by
  exact HasType.const (R := danglingDeclarationRules) (Γ := .nil)
    (name := declaredName) (type := .const missingName) rfl

/-- No conversion or cumulative tail can repair the missing closed
declaration-type formation needed by the refined constant rule. -/
theorem rejects_dangling_declaration {Γ : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing danglingDeclarationRules Γ (.const declaredName) type := by
  intro typing
  obtain ⟨declaredType, u, lookup, formed, _⟩ := typing.constFormation
  have typeEquality : declaredType = .const missingName := by
    change some (.const missingName) = some declaredType at lookup
    exact Option.some.inj lookup.symm
  subst declaredType
  obtain ⟨_, _, missingLookup, _, _⟩ := formed.constFormation
  change (none : Option (Tower.Tm 0)) = some _ at missingLookup
  cases missingLookup

end Examples


#print axioms Examples.formed_declaration_judgment
#print axioms Examples.raw_accepts_dangling_declaration
#print axioms Examples.rejects_dangling_declaration

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
