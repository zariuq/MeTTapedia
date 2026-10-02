import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-! # Distinct sections of a cumulative syntactic comprehension -/

open CategoryTheory
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticContextual

/-! ## Concrete nondegenerate Tower witnesses -/

namespace TowerExamples

/-- The formed empty context for the cumulative Tower presentation. -/
abbrev empty : FormedContext Tower.rules := emptyContext Tower.rules

/-- `U₁` as a formed type over the empty context. -/
def universeOne : TypeOver empty where
  code := sortTm (.succ Tower.zero)
  level := .sort (.succ (.succ Tower.zero))
  isUniverse := .sort (.succ (.succ Tower.zero))
  formed := .headType (.sort (.succ Tower.zero))

/-- `U₀` is one term of `U₁`. -/
def universeZero : Term empty universeOne where
  code := sortTm Tower.zero
  typed := .headType (.sort Tower.zero)

/-- The opaque legacy ground type is another term of `U₁`, obtained by
its native `U₀` formation followed by cumulative lifting. -/
def legacyGround : Term empty universeOne where
  code := .head .legacyGround
  typed := .cumul (.headType .legacyGround) (by
    intro _valuation
    exact Nat.zero_le _)

/-- Turn a closed term of `U₁` into a section of its comprehension. -/
def sectionHom (term : Term empty universeOne) :
    empty ⟶ extendContext empty universeOne :=
  extendHom (𝟙 empty)
    (Term.cast (TypeOver.reindex_id universeOne).symm term)

/-- Negative control: the syntactic contextual category retains which term a
section selected; cumulativity does not collapse `U₀` and the legacy ground
head into one arrow. -/
theorem universeZero_section_ne_legacyGround_section :
    sectionHom universeZero ≠ sectionHom legacyGround := by
  apply extendHom_ne_of_term_code_ne
  intro equalCodes
  have equalHeads :
      LevelTower.Head.sort Tower.zero = LevelTower.Head.legacyGround :=
    Tm.head.inj equalCodes
  cases equalHeads

end TowerExamples

#print axioms TowerExamples.universeOne
#print axioms TowerExamples.universeZero
#print axioms TowerExamples.legacyGround
#print axioms TowerExamples.sectionHom
#print axioms TowerExamples.universeZero_section_ne_legacyGround_section

end SyntacticContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
