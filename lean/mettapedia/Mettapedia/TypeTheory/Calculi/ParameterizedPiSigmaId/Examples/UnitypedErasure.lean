import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.RawUnitypedErasure
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ContextualSections
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ContextualLadderBridge

/-! # Finite execution and admission controls -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace RawUnitypedErasure
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
set_option autoImplicit false
open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open SyntacticContextual

namespace TowerCanary

abbrev empty : FormedContext Tower.rules :=
  SyntacticContextual.TowerExamples.empty

/-- `U₀` as a formed type over the empty telescope. -/
def universeZeroType : TypeOver empty where
  code := sortTm Tower.zero
  level := .sort (.succ Tower.zero)
  isUniverse := .sort (.succ Tower.zero)
  formed := .headType (.sort Tower.zero)

/-- `U₀` and `U₁` are genuinely different formed type objects before
erasure. -/
theorem universeZeroType_ne_universeOne :
    universeZeroType ≠ SyntacticContextual.TowerExamples.universeOne := by
  intro equality
  have equalCodes := congrArg TypeOver.code equality
  have equalHeads :
      Tower.Head.sort Tower.zero = Tower.Head.sort (.succ Tower.zero) :=
    Tm.head.inj equalCodes
  have equalLevels : Tower.zero = .succ Tower.zero :=
    Tower.Head.sort.inj equalHeads
  change LevelExpr.const 0 = LevelExpr.succ (LevelExpr.const 0) at equalLevels
  cases equalLevels

/-- Negative control: the type action of raw erasure is not injective.  It
forgets the distinction between two genuinely different universe types. -/
theorem strictErasure_type_map_not_injective :
    ¬ Function.Injective
      (fun type : TypeOver empty =>
        (erasureFamilyMorphism Tower.rules).mapType type) := by
  intro injective
  exact universeZeroType_ne_universeOne
    (injective (by rfl))

/-- Positive control: despite type collapse, two distinct raw terms in a
fixed type fibre cannot be identified by the erasure. -/
theorem universe_terms_reflect_raw_equality
    (left right : Term empty SyntacticContextual.TowerExamples.universeOne)
    (equalErasures :
      (erasureFamilyMorphism Tower.rules).mapTerm left =
        (erasureFamilyMorphism Tower.rules).mapTerm right) :
    left = right :=
  mapTerm_injective_at_fixed_type Tower.rules equalErasures

end TowerCanary

#print axioms TowerCanary.universeZeroType_ne_universeOne

#print axioms TowerCanary.strictErasure_type_map_not_injective

#print axioms TowerCanary.universe_terms_reflect_raw_equality

end RawUnitypedErasure
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
