import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexControls

/-!
# A computed type-variable solution wakes a heterogeneous residual

The original store includes `X = Ground` and the dependent equation
`snd (X, refl X) = refl Ground`. Conversion alone leaves the latter pending.
The actual flexible-variable rule computes X's assignment, transports both
endpoint types and terms, and discharges the residual. The completed computed
update is principal for both original equations.

This is heterogeneous residual wake-up. It does not implement the full
twin-variable algorithm for processing terms before their types agree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlex.Wakeup

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := Controls.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def universeType : TypeOver (empty Tower.rules) :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩
abbrev frame := extend (empty Tower.rules) universeType
def viewedUniverse : TypeOver frame := universeType.reindex (projectionHom _ universeType)
def unknownType : Term frame viewedUniverse := ⟨.var 0, .var 0⟩
def ground : Term frame viewedUniverse := ⟨.head .legacyGround, .headType .legacyGround⟩

def pairType : TypeOver frame :=
  ⟨.sigma (.head (.sort Tower.zero)) (.id (.head (.sort Tower.zero)) (.var 0) (.var 0)),
    .sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sort _,
    .sigmaForm (.headType (.sort _)) (.sort _)
      (.idForm (.headType (.sort _)) (.sort _) (.var 0) (.var 0)) (.sort _) (.sorts _ _)⟩

def dependentPair : Term frame pairType :=
  ⟨.pair unknownType.code (.refl unknownType.code),
    .pairIntro pairType.formed pairType.universeWitness unknownType.typed (.reflIntro unknownType.typed)⟩

def projectionType : TypeOver frame :=
  ⟨.id (.head (.sort Tower.zero)) (.fst dependentPair.code) (.fst dependentPair.code),
    .sort (.succ Tower.zero), .sort _,
    .idForm (.headType (.sort _)) (.sort _) (.fstElim dependentPair.typed) (.fstElim dependentPair.typed)⟩

def fixedType : TypeOver frame :=
  ⟨.id (.head (.sort Tower.zero)) ground.code ground.code,
    .sort (.succ Tower.zero), .sort _, .idForm (.headType (.sort _)) (.sort _) ground.typed ground.typed⟩

def pending : Equation (TotalTerm frame) :=
  (⟨projectionType, ⟨.snd dependentPair.code, .sndElim dependentPair.typed⟩⟩,
    ⟨fixedType, ⟨.refl ground.code, .reflIntro ground.typed⟩⟩)

theorem endpoint_types_differ : pending.1.1.code ≠ pending.2.1.code := by
  intro same
  cases same

theorem conversion_keeps_heterogeneous_residual :
    Conversion.scan (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ConversionControls.reducer 16 [pending] = [pending] := by rfl'

def computed := stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra Controls.declarations_formed ExecutableTowerChoices.choices
  ConversionControls.reducer 16 unknownType ground [pending]

theorem actual_type_solution_wakes_residual : computed.remaining = [] := by decide +kernel

theorem actual_type_solution_is_principal :
    (frames setting.levels).Principal (equation unknownType ground :: [pending]) computed.answer :=
  computed.completed actual_type_solution_wakes_residual

theorem computed_target_is_empty : computed.target = empty Tower.rules := by rfl'

theorem actual_closed_solution :
    ∃ solution : empty Tower.rules ⟶ frame,
      (frames setting.levels).Models solution (equation unknownType ground :: [pending]) := by
  refine ⟨eqToHom computed_target_is_empty.symm ≫ computed.answer, ?_⟩
  exact Frames.models_comp (X := frames setting.levels) actual_type_solution_is_principal.sound
    (eqToHom computed_target_is_empty.symm)

/-- There is an actual closed solution as well as symbolic solvability;
the update's fixed-point theorem supplies the exact comparison. -/
theorem closed_solution_is_preserved :
    (∃ solution : empty Tower.rules ⟶ frame,
      (frames setting.levels).Models solution (equation unknownType ground :: [pending])) ↔
    ∃ residual : empty Tower.rules ⟶ computed.target,
      (frames setting.levels).Models residual computed.remaining :=
  computed.fixed_point_solutions_iff (empty Tower.rules)

end ContextualDependentFlex.Wakeup
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
