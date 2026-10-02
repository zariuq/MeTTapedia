import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Progress
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration

/-!
# Progress for a package with no constants

The cumulative tower declares no constant. Every constant is rigid, so the
obligations of progress hold vacuously once the type formers are injective and
do not confuse. Progress for annotated types of the tower is the generic
theorem at that instance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace ProgressControls

open Normalization
open TowerInterpretation (towerFormerFacts towerLevels)

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- **The tower over a level order meets the obligations of progress**, because it declares no
constant. -/
theorem towerProgressFacts :
    Progress.ProgressFacts (TowerControls.P₀ (L := L)) TowerModel.roles :=
  Progress.ProgressFacts.ofRigid (roles := TowerModel.roles) towerFormerFacts (fun _ => rfl)

/-- **Progress for annotated types of the tower.** -/
theorem tower_typeProgress {n : Nat} {Γ : CCtx (LevelTower.Head L) n}
    {A : CTm (LevelTower.Head L) n} {u : LevelTower.Head L}
    (formed : CCtxFormed TowerControls.P₀ Γ)
    (hu : (LevelTower.rules L).isUniverse u) (typing : CTyped TowerControls.P₀ Γ A (.head u)) :
    (∃ A', CWhStepR TowerControls.P₀ TowerModel.roles A A') ∨
      IsTypeForm TowerModel.roles A.erase :=
  Progress.typeProgress towerProgressFacts towerLevels TowerModel.algebra formed hu typing

end ProgressControls
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
