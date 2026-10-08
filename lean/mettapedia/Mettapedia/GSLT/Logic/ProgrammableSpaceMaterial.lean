import Mettapedia.GSLT.Core.ProgrammableSpaceReachability
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialInterpretation
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# Material behaviour of programmable spaces

The reachable shared-space executions form an originally small contextual
coalgebra. A context bounds the number of retained session births and events;
every source action is available at the next context, without truncating its
full future dynamics. At a fixed context, the bound can still be observable:
the exact kernel below retains world and context-arrow labels, and is not an
equivalence theorem for an unstaged transition system. Context extension
retains the entire store, scopes, residuals,
policy states and receipts. The larger constructed material recipient and the
observed quotient therefore apply to these executions themselves.

Declaring a reading is independent of running a language. The structured
interpretation identifies exactly contextual bisimilarity preserving those
readings. Its bare material coordinate may forget readings, under the precise
criterion proved below. No global finality or extra set axiom is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceMaterial

open CategoryTheory
open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualCoalgebraLabelledGraph

variable {Atom Tag : Type} (languages : Tag → Language Atom)
  (policies : (tag : Tag) → Policy (languages tag))

/-- These fibres contain real spaces, including all retained evidence. -/
def states : Stagesᵒᵖ ⥤ Type where
  obj point := {space : Space languages policies //
    Started languages policies space ∧ space.extent languages policies ≤ stageIndex point}
  map step := TypeCat.ofHom fun space =>
    ⟨space.val, space.property.1, space.property.2.trans (growthLe step)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem restriction_keeps_space {first second : Stagesᵒᵖ}
    (step : first ⟶ second) (space : (states languages policies).obj first) :
    ((states languages policies).map step space).val = space.val := rfl

theorem states_are_admitted (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point) : WellStarted languages policies space.val :=
  started_well_started languages policies space.val space.property.1

theorem state_receipts_are_valid (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point) : SoundHistory languages policies space.val :=
  started_sound_history languages policies space.val space.property.1

def dynamics : NaturalHom (states languages policies)
    (CoveredFuturePowerFamilies.family (states languages policies)) where
  app _ space := CoveredFuturePowerFamilies.ofFull {
    holds future := Action languages policies space.val future.2.val
    closed := by
      intro first second move action
      have same := congrArg Subtype.val move.2
      change first.2.val = second.2.val at same
      exact same ▸ action }
  naturality _ _ := rfl

theorem dynamics_exact (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point)
    (next : (states languages policies).obj future.1) :
    ((dynamics languages policies).app point space).val.holds ⟨future, next⟩ ↔
      Action languages policies space.val next.val := Iff.rfl

def extend (point : Stagesᵒᵖ) : point ⟶ world (stageIndex point + 1) :=
  (homOfLE (Nat.le_succ (stageIndex point))).op.op

/-- The context bound never removes a real action: the next stage contains
its actual resulting space. -/
def nextState (point : Stagesᵒᵖ) (space : (states languages policies).obj point)
    (after : Space languages policies) (action : Action languages policies space.val after) :
    (states languages policies).obj (world (stageIndex point + 1)) :=
  ⟨after, action_started languages policies action space.property.1, by
    change after.extent languages policies ≤ stageIndex point + 1
    rw [action_extent languages policies action]
    exact Nat.add_le_add_right space.property.2 1⟩

theorem every_action_is_a_child (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point) (after : Space languages policies)
    (action : Action languages policies space.val after) :
    ((dynamics languages policies).app point space).val.holds
      ⟨⟨world (stageIndex point + 1), extend point⟩,
        nextState languages policies point space after action⟩ := action

/-- Erasing the target-stage label recovers exactly the original action
relation. This does not erase the label from a consumer that observes it. -/
theorem future_child_iff_action (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point) (after : Space languages policies) :
    (∃ (future : PowerClassPresheafBaseChange.Future.Objects point)
      (next : (states languages policies).obj future.1),
      next.val = after ∧
        ((dynamics languages policies).app point space).val.holds ⟨future, next⟩) ↔
      Action languages policies space.val after := by
  constructor
  · rintro ⟨future, next, same, action⟩
    exact same ▸ action
  · intro action
    exact ⟨⟨world (stageIndex point + 1), extend point⟩,
      nextState languages policies point space after action, rfl, action⟩

theorem action_leaves_exact_stage (point : Stagesᵒᵖ)
    (space : (states languages policies).obj point)
    (atBound : space.val.extent languages policies = stageIndex point)
    (after : Space languages policies) (action : Action languages policies space.val after) :
    ¬ ∃ earlier : (states languages policies).obj point, earlier.val = after := by
  rintro ⟨earlier, same⟩
  have bound := earlier.property.2
  change earlier.val.extent languages policies ≤ stageIndex point at bound
  rw [same, action_extent languages policies action, atBound] at bound
  exact Nat.not_succ_le_self _ bound

abbrev worlds := ContextualObservedCoalgebraControls.worlds
abbrev arrows := ContextualObservedCoalgebraControls.arrows

variable {Reading : Type} (read : Reading → Space languages policies → Prop)

def observes (reading : Reading) (state : State (states languages policies)) : Prop :=
  read reading state.2.val

variable (coding : ArgumentCoding Reading)

abbrev interpretation := ConstructiveObservedMaterialInterpretation.interpretation
  worlds arrows (dynamics languages policies) (observes languages policies read) coding

/-- The labelled material value records declared readings and context/action
labels. The structured interpretation additionally places its class in the
constructed common recipient. -/
def observedValue (point : Stagesᵒᵖ) (space : (states languages policies).obj point) : HSet :=
  ContextualObservedCoalgebra.value (dynamics languages policies)
    (observes languages policies read) worlds arrows coding ⟨point, space⟩

theorem interpretation_exact (point : Stagesᵒᵖ)
    (first second : (states languages policies).obj point) :
    (interpretation languages policies read coding).app point first =
        (interpretation languages policies read coding).app point second ↔
      ContextualObservedCoalgebra.ObservedBisimilar (dynamics languages policies)
        (observes languages policies read) point first second :=
  ConstructiveObservedMaterialInterpretation.interpretation_kernel worlds arrows
    (dynamics languages policies) (observes languages policies read) coding point first second

theorem structured_material_comparison (point : Stagesᵒᵖ)
    (first second : (states languages policies).obj point) :
    (interpretation languages policies read coding).app point first =
        (interpretation languages policies read coding).app point second ↔
      observedValue languages policies read coding point first =
        observedValue languages policies read coding point second :=
  (interpretation_exact languages policies read coding point first second).trans
    (ContextualObservedCoalgebra.value_eq_iff (dynamics languages policies)
      (observes languages policies read) worlds arrows coding point first second).symm

/-- Preservation and reflection of the declared finitary modal language.
This is interpretation of each formula, not an unrestricted converse
Hennessy--Milner theorem from agreement on every finite formula. -/
theorem modal_interpretation
    (formula : HennessyMilner.Formula Reading (ContextualCoalgebraLabelledGraph.Label Stagesᵒᵖ))
    (point : Stagesᵒᵖ) (space : (states languages policies).obj point) :
    (ContextualObservedCoalgebra.readings (dynamics languages policies)
      (observes languages policies read) worlds arrows coding).materialSat formula
        (observedValue languages policies read coding point space) ↔
      (ContextualObservedCoalgebra.system (dynamics languages policies)
        (observes languages policies read)).sat formula ⟨point, space⟩ :=
  ContextualObservedCoalgebra.material_formula_iff (dynamics languages policies)
    (observes languages policies read) worlds arrows coding formula ⟨point, space⟩

theorem equality_preserves_readings (point : Stagesᵒᵖ)
    (first second : (states languages policies).obj point)
    (same : (interpretation languages policies read coding).app point first =
      (interpretation languages policies read coding).app point second) (reading : Reading) :
    read reading first.val ↔ read reading second.val :=
  ContextualObservedCoalgebra.observed_bisimilar_atoms (dynamics languages policies)
    (observes languages policies read)
    ((interpretation_exact languages policies read coding point first second).mp same) reading

theorem restriction_square {first second : Stagesᵒᵖ} (step : first ⟶ second)
    (space : (states languages policies).obj first) :
    (ConstructiveObservedMaterialInterpretation.structured worlds arrows
      (dynamics languages policies) (observes languages policies read) coding).map step
        ((interpretation languages policies read coding).app first space) =
      (interpretation languages policies read coding).app second
        ((states languages policies).map step space) :=
  (interpretation languages policies read coding).naturality step space

theorem forgetting_readings_exact_iff :
    (∀ point (first second : (states languages policies).obj point),
      (ConstructiveObservedMaterialInterpretation.readout worlds arrows
          (dynamics languages policies)).app point first =
        (ConstructiveObservedMaterialInterpretation.readout worlds arrows
          (dynamics languages policies)).app point second ↔
      ContextualObservedCoalgebra.ObservedBisimilar (dynamics languages policies)
        (observes languages policies read) point first second) ↔
      ConstructiveObservedMaterialInterpretation.PreservesDeclaredAtoms
        (dynamics languages policies) (observes languages policies read) :=
  ConstructiveObservedMaterialInterpretation.bare_readout_exact_iff worlds arrows
    (dynamics languages policies) (observes languages policies read)

end Mettapedia.GSLT.ProgrammableSpaceMaterial
