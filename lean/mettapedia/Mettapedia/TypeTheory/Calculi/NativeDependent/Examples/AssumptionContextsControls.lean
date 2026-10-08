import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsBinderCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Concrete controls for ambient assumptions and full dependent motives

The arbitrary-theory bounded model is instantiated on a theory with two
parallel future arrows. Generated functions retain supplied assumption
witnesses; dependent pair elimination observes both coordinates. A
nonidentity proof-frame substitution drops an ambient assumption while
retaining the two separately bound pair components.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open AssumptionContexts AssumptionContexts.Interpretation

abbrev World := WalkingParallelPair
abbrev objects := AssumptionContextsModel.objects World
abbrev constants := AssumptionContextsModel.constants World
abbrev predicates := AssumptionContextsModel.predicates World
noncomputable abbrev declarations : ∀ {n : Nat} {formula : Formula Nat PUnit.{1} n},
    AssumptionContextsModel.Declaration n formula →
      (PresheafInterpretation.family objects constants predicates formula).sections :=
  @AssumptionContextsModel.declarations World _
abbrev Declaration := AssumptionContextsModel.Declaration
abbrev input := AssumptionContextsModel.input
abbrev emptyScope := AssumptionContextsModel.emptyScope
abbrev pairScope := AssumptionContextsModel.pairScope
abbrev sumScope := AssumptionContextsModel.sumScope
abbrev duplicateScope := AssumptionContextsModel.duplicateScope
abbrev newestProof := AssumptionContextsModel.newestProof
abbrev olderProof := AssumptionContextsModel.olderProof
abbrev answer := AssumptionContextsModel.answer
abbrev branch := AssumptionContextsModel.branch
abbrev eliminated := AssumptionContextsModel.eliminated
noncomputable abbrev motives : ∀ {n : Nat} {scope : Scope Nat PUnit.{1} n},
    AssumptionContextsModel.Motive scope → DisplayedFamily (context objects constants predicates scope) :=
  @AssumptionContextsModel.motives World _
noncomputable abbrev primitives : ∀ {n : Nat} {scope : Scope Nat PUnit.{1} n}
    {body : Family Declaration AssumptionContextsModel.Motive scope},
    AssumptionContextsModel.Primitive scope body →
      (family objects constants predicates declarations motives body).sections :=
  @AssumptionContextsModel.primitives World _
noncomputable abbrev fullMotive := AssumptionContextsModel.fullMotive World

def earlierWorld : Worldᵒᵖ := Opposite.op WalkingParallelPair.one
def laterWorld : Worldᵒᵖ := Opposite.op WalkingParallelPair.zero

def futureLeft : earlierWorld ⟶ laterWorld := Quiver.Hom.op WalkingParallelPairHom.left
def futureRight : earlierWorld ⟶ laterWorld := Quiver.Hom.op WalkingParallelPairHom.right

theorem future_arrows_differ : futureLeft ≠ futureRight := by
  intro same
  have unopSame := congrArg Quiver.Hom.unop same
  cases unopSame

noncomputable abbrev pairPoint (a : Nat) (witness : Fin (a + 1)) :=
  AssumptionContextsModel.pairPoint World earlierWorld a witness
noncomputable abbrev sumPoint (a : Nat) (witness : Fin (a + 1)) :=
  AssumptionContextsModel.sumPoint World earlierWorld a witness

noncomputable def futureElement (a : Nat) (witness : Fin (a + 1)) :
    sumPoint a witness ⟶ AssumptionContextsModel.sumPoint World laterWorld a witness :=
  ⟨futureLeft, rfl⟩

theorem motive_future_witness (a : Nat) (witness : Fin (a + 1))
    (value : fullMotive.obj (sumPoint a witness)) :
    ((fullMotive.map (futureElement a witness)) value).val = value.val := rfl

theorem distinct_assumption_positions : newestProof ≠ olderProof :=
  AssumptionContextsModel.distinct_assumption_positions

theorem duplicate_meanings_differ :
    hypothesis objects constants predicates newestProof ≠ hypothesis objects constants predicates olderProof :=
  AssumptionContextsModel.duplicate_meanings_differ World earlierWorld

theorem no_assumption_erasure :
    ¬ TermEquation AssumptionContextsModel.newestTerm AssumptionContextsModel.olderTerm :=
  AssumptionContextsModel.no_assumption_erasure World earlierWorld

theorem ambient_function_uses_latest_assumption :
    ((evidence objects constants predicates declarations
      (AssumptionContextsModel.ambientCall 17)).val
        (AssumptionContextsModel.duplicatePoint World earlierWorld 2 0 1)).val = 1 :=
  AssumptionContextsModel.ambient_function_computes World earlierWorld 2 17 0 1

theorem ambient_function_uses_supplied_witness :
    ((evidence objects constants predicates declarations
      (AssumptionContextsModel.ambientCall 17)).val
        (AssumptionContextsModel.duplicatePoint World earlierWorld 2 0 1)).val ≠
      ((evidence objects constants predicates declarations
        (AssumptionContextsModel.ambientCall 17)).val
          (AssumptionContextsModel.duplicatePoint World earlierWorld 2 0 2)).val := by
  rw [AssumptionContextsModel.ambient_function_computes,
    AssumptionContextsModel.ambient_function_computes]
  decide

theorem full_motive_type (a : Nat) (witness : Fin (a + 1)) :
    fullMotive.obj (sumPoint a witness) = Fin (a + witness.val + 1) :=
  AssumptionContextsModel.full_motive_type World earlierWorld a witness

instance fullMotiveFinite (a : Nat) (witness : Fin (a + 1)) :
    Fintype (fullMotive.obj (sumPoint a witness)) := by
  change Fintype (Fin (a + witness.val + 1))
  infer_instance

theorem full_motive_second_coordinate_changes_cardinality :
    Fintype.card (fullMotive.obj (sumPoint 2 0)) ≠
      Fintype.card (fullMotive.obj (sumPoint 2 1)) := by
  change Fintype.card (Fin 3) ≠ Fintype.card (Fin 4)
  decide

theorem eliminated_computes (a : Nat) (witness : Fin (a + 1)) :
    ((term objects constants predicates declarations motives primitives eliminated).val
      (sumPoint a witness)).val = a + witness.val :=
  AssumptionContextsModel.eliminated_computes World earlierWorld a witness

theorem changing_second_witness_changes_result :
    ((term objects constants predicates declarations motives primitives eliminated).val (sumPoint 2 0)).val ≠
      ((term objects constants predicates declarations motives primitives eliminated).val (sumPoint 2 1)).val := by
  rw [eliminated_computes, eliminated_computes]
  decide

theorem changing_first_object_changes_result :
    ((term objects constants predicates declarations motives primitives eliminated).val (sumPoint 1 0)).val ≠
      ((term objects constants predicates declarations motives primitives eliminated).val (sumPoint 2 0)).val := by
  rw [eliminated_computes, eliminated_computes]
  decide

theorem pair_eta :
    term objects constants predicates declarations motives primitives
      (.sigmaElim emptyScope input answer (.reindex eliminated (.pack emptyScope input))) =
        term objects constants predicates declarations motives primitives eliminated :=
  AssumptionContextsModel.pair_eta World

abbrev closedInput : Formula Nat PUnit.{1} 0 :=
  .substitute input (ObjectSubstitution.instantiate (.constant 2))
abbrev ambientScope : Scope Nat PUnit.{1} 0 := .proof emptyScope closedInput
abbrev droppedProof : FrameSubstitution Declaration ambientScope emptyScope :=
  .dropProof emptyScope closedInput

noncomputable def ambientPairPoint (ambientWitness : Fin 3) (a : Nat) (witness : Fin (a + 1)) :
    (context objects constants predicates (ambientScope.pair input)).Elements :=
  ⟨earlierWorld, ⟨⟨⟨PUnit.unit, ambientWitness⟩, a⟩, witness⟩⟩

noncomputable def ambientSumPoint (ambientWitness : Fin 3) (a : Nat) (witness : Fin (a + 1)) :
    (context objects constants predicates (ambientScope.sum input)).Elements :=
  ⟨earlierWorld, ⟨⟨PUnit.unit, ambientWitness⟩, ⟨a, witness⟩⟩⟩

theorem dropped_pair_frame_retains_values (ambientWitness : Fin 3) (a : Nat) (witness : Fin (a + 1)) :
    (frame objects constants predicates declarations (.proofLift (.objectLift droppedProof) input)).map.app
        earlierWorld (ambientPairPoint ambientWitness a witness).2 = (pairPoint a witness).2 := by
  rfl

theorem dropped_sum_frame_retains_values (ambientWitness : Fin 3) (a : Nat) (witness : Fin (a + 1)) :
    (frame objects constants predicates declarations (.proofLift droppedProof (.sigma input))).map.app
        earlierWorld (ambientSumPoint ambientWitness a witness).2 = (sumPoint a witness).2 := by
  rfl

theorem dropped_frame_is_noninjective :
    (frame objects constants predicates declarations droppedProof).map.app earlierWorld
        (⟨PUnit.unit, (0 : Fin 3)⟩) =
      (frame objects constants predicates declarations droppedProof).map.app earlierWorld
        (⟨PUnit.unit, (1 : Fin 3)⟩) ∧
      (⟨PUnit.unit, (0 : Fin 3)⟩ :
        (context objects constants predicates ambientScope).obj earlierWorld) ≠ ⟨PUnit.unit, (1 : Fin 3)⟩ := by
  constructor
  · rfl
  · intro same
    have values := congrArg (fun point => point.2.val) same
    exact Nat.zero_ne_one values

set_option backward.isDefEq.respectTransparency false in
theorem dropped_frame_retains_pair_binders :
    (pairIso objects constants predicates ambientScope input).inv ≫
        (frame objects constants predicates declarations (.proofLift droppedProof (.sigma input))).map =
      (frame objects constants predicates declarations (.proofLift (.objectLift droppedProof) input)).map ≫
        (pairIso objects constants predicates emptyScope input).inv :=
  pack_frame_square objects constants predicates declarations droppedProof input

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsControls
