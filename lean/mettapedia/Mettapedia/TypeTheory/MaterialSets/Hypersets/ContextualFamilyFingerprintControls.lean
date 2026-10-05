import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyFingerprint
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodeControls

/-!
# Future-table controls with equal carriers and distinct parallel actions

One authored path acts as identity, while a parallel path resets the member
to the empty material value. Their displayed families have identical carrier
sets at every context point. The complete observation distinguishes their
actual material transport graphs. The nonconstant growing family also keeps
its later cyclic alternative visible from the old world.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyFingerprintControls

open CategoryTheory ContextualGeneratedUniverse ContextualFamilyFingerprint
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open LabelledContextPaths

namespace Parallel

abbrev C := Worldᵒᵖ

def base : Cᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def context : LabelledContext C where
  base := base
  labels := {
    graph point := worlds.graph point.1.unop.unop
    injective := by
      intro first second same
      have bare : first.1.unop.unop = second.1.unop.unop := worlds.injective same
      have parents : first.1 = second.1 := congrArg (fun world => Opposite.op (Opposite.op world)) bare
      rcases first with ⟨X, a⟩
      rcases second with ⟨Y, b⟩
      dsimp only at parents
      subst Y
      cases a
      cases b
      rfl }

def arrowCoding (first second : Cᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph step := (arrows first.unop.unop second.unop.unop).graph step.unop.unop
  injective := by
    intro earlier later same
    have bare : earlier.unop.unop = later.unop.unop :=
      (arrows first.unop.unop second.unop.unop).injective same
    exact congrArg (fun step => step.op.op) bare

abbrev choiceGraph :=
  Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.nonWfChoices

abbrev Model := AccessiblePointedGraph.PowerMemberClass choiceGraph

def model : PresentedType Model := PowerClassContextualMaterialization.powerClassModel choiceGraph

def emptyTerm : Model := model.decode ⟨∅, by
  change ∅ ∈ HSet.range (fun tag : Bool => if tag then HSet.loop else AccessiblePointedGraph.empty)
  exact HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩⟩

def quineTerm : Model := model.decode ⟨HSet.quineAtom, by
  change HSet.quineAtom ∈ HSet.range (fun tag : Bool => if tag then HSet.loop else AccessiblePointedGraph.empty)
  exact HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩⟩

theorem emptyTerm_value : model.value emptyTerm = ∅ := model.value_decode _

theorem quineTerm_value : model.value quineTerm = HSet.quineAtom := model.value_decode _

def identityFamily : MaterialFamily context where
  family := {
    obj _ := Model
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  model _ := model

/-- The action is authored by the complete path, so composition has real
content even though every point has the same two-member carrier. -/
def pathAction (path : List Nat) (term : Model) : Model :=
  if 1 ∈ path then emptyTerm else term

theorem pathAction_nil (term : Model) : pathAction [] term = term := by
  simp [pathAction]

theorem pathAction_append (first second : List Nat) (term : Model) :
    pathAction (first ++ second) term = pathAction second (pathAction first term) := by
  by_cases earlier : 1 ∈ first <;> by_cases later : 1 ∈ second <;>
    simp [pathAction, List.mem_append, earlier, later]

def resetFamily : MaterialFamily context where
  family := {
    obj _ := Model
    map step := TypeCat.ofHom (pathAction step.1.unop.unop.1)
    map_id _ := by
      apply ConcreteCategory.hom_ext
      exact pathAction_nil
    map_comp first second := by
      apply ConcreteCategory.hom_ext
      intro term
      exact pathAction_append first.1.unop.unop.1 second.1.unop.unop.1 term }
  model _ := model

def old : context.base.Elements := ⟨Opposite.op (Opposite.op initial), PUnit.unit⟩

def later : context.base.Elements := ⟨Opposite.op (Opposite.op next), PUnit.unit⟩

def step (label : Nat) : old ⟶ later :=
  CategoryOfElements.homMk old later ((extension label).op.op) rfl

theorem parallel_arrows_distinct : step 0 ≠ step 1 := by
  intro same
  have paths : ([0] : List Nat) = [1] :=
    congrArg (fun arrow : old ⟶ later => arrow.1.unop.unop.1) same
  have labels : (0 : Nat) = 1 := List.cons.inj paths |>.1
  exact Nat.zero_ne_one labels

theorem all_carriers_equal (point : context.base.Elements) :
    (identityFamily.model point).carrier = (resetFamily.model point).carrier := rfl

theorem first_parallel_action_agrees (term : Model) :
    resetFamily.family.map (step 0) term = identityFamily.family.map (step 0) term := by
  change pathAction [0] term = term
  simp [pathAction]

theorem second_parallel_action_differs :
    (identityFamily.model later).value (identityFamily.family.map (step 1) quineTerm) ≠
      (resetFamily.model later).value (resetFamily.family.map (step 1) quineTerm) := by
  change model.value quineTerm ≠ model.value (pathAction [1] quineTerm)
  have reset : pathAction [1] quineTerm = emptyTerm := by simp [pathAction]
  rw [reset]
  rw [emptyTerm_value, quineTerm_value]
  exact HSet.empty_ne_quineAtom.symm

theorem complete_readings_distinct :
    reading arrowCoding identityFamily old ≠ reading arrowCoding resetFamily old := by
  intro same
  have compatible := (reading_eq_iff arrowCoding identityFamily resetFamily old).mp same
  have action := compatible.2 (⟨⟨old, ⟨𝟙 old⟩⟩, later, step 1⟩ : TransportIndex old)
    quineTerm quineTerm rfl
  exact second_parallel_action_differs action

theorem transport_keys_distinguish_parallel_arrows :
    (transportCoding arrowCoding old).reading ⟨⟨old, ⟨𝟙 old⟩⟩, later, step 0⟩ ≠
      (transportCoding arrowCoding old).reading ⟨⟨old, ⟨𝟙 old⟩⟩, later, step 1⟩ := by
  intro same
  have indices := (transportCoding arrowCoding old).injective same
  have second := (Sigma.mk.inj_iff.mp indices).2
  have arrows := (Sigma.mk.inj_iff.mp (eq_of_heq second)).2
  exact parallel_arrows_distinct (eq_of_heq arrows)

end Parallel

namespace Growing

open ContextualGeneratedUniverse.Growing

/-- This present-carrier collision occurs in the actual observed growing
model, not merely in the constant-carrier parallel-path control. -/
theorem equal_present_carriers :
    (input.model old).carrier = ((MaterialFamily.unit context).model old).carrier :=
  ContextualUniverseCodeControls.input_old_carrier.trans
    (ContextualUniverseCodeControls.unit_carrier old).symm

theorem future_fingerprints_distinct :
    reading arrowCoding input old ≠ reading arrowCoding (MaterialFamily.unit context) old := by
  intro same
  have carriers := (reading_eq_iff arrowCoding input (MaterialFamily.unit context) old).mp same |>.1
  exact ContextualUniverseCodeControls.input_later_ne_unit
    (carriers ⟨later, ⟨PowerClassContextualMaterialization.Growing.futureArrow⟩⟩)

theorem later_carrier_row_visible :
    HSet.kpair (context.labels.reading later) ((input.model later).carrier) ∈
      HSet.mk (carrierTableGraph input old) :=
  (tableGraph_entry (carrierCoding (context := context) old)
    (fun future => (input.model future.1).graph) _).mpr
    ⟨⟨later, ⟨PowerClassContextualMaterialization.Growing.futureArrow⟩⟩, rfl⟩

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyFingerprintControls
