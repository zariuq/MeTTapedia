import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareScalars
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStructure
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariantValues
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStringValues
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareShapes

/-! One mutual value/field traversal executes the independent source
comparison on the loaded target service. Recursive structures, source
refusals and the first encountered functional fault share this theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareTraversal

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution OCamlValueWireShapes

private theorem functional_left (state : State) (function : OCaml.FunctionRef) (captured : List OCaml.Value) (other : OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (valueTerm (.closure function captured)), encoded (valueTerm other)]) state
      (encoded (view (OCaml.compareValue (.closure function captured) other))) := by
  rw [OCaml.compare_closure_left]
  obtain ⟨fields, same⟩ := closure_exact function captured
  rw [same]
  exact OCamlCompareScalars.functional_left_returns state fields (valueTerm other)

private theorem functional_right (state : State) (function : OCaml.FunctionRef) (captured : List OCaml.Value) (other : OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (valueTerm other), encoded (valueTerm (.closure function captured))]) state
      (encoded (view (OCaml.compareValue other (.closure function captured)))) := by
  rw [OCaml.compare_closure_right]
  obtain ⟨fields, same⟩ := closure_exact function captured
  rw [same]
  cases other with
  | literal datum =>
    cases datum <;> simp only [integer_exact, OCamlIntegerWire.datum, boolean_exact, OCamlResultServices.booleanTerm,
      unit_exact, nil_exact, string_exact]
    all_goals first
    | exact OCamlCompareShapes.functional_right_returns state _ _ fields (by decide) (by simp [OCamlCompareShapes.scalarOrCompound])
    | split <;> exact OCamlCompareShapes.functional_right_returns state _ _ fields (by decide) (by simp [OCamlCompareShapes.scalarOrCompound])
  | tuple items => rw [value_tuple]; exact OCamlCompareShapes.functional_right_returns state _ _ fields (by decide) (by simp [OCamlCompareShapes.scalarOrCompound])
  | cons head tail => rw [value_cons]; exact OCamlCompareShapes.functional_right_returns state _ _ fields (by decide) (by simp [OCamlCompareShapes.scalarOrCompound])
  | variant typeId constructor items => rw [value_variant]; exact OCamlCompareShapes.functional_right_returns state _ _ fields (by decide) (by simp [OCamlCompareShapes.scalarOrCompound])
  | closure other items =>
    obtain ⟨actualFields, actualSame⟩ := closure_exact other items
    rw [actualSame]
    exact OCamlCompareScalars.functional_left_returns state actualFields _

macro "ml_compare_fallback" : tactic => `(tactic|
  (simp only [OCaml.compareValue, OCamlValueWireShapes.integer_exact, OCamlIntegerWire.datum,
    OCamlValueWireShapes.boolean_exact, OCamlResultServices.booleanTerm, OCamlValueWireShapes.unit_exact,
    OCamlValueWireShapes.nil_exact, OCamlValueWireShapes.string_exact, OCamlCompareWire.value_tuple,
    OCamlCompareWire.value_cons, OCamlCompareWire.value_variant, OCamlOrderExecution.view]
   first
   | exact OCamlCompareShapes.different_returns _ _ _ _ _ (by decide) (by decide)
       (by simp [OCamlCompareShapes.scalarOrCompound]) (by simp [OCamlCompareShapes.scalarOrCompound])
       (by decide) (by decide) (by decide) (by decide) (by decide)
   | (split <;> exact OCamlCompareShapes.different_returns _ _ _ _ _ (by decide) (by decide)
       (by simp [OCamlCompareShapes.scalarOrCompound]) (by simp [OCamlCompareShapes.scalarOrCompound])
       (by decide) (by decide) (by decide) (by decide) (by decide))))

theorem value_returns (state : State) (left right : OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm left), encoded (valueTerm right)]) state
      (encoded (view (OCaml.compareValue left right))) := by
  revert right
  refine OCaml.Value.rec
    (motive_1 := fun left => ∀ right, PureReturns runtime [] state
      (apply "gslt:ml:compare" [encoded (valueTerm left), encoded (valueTerm right)]) state (encoded (view (OCaml.compareValue left right))))
    (motive_2 := fun left => ∀ right, PureReturns runtime [] state
      (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state (encoded (view (OCaml.compareFields left right))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro datum right
    cases right with
    | literal other =>
      cases datum <;> cases other
      all_goals first
      | (rw [integer_exact, integer_exact]; exact OCamlCompareScalars.integer_returns state _ _)
      | (rw [boolean_exact, boolean_exact]; exact OCamlCompareScalars.boolean_returns state _ _)
      | exact OCamlCompareScalars.unit_returns state
      | exact OCamlCompareScalars.nil_returns state
      | exact OCamlCompareStringValues.returns state _ _
      | ml_compare_fallback
    | tuple fields => cases datum <;> ml_compare_fallback
    | cons head tail =>
      cases datum with
      | nil =>
        simp only [OCaml.compareValue, view, ordering]
        metta_call checked
        ml_compare_eval [] unfolding [nil_exact, value_cons, encodeList]
      | integer number => ml_compare_fallback
      | boolean flag => ml_compare_fallback
      | unit => ml_compare_fallback
      | string bytes => ml_compare_fallback
    | variant typeId constructor fields => cases datum <;> ml_compare_fallback
    | closure function captured => exact functional_right state function captured _
  · intro fields ih right
    cases right with
    | literal datum => cases datum <;> ml_compare_fallback
    | tuple other => exact OCamlCompareStructure.tuple_returns state fields other (ih other)
    | cons head tail => ml_compare_fallback
    | variant typeId constructor other => ml_compare_fallback
    | closure function captured => exact functional_right state function captured _
  · intro head tail first later right
    cases right with
    | literal datum =>
      cases datum with
      | nil =>
        simp only [OCaml.compareValue, view, ordering]
        metta_call checked
        ml_compare_eval [] unfolding [nil_exact, value_cons, encodeList]
      | integer number => ml_compare_fallback
      | boolean flag => ml_compare_fallback
      | unit => ml_compare_fallback
      | string bytes => ml_compare_fallback
    | tuple fields => ml_compare_fallback
    | cons other rest => rw [OCaml.compare_cons]; exact OCamlCompareStructure.cons_returns state head tail other rest _ _ (first other) (later rest)
    | variant typeId constructor fields => ml_compare_fallback
    | closure function captured => exact functional_right state function captured _
  · intro typeId constructor fields ih right
    cases right with
    | literal datum => cases datum <;> ml_compare_fallback
    | tuple other => ml_compare_fallback
    | cons head tail => ml_compare_fallback
    | variant otherType otherConstructor other => exact OCamlCompareVariantValues.returns state _ _ _ _ fields other (ih other)
    | closure function captured => exact functional_right state function captured _
  · intro function captured _ right
    exact functional_left state function captured right
  · intro right
    cases right with
    | nil => exact OCamlCompareStructure.fields_nil_returns state
    | cons head tail => exact OCamlCompareStructure.fields_empty_cons_returns state head tail
  · intro head tail first later right
    cases right with
    | nil => exact OCamlCompareStructure.fields_cons_empty_returns state head tail
    | cons other rest => rw [OCaml.compare_fields_cons]; exact OCamlCompareStructure.fields_cons_returns state head other tail rest _ _ (first other) (later rest)

#print axioms value_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareTraversal
