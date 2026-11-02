import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareTraversal

/-! Ordered field lists use the same universal value traversal, preserving
duplicate positions and stopping at the first non-equal comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareFields

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

theorem returns (state : State) (left right : List OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareFields left right))) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact OCamlCompareStructure.fields_nil_returns state
    | cons head tail => exact OCamlCompareStructure.fields_empty_cons_returns state head tail
  | cons head tail ih =>
    cases right with
    | nil => exact OCamlCompareStructure.fields_cons_empty_returns state head tail
    | cons other rest =>
      rw [OCaml.compare_fields_cons]
      exact OCamlCompareStructure.fields_cons_returns state head other tail rest _ _
        (OCamlCompareTraversal.value_returns state head other) (ih rest)

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareFields
