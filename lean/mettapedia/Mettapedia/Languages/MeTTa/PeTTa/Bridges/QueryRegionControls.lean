import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtractionControls

/-! Source-level controls for optional bodies, captured match readers and
their collection/count observers. Duplicate rows remain occurrences.+-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics MeTTaIL.WireKit

def program : Program := { equations := [
  ⟨"keep", [.var "v"], apply "if" [apply "<" [.var "v", integer 3], .var "v", apply "empty" []]⟩,
  ⟨"guard-wrapper", [.var "w"], apply "keep" [.var "w"]⟩], declarations := [] }

def rows : List Atom := [apply "edge" [integer 1], apply "edge" [integer 1],
  apply "edge" [integer 3], apply "other" [integer 2], apply "edge" [integer 2]]
def state : Effects.State := NamedSpaces.Store.new rows []
def caller : Subst := [("s", .symbol "&self")]
def pattern : Atom := apply "edge" [.var "x"]
def body : Atom := apply "guard-wrapper" [.var "x"]

theorem preserves_duplicate_answers_and_source_order :
    (prepare 7 program caller "s" pattern body state).map (fun p => p.compiled.values) =
      some [integer 1, integer 1, integer 2] := by decide +kernel

def prepared : Prepared program caller "s" pattern body :=
  (prepare 7 program caller "s" pattern body state).get (by decide +kernel)

theorem captured_complete_rows : prepared.rows = rows := by decide +kernel

theorem count_is_three_not_two : prepared.value .count = integer 3 := by decide +kernel

theorem actual_collection_source :
    PureReturns program caller state (collectionSource "s" pattern body) state
      (.expression [integer 1, integer 1, integer 2]) := by
  have returned := prepared.collection_returns state (by rw [captured_complete_rows]; rfl)
  have values : prepared.compiled.values = [integer 1, integer 1, integer 2] := by decide +kernel
  simpa [values] using returned

theorem actual_count_source :
    PureReturns program caller state (countSource "s" pattern body) state (integer 3) := by
  have returned := prepared.returns .count state (by rw [captured_complete_rows]; rfl)
  simpa only [source, count_is_three_not_two] using returned

def changed : Effects.State := NamedSpaces.Store.new [apply "edge" [integer 2]] []

theorem mutation_cannot_reuse_old_reader :
    (prepared.region .count).attempt changed = .declined changed := by
  apply snapshot_change_declines
  rw [captured_complete_rows]
  decide +kernel

def unrelated : Effects.State := state.putCell "outside" (integer 99)

theorem unrelated_cells_preserve_admission :
    (prepared.region .count).attempt unrelated =
      .committed (PureCallPortfolio.complete unrelated (integer 3)) := by
  have same : read unrelated caller "s" = some prepared.rows := by
    rw [captured_complete_rows]
    rfl
  simp [Prepared.region, same, count_is_three_not_two]

def invalidCaller : Subst := [("s", .symbol "not-a-space")]

theorem missing_space_is_not_empty_space :
    (prepare 7 program invalidCaller "s" pattern body state).isNone = true := by decide +kernel

def emptyState : Effects.State := NamedSpaces.Store.new [] []

theorem genuinely_empty_domain_is_certified :
    (prepare 7 program caller "s" pattern body emptyState).map (fun p => p.value .count) =
      some (integer 0) := by decide +kernel

def badRows : Effects.State := NamedSpaces.Store.new [apply "edge" [.symbol "abc"]] []

theorem invalid_order_type_refuses_before_publication :
    (prepare 7 program caller "s" pattern body badRows).isNone = true := by decide +kernel

def repeated : Atom := apply "pair" [.var "x", .var "x"]
def pairs : Effects.State := NamedSpaces.Store.new
  [apply "pair" [integer 1, integer 2], apply "pair" [integer 1, integer 1]] []

theorem one_frame_for_repeated_variables :
    (prepare 7 program caller "s" repeated (.var "x") pairs).map (fun p => p.compiled.values) =
      some [integer 1] := by decide +kernel

theorem empty_equation_is_proved_inert :
    (OptionalCallExtraction.prepare 8 PureCallExtraction.Controls.extraEmpty []
      PureCallExtraction.Controls.callSource).map (fun p => p.value) =
      some (some (integer 6)) := by decide +kernel

theorem two_answer_equations_still_refuse :
    (OptionalCallExtraction.prepare 8 PureCallExtraction.Controls.duplicate []
      PureCallExtraction.Controls.callSource).isNone = true := by decide +kernel

theorem selected_false_guard_is_successful_empty :
    (OptionalCallExtraction.prepare 4 program [] (apply "keep" [integer 3])).map (fun p => p.value) =
      some none := by decide +kernel

theorem cutoff_is_not_successful_empty :
    (OptionalCallExtraction.prepare 0 program [] (apply "keep" [integer 3])).map (fun p => p.value) =
      none := rfl

theorem source_shape_classifies_count :
    (classify .completedResult 7 program caller state (countSource "s" pattern body)).isSome = true := by
  decide +kernel

theorem exact_page_source_shape_declines :
    (classify .exactPage 7 program caller state (countSource "s" pattern body)).isNone = true := rfl

def booleanRows : Effects.State := NamedSpaces.Store.new
  [apply "edge" [Effects.boolean true], apply "edge" [Effects.boolean false],
   apply "edge" [Effects.boolean true]] []

theorem boolean_keys_remain_distinct_and_repeated :
    (prepare 3 program caller "s" pattern (.var "x") booleanRows).map (fun p => p.compiled.values) =
      some [Effects.boolean true, Effects.boolean false, Effects.boolean true] := by decide +kernel

theorem effectful_query_body_refuses :
    (prepare 4 program caller "s" pattern (apply "println!" [.var "x"]) state).isNone = true := by
  decide +kernel

theorem a_stale_count_would_change_the_source :
    (prepare 7 program caller "s" pattern body changed).map (fun p => p.value .count) =
      some (integer 1) ∧ prepared.value .count = integer 3 := by
  constructor
  · decide +kernel
  · exact count_is_three_not_two

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction.Controls
