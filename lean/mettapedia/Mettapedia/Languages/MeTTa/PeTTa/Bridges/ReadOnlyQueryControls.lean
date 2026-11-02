import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction

/-! Actual source controls for read-dependent nested query preparation.
The source profile is `Eval`; no two-way-unification or native-C claim is made. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics ReadOnlyQuerySource

def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def integer (value : Int) : Atom := .grounded (.int value)

def query (space : Atom) : Atom :=
  app "match" [space, app "r" [.var "x", .var "y"],
    app "match" [space, app "s" [.var "y", .var "z"], app "triple" [.var "x", .var "y", .var "z"]]]

def program : Program := { equations := [
  ⟨"paths", [.var "space"], query (.var "space")⟩,
  ⟨"wrapper", [.var "table"], app "paths" [.var "table"]⟩], declarations := [] }

def rows : List Atom := [app "r" [integer 0, integer 1], app "r" [integer 0, integer 1],
  app "s" [integer 1, integer 2], app "s" [integer 1, integer 0]]

def state : Effects.State := NamedSpaces.Store.new rows []
def direct : Atom := query (.symbol "&self")
def wrapped : Atom := app "wrapper" [.symbol "&self"]
def collected : Atom := app "collapse" [wrapped]
def counted : Atom := app "size-atom" [collected]

def answers : List Atom := [app "triple" [integer 0, integer 1, integer 2],
  app "triple" [integer 0, integer 1, integer 0], app "triple" [integer 0, integer 1, integer 2],
  app "triple" [integer 0, integer 1, integer 0]]

theorem direct_and_wrapped_keep_every_ordered_answer :
    (prepare 12 program [] state direct).map (·.values) = some answers ∧
      (prepare 12 program [] state wrapped).map (·.values) = some answers := by decide +kernel

theorem collapse_and_count_observe_four_not_two :
    (prepare 12 program [] state collected).map (·.values) = some [.expression answers] ∧
      (prepare 12 program [] state counted).map (·.values) = some [integer 4] := by decide +kernel

def prepared : Certified program [] counted :=
  (prepare 12 program [] state counted).get (by decide +kernel)

theorem every_recorded_read_is_current : Valid prepared.reads state := by decide +kernel

theorem repeated_snapshot_requirements_can_be_shared :
    prepared.reads.length = 3 ∧ prepared.normalize.reads.length = 1 ∧
      prepared.normalize.values = prepared.values := by decide +kernel

theorem different_snapshots_of_one_handle_are_not_duplicates :
    ([((.symbol "&self" : Atom), rows), (.symbol "&self", [])] : List Reading).dedup.length = 2 ∧
      ¬Valid [(.symbol "&self", rows), (.symbol "&self", [])] state ∧
      Valid [(.symbol "&self", rows)] state := by decide +kernel

theorem actual_evaluator_count : Returns program [] state counted state [integer 4] := by
  have returned := prepared.returns state every_recorded_read_is_current
  have value : prepared.values = [integer 4] := by decide +kernel
  simpa only [value] using returned

def changed : Effects.State := NamedSpaces.Store.new
  [app "r" [integer 0, integer 1], app "s" [integer 1, integer 2]] []

theorem changed_read_declines : prepared.region.attempt changed = .declined changed := by
  apply stale_read_declines
  decide +kernel

theorem changed_source_really_counts_differently :
    (prepare 12 program [] changed counted).map (·.values) = some [integer 1] := by decide +kernel

def unrelated : Effects.State := state.putCell "outside" (integer 99)

theorem unrelated_state_is_preserved_not_replaced :
    prepared.region.attempt unrelated = .committed ⟨unrelated, [integer 4], [], []⟩ := by
  have valid : Valid prepared.reads unrelated := by decide +kernel
  have value : prepared.values = [integer 4] := by decide +kernel
  simp [Certified.region, valid, value]

theorem missing_space_is_not_certified_empty :
    (prepare 12 program [] state (query (.symbol "not-a-space"))).isNone = true := by decide +kernel

theorem empty_space_is_successfully_empty :
    (prepare 12 program [] (NamedSpaces.Store.new [] []) counted).map (·.values) = some [integer 0] := by decide +kernel

def repeated : Atom := app "match" [.symbol "&self", app "r" [.var "x", .var "x"], .var "x"]

theorem repeated_variable_does_not_become_two_holes :
    (prepare 8 program [] state repeated).map (·.values) = some [] := by decide +kernel

def effectful : Atom := app "match" [.symbol "&self", app "r" [.var "x", .var "y"],
  app "println!" [.var "x"]]

theorem effects_refuse_without_a_prepared_publication :
    (prepare 12 program [] state effectful).isNone = true := by decide +kernel

theorem exact_source_pages_do_not_use_the_cache :
    classify .exactPage 12 program [] state counted = none := rfl

theorem cutoff_keeps_reference_execution :
    execute .completedResult 0 7 program [] state counted =
      Eval.run program 7 {state, control := .evaluate [] counted} := by
  apply unsupported_uses_reference
  rfl

def extraEmpty : Program := { program with equations := program.equations ++
  [⟨"wrapper", [.var "table"], app "empty" []⟩] }

def extraAnswer : Program := { program with equations := program.equations ++
  [⟨"wrapper", [.var "table"], integer 99⟩] }

theorem inert_extra_equation_is_checked_as_empty :
    (prepare 12 extraEmpty [] state counted).map (·.values) = some [integer 4] := by decide +kernel

theorem productive_extra_equation_is_not_ignored :
    (prepare 12 extraAnswer [] state counted).map (·.values) = some [integer 5] := by decide +kernel

def letWrapped : Atom := app "let" [.var "saved", app "quote" [.symbol "&self"], query (.var "saved")]

theorem let_wrapper_preserves_the_captured_handle :
    (prepare 12 program [] state letWrapped).map (·.values) = some answers := by decide +kernel

def booleanConsumer : Atom := app "tag" [app "<" [counted, integer 5]]

theorem comparison_of_nested_count_keeps_boolean_sort :
    (prepare 16 program [] state booleanConsumer).map (·.values) =
      some [app "tag" [Effects.boolean true]] := by decide +kernel

theorem unsupported_order_type_declines :
    (prepare 16 program [] state (app "<" [counted, .symbol "abc"])).isNone = true := by decide +kernel

theorem conditional_read_and_empty_branch :
    (prepare 16 program [] state
      (app "if" [app "<" [counted, integer 3], integer 99, app "empty" []])).map (·.values) =
      some [] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction.Controls
