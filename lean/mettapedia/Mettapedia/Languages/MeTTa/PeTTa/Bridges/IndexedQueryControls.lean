import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction

/-! Source, observer and declaration controls for indexed-query extraction. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval SpaceSemantics ReadOnlyQuerySource FlatQueryRowCodec CapturedQuerySource

def app (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def integer (value : Int) : Atom := .grounded (.int value)

def patterns : List Atom := FlatQueryConjunctionCompilation.Controls.patterns
def rows : List Atom := FlatQueryConjunctionCompilation.Controls.rows
def state : Effects.State := NamedSpaces.Store.new rows []

def program : Program := { equations := [
  ⟨"count-paths", [.var "space"], countTerm (.var "space") patterns⟩,
  ⟨"wrapper", [.var "table"], app "count-paths" [.var "table"]⟩], declarations := [] }

def source : Atom := app "wrapper" [.symbol "&self"]

def compiled : Certified program [] source :=
  (prepare integers 0 12 12 program [] state source).get (by decide +kernel)

def reference : Certified program [] source :=
  (ReadOnlyQueryExtraction.prepare 12 program [] state source).get (by decide +kernel)

theorem wrapper_uses_the_query_leaf :
    (SourceRegionExtraction.prepare (fun _ _ _ _ => none) 12 program [] state source).isNone = true := by decide +kernel

theorem wrapper_preserves_count : compiled.values = [integer 4] := by
  have agrees := SourceRegionExtraction.certificates_agree compiled reference state (by decide +kernel) (by decide +kernel)
  have expected : reference.values = [integer 4] := by decide +kernel
  exact agrees.trans expected

theorem wrapper_reaches_actual_source_result : Returns program [] state source state [integer 4] := by
  simpa only [wrapper_preserves_count] using compiled.returns state (by decide +kernel)

def withEmpty : Program := { program with equations := program.equations ++
  [⟨"count-paths", [.var "unused"], app "empty" []⟩] }

def withExtra : Program := { program with equations := program.equations ++
  [⟨"count-paths", [.var "unused"], integer 99⟩] }

def withUnmatchable : Program := { program with equations := program.equations ++
  [⟨"count-paths", [integer 42], integer 99⟩] }

def emptyCompiled : Certified withEmpty [] source :=
  (prepare integers 0 12 12 withEmpty [] state source).get (by decide +kernel)
def extraCompiled : Certified withExtra [] source :=
  (prepare integers 0 12 12 withExtra [] state source).get (by decide +kernel)
def unmatchableCompiled : Certified withUnmatchable [] source :=
  (prepare integers 0 12 12 withUnmatchable [] state source).get (by decide +kernel)

def emptyReference : Certified withEmpty [] source :=
  (ReadOnlyQueryExtraction.prepare 12 withEmpty [] state source).get (by decide +kernel)
def extraReference : Certified withExtra [] source :=
  (ReadOnlyQueryExtraction.prepare 12 withExtra [] state source).get (by decide +kernel)
def unmatchableReference : Certified withUnmatchable [] source :=
  (ReadOnlyQueryExtraction.prepare 12 withUnmatchable [] state source).get (by decide +kernel)

theorem empty_equation_contributes_no_answer : emptyCompiled.values = [integer 4] := by
  exact (SourceRegionExtraction.certificates_agree emptyCompiled emptyReference state (by decide +kernel) (by decide +kernel)).trans
    (by decide +kernel)

theorem productive_equation_is_not_discarded : extraCompiled.values = [integer 4, integer 99] := by
  exact (SourceRegionExtraction.certificates_agree extraCompiled extraReference state (by decide +kernel) (by decide +kernel)).trans
    (by decide +kernel)

theorem unmatchable_equation_is_operationally_inert : unmatchableCompiled.values = [integer 4] := by
  exact (SourceRegionExtraction.certificates_agree unmatchableCompiled unmatchableReference state
    (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

def effectfulProgram : Program := { program with equations := program.equations ++
  [⟨"count-paths", [.var "unused"], app "println!" [integer 99]⟩] }

theorem extra_effect_refuses_the_whole_wrapper :
    (prepare integers 0 12 12 effectfulProgram [] state source).isNone = true := by decide +kernel

theorem missing_space_refuses_instead_of_counting_zero :
    (prepare integers 0 12 12 program [] state (app "wrapper" [.symbol "not-a-space"])).isNone = true := by decide +kernel

theorem quoted_unbound_handle_is_not_stable :
    prepareOperand [] (app "quote" [.var "space"]) = none := by decide +kernel

theorem quoted_captured_handle_is_substituted :
    (prepareOperand [("space", .symbol "&self")] (app "quote" [.var "space"])).map (·.value) =
      some (.symbol "&self") := by decide +kernel

def rawProgram : Program := { program with declarations :=
  [app ":" [.symbol "wrapper", app "->" [.symbol "Atom", .symbol "Atom"]]] }

theorem changed_argument_demand_refuses :
    (prepare integers 0 12 12 rawProgram [] state source).isNone = true := by decide +kernel

def changed : Effects.State := NamedSpaces.Store.new
  [app "r" [integer 0, integer 1], app "s" [integer 1, integer 2]] []

theorem stale_snapshot_keeps_reference_entrance :
    ReadOnlyRegionExecution.execute .completedResult 7 program [] changed source (some compiled) =
      Eval.run program 7 {state := changed, control := .evaluate [] source} := by
  apply ReadOnlyRegionExecution.stale_uses_reference
  decide +kernel

theorem unsupported_effect_keeps_reference_execution :
    SourceRegionExtraction.execute (leaf integers 0 12) .completedResult 12 7 effectfulProgram [] state source =
      Eval.run effectfulProgram 7 {state, control := .evaluate [] source} := by
  apply SourceRegionExtraction.unsupported_uses_reference
  decide +kernel

def booleanSource : Atom := app "tag" [app "<" [source, integer 5]]
def booleanCompiled : Certified program [] booleanSource :=
  (prepare integers 0 12 16 program [] state booleanSource).get (by decide +kernel)
def booleanReference : Certified program [] booleanSource :=
  (ReadOnlyQueryExtraction.prepare 16 program [] state booleanSource).get (by decide +kernel)

theorem surrounding_comparison_keeps_boolean_not_integer :
    booleanCompiled.values = [app "tag" [Effects.boolean true]] := by
  exact (SourceRegionExtraction.certificates_agree booleanCompiled booleanReference state
    (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedQueryExtraction.Controls
