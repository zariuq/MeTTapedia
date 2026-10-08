import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Controls

/-!
# Source occurrence receipts and generated activations

Two derivations of the same conclusion remain two matcher rows, while
compact-key support contains the conclusion once. A generated activation
then consumes the actual emitted source atom with its already captured
variables. These are properties of the existing source executor; native
programme replays are separate evidence for the corresponding fixtures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open ProgrammableSpaceMM2Controls ProgrammableSpaceMM2 MM2MatchingCursor

def additionRequest (name : String) (inputs outputs : List Atom) : Request where
  directive := {
    atom := instruction "0" name inputs (outputs.map fun value => form "+" [value])
    loc := form "0" [.symbol name]
    rule := ⟨0, name, .compat ⟨inputs⟩, [], ⟨outputs.map Sink.add⟩⟩ }
  pattern := ⟨inputs⟩
  factorization := rfl

def edge (first second : String) : Atom := form "edge" [.symbol first, .symbol second]

def context : List Atom :=
  [form "selected" [form "query" [.symbol "A", .symbol "C"]],
    edge "A" "B", edge "B" "C", edge "A" "D", edge "D" "C"]

def inputs : List Atom :=
  [form "selected" [form "query" [.var "from", .var "to"]],
    form "edge" [.var "from", .var "middle"], form "edge" [.var "middle", .var "to"]]

def conclusion : Atom := form "reachable" [.var "from", .var "to"]
def reachable : Atom := form "reachable" [.symbol "A", .symbol "C"]
def joinRequest : Request := additionRequest "inference" inputs [conclusion]
def joinSource : List Atom := context ++ [joinRequest.directive.atom]

theorem join_source_admitted : Admitted joinRequest.directive.atom joinRequest := by
  unfold Admitted
  decide +kernel

def joinRows : List Row :=
  StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot joinSource joinRequest))
    (ProgrammableSpaceMM2Matching.initial joinSource joinRequest)

theorem two_paths_retain_physical_positions :
    (Receipt.witnessesInSourceOrder ⟨joinRequest, joinSource, joinRows⟩).map
      (List.map Prod.snd) = [[0, 1, 2], [0, 3, 4]] := by
  decide +kernel

theorem two_paths_have_distinct_substitutions :
    (joinRows.map Prod.fst).length = 2 ∧
      (joinRows.map Prod.fst).Nodup := by decide +kernel

theorem two_paths_emit_same_conclusion :
    joinRows.map (fun row => applySubst row.1 conclusion) = [reachable, reachable] := by
  decide +kernel

theorem publication_preserves_support_not_derivation_multiplicity :
    ProgrammableSpaceMM2Matching.finalize joinSource joinRequest joinRows =
      context ++ [reachable] := by decide +kernel

theorem join_has_actual_event :
    ∃ receipt after,
      language.advance .leaveInert joinSource (.pending joinRequest)
        receipt (context ++ [reachable]) after := by
  have selected : MM2MatchingBatch.SelectedFor .leaveInert joinSource joinRequest.directive := by
    unfold MM2MatchingBatch.SelectedFor
    decide +kernel
  obtain ⟨receipt, after, step⟩ := selected_has_event .leaveInert joinSource joinRequest selected
  refine ⟨receipt, after, ?_⟩
  have exactStore : cFireRuleScopedSourceExecFact joinSource joinRequest.directive =
      context ++ [reachable] := by decide +kernel
  rw [exactStore] at step
  exact step

def second : Atom := form "exec" [.symbol "second",
  form "," [form "reachable" [.symbol "A", .var "to"], form "edge" [.var "to", .symbol "E"]],
  form "O" [form "+" [form "finished" [.var "to"]]]]

def first : Atom := form "exec" [.symbol "first", form "," inputs,
  form "O" [form "+" [conclusion], form "+" [second]]]

def generatedSource : List Atom := context ++ [edge "C" "E", first]

theorem generated_activation_uses_captured_result :
    run 3 generatedSource =
      (context ++ [edge "C" "E", reachable, form "finished" [.symbol "C"]], 2) := by
  decide +kernel

/-- The final conclusion cannot recover which of the two source paths was
used. The retained receipt can, so a path-sensitive consumer cannot descend
through the conclusion-only readout. -/
theorem no_recovering_path_from_conclusion :
    ¬ ∃ recover : Atom → List Nat,
      recover reachable = [0, 1, 2] ∧ recover reachable = [0, 3, 4] := by
  rintro ⟨recover, left, right⟩
  have impossible : ([0, 1, 2] : List Nat) = [0, 3, 4] := left.symm.trans right
  contradiction

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls
