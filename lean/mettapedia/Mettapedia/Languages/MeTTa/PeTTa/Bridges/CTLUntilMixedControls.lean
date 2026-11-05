import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRowsControls

/-! Interleaved integer-labeled rows, retained open declarations, publication
stability, live output membership and unsupported-row refusal. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open CTLUntilSourceRows (number)
open CTLUntilMixedCapture (publication)
open EagerDFS.Destination

def rows : List (Row Int) := [
  .other "payload" [.var "unrelated"], .frontier 10 0 2, .satisfaction 20 1,
  .edge 1 2, .other "=" [.expression [.symbol "irrelevant", .var "x"], .var "x"],
  .frontier 10 0 2, .edge 1 2, .satisfaction 20 1, .frontier 10 1 9, .satisfaction 99 1]
def atoms := rows.map (render FlatQueryRowCodec.integers)
def selected := sourceCandidates FlatQueryRowCodec.integers 10 0 20 "next" "prior" rows rows rows

theorem raw_rows_decode_without_loss : decodeRows FlatQueryRowCodec.integers atoms = some rows :=
  decode_rows_complete _ _ (by simp [rows, Row.admitted])

theorem original_mixed_positions :
    selected.map (fun row => (row.frontierOccurrence, row.edgeOccurrence, row.predicateOccurrence)) =
      [(1, 3, 2), (1, 3, 7), (1, 6, 2), (1, 6, 7),
       (5, 3, 2), (5, 3, 7), (5, 6, 2), (5, 6, 7)] := by decide +kernel

theorem eight_original_occurrences :
    selected.map (fun row => applySubst row.bindings (.var "prior")) = List.replicate 8 (number 1) := by decide +kernel

def after := atoms ++ (publication (10 : Int) 0 1).map (render FlatQueryRowCodec.integers)
def current := frontierPattern FlatQueryRowCodec.integers 10 0 "next"
def operand := CTLUntilMixedCapture.preparedSatisfaction FlatQueryRowCodec.integers 20 1
def output := CTLUntilMixedCapture.preparedSatisfaction FlatQueryRowCodec.integers 10 1

theorem publication_keeps_inputs_but_changes_output_membership :
    FlatQueryRelationCompilation.sourceScan [] current 0 after =
      FlatQueryRelationCompilation.sourceScan [] current 0 atoms ∧
    FlatQueryRelationCompilation.sourceScan [] operand 0 after =
      FlatQueryRelationCompilation.sourceScan [] operand 0 atoms ∧
    FlatQueryRelationCompilation.sourceScan [] output 0 atoms = [] ∧
    FlatQueryRelationCompilation.sourceScan [] output 0 after = [(10, [])] := by decide +kernel

theorem decoder_rejects_open_candidate :
    decodeRows FlatQueryRowCodec.integers
      (atoms ++ [.expression [.symbol "fr", number 10, number 0, .var "stored"]]) = none := by decide +kernel

theorem malformed_known_head_is_not_an_unrelated_row :
    decode FlatQueryRowCodec.integers (.expression [.symbol "fr", .symbol "bad"]) = none := by decide +kernel

theorem negative_coordinate_does_not_wrap_to_zero :
    decode FlatQueryRowCodec.integers
      (.expression [.symbol "rt", .grounded (.int (-1)), number 0]) = none := by decide +kernel

theorem symbol_labels_are_the_same_profile :
    decodeRows FlatQueryRowCodec.symbols
      [.expression [.symbol "fr", .symbol "f", number 0, number 2],
       .expression [.symbol "sat", .symbol "a", number 1]] =
      some [.frontier "f" 0 2, .satisfaction "a" 1] := by decide +kernel

def openReference : Bool :=
  match ScopedQuerySource.Controls.execute ScopedQuerySource.Controls.program
      [.expression [.symbol "fr", number 10, number 0, .var "stored"]]
      (ScopedQuerySource.Controls.call "match" [.symbol "&self", current,
        ScopedQuerySource.Controls.call "quote" [.var "next"]]) with
  | some ([], .suspended (.branch (.invoke "match" _ _)) _) => true
  | _ => false
#guard openReference

#print axioms candidate_values
#print axioms decode_rows_sound
#print axioms CTLUntilMixedCapture.frontier_entry
#print axioms CTLUntilMixedCapture.edge_entry
#print axioms CTLUntilMixedCapture.satisfaction_entry
#print axioms CTLUntilMixedCapture.operand_capture_after_publication

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore.Controls
