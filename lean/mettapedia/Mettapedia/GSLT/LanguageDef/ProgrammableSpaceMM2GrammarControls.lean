import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls

/-!
# Explicit BTM source, physical receipts and actual cursor resumption

Three ordered premises have two distinct physical derivations. Both the raw
cursor stack and the public source-order receipt are checked, and an actual
two-grant execution commits the original explicit-input directive. A
reflective self-read shows why changing its input spelling is not a neutral
rewrite of a programme.

Malformed BTM and non-MM2 factors fail this admitted-language boundary.
The runtime's separate suspended unsupported-syntax obligation is exercised
by the portable native fixtures; it is not a transition of this language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2GrammarControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor Mettapedia.Machines.Cursor
open ProgrammableSpaceMM2Controls ProgrammableSpaceMM2ReceiptControls
open ProgrammableSpaceMM2Grammar ProgrammableSpaceMM2Resumable

def explicitRequest : Request where
  directive := {
    atom := form "exec" [form "0" [.symbol "inference"],
      form "I" (inputs.map btmAtom), form "O" [form "+" [conclusion]]]
    loc := form "0" [.symbol "inference"]
    rule := ⟨0, "inference", .explicit (inputs.map SourceFactor.btm), [],
      ⟨[.add conclusion]⟩⟩ }
  pattern := ⟨inputs⟩
  factorization := rfl

def explicitSource : List Atom := context ++ [explicitRequest.directive.atom]

theorem explicit_source_admitted :
    language.admit explicitRequest.directive.atom explicitRequest := by
  change ProgrammableSpaceMM2.Admitted explicitRequest.directive.atom explicitRequest
  unfold ProgrammableSpaceMM2.Admitted
  decide +kernel

theorem explicit_input_is_retained :
    explicitRequest.directive.rule.input = .explicit (inputs.map SourceFactor.btm) ∧
      explicitRequest.directive.atom ≠ joinRequest.directive.atom := by
  decide +kernel

def explicitRows : List Row :=
  StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot explicitSource explicitRequest))
    (ProgrammableSpaceMM2Matching.initial explicitSource explicitRequest)

theorem raw_stack_positions :
    (explicitRows.map Prod.snd).map (List.map Prod.snd) = [[2, 1, 0], [4, 3, 0]] := by
  decide +kernel

theorem public_source_positions :
    (ProgrammableSpaceMM2.Receipt.witnessesInSourceOrder
      ⟨explicitRequest, explicitSource, explicitRows⟩).map (List.map Prod.snd) =
        [[0, 1, 2], [0, 3, 4]] := by
  decide +kernel

theorem full_source_rows :
    explicitRows.map (sourceRow explicitRequest.directive.rule.input) =
      cMatchInputSpecMork []
        (ProgrammableSpaceMM2Matching.snapshot explicitSource explicitRequest)
        explicitRequest.directive.rule.input :=
  btm_cursor_rows _ _ explicitRequest.pattern explicitRequest.factorization []

theorem erasure_without_reversal_is_wrong :
    explicitRows.map eraseRow ≠
      cMatchInputSpecMork []
        (ProgrammableSpaceMM2Matching.snapshot explicitSource explicitRequest)
        explicitRequest.directive.rule.input := by
  decide +kernel

theorem explicit_finalization :
    ProgrammableSpaceMM2Matching.finalize explicitSource explicitRequest explicitRows =
      context ++ [reachable] := by
  decide +kernel

def pausedPacket? (result :
    ProgrammableSpaceMM2Matching.Result explicitSource explicitRequest) :
    Option (PacketFor explicitSource explicitRequest) :=
  match result with
  | .paused packet => some packet
  | .done _ => none

def packet100 : PacketFor explicitSource explicitRequest :=
  (pausedPacket? (ProgrammableSpaceMM2Matching.run explicitSource explicitRequest 100).2).get
    (by decide +kernel)

def start : Checkpoint := Checkpoint.start explicitSource explicitRequest

def checkpoint100 : Checkpoint where
  before := explicitSource
  request := explicitRequest
  granted := 100
  spent := 100
  packet := packet100
  reached := rfl

theorem explicit_selected :
    MM2MatchingBatch.SelectedFor .leaveInert explicitSource explicitRequest.directive := by
  unfold MM2MatchingBatch.SelectedFor
  decide +kernel

theorem partial_answer_stays_private :
    checkpoint100.privateRows.length = 1 ∧ checkpoint100.remainingSyntax ≠ [] ∧
      ProgrammableSpaceMM2Matching.publish explicitSource explicitRequest
        (start.resume 100).2 = none := by
  decide +kernel

theorem actual_private_step :
    language.advance .leaveInert explicitSource (.matching start) ⟨100, 0, 100, none⟩
      explicitSource (.matching checkpoint100) :=
  Advance.pause start 100 100 packet100 explicit_selected (by rfl)

def finished : FinishedFor explicitSource explicitRequest := ⟨(), explicitRows, []⟩

theorem continued_cursor_finishes :
    checkpoint100.resume 100 = (177, .done finished) := by rfl

theorem actual_publication :
    language.advance .leaveInert explicitSource (.matching checkpoint100)
      ⟨100, 100, 177, some ⟨explicitRequest, explicitSource, explicitRows⟩⟩
      (context ++ [reachable]) (.committed ⟨explicitRequest, explicitSource, explicitRows⟩) := by
  have committed := Advance.commit (scope := .leaveInert) checkpoint100 100 177
    finished explicit_selected continued_cursor_finishes
  change Advance .leaveInert explicitSource (.matching checkpoint100)
    ⟨100, 100, 177, some ⟨explicitRequest, explicitSource, explicitRows⟩⟩
    (ProgrammableSpaceMM2Matching.finalize explicitSource explicitRequest explicitRows)
    (.committed ⟨explicitRequest, explicitSource, explicitRows⟩) at committed
  rwa [explicit_finalization] at committed

theorem actual_two_grant_run :
    Relation.ReflTransGen (Transition .leaveInert)
      (explicitSource, language.initial .leaveInert explicitRequest explicitSource)
      (context ++ [reachable], .committed ⟨explicitRequest, explicitSource, explicitRows⟩) := by
  have first : Transition .leaveInert (explicitSource, .matching start)
      (explicitSource, .matching checkpoint100) := ⟨_, actual_private_step⟩
  have second : Transition .leaveInert (explicitSource, .matching checkpoint100)
      (context ++ [reachable], .committed ⟨explicitRequest, explicitSource, explicitRows⟩) :=
    ⟨_, actual_publication⟩
  exact (Relation.ReflTransGen.single first).trans (Relation.ReflTransGen.single second)

theorem exact_atomic_source_comparison :
    Relation.ReflTransGen (AtomicTransition .leaveInert)
      (explicitSource, .pending explicitRequest)
      (context ++ [reachable], .committed ⟨explicitRequest, explicitSource, explicitRows⟩) :=
  run_refines_atomic_run actual_two_grant_run

def selfPattern : Atom := form "exec" [.var "location", .var "input", .var "output"]

def selfReader (explicit : Bool) : Atom :=
  form "exec" [.symbol "self",
    if explicit then form "I" [btmAtom selfPattern] else form "," [selfPattern],
    form "O" [form "+" [form "seen" [.var "input"]]]]

theorem explicit_self_read_keeps_authored_input :
    (run 1 [selfReader true]).1 = [form "seen" [form "I" [btmAtom selfPattern]]] := by
  decide +kernel

theorem normalization_changes_reflective_observation :
    (run 1 [selfReader true]).1 ≠ (run 1 [selfReader false]).1 := by
  decide +kernel

def malformedBTM : Atom :=
  form "exec" [.symbol "malformed",
    form "I" [form "BTM" [form "p" [.var "x"], form "q" [.var "x"]]],
    form "O" [form "+" [.symbol "Wrong"]]]

theorem malformed_btm_not_admitted :
    ¬ ∃ request, language.admit malformedBTM request := by
  change ¬ ∃ request : Request, ProgrammableSpaceMM2.Admitted malformedBTM request
  rw [ProgrammableSpaceMM2.admitted_iff_grammar]
  decide +kernel

theorem other_resource_factors_not_mm2 :
    inputGrammar (form "I" [form "read" [.symbol "Token"]]) = false ∧
    inputGrammar (form "I" [form "take" [.symbol "Token"]]) = false ∧
    inputGrammar (form "I" [form "absent" [.symbol "Stop"]]) = false ∧
    inputGrammar (form "I" [form "all" [form "p" [.var "x"], .var "rows"]]) = false ∧
    inputGrammar (form "I" [form "==" [.symbol "Token", .var "x"]]) = false ∧
    inputGrammar (form "I" [form "!=" [.symbol "Token", .var "x"]]) = false := by
  decide +kernel

theorem empty_explicit_input_admitted :
    ∃ request, language.admit
      (form "exec" [.symbol "empty", form "I" [], form "O" []]) request := by
  change ∃ request : Request, ProgrammableSpaceMM2.Admitted
    (form "exec" [.symbol "empty", form "I" [], form "O" []]) request
  rw [ProgrammableSpaceMM2.admitted_iff_grammar]
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2GrammarControls
