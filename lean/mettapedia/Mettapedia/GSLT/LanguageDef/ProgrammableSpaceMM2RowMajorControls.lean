import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorResumable
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2GrammarControls

/-!
# Mixed-effect agreement and an actual separating MM2 execution

Two matched edges induce an add and a remove per row. Disjoint instantiated
keys satisfy the general support agreement theorem. A shared middle key
separates the two finalization profiles. The row-major language executes the
same admitted directive through a retained pause and actual publication;
the complete source receipt and physical positions remain available.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor
open ProgrammableSpaceMM2Controls (form)
open ProgrammableSpaceMM2RowMajorResumable

def edge (first second : String) : Atom := form "edge" [.symbol first, .symbol second]

def request : Request where
  directive := {
    atom := form "exec" [.expression [.grounded (.int 0), .symbol "overlap"],
      form "," [form "edge" [.var "x", .var "y"]],
      form "O" [form "+" [.var "x"], form "-" [.var "y"]]]
    loc := .expression [.grounded (.int 0), .symbol "overlap"]
    rule := ⟨0, "overlap", .compat ⟨[form "edge" [.var "x", .var "y"]]⟩, [],
      ⟨[.add (.var "x"), .remove (.var "y")]⟩⟩ }
  pattern := ⟨[form "edge" [.var "x", .var "y"]]⟩
  factorization := rfl

def facts : List Atom := [edge "a" "b", edge "b" "c"]
def source : List Atom := facts ++ [request.directive.atom]

def actualRows : List Row :=
  StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot source request))
    (ProgrammableSpaceMM2Matching.initial source request)

def nativeAfter : List Atom := facts ++ [.symbol "a", .symbol "b"]
def sourceAfter : List Atom := facts ++ [.symbol "a"]

theorem admitted : language.admit request.directive.atom request := by
  change ProgrammableSpaceMM2.Admitted request.directive.atom request
  unfold ProgrammableSpaceMM2.Admitted
  decide +kernel

theorem selected : MM2MatchingBatch.SelectedFor .leaveInert source request.directive := by
  unfold MM2MatchingBatch.SelectedFor
  decide +kernel

theorem physical_origins :
    (ProgrammableSpaceMM2.Receipt.witnessesInSourceOrder
      ⟨request, source, actualRows⟩).map (List.map Prod.snd) = [[0], [1]] := by
  decide +kernel

theorem actual_write_order :
    ProgrammableSpaceMM2RowMajorWrites.rowWrites request.directive.rule.input
      ((ProgrammableSpaceMM2Matching.guarded request actualRows).map Prod.fst)
      request.directive.rule.tmpl.sinks =
        [.add (.symbol "a"), .remove (.symbol "b"),
          .add (.symbol "b"), .remove (.symbol "c")] := by
  decide +kernel

theorem native_finalization :
    ProgrammableSpaceMM2RowMajor.finalize source request actualRows = nativeAfter := by
  decide +kernel

theorem source_finalization :
    ProgrammableSpaceMM2Matching.finalize source request actualRows = sourceAfter := by
  decide +kernel

theorem support_separation :
    ProgrammableSpaceMM2RowMajorWrites.support nativeAfter ≠
      ProgrammableSpaceMM2RowMajorWrites.support sourceAfter := by
  decide +kernel

theorem observed_outcomes_separate :
    ProgrammableSpaceMM2RowMajor.language.observes
      (.committed ⟨request, source, actualRows⟩) ⟨nativeAfter, actualRows⟩ ∧
    ¬ ProgrammableSpaceMM2.language.observes
      (.committed ⟨request, source, actualRows⟩) ⟨nativeAfter, actualRows⟩ := by
  change (nativeAfter = ProgrammableSpaceMM2RowMajor.finalize source request actualRows ∧
    actualRows = actualRows) ∧
      ¬ (nativeAfter = ProgrammableSpaceMM2Matching.finalize source request actualRows ∧
        actualRows = actualRows)
  rw [native_finalization, source_finalization]
  decide +kernel

def pausedPacket? (result : ProgrammableSpaceMM2Matching.Result source request) :
    Option (PacketFor source request) :=
  match result with
  | .paused packet => some packet
  | .done _ => none

def packet10 : PacketFor source request :=
  (pausedPacket? (ProgrammableSpaceMM2Matching.run source request 10).2).get (by decide +kernel)

def start : Checkpoint := ProgrammableSpaceMM2Resumable.Checkpoint.start source request

def checkpoint10 : Checkpoint where
  before := source
  request := request
  granted := 10
  spent := 10
  packet := packet10
  reached := rfl

def finished : FinishedFor source request := ⟨(), actualRows, []⟩

theorem continued_cursor_finishes : checkpoint10.resume 100 = (30, .done finished) := by rfl

theorem actual_private_step :
    language.advance .leaveInert source (.matching start) ⟨10, 0, 10, none⟩
      source (.matching checkpoint10) :=
  Advance.pause start 10 10 packet10 selected (by rfl)

theorem actual_publication :
    language.advance .leaveInert source (.matching checkpoint10)
      ⟨100, 10, 30, some ⟨request, source, actualRows⟩⟩ nativeAfter
      (.committed ⟨request, source, actualRows⟩) := by
  have committed := Advance.commit (scope := .leaveInert) checkpoint10 100 30
    finished selected continued_cursor_finishes
  change Advance .leaveInert source (.matching checkpoint10)
    ⟨100, 10, 30, some ⟨request, source, actualRows⟩⟩
    (ProgrammableSpaceMM2RowMajor.finalize source request actualRows)
    (.committed ⟨request, source, actualRows⟩) at committed
  rwa [native_finalization] at committed

theorem actual_atomic_publication :
    ProgrammableSpaceMM2RowMajor.language.advance .leaveInert source (.pending request)
      ⟨request, source, actualRows⟩ nativeAfter (.committed ⟨request, source, actualRows⟩) := by
  have committed := ProgrammableSpaceMM2RowMajor.Advance.commit (scope := .leaveInert)
    source request 100 actualRows selected (by rfl)
  rwa [native_finalization] at committed

theorem actual_two_grant_run :
    Relation.ReflTransGen (Transition .leaveInert)
      (source, language.initial .leaveInert request source)
      (nativeAfter, .committed ⟨request, source, actualRows⟩) := by
  have first : Transition .leaveInert (source, .matching start)
      (source, .matching checkpoint10) := ⟨_, actual_private_step⟩
  have second : Transition .leaveInert (source, .matching checkpoint10)
      (nativeAfter, .committed ⟨request, source, actualRows⟩) := ⟨_, actual_publication⟩
  exact (Relation.ReflTransGen.single first).trans (Relation.ReflTransGen.single second)

theorem exact_atomic_comparison :
    Relation.ReflTransGen (AtomicTransition .leaveInert) (source, .pending request)
      (nativeAfter, .committed ⟨request, source, actualRows⟩) :=
  run_refines_atomic_run actual_two_grant_run

def disjointSource : List Atom := [edge "a" "b", edge "c" "d", request.directive.atom]

def disjointRows : List Row :=
  StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot disjointSource request))
    (ProgrammableSpaceMM2Matching.initial disjointSource request)

/-- Mixed positive and negative effects agree when all cross-polarity keys
are distinct. This uses the general actual-finalizer comparison. -/
theorem disjoint_mixed_effects_agree :
    ProgrammableSpaceMM2RowMajorWrites.support
      (ProgrammableSpaceMM2RowMajor.finalize disjointSource request disjointRows) =
    ProgrammableSpaceMM2RowMajorWrites.support
      (ProgrammableSpaceMM2Matching.finalize disjointSource request disjointRows) :=
  ProgrammableSpaceMM2RowMajor.finalization_source_agreement disjointSource request disjointRows
    (ProgrammableSpaceMM2RowMajor.admitted_sinks request.directive.atom request admitted)
    (by unfold ProgrammableSpaceMM2RowMajorWrites.Independent; decide +kernel)

theorem disjoint_actual_values :
    ProgrammableSpaceMM2RowMajor.finalize disjointSource request disjointRows =
      [edge "a" "b", edge "c" "d", .symbol "a", .symbol "c"] ∧
    ProgrammableSpaceMM2Matching.finalize disjointSource request disjointRows =
      [edge "a" "b", edge "c" "d", .symbol "a", .symbol "c"] := by
  decide +kernel

theorem original_explicit_positive_agrees :
    ProgrammableSpaceMM2RowMajorWrites.support
      (ProgrammableSpaceMM2RowMajor.finalize ProgrammableSpaceMM2GrammarControls.explicitSource
        ProgrammableSpaceMM2GrammarControls.explicitRequest ProgrammableSpaceMM2GrammarControls.explicitRows) =
    ProgrammableSpaceMM2RowMajorWrites.support
      (ProgrammableSpaceMM2Matching.finalize ProgrammableSpaceMM2GrammarControls.explicitSource
        ProgrammableSpaceMM2GrammarControls.explicitRequest ProgrammableSpaceMM2GrammarControls.explicitRows) :=
  ProgrammableSpaceMM2RowMajor.finalization_source_agreement _ _ _
    (ProgrammableSpaceMM2RowMajor.admitted_sinks _ _
      ProgrammableSpaceMM2GrammarControls.explicit_source_admitted)
    (by unfold ProgrammableSpaceMM2RowMajorWrites.Independent; decide +kernel)

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorControls
