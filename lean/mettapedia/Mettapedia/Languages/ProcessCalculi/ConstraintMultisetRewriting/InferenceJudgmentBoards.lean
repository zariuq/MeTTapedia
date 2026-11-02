import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory

/-!
# Ordered protected-judgment projections of physical stores

A board lists every occupied occurrence in protected judgment space once,
retaining both its physical identity and its source judgment. Equal judgments
at different occurrences remain distinct premise positions. Request data is
outside this projection, including the request consumed by a server step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value)
open InferenceRequestExecution (Occurrence label location)

/-- An ordered, occurrence-exact projection of the protected space. -/
structure Board (state : Configuration Value Occurrence) where
  entries : List (Occurrence × Pattern)
  distinct : (entries.map Prod.fst).Nodup
  occupied : ∀ occurrence,
    occurrence ∈ entries.map Prod.fst ↔
      occurrence ∈ state.present ∧ location occurrence = .judgments
  readback : ∀ entry ∈ entries,
    label entry.1 = (.judgments, judgment entry.2)
  supported : ∀ entry ∈ entries, entry.2.isWellScoped = true

namespace Board

variable {state : Configuration Value Occurrence}

def occurrences (board : Board state) : List Occurrence := board.entries.map Prod.fst
def judgments (board : Board state) : List Pattern := board.entries.map Prod.snd
def context (board : Board state) (definition : ValidatedCalculusLanguageDef) :
    ClassifyingContext definition := ⟨board.judgments⟩

def occurrenceAt (board : Board state) (index : Fin board.entries.length) : Occurrence :=
  (board.entries.get index).1

def judgmentAt (board : Board state) (index : Fin board.entries.length) : Pattern :=
  (board.entries.get index).2

theorem at_readback (board : Board state) (index : Fin board.entries.length) :
    label (board.occurrenceAt index) = (.judgments, judgment (board.judgmentAt index)) :=
  board.readback _ (List.get_mem _ index)

theorem at_scoped (board : Board state) (index : Fin board.entries.length) :
    (board.judgmentAt index).isWellScoped = true :=
  board.supported _ (List.get_mem _ index)

/-- Physical identity determines its unique context position. -/
noncomputable def position (board : Board state) (occurrence : Occurrence)
    (present : occurrence ∈ state.present) (protectedHere : location occurrence = .judgments) :
    Fin board.entries.length := by
  classical
  exact ⟨board.occurrences.idxOf occurrence, by
    have member := (board.occupied occurrence).mpr ⟨present, protectedHere⟩
    simpa only [occurrences, List.length_map] using List.idxOf_lt_length_iff.mpr member⟩

theorem position_occurrence (board : Board state) (occurrence : Occurrence)
    (present : occurrence ∈ state.present) (protectedHere : location occurrence = .judgments) :
    board.occurrenceAt (board.position occurrence present protectedHere) = occurrence := by
  classical
  have found := List.idxOf_get (l := board.occurrences) (a := occurrence)
    (show board.occurrences.idxOf occurrence < board.occurrences.length from
      List.idxOf_lt_length_iff.mpr ((board.occupied occurrence).mpr ⟨present, protectedHere⟩))
  simpa only [occurrences, List.get_eq_getElem, List.getElem_map, occurrenceAt, position] using found

/-- Every context position is represented by an assumption node, retaining
the position even when another row has an equal judgment. -/
def assumption (board : Board state) (definition : ValidatedCalculusLanguageDef)
    (index : Fin board.entries.length) :
    OpenDerivation definition board.judgments (board.judgmentAt index) := by
  simpa only [judgments, List.get_eq_getElem, List.getElem_map, judgmentAt] using
    (OpenDerivation.assumption (definition := definition) (context := board.judgments)
      ⟨index.val, by simpa only [judgments, List.length_map] using index.isLt⟩)

/-- The empty physical protected space has the empty premise context. -/
def empty (state : Configuration Value Occurrence) (none : state.present = ∅) : Board state where
  entries := []
  distinct := List.nodup_nil
  occupied := by intro occurrence; simp [none]
  readback := by intro entry member; cases member
  supported := by intro entry member; cases member

/-- Request-only changes keep the same ordered judgment entries. -/
def retain {after : Configuration Value Occurrence} (board : Board state)
    (same : ∀ occurrence,
      (occurrence ∈ after.present ∧ location occurrence = .judgments) ↔
      (occurrence ∈ state.present ∧ location occurrence = .judgments)) : Board after where
  entries := board.entries
  distinct := board.distinct
  occupied := fun occurrence => (board.occupied occurrence).trans (same occurrence).symm
  readback := board.readback
  supported := board.supported

/-- Appending the one freshly published judgment extends the protected
projection while preserving all earlier physical positions. -/
def extend {after : Configuration Value Occurrence} (board : Board state)
    (output : Occurrence) (conclusion : Pattern)
    (fresh : output ∉ board.occurrences)
    (atOutput : label output = (.judgments, judgment conclusion))
    (scope : conclusion.isWellScoped = true)
    (exactAfter : ∀ occurrence,
      (occurrence ∈ after.present ∧ location occurrence = .judgments) ↔
        occurrence ∈ board.occurrences ∨ occurrence = output) : Board after where
  entries := board.entries ++ [(output, conclusion)]
  distinct := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨board.distinct, by simp, ?_⟩
    intro occurrence member other inOutput same
    have otherEq : other = output := by simpa using inOutput
    subst other
    subst occurrence
    exact fresh member
  occupied := by
    intro occurrence
    simpa only [occurrences, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton] using (exactAfter occurrence).symm
  readback := by
    intro entry member
    rcases List.mem_append.mp member with old | new
    · exact board.readback entry old
    · have same : entry = (output, conclusion) := List.mem_singleton.mp new
      subst entry
      exact atOutput
  supported := by
    intro entry member
    rcases List.mem_append.mp member with old | new
    · exact board.supported entry old
    · have same : entry = (output, conclusion) := List.mem_singleton.mp new
      subst entry
      exact scope

@[simp] theorem extend_judgments {after : Configuration Value Occurrence}
    (board : Board state) (output : Occurrence) (conclusion : Pattern)
    (fresh : output ∉ board.occurrences)
    (atOutput : label output = (.judgments, judgment conclusion))
    (scope : conclusion.isWellScoped = true)
    (exactAfter : ∀ occurrence,
      (occurrence ∈ after.present ∧ location occurrence = .judgments) ↔
        occurrence ∈ board.occurrences ∨ occurrence = output) :
    (board.extend output conclusion fresh atOutput scope exactAfter).judgments =
      board.judgments ++ [conclusion] := by
  simp only [extend, judgments, List.map_append, List.map_cons, List.map_nil]

end Board
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards
