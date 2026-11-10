import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRuns
import Mettapedia.GSLT.Parsing.LanguageDefScalarDeterminism

/-! # Exact scalar-source recovery for the authored transform entry

The authored production prefixes establish uniqueness for this structural
profile. The semantic reader below is specified by the actual source grammar;
it is not a native parser implementation. Every replayed packed result agrees
with that reader. Canonical recovery therefore does not select a convenient
tree while ignoring another parse of the same input.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics
open Interface Payloads OccurrenceProfile

theorem prefixes_separated :
    LanguageDefScalarDeterminism.Separated literalScalars authoredLanguage := by
  unfold LanguageDefScalarDeterminism.Separated
  decide +kernel

theorem parse_unique {sort : String} {input : List Nat} {first second : CST}
    (left : Parses sort input first) (right : Parses sort input second) : first = second :=
  (LanguageDefScalarDeterminism.unique rfl prefixes_separated left right rfl rfl).2

theorem canonical_request_recovery (state : State) (candidate : Candidate)
    {tree : CST} (parsed : Parses "Proc" (requestInput state candidate) tree) :
    LanguageDefScalarStructural.tree? tree =
      some (request (statePattern state) (firingPattern ⟨state, candidate⟩)) := by
  obtain ⟨printed, erased, ⟨derived⟩⟩ := canonical_request_source state candidate
  have same := parse_unique parsed derived
  simpa only [same] using erased

/-- A mathematical reader of the source grammar. Executable packed parsers
are related to it by `packed_reader_agrees`; no host parser is assumed. -/
noncomputable def parseTree (sort : String) (input : List Nat) : Option CST := by
  classical
  exact if found : ∃ tree, Nonempty (Parses sort input tree) then some found.choose else none

theorem parseTree_of_derivation {sort : String} {input : List Nat} {tree : CST}
    (parsed : Parses sort input tree) : parseTree sort input = some tree := by
  classical
  have found : ∃ tree, Nonempty (Parses sort input tree) := ⟨tree, ⟨parsed⟩⟩
  simp only [parseTree, dif_pos found]
  exact congrArg some (parse_unique (Classical.choice found.choose_spec) parsed)

theorem parseTree_reflects {sort : String} {input : List Nat} {tree : CST}
    (read : parseTree sort input = some tree) : Nonempty (Parses sort input tree) := by
  classical
  unfold parseTree at read
  split at read
  next found =>
    have same := Option.some.inj read
    exact same ▸ found.choose_spec
  next => cases read

theorem packed_reader_agrees (forest : ClassAwarePackedForest.Forest)
    {sort : String} {input : List Nat} {tree : CST} (packed : Nonempty (Packed forest sort input tree)) :
    parseTree sort input = some tree := by
  obtain ⟨parsed⟩ := packed_reflects forest sort input tree packed
  exact parseTree_of_derivation parsed

abbrev RequestAST := (_state : State) × Candidate

/-- Configuration normalization and source-index validation are performed
by the existing lowering; the candidate codec then recovers the indexed AST. -/
def readRequest (body : Pattern) : Option RequestAST :=
  (lowerRequest body).bind fun
    | .apply "Request" [_, firing] => readFiring firing
    | _ => none

theorem readRequest_of_lower {body : Pattern} (state : State) (candidate : Candidate)
    (lowered : lowerRequest body =
      some (request (statePattern state) (firingPattern ⟨state, candidate⟩))) :
    readRequest body = some ⟨state, candidate⟩ := by
  simp only [readRequest, lowered, Option.bind_some, request, read_firing_pattern]

def readTree (tree : CST) : Option RequestAST :=
  (LanguageDefScalarStructural.tree? tree).bind readRequest

noncomputable def readInput (input : List Nat) : Option RequestAST :=
  (parseTree "Proc" input).bind readTree

theorem readInput_of_parse {input : List Nat} {tree : CST}
    (parsed : Parses "Proc" input tree) : readInput input = readTree tree := by
  simp only [readInput, parseTree_of_derivation parsed, Option.bind_some]

theorem readInput_print (ast : RequestAST) :
    readInput (requestInput ast.1 ast.2) = some ast := by
  rcases ast with ⟨state, candidate⟩
  obtain ⟨tree, erased, ⟨parsed⟩⟩ := canonical_request_source state candidate
  rw [readInput_of_parse parsed]
  simp only [readTree, erased, Option.bind_some]
  exact readRequest_of_lower state candidate (lower_canonical state candidate)

noncomputable def requestPresentation :
    ExactPresentation.Presentation (fun _ : Unit => RequestAST) (fun _ => List Nat) where
  key := ⟨"tcalc.transform.request.scalar", 1⟩
  view ast := requestInput ast.1 ast.2
  expand := readInput
  expand_view := readInput_print

theorem versioned_request_recovery (ast : RequestAST) :
    ExactPresentation.expandDocument requestPresentation
      (ExactPresentation.viewDocument requestPresentation (sort := ()) ast) = some ast :=
  ExactPresentation.expand_viewDocument requestPresentation ast

theorem stale_request_refused (input : List Nat) :
    ExactPresentation.expandDocument requestPresentation (sort := ())
      ⟨⟨"tcalc.transform.request.scalar", 0⟩, input⟩ = none := rfl

theorem event_input_recovery (label : Nat → Term)
    (decision : Decisions (effect label) (admission label))
    {keep : ParsePolicy} {source target : State}
    (event : SelectedEvent label decision keep source target) :
    readInput event.input = some ⟨source, event.candidate⟩ := by
  rw [readInput_of_parse event.parsed]
  simp only [readTree, event.erased, Option.bind_some]
  exact readRequest_of_lower source event.candidate event.lowered

/-- Normalization preserves the event's state and candidate, rather than
promising to preserve its noncanonical source ordering or CST provenance. -/
theorem event_input_normalizes (label : Nat → Term)
    (decision : Decisions (effect label) (admission label))
    {keep : ParsePolicy} {source target : State}
    (event : SelectedEvent label decision keep source target) :
    ExactPresentation.normalize requestPresentation (sort := ()) event.input =
      some (requestInput source event.candidate) := by
  change (readInput event.input).map (fun ast => requestInput ast.1 ast.2) = _
  rw [event_input_recovery label decision event]
  rfl

#print axioms prefixes_separated
#print axioms canonical_request_recovery
#print axioms packed_reader_agrees
#print axioms readInput_print
#print axioms event_input_normalizes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source
