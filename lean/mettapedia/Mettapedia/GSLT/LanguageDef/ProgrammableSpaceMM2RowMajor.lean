import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorWrites

/-!
# Row-major MM2 finalization as a separate programmable language

The request, original directive, rule-local variable discipline, actual
matching cursor, selected source scope and physical receipt are shared with
the existing MM2 source profile. Finalization follows each row through its
authored add/remove sinks. No default profile is changed. This is an explicit
semantic model of the provider's effect order, not verification of compiled C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor WQComputable
open Mettapedia.GSLT.Core.ProgrammableSpace (Language)

abbrev Request := ProgrammableSpaceMM2.Request
abbrev Scope := ProgrammableSpaceMM2.Scope
abbrev Receipt := ProgrammableSpaceMM2.Receipt
abbrev Residual := ProgrammableSpaceMM2.Residual
abbrev Outcome := ProgrammableSpaceMM2.Outcome

def finalize (space : List Atom) (request : Request) (rows : List Row) : List Atom :=
  ProgrammableSpaceMM2RowMajorWrites.rows request.directive.rule.input
    ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
    request.directive.rule.tmpl.sinks (ProgrammableSpaceMM2Matching.live space request)

def after (receipt : Receipt) : List Atom :=
  finalize receipt.before receipt.request receipt.rows

/-- Whole source execution with the same actual matcher and distinct effect
order. This does not change the existing sink-major source executor. -/
def fire (space : List Atom) (directive : SourceExecFact) : List Atom :=
  let live := morkEraseSupport space directive.atom
  let snapshot := morkInsertSupport live directive.atom
  let found := cMatchInputSpecMork [] snapshot directive.rule.input
  let selected := found.filter fun row => matchSourceGuards row.1 directive.rule.guards
  ProgrammableSpaceMM2RowMajorWrites.rows directive.rule.input (selected.map Prod.fst)
    directive.rule.tmpl.sinks live

def sourceStep (scope : Scope) (space : List Atom) : Option (List Atom) :=
  match scope with
  | .leaveInert => (selectNextScheduled (cSupportedSourceExecFacts space)).map (fire space)
  | .consume =>
      (selectNextScheduled (cRawExecFacts space)).map fun raw =>
        match decodeSupportedSourceExec raw with
        | none => morkEraseSupport space raw.atom
        | some directive => fire space directive

theorem completed_finalize (space : List Atom) (request : Request) (fuel : Nat)
    (rows : List Row)
    (completed : HostCalls.collect
      (StructuralQuanta.pull (entries (ProgrammableSpaceMM2Matching.snapshot space request)))
      fuel (ProgrammableSpaceMM2Matching.initial space request) = some rows) :
    finalize space request rows = fire space request.directive := by
  unfold finalize
  rw [ProgrammableSpaceMM2Matching.guarded_substitutions,
    ProgrammableSpaceMM2Matching.completed_rows space request fuel rows completed]
  rfl

theorem selected_source_step (scope : Scope) (space : List Atom) (request : Request)
    (selected : MM2MatchingBatch.SelectedFor scope space request.directive) :
    sourceStep scope space = some (fire space request.directive) := by
  cases scope with
  | leaveInert =>
      change selectNextScheduled (cSupportedSourceExecFacts space) =
        some request.directive at selected
      simp [sourceStep, selected]
  | consume =>
      obtain ⟨raw, selected, decoded⟩ := selected
      simp [sourceStep, selected, decoded]

inductive Advance (scope : Scope) : List Atom → Residual → Receipt →
    List Atom → Residual → Prop where
  | commit (space : List Atom) (request : Request) (fuel : Nat) (rows : List Row)
      (selected : MM2MatchingBatch.SelectedFor scope space request.directive)
      (completed : HostCalls.collect
        (StructuralQuanta.pull (entries (ProgrammableSpaceMM2Matching.snapshot space request)))
        fuel (ProgrammableSpaceMM2Matching.initial space request) = some rows) :
      Advance scope space (.pending request) ⟨request, space, rows⟩
        (finalize space request rows) (.committed ⟨request, space, rows⟩)

def Observes : Residual → Outcome → Prop
  | .pending _, _ => False
  | .committed receipt, outcome => outcome.store = after receipt ∧ outcome.rows = receipt.rows

def language : Language Atom where
  Scope := Scope
  Request := Request
  Residual := Residual
  Outcome := Outcome
  Receipt := Receipt
  admit := ProgrammableSpaceMM2.Admitted
  initial _ request _ := .pending request
  advance := Advance
  observes := Observes

theorem admitted_iff_grammar (atom : Atom) :
    (∃ request, language.admit atom request) ↔
      ProgrammableSpaceMM2Grammar.grammar atom = true :=
  ProgrammableSpaceMM2.admitted_iff_grammar atom

theorem unary_sink_allowed (raw : Atom)
    (accepted : ProgrammableSpaceMM2Grammar.unarySink raw = true) :
    ∃ sink, parseSupportedSink raw = some sink ∧
      ProgrammableSpaceMM2RowMajorWrites.Allowed sink := by
  unfold ProgrammableSpaceMM2Grammar.unarySink at accepted
  split at accepted
  · exact ⟨_, rfl, trivial⟩
  · exact ⟨_, rfl, trivial⟩
  · cases accepted

theorem unary_sinks_allowed (raw : List Atom)
    (accepted : raw.all ProgrammableSpaceMM2Grammar.unarySink = true) :
    ∃ sinks, parseSupportedSinkList raw = some sinks ∧
      ∀ sink ∈ sinks, ProgrammableSpaceMM2RowMajorWrites.Allowed sink := by
  induction raw with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at accepted
      obtain ⟨sink, parsed, allowed⟩ := unary_sink_allowed first accepted.1
      obtain ⟨sinks, restParsed, restAllowed⟩ := ih accepted.2
      refine ⟨sink :: sinks, by simp [parseSupportedSinkList, parsed, restParsed], ?_⟩
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact restAllowed other member

/-- Every admitted request really has only the sinks interpreted by this
profile; the broader parser's extrema constructors are never silently used. -/
theorem admitted_sinks (atom : Atom) (request : Request)
    (accepted : language.admit atom request) :
    ∀ sink ∈ request.directive.rule.tmpl.sinks,
      ProgrammableSpaceMM2RowMajorWrites.Allowed sink := by
  obtain ⟨original, parsed, grammatical⟩ := accepted
  unfold ProgrammableSpaceMM2.explicitAddRemove ProgrammableSpaceMM2Grammar.grammar at grammatical
  split at grammatical
  · rename_i location input raw
    simp only [Bool.and_eq_true] at grammatical
    obtain ⟨patterns, authored⟩ :=
      (ProgrammableSpaceMM2Grammar.inputGrammar_iff input).mp grammatical.1
    obtain ⟨decodedInput, inputParsed, _⟩ := authored.decoded
    obtain ⟨sinks, sinksParsed, allowed⟩ := unary_sinks_allowed raw grammatical.2
    simp [extractSupportedSourceExecFact, extractRawExecFact, decodeSupportedSourceExec,
      inputParsed, parseSupportedTemplate, sinksParsed, mkTemplate] at parsed
    rw [← parsed]
    exact allowed
  · cases grammatical

theorem advance_source_step {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after) :
    sourceStep scope space = some target := by
  cases step with
  | commit request fuel rows selected completed =>
      rw [completed_finalize space request fuel rows completed]
      exact selected_source_step scope space request selected

theorem advance_preserves_physical_support {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after)
    (normalized : MorkSupportNodup space) : MorkSupportNodup target := by
  cases step with
  | commit request fuel rows selected completed =>
      exact ProgrammableSpaceMM2RowMajorWrites.rows_nodup _ _ _ _
        (morkEraseSupport_nodup space request.directive.atom normalized)

theorem selected_has_event (scope : Scope) (space : List Atom) (request : Request)
    (selected : MM2MatchingBatch.SelectedFor scope space request.directive) :
    ∃ receipt residual,
      Advance scope space (.pending request) receipt (fire space request.directive) residual := by
  let rows := StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot space request))
    (ProgrammableSpaceMM2Matching.initial space request)
  have completed := ProgrammableSpaceMM2Matching.collect_complete space request
  have exactStore := completed_finalize space request _ rows completed
  refine ⟨⟨request, space, rows⟩, .committed ⟨request, space, rows⟩, ?_⟩
  rw [← exactStore]
  exact .commit space request _ rows selected completed

theorem event_iff_selected_firing (scope : Scope) (space target : List Atom)
    (request : Request) :
    (∃ receipt residual, Advance scope space (.pending request) receipt target residual) ↔
      MM2MatchingBatch.SelectedFor scope space request.directive ∧
        target = fire space request.directive := by
  constructor
  · rintro ⟨receipt, residual, step⟩
    cases step with
    | commit _ fuel rows selected completed =>
        exact ⟨selected, completed_finalize space request fuel rows completed⟩
  · rintro ⟨selected, rfl⟩
    exact selected_has_event scope space request selected

theorem committed_does_not_fire {scope : Scope} {space target : List Atom}
    (old receipt : Receipt) (residual : Residual) :
    ¬ Advance scope space (.committed old) receipt target residual := by
  intro impossible
  cases impossible

theorem completed_receipt_unique {scope : Scope} {space firstTarget secondTarget : List Atom}
    {request : Request} {first second : Receipt} {firstAfter secondAfter : Residual}
    (firstStep : Advance scope space (.pending request) first firstTarget firstAfter)
    (secondStep : Advance scope space (.pending request) second secondTarget secondAfter) :
    first = second ∧ firstTarget = secondTarget ∧ firstAfter = secondAfter := by
  cases firstStep with
  | commit _ firstFuel firstRows firstSelected firstCompleted =>
    cases secondStep with
    | commit _ secondFuel secondRows secondSelected secondCompleted =>
      have firstExact := StructuralQuanta.completed_rows _ _ [] firstFuel firstRows firstCompleted
      have secondExact := StructuralQuanta.completed_rows _ _ [] secondFuel secondRows secondCompleted
      have same : firstRows = secondRows := firstExact.trans secondExact.symm
      cases same
      exact ⟨rfl, rfl, rfl⟩

theorem finalization_ordered_writes (space : List Atom) (request : Request) (rows : List Row) :
    finalize space request rows =
      (ProgrammableSpaceMM2RowMajorWrites.rowWrites request.directive.rule.input
        ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
        request.directive.rule.tmpl.sinks).foldl
          ProgrammableSpaceMM2RowMajorWrites.Write.apply
            (ProgrammableSpaceMM2Matching.live space request) :=
  ProgrammableSpaceMM2RowMajorWrites.rows_ordered_writes _ _ _ _

theorem finalization_source_agreement (space : List Atom) (request : Request) (rows : List Row)
    (allowed : ∀ sink ∈ request.directive.rule.tmpl.sinks,
      ProgrammableSpaceMM2RowMajorWrites.Allowed sink)
    (independent : ∀ first ∈ ProgrammableSpaceMM2RowMajorWrites.rowWrites
      request.directive.rule.input ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
      request.directive.rule.tmpl.sinks,
      ∀ second ∈ ProgrammableSpaceMM2RowMajorWrites.rowWrites
        request.directive.rule.input ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
        request.directive.rule.tmpl.sinks,
        ProgrammableSpaceMM2RowMajorWrites.Independent first second) :
    ProgrammableSpaceMM2RowMajorWrites.support (finalize space request rows) =
      ProgrammableSpaceMM2RowMajorWrites.support
        (ProgrammableSpaceMM2Matching.finalize space request rows) :=
  ProgrammableSpaceMM2RowMajorWrites.source_agreement _ _ _ allowed _ independent

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajor
