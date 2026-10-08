import Mettapedia.GSLT.Core.ProgrammableSpace
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Matching
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxUTF8

/-!
# A source-bound MM2 language for programmable spaces

An admitted atom is an actual decoded conjunction or explicit-BTM `exec` with
explicit add/remove sinks. A session requests that directive in a named source queue
profile. One event commits a completed structural matcher batch, retaining the
chosen source, store snapshot, substitutions and physical witness positions.

This is the atomic publication boundary, not a claim that a C activation is
one machine instruction. Private matching suspension is qualified separately.
The two unsupported-exec policies are formal source profiles; native replay
here concerns interpreted directives only. In particular, neither formal
policy describes the native suspended obligation for unsupported syntax.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor WQComputable
open Mettapedia.GSLT.Core.ProgrammableSpace

abbrev Request := ProgrammableSpaceMM2Matching.Request
abbrev Scope := UnsupportedExecPolicy

def explicitAddRemove : Atom → Bool :=
  ProgrammableSpaceMM2Grammar.grammar

def Admitted (atom : Atom) (request : Request) : Prop :=
  atom = request.directive.atom ∧
    extractSupportedSourceExecFact atom = some request.directive ∧
    explicitAddRemove atom = true

/-- Exact admission for both native MM2 input presentations. The decoded
request retains the original atom, rather than replacing an explicit input
by a comma-input directive. -/
theorem admitted_iff_grammar (atom : Atom) :
    (∃ request, Admitted atom request) ↔
      ProgrammableSpaceMM2Grammar.grammar atom = true := by
  constructor
  · rintro ⟨request, _, _, accepted⟩
    exact accepted
  · intro accepted
    obtain ⟨directive, pattern, parsed, original, factorization, _⟩ :=
      ProgrammableSpaceMM2Grammar.grammar_decodes atom accepted
    exact ⟨⟨directive, pattern, factorization⟩, original.symm, parsed, accepted⟩

theorem admitted_has_no_guards {atom : Atom} {request : Request}
    (admitted : Admitted atom request) : request.directive.rule.guards = [] := by
  obtain ⟨directive, _, parsed, _, _, noGuards⟩ :=
    ProgrammableSpaceMM2Grammar.grammar_decodes atom admitted.2.2
  have same := Option.some.inj (admitted.2.1.symm.trans parsed)
  exact same ▸ noGuards

structure Receipt where
  request : Request
  before : List Atom
  rows : List Row

def Receipt.after (receipt : Receipt) : List Atom :=
  ProgrammableSpaceMM2Matching.finalize receipt.before receipt.request receipt.rows

/-- The cursor accumulates premise witnesses on a stack. A source-order
receipt reverses each stack, retaining every atom and physical position. -/
def Receipt.witnessesInSourceOrder (receipt : Receipt) : List (List Entry) :=
  receipt.rows.map fun row => row.2.reverse

theorem Receipt.witness_order_recoverable (receipt : Receipt) :
    receipt.witnessesInSourceOrder.map List.reverse = receipt.rows.map Prod.snd := by
  simp [witnessesInSourceOrder, List.map_map]

inductive Residual where
  | pending (request : Request)
  | committed (receipt : Receipt)

structure Outcome where
  store : List Atom
  rows : List Row

/-- A selected directive may commit only after the retained structural cursor
has produced its complete ordered row list for this exact store. -/
inductive Advance (scope : Scope) : List Atom → Residual → Receipt →
    List Atom → Residual → Prop where
  | commit (space : List Atom) (request : Request) (fuel : Nat) (rows : List Row)
      (selected : MM2MatchingBatch.SelectedFor scope space request.directive)
      (completed : HostCalls.collect
        (StructuralQuanta.pull (entries (ProgrammableSpaceMM2Matching.snapshot space request)))
        fuel (ProgrammableSpaceMM2Matching.initial space request) = some rows) :
      Advance scope space (.pending request) ⟨request, space, rows⟩
        (ProgrammableSpaceMM2Matching.finalize space request rows)
        (.committed ⟨request, space, rows⟩)

def Observes : Residual → Outcome → Prop
  | .pending _, _ => False
  | .committed receipt, outcome =>
      outcome.store = receipt.after ∧ outcome.rows = receipt.rows

def language : Language Atom where
  Scope := Scope
  Request := Request
  Residual := Residual
  Outcome := Outcome
  Receipt := Receipt
  admit := Admitted
  initial _ request _ := .pending request
  advance := Advance
  observes := Observes

theorem selected_source_step (scope : Scope) (space : List Atom) (request : Request)
    (selected : MM2MatchingBatch.SelectedFor scope space request.directive) :
    cRuleScopedSourceWorkQueueStep scope space =
      some (cFireRuleScopedSourceExecFact space request.directive) := by
  cases scope with
  | leaveInert =>
      change selectNextScheduled (cSupportedSourceExecFacts space) =
        some request.directive at selected
      simp [cRuleScopedSourceWorkQueueStep, selected]
  | consume =>
      obtain ⟨raw, selected, decoded⟩ := selected
      simp [cRuleScopedSourceWorkQueueStep, selected, decoded]

/-- Every admitted-language event is an actual source execution step. -/
theorem advance_source_step {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after) :
    cRuleScopedSourceWorkQueueStep scope space = some target := by
  cases step with
  | commit request fuel rows selected completed =>
      rw [ProgrammableSpaceMM2Matching.completed_finalize space request fuel rows completed]
      exact selected_source_step scope space request selected

theorem advance_preserves_physical_support {scope : Scope} {space target : List Atom}
    {before after : Residual} {receipt : Receipt}
    (step : Advance scope space before receipt target after)
    (normalized : MorkSupportNodup space) : MorkSupportNodup target := by
  cases step with
  | commit request fuel rows selected completed =>
      rw [ProgrammableSpaceMM2Matching.completed_finalize space request fuel rows completed]
      exact cFireRuleScopedSourceExecFact_mork_nodup space request.directive normalized

/-- Every selected admitted input has a complete receipt;
an unfinished cursor is not interpreted as an empty successful match. -/
theorem selected_has_event (scope : Scope) (space : List Atom) (request : Request)
    (selected : MM2MatchingBatch.SelectedFor scope space request.directive) :
    ∃ receipt after,
      Advance scope space (.pending request) receipt
        (cFireRuleScopedSourceExecFact space request.directive) after := by
  let rows := StructuralQuanta.residualRows
    (entries (ProgrammableSpaceMM2Matching.snapshot space request))
    (ProgrammableSpaceMM2Matching.initial space request)
  have completed := ProgrammableSpaceMM2Matching.collect_complete space request
  have exactStore := ProgrammableSpaceMM2Matching.completed_finalize
    space request _ rows completed
  refine ⟨⟨request, space, rows⟩, .committed ⟨request, space, rows⟩, ?_⟩
  rw [← exactStore]
  exact .commit space request _ rows selected completed

theorem event_iff_selected_firing (scope : Scope) (space target : List Atom)
    (request : Request) :
    (∃ receipt after, Advance scope space (.pending request) receipt target after) ↔
      MM2MatchingBatch.SelectedFor scope space request.directive ∧
        target = cFireRuleScopedSourceExecFact space request.directive := by
  constructor
  · rintro ⟨receipt, after, step⟩
    cases step with
    | commit _ fuel rows selected completed =>
        exact ⟨selected,
          ProgrammableSpaceMM2Matching.completed_finalize space request fuel rows completed⟩
  · rintro ⟨selected, rfl⟩
    exact selected_has_event scope space request selected

theorem committed_does_not_fire {scope : Scope} {space target : List Atom}
    (old receipt : Receipt) (after : Residual) :
    ¬ Advance scope space (.committed old) receipt target after := by
  intro impossible
  cases impossible

/-- Changing the amount of private matching fuel cannot change a completed
receipt's substitutions, physical witnesses or final support. -/
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

/-- Loading uses physical compact-key support, rather than treating distinct
spellings of the same variable incidence as distinct workspace members. -/
def load (atoms : List Atom) : List Atom := morkUnionSupport [] atoms

theorem load_support_nodup (atoms : List Atom) : MorkSupportNodup (load atoms) :=
  morkUnionSupport_nodup [] atoms (by simp [MorkSupportNodup])

/-- The same atom program that is retained by a byte parser is loaded. No
unverified foreign parser or hidden source transformation enters this step. -/
def loadParsed {bytes : ByteArray} (parsed : MM2SyntaxUTF8.ByteParsedProgram bytes) : List Atom :=
  load parsed.atoms

theorem rendered_bytes_load_exactly {program : List Atom} {rendered : String}
    (renderedExact : MM2Surface.renderProgram? program = some rendered) :
    ∃ parsed : MM2SyntaxUTF8.ByteParsedProgram rendered.toUTF8,
      parsed.atoms = program ∧ loadParsed parsed = load program := by
  obtain ⟨parsed, exactAtoms⟩ :=
    MM2SyntaxUTF8.successful_render_has_exact_byte_parser_lowering renderedExact
  exact ⟨parsed, exactAtoms, congrArg load exactAtoms⟩

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2
