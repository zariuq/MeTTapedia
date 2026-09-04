import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.BoundedCompletion
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ReflectiveMM2Bridge
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SemanticObserver
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mathlib.Tactic

/-!
# MM2 OEIS fragment obligations for typed graph decoding

The OEIS MM2 programs use quoted worker rules.  A worker is inert data until
the reflective clock instantiates a later `exec` directive from it.  This file
states that staging boundary on the actual MM2 atom carrier, computes the
finite producer closure used by the declared OEIS fragment, and isolates the
budget, observer-composition, and scheduler laws needed by the next decoder.

The producer analysis is intentionally fragment-specific.  It recognizes the
`g` rows and the comma/add/pure output forms emitted by the current OEIS
translator.  It is not presented as a decision procedure for unrestricted
MM2 saturation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2OEISFragment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.StagedBinding
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SemanticObserver

/-! ## Quoted workers and the reflective clock boundary -/

/-- One worker stored as data in the OEIS MM2 profile. -/
structure QuotedWorker where
  key : Atom
  pattern : Atom
  template : Atom
  deriving Repr, DecidableEq

namespace QuotedWorker

/-- Exact stored form `((step key) (, ...) template)`. -/
def encode (worker : QuotedWorker) : Atom :=
  .expression
    [.expression [.symbol "step", worker.key], worker.pattern, worker.template]

/-- The clock-generated executable directive for one stored worker. -/
def lift (worker : QuotedWorker) : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "a0", worker.key],
      worker.pattern, worker.template]

end QuotedWorker

/-- Decode only the quoted worker shape whose pattern has the MM2 comma
wrapper.  Other data headed by `step` remains ordinary open-world data. -/
def decodeQuotedWorker? : Atom → Option QuotedWorker
  | .expression
      [.expression [.symbol "step", key], pattern, template] =>
      match pattern with
      | .expression (.symbol "," :: _) => some ⟨key, pattern, template⟩
      | _ => none
  | _ => none

@[simp] theorem decodeQuotedWorker?_encode (worker : QuotedWorker)
    (commaPattern : ∃ patterns,
      worker.pattern = .expression (.symbol "," :: patterns)) :
    decodeQuotedWorker? worker.encode = some worker := by
  rcases worker with ⟨key, pattern, template⟩
  obtain ⟨patterns, rfl⟩ := commaPattern
  rfl

/-- The exact outer template authored by the OEIS reflective clock. -/
def clockLiftTemplate : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "a0", .var "k"],
      .var "pp", .var "tt"]

/-- One clock match.  Captured pattern and template atoms are values at this
stage even when they contain variables for the later worker rule. -/
def clockSubstitution (worker : QuotedWorker) : Subst :=
  [("k", worker.key), ("pp", worker.pattern), ("tt", worker.template)]

theorem clockLiftTemplate_covered (worker : QuotedWorker) :
    templateCovered (clockSubstitution worker) clockLiftTemplate = true := by
  simp [clockSubstitution, clockLiftTemplate, templateCovered,
    templatesCovered, Subst.lookup]

/-- One stored worker produces exactly one executable shell under the clock
substitution, without recursively substituting variables inside its captured
pattern or template. -/
theorem clockLiftTemplate_instantiates (worker : QuotedWorker) :
    instantiateTemplateAtom? (clockSubstitution worker) clockLiftTemplate =
      some worker.lift := by
  rw [instantiateTemplateAtom_of_covered _ _
    (clockLiftTemplate_covered worker)]
  simp [clockSubstitution, clockLiftTemplate, QuotedWorker.lift,
    applySubst, applySubst.applySubstList, Subst.lookup]

/-- Every lifted worker is a scheduler-visible MM2 directive. -/
@[simp] theorem extractRawExecFact_lift_isSome (worker : QuotedWorker) :
    (extractRawExecFact worker.lift).isSome = true := by
  rfl

/-- The quoted worker is opaque to the enclosing binding stage. -/
theorem quotedWorker_preserves_outer_binding_state
    (worker : QuotedWorker) (state : State String) :
    State.observe state (.opaqueCapture 1 worker.encode) = state := by
  rfl

private def incompleteClockSubstitution (worker : QuotedWorker) : Subst :=
  [("k", worker.key), ("pp", worker.pattern)]

/-- Missing an outer clock binding fails before a worker event is emitted.
Inner worker variables are not the cause of rejection; the missing captured
template value is. -/
theorem clock_without_template_capture_is_rejected (worker : QuotedWorker) :
    instantiateTemplateAtom? (incompleteClockSubstitution worker)
      clockLiftTemplate = none := by
  simp [instantiateTemplateAtom?, incompleteClockSubstitution,
    clockLiftTemplate, templateCovered, templatesCovered, Subst.lookup]

/-! ## Finite producer closure for the declared OEIS forms -/

/-- Recognize the key of one produced `g` row. -/
def gotKey? : Atom → Option Atom
  | .expression [.symbol "g", key, _, _, _] => some key
  | _ => none

/-- Output atoms whose producer role is explicit in the admitted OEIS
fragment: comma outputs, `O (+ atom)`, and the output row of a pure provider.
Unknown providers contribute no invented producer fact. -/
def producerOutputAtoms : Atom → List Atom
  | .expression (.symbol "," :: outputs) => outputs
  | .expression (.symbol "O" :: sinks) =>
      sinks.filterMap fun sink =>
        match sink with
        | .expression [.symbol "+", output] => some output
        | .expression [.symbol "pure", output, _, _] => some output
        | _ => none
  | _ => []

def producerKeys (template : Atom) : List Atom :=
  (producerOutputAtoms template).filterMap gotKey?

def directProducerKeys (atom : Atom) : List Atom :=
  match extractRawExecFact atom with
  | some directive => producerKeys directive.templateExpr
  | none => []

def generatedProducerKeys (atom : Atom) : List Atom :=
  match decodeQuotedWorker? atom with
  | some worker => producerKeys worker.template
  | none => []

def directProducerInventory (program : List Atom) : List Atom :=
  program.flatMap directProducerKeys

def generatedProducerInventory (program : List Atom) : List Atom :=
  program.flatMap generatedProducerKeys

/-- Directives already present and directives generated from quoted workers
are kept separate until this explicit finite union. -/
def producerClosure (program : List Atom) : Finset Atom :=
  (directProducerInventory program ++
    generatedProducerInventory program).toFinset

theorem mem_producerClosure_iff (program : List Atom) (key : Atom) :
    key ∈ producerClosure program ↔
      key ∈ directProducerInventory program ∨
        key ∈ generatedProducerInventory program := by
  simp [producerClosure]

theorem worker_producer_mem_closure (worker : QuotedWorker)
    (commaPattern : ∃ patterns,
      worker.pattern = .expression (.symbol "," :: patterns))
    (key : Atom) (produces : key ∈ producerKeys worker.template) :
    key ∈ producerClosure [worker.encode] := by
  rw [mem_producerClosure_iff]
  right
  simp [generatedProducerInventory, generatedProducerKeys,
    decodeQuotedWorker?_encode worker commaPattern, produces]

/-- The generated executable inventory has exactly one entry per quoted
worker.  This is the finite fragment boundary; unrestricted saturation is not
silently substituted for it. -/
def generatedExecInventory (workers : List QuotedWorker) : List Atom :=
  workers.map QuotedWorker.lift

@[simp] theorem generatedExecInventory_length (workers : List QuotedWorker) :
    (generatedExecInventory workers).length = workers.length := by
  simp [generatedExecInventory]

theorem mem_generatedExecInventory_iff (workers : List QuotedWorker)
    (directive : Atom) :
    directive ∈ generatedExecInventory workers ↔
      ∃ worker ∈ workers, worker.lift = directive := by
  simp [generatedExecInventory]

/-- The finite generated inventory is not merely a syntactic map: membership
is equivalent to successful instantiation by the authored clock template for
one stored worker. -/
theorem mem_generatedExecInventory_iff_clock_instantiation
    (workers : List QuotedWorker) (directive : Atom) :
    directive ∈ generatedExecInventory workers ↔
      ∃ worker ∈ workers,
        instantiateTemplateAtom? (clockSubstitution worker)
          clockLiftTemplate = some directive := by
  rw [mem_generatedExecInventory_iff]
  constructor
  · rintro ⟨worker, member, rfl⟩
    exact ⟨worker, member, clockLiftTemplate_instantiates worker⟩
  · rintro ⟨worker, member, instantiated⟩
    refine ⟨worker, member, ?_⟩
    rw [clockLiftTemplate_instantiates worker] at instantiated
    exact Option.some.inj instantiated

private def workerFixture : QuotedWorker := {
  key := .symbol "worker"
  pattern := .expression [.symbol ",", .expression
    [.symbol "w", .symbol "r", .var "x", .var "y"]]
  template := .expression [.symbol ",", .expression
    [.symbol "g", .symbol "r", .var "x", .var "y", .symbol "7"]]
}

/-- A flat direct-directive census misses a producer supplied by a quoted
worker, while the declared reflective closure contains it. -/
theorem direct_only_producer_census_misses_reflective_worker :
    (.symbol "r" : Atom) ∉
        (directProducerInventory [workerFixture.encode]).toFinset ∧
      (.symbol "r" : Atom) ∈ producerClosure [workerFixture.encode] := by
  decide +kernel

/-! ## Obligation budget feasibility -/

namespace ObligationBudget

universe uObligation

variable {Obligation : Type uObligation} [DecidableEq Obligation]

/-- One cursor action can discharge at most the named single obligation. -/
def run : Finset Obligation → List Obligation → Finset Obligation
  | pending, [] => pending
  | pending, action :: actions => run (pending.erase action) actions

/-- Each action removes at most one outstanding obligation. -/
theorem card_le_length_add_card_run (pending : Finset Obligation) :
    ∀ actions : List Obligation,
      pending.card ≤ actions.length + (run pending actions).card := by
  intro actions
  induction actions generalizing pending with
  | nil => simp [run]
  | cons action actions induction =>
      have eraseBound : pending.card ≤ (pending.erase action).card + 1 := by
        by_cases member : action ∈ pending
        · rw [Finset.card_erase_add_one member]
        · rw [Finset.erase_eq_of_notMem member]
          omega
      have tailBound := induction (pending.erase action)
      simp only [run, List.length_cons]
      omega

/-- A trace that discharges every obligation needs at least one action per
outstanding obligation under the single-discharge cursor contract. -/
theorem card_le_length_of_run_empty (pending : Finset Obligation)
    (actions : List Obligation) (complete : run pending actions = ∅) :
    pending.card ≤ actions.length := by
  have bound := card_le_length_add_card_run pending actions
  simpa [complete] using bound

/-- Structural completion and semantic-obligation completion share decoder
actions.  Without a disjoint-cost certificate, `max` is the sound combined
lower bound; adding the two bounds can double-count one action. -/
theorem max_lowerBound_le
    {structural obligation traceLength : Nat}
    (structuralBound : structural ≤ traceLength)
    (obligationBound : obligation ≤ traceLength) :
    max structural obligation ≤ traceLength :=
  max_le structuralBound obligationBound

theorem no_completion_within_of_remaining_lt_max
    {structural obligation remaining : Nat}
    (tooSmall : remaining < max structural obligation) :
    ¬ ∃ traceLength,
        traceLength ≤ remaining ∧
        structural ≤ traceLength ∧ obligation ≤ traceLength := by
  rintro ⟨traceLength, within, structuralBound, obligationBound⟩
  have := max_lowerBound_le structuralBound obligationBound
  omega

/-- Negative fixture: one action may simultaneously fill the last syntax
hole and discharge the last semantic obligation.  An additive lower bound
would reject this valid one-step completion. -/
theorem additive_lowerBounds_can_double_count :
    max 1 1 ≤ 1 ∧ ¬ 1 + 1 ≤ 1 := by
  decide

end ObligationBudget

/-! ## Shared-witness composition for semantic observers -/

namespace Observer

universe uBase uAction

variable {Base : Type uBase} {Action : Type uAction}

def AcceptsTrace
    (observer : SemanticObserver.Observer.{uBase, uAction, 0}
      Base Action)
    (base : Base)
    (edges : List (Edge Base Action)) : Prop :=
  ∃ finalObservation,
    observer.run (observer.initial base) edges = some finalObservation ∧
      observer.terminal finalObservation

theorem product_acceptsTrace_iff
    (left : SemanticObserver.Observer.{uBase, uAction, 0}
      Base Action)
    (right : SemanticObserver.Observer.{uBase, uAction, 0}
      Base Action)
    (base : Base) (edges : List (Edge Base Action)) :
    AcceptsTrace (left.product right) base edges ↔
      AcceptsTrace left base edges ∧ AcceptsTrace right base edges := by
  constructor
  · rintro ⟨finalObservation, run, terminal⟩
    have separate :=
      (SemanticObserver.Observer.product_run_eq_some_iff left right edges
        (left.initial base, right.initial base) finalObservation).mp run
    exact
      ⟨⟨finalObservation.1, separate.1, terminal.1⟩,
        ⟨finalObservation.2, separate.2, terminal.2⟩⟩
  · rintro ⟨⟨leftFinal, leftRun, leftTerminal⟩,
      ⟨rightFinal, rightRun, rightTerminal⟩⟩
    refine ⟨(leftFinal, rightFinal), ?_, leftTerminal, rightTerminal⟩
    exact (SemanticObserver.Observer.product_run_eq_some_iff left right edges
      (left.initial base, right.initial base) (leftFinal, rightFinal)).mpr
        ⟨leftRun, rightRun⟩

/-- Three layers are non-stranding on a canonical trace only when they share
that same trace witness.  Separate existential suffixes are insufficient. -/
theorem triple_acceptsTrace_iff
    (syntaxObserver :
      SemanticObserver.Observer.{uBase, uAction, 0} Base Action)
    (bindingObserver :
      SemanticObserver.Observer.{uBase, uAction, 0} Base Action)
    (protocolObserver :
      SemanticObserver.Observer.{uBase, uAction, 0} Base Action)
    (base : Base) (edges : List (Edge Base Action)) :
    AcceptsTrace
        ((syntaxObserver.product bindingObserver).product protocolObserver)
        base edges ↔
      AcceptsTrace syntaxObserver base edges ∧
        AcceptsTrace bindingObserver base edges ∧
          AcceptsTrace protocolObserver base edges := by
  rw [product_acceptsTrace_iff, product_acceptsTrace_iff]
  tauto

end Observer

/-! ## Scheduler-sensitive and scheduler-insensitive names -/

private def schedulerExec (schedulerName payload : String) : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "0", .symbol schedulerName],
      .expression [.symbol ","],
      .expression [.symbol ",", .expression
        [.symbol "g", .symbol payload, .symbol "0", .symbol "0",
          .symbol "1"]]]

private def lowPayloadFact : SourceExecFact :=
  (extractSupportedSourceExecFact (schedulerExec "a" "left")).get
    (by decide)

private def highPayloadFact : SourceExecFact :=
  (extractSupportedSourceExecFact (schedulerExec "z" "right")).get
    (by decide)

private def renamedLowPayloadFact : SourceExecFact :=
  (extractSupportedSourceExecFact (schedulerExec "z" "left")).get
    (by decide)

private def renamedHighPayloadFact : SourceExecFact :=
  (extractSupportedSourceExecFact (schedulerExec "a" "right")).get
    (by decide)

/-- Scheduler names are semantic for finite execution: swapping only those
names changes which payload is selected first. -/
theorem scheduler_name_swap_changes_first_directive :
    selectNextScheduled [highPayloadFact, lowPayloadFact] =
        some lowPayloadFact ∧
      selectNextScheduled [renamedHighPayloadFact, renamedLowPayloadFact] =
        some renamedHighPayloadFact := by
  decide +kernel

private def alphaLeft : Atom :=
  .expression [.symbol "pair", .var "x", .var "x"]

private def alphaRight : Atom :=
  .expression [.symbol "pair", .var "renamed", .var "renamed"]

/-- In contrast, consistent variable spelling changes are erased by the
physical compact key on this non-scheduler fixture. -/
theorem alpha_spelling_fixture_has_same_physical_key :
    morkSupportKey alphaLeft = morkSupportKey alphaRight := by
  decide +kernel

/-- The physical support layer therefore coalesces the alpha-spelling
fixture, while the scheduler-name theorem above forbids a general key
canonicalization claim. -/
theorem alpha_spelling_fixture_coalesces :
    morkInsertSupport [alphaLeft] alphaRight = [alphaLeft] := by
  decide +kernel

#print axioms clockLiftTemplate_instantiates
#print axioms clock_without_template_capture_is_rejected
#print axioms mem_producerClosure_iff
#print axioms mem_generatedExecInventory_iff_clock_instantiation
#print axioms direct_only_producer_census_misses_reflective_worker
#print axioms ObligationBudget.card_le_length_of_run_empty
#print axioms ObligationBudget.no_completion_within_of_remaining_lt_max
#print axioms ObligationBudget.additive_lowerBounds_can_double_count
#print axioms Observer.product_acceptsTrace_iff
#print axioms Observer.triple_acceptsTrace_iff
#print axioms scheduler_name_swap_changes_first_directive
#print axioms alpha_spelling_fixture_has_same_physical_key

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2OEISFragment
