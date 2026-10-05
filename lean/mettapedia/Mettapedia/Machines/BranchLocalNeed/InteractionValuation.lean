import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Machines.BranchLocalNeed.InteractionAuthority
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.GSLT.Core.CostedOperational
import Mettapedia.GSLT.Dynamics.StepSpendObservation
import Mettapedia.Algebra.SharedCoefficientLedger
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Cost and sharing of occurrence-authenticated reference Need paths

The reference machine already carries an exact abstract transition clock.
The generic interaction-path event count agrees with that clock: no
independent cost semantics is introduced. Completed-cache observations classify
actual productions and deliveries while retaining every machine-occurrence
position. Their total chronological valuation composes with the existing
partial valuations and erases without changing their acceptance or result.
Production accounts are valid by the actual lifecycle and fold in chronological
order without charging cached deliveries again. These projections alone are not
a full endpoint or source-version replay key. Richer physical costs, evidence,
provenance, and attention may be product valuations over the same events.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation

open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

/-- The reference transition metric is the existing constant writer grading.
It counts authentic machine transitions, not the other runtime event kinds. -/
abbrev transitionSpend
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  WriterGSLT.constGrading (machineTheory spec) (Multiplicative.ofAdd (1 : Nat))

/-- Forgetting the meter preserves and reflects the actual reference machine's
steps. The generic writer cover supplies both directions. -/
def transitionMeterErasure
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    SemanticCoveredTranslation
      ((machineTheory spec).spendLift (transitionSpend spec)) (machineTheory spec) :=
  spendErasureCover (transitionSpend spec)
    (WriterGSLT.constGrading_total _)

theorem metered_step_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat) :
    ((machineTheory spec).spendLift (transitionSpend spec)).Step
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after) ↔
      (machineTheory spec).Step source target ∧ after = before + 1 := by
  change (∃ grade, ((machineTheory spec).Step source target ∧
    grade = Multiplicative.ofAdd (1 : Nat)) ∧
    Multiplicative.ofAdd after = Multiplicative.ofAdd before * grade) ↔ _
  constructor
  · rintro ⟨grade, ⟨step, rfl⟩, accumulated⟩
    exact ⟨step, congrArg Multiplicative.toAdd accumulated⟩
  · rintro ⟨step, accumulated⟩
    exact ⟨Multiplicative.ofAdd 1, ⟨step, rfl⟩,
      congrArg Multiplicative.ofAdd accumulated⟩

/-- The meter cannot change a cost-blind behavioural observation of this
machine. Cost inspection itself requires a richer observation than erasure. -/
theorem metered_bisimilar_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat) :
    ((machineTheory spec).spendLift (transitionSpend spec)).Bisimilar
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after) ↔
      (machineTheory spec).Bisimilar source target :=
  WriterGSLT.spendLift_bisimilar_iff (transitionSpend spec)
    (WriterGSLT.constGrading_total _) _ _

/-- When the meter begins at the existing clock, an actual metered step keeps
them aligned. No independent transition count is assigned to the evaluator. -/
theorem metered_step_preserves_clock
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat)
    (aligned : before = source.work.transitions)
    (metered : ((machineTheory spec).spendLift (transitionSpend spec)).Step
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after)) :
    after = target.work.transitions := by
  obtain ⟨⟨occurrence⟩, accumulated⟩ := (metered_step_iff spec source target before after).mp metered
  rw [accumulated, aligned, step_increments_transition spec source target (occurrence.mem spec)]

/-- The reference transition counter is exactly the length of every
occurrence-authenticated interaction path. -/
theorem transitions_eq_pathLength
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    → (path : EventPath (machinePresentation spec) initial final) →
      final.work.transitions = initial.work.transitions +
        EventPath.pathLength (machinePresentation spec) path
  | _, _, .nil _ => rfl
  | source, target, .cons (middle := middle) (site := site) event rest => by
      have occurrence : StepOccurrence spec source middle :=
        { index := site
          successorAt := event.successorAt }
      have oneStep := step_increments_transition spec source middle
        (occurrence.mem spec)
      have inductionHypothesis := transitions_eq_pathLength spec rest
      calc
        target.work.transitions = middle.work.transitions +
            EventPath.pathLength (machinePresentation spec) rest :=
          inductionHypothesis
        _ = (source.work.transitions + 1) +
            EventPath.pathLength (machinePresentation spec) rest := by
          rw [oneStep]
        _ = source.work.transitions +
            EventPath.pathLength (machinePresentation spec)
              (.cons event rest) := by
          simp only [EventPath.pathLength]
          omega

/-- The generic event-count valuation and reference work clock report
the same exact count on every authenticated path. -/
theorem eventCount_matches_workClock
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : EventPath (machinePresentation spec) initial final) :
    EventPath.grade (machinePresentation spec)
        (EventPath.eventCountValuation (machinePresentation spec)) path =
        some (EventPath.pathLength (machinePresentation spec) path) ∧
      final.work.transitions = initial.work.transitions +
        EventPath.pathLength (machinePresentation spec) path :=
  ⟨EventPath.eventCount_grade (machinePresentation spec) path,
    transitions_eq_pathLength spec path⟩

/-! ## Chronological completed-cache observations -/

/-- Every machine occurrence keeps its position, with an optional completed
receipt classification. A non-cache instruction is retained as `none`, not
silently removed. This projection alone is not an endpoint replay key. -/
abbrev completedReceiptValuation
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Valuation (Occurrence (machinePresentation spec)) :=
  chronological fun event => (event.2.site, completedReceipt? event.1)

theorem completedReceiptValuation_total
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (completedReceiptValuation spec).IsTotal :=
  { grade_some := fun _event => ⟨_, rfl⟩
    op_some := fun _first _second => ⟨_, rfl⟩ }

/-- The history observer is the chronological image of actual authenticated
events, including repetitions and non-cache instruction positions. -/
theorem completed_receipt_history_exact
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : EventPath (machinePresentation spec) initial final) :
    EventPath.grade (machinePresentation spec) (completedReceiptValuation spec) path =
      some ((EventPath.events (machinePresentation spec) path).map
        fun event => (event.2.site, completedReceipt? event.1)) :=
  chronological_historyGrade _ _

theorem completed_receipt_history_append
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial middle final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (first : EventPath (machinePresentation spec) initial middle)
    (second : EventPath (machinePresentation spec) middle final) :
    EventPath.grade (machinePresentation spec) (completedReceiptValuation spec)
        (EventPath.append (machinePresentation spec) first second) =
      some (((EventPath.events (machinePresentation spec) first).map
        fun event => (event.2.site, completedReceipt? event.1)) ++
        ((EventPath.events (machinePresentation spec) second).map
          fun event => (event.2.site, completedReceipt? event.1))) := by
  rw [completed_receipt_history_exact]
  have joined := congrArg
    (fun events : List (Occurrence (machinePresentation spec)) =>
      some (events.map fun event => (event.2.site, completedReceipt? event.1)))
    (EventPath.events_append (machinePresentation spec) first second)
  simpa only [List.map_append] using joined

/-- A total observational coordinate cannot change acceptance or the result
of an independently selected weight/resource valuation. -/
theorem completed_receipt_history_erasure
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (valuation : Valuation (Occurrence (machinePresentation spec)))
    {initial final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : EventPath (machinePresentation spec) initial final) :
    Option.map Prod.fst
        (EventPath.grade (machinePresentation spec)
          (valuation.prod (completedReceiptValuation spec)) path) =
      EventPath.grade (machinePresentation spec) valuation path :=
  Valuation.map_fst_prod_historyGrade_of_right_total _ _
    (completedReceiptValuation_total spec) _

/-- Each completed annotation is checked against its actual target, rather
than deriving correctness from the annotated graph's own validity flag. -/
theorem completed_receipt_event_sound
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (event : Occurrence (machinePresentation spec))
    (receipt : CompletedReceipt Value StableFault RetryableFault)
    (classified : completedReceipt? event.1 = some receipt) :
    event.2.target.world.receipts.nodes =
      ⟨receipt.id, event.1.world.receipts.roots, .observe receipt.cell receipt.outcome⟩ ::
        event.1.world.receipts.nodes ∧
      event.2.target.world.receipts.roots = [receipt.id] ∧
      event.2.target.world.receipts.nextSerial = event.1.world.receipts.nextSerial + 1 := by
  exact completedReceipt?_step_receipt spec classified
    (({ index := event.2.site, successorAt := event.2.evidence.successorAt } :
      StepOccurrence spec event.1 event.2.target).mem spec)


/-! ## Production accounts of authentic paths

The reference lifecycle supplies production uniqueness before any ledger is
constructed. The account reuses the shared-coefficient ledger and existing
multiplicative valuation algebra, preserving order even for noncommutative
coefficients. Deliveries remain in chronological history and work accounting.

This is an incremental account: an already completed imported cell needs its
retained earlier ledger or external provenance. Logical receipt identities do
not establish C serial correspondence, physical lifetimes, or permissions for
parallel execution. The coefficient assignment here is total; suspended native
coefficient callbacks require their own refinement.
-/

open Mettapedia.Algebra.SharedCoefficientLedger

local notation "MachineState" =>
  Machine Origin Local Resume Rule Value StableFault RetryableFault Effect

/-- An authenticated interaction path supplies the reference machine's actual transition relation, including every intermediate instruction. -/
theorem eventPath_steps
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    {initial final : MachineState} →
    (path : EventPath (machinePresentation spec) initial final) →
    Steps spec (EventPath.pathLength (machinePresentation spec) path) initial final
  | _, _, .nil _ => .refl _
  | initial, _, .cons (middle := middle) (site := site) event rest => by
    simpa only [EventPath.pathLength, Nat.add_comm 1] using
      Steps.cons (⟨site, event.successorAt⟩ : StepOccurrence spec initial middle)
        (eventPath_steps spec rest)

/-- Keep the production role derived from the actual source machine.
A cached delivery and a non-cache instruction contribute no new factor. -/
def productionReceipt?
    (source : MachineState) : Option (CompletedReceipt Value StableFault RetryableFault) := do
  let receipt ← completedReceipt? source
  if receipt.kind = .production then some receipt else none

/-- The production filter neither invents a completed receipt nor
changes its independently checked role. -/
theorem productionReceipt?_iff {source : MachineState}
    {receipt : CompletedReceipt Value StableFault RetryableFault} :
    productionReceipt? source = some receipt ↔
      completedReceipt? source = some receipt ∧ receipt.kind = .production := by
  unfold productionReceipt?
  dsimp only [bind, Option.bind]
  cases classified : completedReceipt? source with
  | none => simp
  | some actual =>
    dsimp only [bind, Option.bind]
    by_cases production : actual.kind = .production
    · simp only [if_pos production, Option.some.injEq]
      constructor
      · intro same
        subst receipt
        exact ⟨rfl, production⟩
      · exact fun accepted => accepted.1
    · simp only [if_neg production, reduceCtorEq, false_iff, Option.some.injEq]
      rintro ⟨same, produced⟩
      cases same
      exact production produced

/-- Production occurrences in their actual chronological order.
This projection is an accounting observer, not a replacement for full history. -/
def productionReceipts
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final) :=
  (EventPath.events (machinePresentation spec) path).filterMap
    fun event => productionReceipt? event.1

/-- Accounting retains a head production exactly when the actual
head instruction completes one. -/
theorem productionReceipts_cons
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial middle final : MachineState} {site : Nat}
    (event : OccurrenceEvidence spec site initial middle)
    (rest : EventPath (machinePresentation spec) middle final) :
    productionReceipts spec (.cons event rest) =
      (productionReceipt? initial).toList ++ productionReceipts spec rest := by
  simp only [productionReceipts, EventPath.events, List.filterMap_cons]
  cases productionReceipt? initial <;> rfl

/-- Each accounting receipt comes from a particular authenticated
source occurrence with the production role. -/
theorem mem_productionReceipts
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final)
    (receipt : CompletedReceipt Value StableFault RetryableFault) :
    receipt ∈ productionReceipts spec path ↔
      ∃ event ∈ EventPath.events (machinePresentation spec) path,
        completedReceipt? event.1 = some receipt ∧ receipt.kind = .production := by
  rw [productionReceipts, List.mem_filterMap]
  constructor
  · rintro ⟨event, member, classified⟩
    exact ⟨event, member, productionReceipt?_iff.mp classified⟩
  · rintro ⟨event, member, classified⟩
    exact ⟨event, member, productionReceipt?_iff.mpr classified⟩

/-- A completed cell at the beginning of a path cannot produce again
later on that path. Imported completed cells require an earlier ledger account. -/
theorem completed_cell_absent_from_productionReceipts
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final)
    {cell : CellId} {record : CellRecord Origin Value StableFault}
    (cached : initial.world.heap.lookup cell = some record)
    (completed : Cache.Completed record.cache) :
    cell ∉ (productionReceipts spec path).map CompletedReceipt.cell := by
  intro member
  obtain ⟨receipt, present, same⟩ := List.mem_map.mp member
  obtain ⟨event, eventMember, classified, production⟩ :=
    (mem_productionReceipts spec path receipt).mp present
  obtain ⟨priorPath⟩ := EventPath.mem_events_prefix (machinePresentation spec) path event eventMember
  exact (steps_completed_cache_forbids_production spec
    (eventPath_steps spec priorPath) cached completed classified same) production

/-- The lifecycle itself gives path-local production uniqueness;
ledger validity is a conclusion, not a supplied premise. Sibling paths remain separate. -/
theorem production_cells_nodup
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    {initial final : MachineState} →
    (path : EventPath (machinePresentation spec) initial final) →
    ((productionReceipts spec path).map CompletedReceipt.cell).Nodup
  | _, _, .nil _ => List.nodup_nil
  | initial, _, .cons (middle := middle) (site := site) event rest => by
    have consEq := productionReceipts_cons spec event rest
    apply (congrArg
      (fun receipts : List (CompletedReceipt Value StableFault RetryableFault) =>
        (receipts.map CompletedReceipt.cell).Nodup) consEq).mpr
    cases classified : productionReceipt? initial with
    | none => simpa using production_cells_nodup spec rest
    | some receipt =>
      simp only [Option.toList_some, List.singleton_append, List.map_cons, List.nodup_cons]
      obtain ⟨classified, production⟩ := productionReceipt?_iff.mp classified
      obtain ⟨record, cached, completed⟩ :=
        (completedReceipt?_witness initial receipt classified).production_completes_cache spec
          ((⟨site, event.successorAt⟩ : StepOccurrence spec initial middle).mem spec) production
      exact ⟨completed_cell_absent_from_productionReceipts spec rest cached completed,
        production_cells_nodup spec rest⟩


variable {V : Type*}

/-- An incremental production account in the existing shared-factor
ledger. The identity includes the cell and its actual receipt occurrence.
The coefficient function is total; resolving native callbacks remains a separate obligation. -/
def productionLedger
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final) :
    Ledger (CellId × ReceiptId) (Produced Value StableFault RetryableFault) V :=
  (productionReceipts spec path).map fun receipt =>
    ⟨(receipt.cell, receipt.id), receipt.outcome, coefficient receipt⟩

/-- Every authentic reference path produces a valid identity ledger
without assuming validity of a supplied ledger or graph. -/
theorem productionLedger_valid
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final) :
    Valid (productionLedger spec coefficient path) := by
  apply List.Nodup.of_map Prod.fst
  simpa only [Valid, identities, productionLedger, List.map_map, Function.comp_def] using
    production_cells_nodup spec path

/-- Resumption concatenates incremental production accounts in the
same order as the authentic paths. -/
theorem productionLedger_append
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    {initial middle final : MachineState}
    (first : EventPath (machinePresentation spec) initial middle)
    (second : EventPath (machinePresentation spec) middle final) :
    productionLedger spec coefficient
        (EventPath.append (machinePresentation spec) first second) =
      productionLedger spec coefficient first ++ productionLedger spec coefficient second := by
  have joined := congrArg
    (fun events : List (Occurrence (machinePresentation spec)) =>
      (events.filterMap fun event => productionReceipt? event.1).map fun receipt =>
        (⟨(receipt.cell, receipt.id), receipt.outcome, coefficient receipt⟩ :
          Factor (CellId × ReceiptId) (Produced Value StableFault RetryableFault) V))
    (EventPath.events_append (machinePresentation spec) first second)
  simpa only [productionLedger, productionReceipts, List.filterMap_append, List.map_append]
    using joined

/-- Production grades compose chronologically in any monoid.
Commutativity is not required and cannot be inferred from answer equality. -/
theorem productionLedger_denote_append [Monoid V]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    {initial middle final : MachineState}
    (first : EventPath (machinePresentation spec) initial middle)
    (second : EventPath (machinePresentation spec) middle final) :
    denote (productionLedger spec coefficient
        (EventPath.append (machinePresentation spec) first second)) =
      denote (productionLedger spec coefficient first) *
        denote (productionLedger spec coefficient second) := by
  rw [productionLedger_append, denote_append]

/-- The per-occurrence semantic grade uses the existing monoidal
valuation algebra. Deliveries and other instructions have neutral factor one. -/
def productionValuation [Monoid V]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V) :
    Mettapedia.GSLT.Dynamics.IndexedEventValuation.Valuation
      (Occurrence (machinePresentation spec)) where
  Grade := V
  algebra := Mettapedia.GSLT.Dynamics.StepSpendObservation.multiplicativePartialMonoid V
  grade := fun event => some ((productionReceipt? event.1).elim 1 coefficient)

/-- A total coefficient assignment gives a total accounting observer.
This law does not assert that every runtime callback has already been evaluated. -/
theorem productionValuation_total [Monoid V]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V) :
    (productionValuation spec coefficient).IsTotal :=
  { grade_some := fun _ => ⟨_, rfl⟩
    op_some := fun _ _ => ⟨_, rfl⟩ }

/-- The independently defined per-occurrence grade folds to exactly
the chronological shared-factor ledger of the actual path. -/
theorem production_history_grade [Monoid V]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    {initial final : MachineState}
    (path : EventPath (machinePresentation spec) initial final) :
    EventPath.grade (machinePresentation spec) (productionValuation spec coefficient) path =
      some (denote (productionLedger spec coefficient path)) := by
  have fold : ∀ events : List (Occurrence (machinePresentation spec)),
      (productionValuation spec coefficient).historyGrade events =
        some (((events.filterMap fun event => productionReceipt? event.1).map coefficient).prod) := by
    intro events
    induction events with
    | nil => rfl
    | cons event rest ih =>
      rw [Mettapedia.GSLT.Dynamics.IndexedEventValuation.Valuation.historyGrade_cons, ih]
      cases classified : productionReceipt? event.1 <;>
        simp [productionValuation, classified,
          Mettapedia.GSLT.Dynamics.StepSpendObservation.multiplicativePartialMonoid]
  simpa only [EventPath.grade, productionLedger, productionReceipts, denote,
    List.map_map, Function.comp_def] using fold (EventPath.events (machinePresentation spec) path)

/-- A checked cached delivery does not multiply its production
coefficient again. Its transition still belongs to the full work/history observers. -/
theorem cached_delivery_factor_is_one [Monoid V]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (event : Occurrence (machinePresentation spec))
    {receipt : CompletedReceipt Value StableFault RetryableFault}
    (classified : completedReceipt? event.1 = some receipt)
    (delivery : receipt.kind = .delivery) :
    (productionValuation spec coefficient).grade event = some (1 : V) := by
  simp [productionValuation, productionReceipt?, classified, delivery]


namespace ProductionLedgerControls

open CompletedReceiptControls (spec start)

private def stage : Nat → Machine Unit Nat Nat Unit Nat Unit Unit Unit
  | 0 => start
  | depth + 1 => (step spec (stage depth)).headD start

private def sharedPath : EventPath (machinePresentation spec) start (stage 7) :=
  .cons (middle := stage 1) (site := (0 : Nat)) ⟨rfl⟩
    (.cons (middle := stage 2) (site := (0 : Nat)) ⟨rfl⟩
      (.cons (middle := stage 3) (site := (0 : Nat)) ⟨rfl⟩
        (.cons (middle := stage 4) (site := (0 : Nat)) ⟨rfl⟩
          (.cons (middle := stage 5) (site := (0 : Nat)) ⟨rfl⟩
            (.cons (middle := stage 6) (site := (0 : Nat)) ⟨rfl⟩
              (.cons (middle := stage 7) (site := (0 : Nat)) ⟨rfl⟩ (.nil _)))))))

theorem one_production_many_deliveries :
    (productionLedger spec (fun _ => (2 : Nat)) sharedPath).map Factor.coefficient = [2] ∧
      ((EventPath.events (machinePresentation spec) sharedPath).filterMap
        fun event => completedReceipt? event.1).length = 3 := by decide

theorem graded_production_and_all_step_work :
    EventPath.grade (machinePresentation spec)
        (productionValuation spec (fun _ => (2 : Nat))) sharedPath = some (2 : Nat) ∧
      EventPath.grade (machinePresentation spec)
        (EventPath.eventCountValuation (machinePresentation spec)) sharedPath = some (7 : Nat) := by
  constructor
  · calc
      _ = some (denote (productionLedger spec (fun _ => (2 : Nat)) sharedPath)) :=
        production_history_grade spec (fun _ => (2 : Nat)) sharedPath
      _ = some (2 : Nat) := by decide
  · calc
      _ = some (EventPath.pathLength (machinePresentation spec) sharedPath) :=
        EventPath.eventCount_grade (machinePresentation spec) sharedPath
      _ = some (7 : Nat) := rfl

theorem per_delivery_charge_is_wrong :
    denote (productionLedger spec (fun _ => (2 : Nat)) sharedPath) ≠
      (((EventPath.events (machinePresentation spec) sharedPath).filterMap
        fun event => completedReceipt? event.1).map fun _ => (2 : Nat)).prod := by decide

theorem zero_factor_retains_production :
    (productionLedger spec (fun _ => (0 : Nat)) sharedPath).length = 1 ∧
      denote (productionLedger spec (fun _ => (0 : Nat)) sharedPath) = 0 ∧
      EventPath.pathLength (machinePresentation spec) sharedPath = 7 := by decide

private def secondCell : CellId := ⟨1, [], 1, 0⟩

private def twoStart : Machine Unit Nat Nat Unit Nat Unit Unit Unit :=
  { start with
    world := { start.world with
      heap := {
        current := fun cell => if cell = secondCell then some ⟨(), .evaluating 4⟩
          else start.world.heap.lookup cell
        spine := .cache secondCell (.evaluating 4) :: .allocate secondCell () ::
          start.world.heap.spine } }
    control := .returned (.value 21) [.commit ⟨1, [], 0, 0⟩ 3, .commit secondCell 4] }

private def twoStage : Nat → Machine Unit Nat Nat Unit Nat Unit Unit Unit
  | 0 => twoStart
  | depth + 1 => (step spec (twoStage depth)).headD twoStart

private def twoPath : EventPath (machinePresentation spec) twoStart (twoStage 2) :=
  .cons (middle := twoStage 1) (site := (0 : Nat)) ⟨rfl⟩
    (.cons (middle := twoStage 2) (site := (0 : Nat)) ⟨rfl⟩ (.nil _))

private def orderedCoefficient (receipt : CompletedReceipt Nat Unit Unit) : FreeMonoid Nat :=
  FreeMonoid.of receipt.cell.slot

theorem equal_outcomes_retain_two_productions :
    (productionLedger spec orderedCoefficient twoPath).length = 2 ∧
      (productionReceipts spec twoPath).map CompletedReceipt.outcome =
        [.value 21, .value 21] := by decide

theorem ordered_production_word :
    FreeMonoid.toList (denote (productionLedger spec orderedCoefficient twoPath)) = [0, 1] := rfl

theorem reversing_productions_changes_grade :
    denote (productionLedger spec orderedCoefficient twoPath) ≠
      denote (productionLedger spec orderedCoefficient twoPath).reverse := by
  intro equal
  have words := congrArg FreeMonoid.toList equal
  change ([0, 1] : List Nat) = [1, 0] at words
  cases words

end ProductionLedgerControls


/-! ## Positive canary -/

namespace Canary

open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority.Canary

def oneStepPath :
    EventPath (machinePresentation demoSpec) start next :=
  .cons ⟨firstOccurrence.successorAt⟩
    (.nil (presentation := machinePresentation demoSpec) next)

theorem one_step_grade_and_clock :
    EventPath.grade (machinePresentation demoSpec)
        (EventPath.eventCountValuation (machinePresentation demoSpec))
        oneStepPath = some 1 ∧
      next.work.transitions = start.work.transitions + 1 := by
  exact eventCount_matches_workClock demoSpec oneStepPath

theorem metered_transition_advances :
    ((machineTheory demoSpec).spendLift (transitionSpend demoSpec)).Step
      (start, Multiplicative.ofAdd 4) (next, Multiplicative.ofAdd 5) :=
  (metered_step_iff demoSpec start next 4 5).mpr ⟨⟨firstOccurrence⟩, rfl⟩

theorem transition_does_not_reset_meter :
    ¬((machineTheory demoSpec).spendLift (transitionSpend demoSpec)).Step
      (start, Multiplicative.ofAdd 4) (next, Multiplicative.ofAdd 1) := by
  rw [metered_step_iff]
  rintro ⟨_, impossible⟩
  omega

end Canary

end Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
