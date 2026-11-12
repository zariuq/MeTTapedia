import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.RowWorlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.HEMachine

/-!
# HE's machine on the step with honest read footprints

`HEOnTheStep.HEMachine` placed HE's read-only machine on the step with its space as one occurrence,
so every move that kept the space read all of it, `(p a)` included. Here the space is one
occurrence per row (`RowWorlds`), and each move of HE's machine declares the region of rows it
depends on (`heFoot`):

* an **equation query** (`callAbsent`, `callEquations`, `invocationAbsent`, `invocationEquations`)
  depends on the rows of its region (`eqRegion`): the rows that are not inert for the query, where a
  row is inert when its only possible contribution to the complete frontier is nothing (it is not an
  equation, or every fresh variant of it misses). Its firing reads the matched rows and observes that
  the region holds nothing else: the matched rows plus an absence guard;
* the moves that consult the cast lookup, the argument admission service, the context payload of
  the space, or a completed native return depend on the whole space: those services are parameters
  of the machine, so nothing smaller is honest for them in this generality;
* every other move reads no row.

## Results

* `frontier_transfer`: an equation frontier depends on the space only through the rows of its region,
  with their positions.
* `localStep_transfer`: **every transition rule of HE's machine (all 81) depends on the space only
  through the rows of its footprint**.
* `he_rows_on_the_step`: HE's read-only machine is strongly bisimilar to the step under its
  footprinted rules (`RowWorlds.row_bisimulation`); `he_rows_outcomes_eq` reads off the answers and
  the rows; `he_reads_exact` states that a firing reads exactly the rows of its region.

## Controls

* `eqRegion_not_equation`, `Controls.pa_outside`: a row that is not an equation, such as `(p a)`, is
  outside every equation query's region, so no equation query reads it (H1's `reads_differ` row).
* `Controls.tuple_reads_nothing`: every firing from a store whose pending work is a tuple reads no
  row; H1's encoding read the whole space there.
* `Controls.fixture_region`: on the tree's frontier fixture (`(= a result)`, `metadata`,
  `(= b missed)`, `(= a result)`) the query `a` has the two copies of `(= a result)`, at positions
  `0` and `3`, as its region's rows: the irrelevant row and the missed equation are outside.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith LocalStep)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation Task)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup)
open HEOnTheStep (heMachine he_local toConfig HEConfig Store Cell)
open FragmentsOfTheStep.TransitionMaps

/-! ## The region of an equation query -/

section EquationRegion

/-- A row is **inert** for an equation query when, at every position, its only possible block of
works is empty. -/
def Inert (live : List Atom) (query : Atom) (incoming : Mettapedia.Languages.MeTTa.HE.Bindings)
    (row : Atom) : Prop :=
  ∀ position block, EquationRowResultsRel live query incoming position row block ↔ block = []

open Classical in
/-- **The region of an equation query**: the rows that are not inert for it. -/
def eqRegion (live : List Atom) (query : Atom) (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) :
    Atom → Bool :=
  fun row => decide (¬ Inert live query incoming row)

theorem inert_of_eqRegion {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {row : Atom}
    (outside : ¬ eqRegion live query incoming row = true) : Inert live query incoming row := by
  simpa [eqRegion] using outside

theorem eqRegion_of_not_inert {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {row : Atom}
    (live' : ¬ Inert live query incoming row) : eqRegion live query incoming row = true := by
  simpa [eqRegion] using live'

/-- **A row that is not an equation is outside every equation query's region.** -/
theorem eqRegion_not_equation {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {row : Atom}
    (notEquation : ∀ left right, row ≠ .expression [.symbol "=", left, right]) :
    eqRegion live query incoming row = false := by
  have inert : Inert live query incoming row := by
    intro position block
    constructor
    · intro derived
      cases derived with
      | irrelevant => rfl
      | miss => exact absurd rfl (notEquation _ _)
      | hit => exact absurd rfl (notEquation _ _)
    · rintro rfl
      exact .irrelevant position row notEquation
  simpa [eqRegion] using inert

/-- A frontier over a list of positioned rows, as a relation. -/
def FrontierOver (live : List Atom) (query : Atom) (incoming : Mettapedia.Languages.MeTTa.HE.Bindings)
    (rows : List (Atom × ℕ)) (works : List EquationWork) : Prop :=
  ∃ blocks : List (List EquationWork), List.Forall₂ (fun row block =>
    EquationRowResultsRel live query incoming row.2 row.1 block) rows blocks ∧
      blocks.flatten = works

/-- **Inert rows contribute nothing**: the frontier over a list of rows is the frontier over its
rows in the region. -/
theorem frontierOver_filter_iff (live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) :
    ∀ (rows : List (Atom × ℕ)) (works : List EquationWork),
      FrontierOver live query incoming rows works ↔
        FrontierOver live query incoming
          (rows.filter fun p => eqRegion live query incoming p.1) works
  | [], _ => Iff.rfl
  | (row, position) :: rows, works => by
      by_cases inside : eqRegion live query incoming row = true
      · have shape : (((row, position) :: rows).filter fun p => eqRegion live query incoming p.1) =
            (row, position) :: rows.filter (fun p => eqRegion live query incoming p.1) := by
          simp [inside]
        rw [shape]
        constructor
        · rintro ⟨_ | ⟨block, blocks⟩, paired, rfl⟩
          · cases paired
          · obtain ⟨here, rest⟩ := List.forall₂_cons.mp paired
            obtain ⟨blocks', paired', same⟩ :=
              (frontierOver_filter_iff live query incoming rows blocks.flatten).mp ⟨blocks, rest, rfl⟩
            exact ⟨block :: blocks', List.Forall₂.cons here paired', by simp [same]⟩
        · rintro ⟨_ | ⟨block, blocks⟩, paired, rfl⟩
          · cases paired
          · obtain ⟨here, rest⟩ := List.forall₂_cons.mp paired
            obtain ⟨blocks', paired', same⟩ :=
              (frontierOver_filter_iff live query incoming rows blocks.flatten).mpr ⟨blocks, rest, rfl⟩
            exact ⟨block :: blocks', List.Forall₂.cons here paired', by simp [same]⟩
      · have inert := inert_of_eqRegion inside
        have shape : (((row, position) :: rows).filter fun p => eqRegion live query incoming p.1) =
            rows.filter (fun p => eqRegion live query incoming p.1) := by
          simp [inside]
        rw [shape]
        constructor
        · rintro ⟨_ | ⟨block, blocks⟩, paired, rfl⟩
          · cases paired
          · obtain ⟨here, rest⟩ := List.forall₂_cons.mp paired
            have empty := (inert position block).mp here
            subst empty
            exact (frontierOver_filter_iff live query incoming rows _).mp ⟨blocks, rest, by simp⟩
        · intro filtered
          obtain ⟨blocks, paired, same⟩ :=
            (frontierOver_filter_iff live query incoming rows works).mpr filtered
          exact ⟨[] :: blocks, List.Forall₂.cons ((inert position []).mpr rfl) paired, by simp [same]⟩

theorem frontier_iff (space : Space) (live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) (works : List EquationWork) :
    EquationFrontierRel space live query incoming works ↔
      FrontierOver live query incoming space.atoms.zipIdx works := by
  constructor
  · rintro ⟨covered⟩
    exact ⟨_, covered, rfl⟩
  · rintro ⟨blocks, covered, rfl⟩
    exact .completed covered

/-- **An equation frontier depends on the space only through its region's rows.** -/
theorem frontier_transfer {space space₀ : Space} {live : List Atom} {query : Atom}
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} {works : List EquationWork}
    (same : regionRows (eqRegion live query incoming) space.atoms =
      regionRows (eqRegion live query incoming) space₀.atoms)
    (frontier : EquationFrontierRel space live query incoming works) :
    EquationFrontierRel space₀ live query incoming works := by
  rw [frontier_iff, frontierOver_filter_iff] at frontier ⊢
  unfold regionRows at same
  rw [← same]
  exact frontier

end EquationRegion

/-! ## The footprint of HE's machine -/

section Footprint

open Classical in
/-- An atom's pending work: delivering it reads nothing; casting or interpreting it consults the
cast lookup or the argument admission service with the whole space. -/
def atomRegion (policy : Policy) (value : Entry.Value) (expected : Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) : Atom → Bool :=
  if Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .deliver then fun _ => false
  else fun _ => true

open Classical in
/-- A call: an error or an embedded instruction reads nothing; otherwise its equation query reads
its region. -/
def heCallRegion (live : List Atom) (value : Entry.Value) (expected : Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) : Control → Atom → Bool
  | .work (.invocation _ _ _ _ _) => fun _ => false
  | _ => if IsErrorRel value.erase then fun _ => false
      else eqRegion (expected :: live) value.erase activation.bindings

/-- An invocation: an embedded instruction reads nothing; otherwise its equation query reads its
region. -/
def invocationRegion (live : List Atom) (value : Entry.Value)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) : Control → Atom → Bool
  | .work (.minimal _ _ _ _ _) => fun _ => false
  | _ => eqRegion live value.erase activation.bindings

/-- `(context-space)` returns the whole space as a payload. -/
def minimalRegion : Entry.Value → Atom → Bool
  | .expression _ [.symbol "context-space"] => fun _ => true
  | _ => fun _ => false

/-- A completed native return with an expected type consults the cast lookup. -/
def boundaryRegion : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Boundary → Atom → Bool
  | .native _ (some _) .completed => fun _ => true
  | _ => fun _ => false

/-- The region of a move from pending work. -/
def taskRegion (policy : Policy) : Task → Control → Atom → Bool
  | .atom _ _ value expected activation, _ => atomRegion policy value expected activation
  | .call live _ value expected activation, after => heCallRegion live value expected activation after
  | .invocation live _ _ value activation, after => invocationRegion live value activation after
  | .minimal _ _ _ value _, _ => minimalRegion value
  | .boundary _ _ _ site _ _, _ => boundaryRegion site
  | _, _ => fun _ => false

/-- **The region of rows a move of HE's machine depends on**, from its control before and after.
Returning batches and context steps read no row of the space. -/
def heRegion (policy : Policy) : Control → Control → Atom → Bool
  | .work task, after => taskRegion policy task after
  | _, _ => fun _ => false

/-- **HE's footprint.** -/
def heFoot (policy : Policy) : Footprint Control Continuation Atom :=
  fun before _ after _ => heRegion policy before after

open Classical in
theorem heRegion_call_returning (policy : Policy) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) (results : List Result) :
    heRegion policy (.work (.call live scope value expected activation)) (.returning results) =
      if IsErrorRel value.erase then fun _ => false
      else eqRegion (expected :: live) value.erase activation.bindings := rfl

open Classical in
theorem heRegion_call_equations (policy : Policy) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    (works : List EquationWork) :
    heRegion policy (.work (.call live scope value expected activation))
        (.work (.equations live scope value expected activation works)) =
      if IsErrorRel value.erase then fun _ => false
      else eqRegion (expected :: live) value.erase activation.bindings := rfl

theorem heRegion_invocation_returning (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (value : Entry.Value)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) (results : List Result) :
    heRegion policy (.work (.invocation live scope caller value activation)) (.returning results) =
      eqRegion live value.erase activation.bindings := rfl

theorem heRegion_invocation_equations (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (value : Entry.Value)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    (works : List EquationWork) :
    heRegion policy (.work (.invocation live scope caller value activation))
        (.work (.invocationEquations live scope value activation works)) =
      eqRegion live value.erase activation.bindings := rfl

theorem heRegion_context_space (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (readiness : Entry.Status)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) (after : Control) :
    heRegion policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "context-space"])
          activation)) after = fun _ => true := rfl

theorem heRegion_native_completed (policy : Policy) (live : List Atom) (scope : List String)
    (caller : Option Atom) (original : Entry.Value) (expected : Atom) (value : Entry.Value)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) (after : Control) :
    heRegion policy
        (.work (.boundary live scope caller (.native original (some expected) .completed) value
          activation)) after = fun _ => true := rfl

theorem atomRegion_whole {policy : Policy} {value : Entry.Value} {expected : Atom}
    {activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame} {action : Entry.Action}
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected action) (notDeliver : action ≠ .deliver) :
    ∀ a, atomRegion policy value expected activation a = true := by
  intro a
  have refused : ¬ Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .deliver :=
    fun deliver => notDeliver (Entry.functional entry deliver)
  simp [atomRegion, refused]

/-- Two spaces with the same rows in the full region are the same space. -/
theorem space_eq_of_whole {space space₀ : Space} {ρ : Atom → Bool} (whole : ∀ a, ρ a = true)
    (same : regionRows ρ space.atoms = regionRows ρ space₀.atoms) : space = space₀ := by
  have all : ρ = fun _ => true := funext whole
  subst all
  rw [regionRows_all, regionRows_all] at same
  have atoms := eq_of_zipIdx_eq same
  cases space
  cases space₀
  cases atoms
  rfl

end Footprint

/-! ## Every transition depends on the space only through its footprint -/

section Transfer

variable {admission : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.ArgumentService}
  {dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch} {lookup : CastLookup}
  {policy : Policy}

/-- **Every transition rule of HE's machine depends on the space only through the rows of its
footprint**, with their positions: the same move is a transition at every space with those rows. -/
theorem localStep_transfer {space space₀ : Space} {c c' : Control} {s s' : List Continuation}
    (step : LocalStepWith admission space dispatch lookup policy (c, s) (c', s'))
    (same : regionRows (heRegion policy c c') space.atoms =
      regionRows (heRegion policy c c') space₀.atoms) :
    LocalStepWith admission space₀ dispatch lookup policy (c, s) (c', s') := by
  cases step
  case delivered => apply LocalStepWith.delivered; all_goals assumption
  case cast =>
    obtain rfl := space_eq_of_whole (atomRegion_whole ‹Entry.Rel _ _ _ _ .cast› (by decide)) same
    apply LocalStepWith.cast; all_goals assumption
  case atomTuple =>
    obtain rfl :=
      space_eq_of_whole (atomRegion_whole ‹Entry.Rel _ _ _ _ .interpret› (by decide)) same
    apply LocalStepWith.atomTuple; all_goals assumption
  case atomFunction =>
    obtain rfl :=
      space_eq_of_whole (atomRegion_whole ‹Entry.Rel _ _ _ _ .interpret› (by decide)) same
    apply LocalStepWith.atomFunction; all_goals assumption
  case atomFallback =>
    obtain rfl :=
      space_eq_of_whole (atomRegion_whole ‹Entry.Rel _ _ _ _ .interpret› (by decide)) same
    apply LocalStepWith.atomFallback; all_goals assumption
  case atomSelectionFailed =>
    obtain rfl :=
      space_eq_of_whole (atomRegion_whole ‹Entry.Rel _ _ _ _ .interpret› (by decide)) same
    apply LocalStepWith.atomSelectionFailed; all_goals assumption
  case tupleNil => apply LocalStepWith.tupleNil
  case tupleSingleton => apply LocalStepWith.tupleSingleton
  case tupleCons => apply LocalStepWith.tupleCons
  case branchesNil => apply LocalStepWith.branchesNil
  case branchesStopped => apply LocalStepWith.branchesStopped; all_goals assumption
  case branchesContinue => apply LocalStepWith.branchesContinue; all_goals assumption
  case argumentsNil => apply LocalStepWith.argumentsNil
  case argumentsCons => apply LocalStepWith.argumentsCons
  case argumentBranchesNil => apply LocalStepWith.argumentBranchesNil
  case argumentBranchesStopped => apply LocalStepWith.argumentBranchesStopped; all_goals assumption
  case argumentBranchesContinue => apply LocalStepWith.argumentBranchesContinue; all_goals assumption
  case functionStart => apply LocalStepWith.functionStart; all_goals assumption
  case functionBranchesNil => apply LocalStepWith.functionBranchesNil
  case functionBranchesStopped => apply LocalStepWith.functionBranchesStopped; all_goals assumption
  case functionBranchesContinue => apply LocalStepWith.functionBranchesContinue; all_goals assumption
  case invocationsNil => apply LocalStepWith.invocationsNil
  case invocationsCons => apply LocalStepWith.invocationsCons
  case callsNil => apply LocalStepWith.callsNil
  case callsCons => apply LocalStepWith.callsCons
  case callError => apply LocalStepWith.callError; all_goals assumption
  case callEmbedded => apply LocalStepWith.callEmbedded; all_goals assumption
  case callAbsent =>
    rw [heRegion_call_returning, if_neg ‹¬ IsErrorRel _›] at same
    exact .callAbsent ‹_› ‹_› (frontier_transfer same ‹_›)
  case callEquations =>
    rw [heRegion_call_equations, if_neg ‹¬ IsErrorRel _›] at same
    exact .callEquations ‹_› ‹_› (frontier_transfer same ‹_›) ‹_›
  case equationsNil => apply LocalStepWith.equationsNil
  case equationsCons => apply LocalStepWith.equationsCons; all_goals assumption
  case returnRefused => apply LocalStepWith.returnRefused; all_goals assumption
  case returnStopped => apply LocalStepWith.returnStopped; all_goals assumption
  case returnEvaluate => apply LocalStepWith.returnEvaluate; all_goals assumption
  case minimalData => apply LocalStepWith.minimalData; all_goals assumption
  case minimalEval => apply LocalStepWith.minimalEval
  case minimalEvalc => apply LocalStepWith.minimalEvalc; all_goals assumption
  case minimalChain => apply LocalStepWith.minimalChain
  case minimalUnifyYes => apply LocalStepWith.minimalUnifyYes; all_goals assumption
  case minimalUnifyNo => apply LocalStepWith.minimalUnifyNo; all_goals assumption
  case minimalUnifyBadArity => apply LocalStepWith.minimalUnifyBadArity; all_goals assumption
  case minimalConsAtom => apply LocalStepWith.minimalConsAtom
  case minimalDeconsAtom => apply LocalStepWith.minimalDeconsAtom
  case minimalFunction => apply LocalStepWith.minimalFunction; all_goals assumption
  case minimalMetta => apply LocalStepWith.minimalMetta; all_goals assumption
  case minimalContextSpace =>
    rw [heRegion_context_space] at same
    obtain rfl := space_eq_of_whole (fun _ => rfl) same
    apply LocalStepWith.minimalContextSpace; all_goals assumption
  case bodyStart => apply LocalStepWith.bodyStart
  case invocationEmbedded => apply LocalStepWith.invocationEmbedded; all_goals assumption
  case invocationAbsent =>
    rw [heRegion_invocation_returning] at same
    exact .invocationAbsent ‹_› (frontier_transfer same ‹_›)
  case invocationEquations =>
    rw [heRegion_invocation_equations] at same
    exact .invocationEquations ‹_› (frontier_transfer same ‹_›) ‹_›
  case invocationEquationsNil => apply LocalStepWith.invocationEquationsNil
  case invocationEquationsCons => apply LocalStepWith.invocationEquationsCons; all_goals assumption
  case boundaryChain => apply LocalStepWith.boundaryChain
  case boundaryBodyTerminal => apply LocalStepWith.boundaryBodyTerminal; all_goals assumption
  case boundaryBodyResume => apply LocalStepWith.boundaryBodyResume; all_goals assumption
  case boundaryFunctionReturn => apply LocalStepWith.boundaryFunctionReturn
  case boundaryFunctionNoReturn => apply LocalStepWith.boundaryFunctionNoReturn; all_goals assumption
  case boundaryProducerRaw => apply LocalStepWith.boundaryProducerRaw; all_goals assumption
  case boundaryProducerFunction => apply LocalStepWith.boundaryProducerFunction; all_goals assumption
  case boundaryReturned => apply LocalStepWith.boundaryReturned
  case boundaryBatchNil => apply LocalStepWith.boundaryBatchNil
  case boundaryBatchCons => apply LocalStepWith.boundaryBatchCons
  case boundaryNativeEmittedRaw => apply LocalStepWith.boundaryNativeEmittedRaw
  case boundaryNativeEmittedReturn => apply LocalStepWith.boundaryNativeEmittedReturn
  case boundaryNativeCompletedRaw => apply LocalStepWith.boundaryNativeCompletedRaw
  case boundaryNativeCompletedReturn =>
    rw [heRegion_native_completed] at same
    obtain rfl := space_eq_of_whole (fun _ => rfl) same
    apply LocalStepWith.boundaryNativeCompletedReturn; all_goals assumption
  case publish => apply LocalStepWith.publish; all_goals assumption
  case singleton => apply LocalStepWith.singleton
  case branches => apply LocalStepWith.branches
  case tupleTail => apply LocalStepWith.tupleTail
  case arguments => apply LocalStepWith.arguments
  case argumentTail => apply LocalStepWith.argumentTail
  case functionHeads => apply LocalStepWith.functionHeads
  case functionAssemble => apply LocalStepWith.functionAssemble
  case diagnostics => apply LocalStepWith.diagnostics
  case boundaryBatch => apply LocalStepWith.boundaryBatch
  case calls => apply LocalStepWith.calls
  case append => apply LocalStepWith.append
  case prepend => apply LocalStepWith.prepend
  case contextStep => apply LocalStepWith.contextStep; all_goals assumption
  case contextReturn => apply LocalStepWith.contextReturn

end Transfer

/-! ## HE on the step, one occurrence per row -/

section OnTheStep

variable {dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch} {lookup : CastLookup}
  {policy : Policy}

/-- **HE's machine is world-local for its footprint.** -/
theorem he_worldLocal : WorldLocal (heMachine dispatch lookup policy) Space.atoms (heFoot policy) := by
  intro space space₀ c c' pop push same framed base
  obtain ⟨_, step⟩ := framed base
  exact ⟨rfl, localStep_transfer step same⟩

theorem he_readOnly : ReadOnly (heMachine dispatch lookup policy) := fun transition => transition.1

/-- **HE on the step with honest footprints.** The step under the footprinted rules of HE's
read-only machine, with its space as one occurrence per row, is strongly bisimilar to the machine:
one HE transition is one firing, which reads exactly the rows of its region and observes that the
region holds nothing else. -/
theorem he_rows_on_the_step :
    IsBisimulation (RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy))
      (heMachine dispatch lookup policy).Step (RowRepresents Space.atoms) :=
  row_bisimulation he_local he_readOnly he_worldLocal

/-- **The observations agree**: answers and rows reached. -/
theorem he_rows_outcomes_eq {S : Store (Atom × ℕ) Control Continuation Result} {x : HEConfig}
    (represented : RowRepresents Space.atoms S (toConfig x)) :
    rowStoreOutcomes (heMachine dispatch lookup policy) Space.atoms (heFoot policy) S =
      rowMachineOutcomes (heMachine dispatch lookup policy) Space.atoms (toConfig x) :=
  row_outcomes_eq he_local he_readOnly he_worldLocal represented

/-- **What an HE firing reads is the rows of its region, and nothing else**, and its region is the
footprint of a move from the store's control or the empty region of publication. -/
theorem he_reads_exact {S S' : Store (Atom × ℕ) Control Continuation Result} {x : HEConfig}
    (represented : RowRepresents Space.atoms S (toConfig x))
    (step : RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy) S S') :
    ∃ (rule : RuleInstance (RowCell Atom Control Continuation Result)) (ρ : Atom → Bool),
      rule.read = (regionRows ρ x.space.atoms).map Cell.world ∧
      ((∃ c', ρ = heRegion policy x.control c') ∨ ρ = fun _ => false) := by
  obtain ⟨rule, ρ, _, reads, region⟩ := row_firing_region represented step
  refine ⟨rule, ρ, reads, ?_⟩
  rcases region with ⟨_, c', _, rfl⟩ | rfl
  · exact Or.inl ⟨c', rfl⟩
  · exact Or.inr rfl

end OnTheStep

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (AlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (rule missedRule context)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic
  semanticLoopFree_empty symbol_mismatch_not_match)

/-- `(p a)`. -/
def pa : Atom := .expression [.symbol "p", .symbol "a"]

/-- **Negative control: `(p a)` is outside every equation query's region**, so no equation query of
HE reads it. -/
theorem pa_outside (live : List Atom) (query : Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) : eqRegion live query incoming pa = false :=
  eqRegion_not_equation fun left right same => by simp [pa] at same

/-- **Positive control: pending work on a tuple reads no row.** Every firing of HE's footprinted
rules from a store whose control is a tuple's pending work reads nothing. H1's encoding read the
whole space there. -/
theorem tuple_reads_nothing {dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch}
    {lookup : CastLookup} {policy : Policy}
    {S S' : Store (Atom × ℕ) Control Continuation Result} {space : Space} {live : List Atom}
    {scope : List String} {values : List Entry.Value}
    {activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame}
    {stack : List Continuation} {emitted : List Result}
    (represented : RowRepresents Space.atoms S
      (toConfig ⟨space, .work (.tuple live scope values activation), stack, emitted⟩))
    (step : RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy) S S') :
    ∃ rule : RuleInstance (RowCell Atom Control Continuation Result), rule.read = [] := by
  obtain ⟨rule, ρ, reads, region⟩ := he_reads_exact represented step
  refine ⟨rule, ?_⟩
  rcases region with ⟨c', rfl⟩ | rfl
  · rw [reads]
    exact congrArg (List.map Cell.world) (regionRows_none _)
  · rw [reads, regionRows_none]
    rfl

/-- The empty logical merge. -/
theorem mergeEmpty :
    Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel
      Mettapedia.Languages.MeTTa.HE.Bindings.empty Mettapedia.Languages.MeTTa.HE.Bindings.empty
      Mettapedia.Languages.MeTTa.HE.Bindings.empty := by
  refine ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _,
    fun name => .var name, ?_⟩
  simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
    Mettapedia.Languages.MeTTa.HE.Bindings.empty]

/-- `(= a result)` is in the region of the query `a`: it can contribute a work item. -/
theorem rule_inside (live : List Atom) :
    eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty rule = true := by
  apply eqRegion_of_not_inert
  intro inert
  have hit : EquationRowResultsRel live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty 0
      rule [⟨0, .symbol "a", .symbol "result", .symbol "a", .symbol "result",
        Mettapedia.Languages.MeTTa.HE.Bindings.empty⟩] :=
    .hit _ _ _ _ _ _ _ (AlphaVariantRel.symbols _ _ _ _ _)
      (.symSym "a" semanticLoopFree_empty) mergeEmpty
  have empty := (inert 0 _).mp hit
  cases empty

/-- `(= b missed)` is outside the region of the query `a`: every fresh variant of it misses. -/
theorem missed_outside (live : List Atom) :
    eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty missedRule = false := by
  have inert : Inert live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty missedRule := by
    intro position block
    constructor
    · intro derived
      cases derived with
      | irrelevant =>
          rename_i notEquation
          exact absurd rfl (notEquation _ _)
      | miss => rfl
      | hit =>
          obtain ⟨_, _, renamed, _, _⟩ := ‹AlphaVariantRel _ _ _ _ _ _ _›
          cases renamed
          exact absurd ‹MatchRel _ _ _ _› (symbol_mismatch_not_match (by decide) _)
    · rintro rfl
      apply EquationRowResultsRel.miss position (.symbol "b") (.symbol "missed")
        (.symbol "b") (.symbol "missed") (AlphaVariantRel.symbols _ _ _ _ _)
      intro pattern body alpha matched output viable
      obtain ⟨_, _, renamed, _, _⟩ := alpha
      cases renamed
      exact symbol_mismatch_not_match (by decide) matched viable.1
  simpa [eqRegion] using inert

/-- **Positive control: the region of the query `a` on the tree's frontier fixture** is the two
copies of `(= a result)`, at positions `0` and `3`; the row `metadata` and the missed equation
`(= b missed)` are outside. -/
theorem fixture_region (live : List Atom) :
    regionRows (eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty)
      context.atoms = [(rule, 0), (rule, 3)] := by
  have metadata : eqRegion live (.symbol "a") Mettapedia.Languages.MeTTa.HE.Bindings.empty
      (.symbol "metadata") = false :=
    eqRegion_not_equation fun _ _ same => by cases same
  simp [regionRows, context, Mettapedia.Languages.MeTTa.HE.Space.ofList, rule_inside,
    missed_outside, metadata]

end Controls

#print axioms eqRegion_not_equation
#print axioms frontierOver_filter_iff
#print axioms frontier_transfer
#print axioms localStep_transfer
#print axioms he_worldLocal
#print axioms he_rows_on_the_step
#print axioms he_rows_outcomes_eq
#print axioms he_reads_exact
#print axioms Controls.pa_outside
#print axioms Controls.tuple_reads_nothing
#print axioms Controls.rule_inside
#print axioms Controls.missed_outside
#print axioms Controls.fixture_region

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
