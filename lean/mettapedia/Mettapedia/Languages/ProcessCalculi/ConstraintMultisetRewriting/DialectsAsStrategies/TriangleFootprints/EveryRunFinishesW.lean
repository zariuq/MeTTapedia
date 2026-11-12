import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRunFinishes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedArithmetic

/-!
# Every run of HE's world machine on a settling term with arithmetic finishes

`EveryRunFinishes` shows that no run of HE's contextual machine on a term of
`CompoundBindings.SettlesK` is stuck or infinite. Integer operations run only on HE's world
machine, whose host service executes them. Here the same holds there, on the class of
`NestedArithmetic.SettlesKG`: compound bindings, nested calls and integer operations in any
position.

**`FineW x`**: `x` is final, or `x` can step on the world machine and every successor is `FineW`.

**The reduction to the contextual machine (`world_core`).** On a configuration whose control is
neither a host call, a minimal instruction, a capture or restore, a collector, nor a saved context
(`Plain`), every world step is a step of the contextual machine. So every continuation frame and
every task of the fragment that is not a host call keeps exactly its contextual successors, and the
continuation-passing proof of `EveryRunFinishes` carries over unchanged.

**The host call (`fine_grounded_query`).** On a call value of `(op a b)`, the world machine has
exactly the host step: the host service's only outcome is the operation's value, the plan resumes
with one row, whatever frame the native merge renews, and the native boundary, the cast of the
value and the batch frames then run deterministically.

## Results

* `every_run_finishes_kg`: from the entry of a settling term (historical lookup, any policy, any
  minimal services), the world step relation is well founded (no infinite run), and every reachable
  world configuration either steps or is final, and a final one publishes the term's answers, which
  PeTTa's run yields from some fuel on.
* `every_run_finishes_kg_with_he_lookups`: the same, together with the existence of a complete run,
  under both of HE's own lookups (historical list storage and scoped fresh variants). The class
  contains the compound-binding class of `CompoundBindings` on HE's integer dispatch
  (`NestedArithmetic.settlesK_settlesKG`), so those programs get both lookups too.

## Controls

* `Controls.quad_every_run_finishes`, `Controls.toInt_every_run_finishes`,
  `Controls.arith_every_run_finishes` (positive): `(quad 4)`, `(toInt (S (S Z)))` and
  `(+ (* 2 3) 1)` finish on every run with `16`, `2` and `7`.
* `Controls.host_steps_on_world` (the extension is needed): the host call `(+ 4 4)`, stuck on the
  contextual machine, steps on the world machine.
* `Controls.loop_diverges_world` (negative): outside the class the world machine diverges; `(loop)`
  on `{(= (loop) (loop))}` has an infinite world run (`acc_of_world_acc`: every contextual step is
  a world step).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace EveryRunFinishesW

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom isEmptyOrError GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load WorldStep WorldSteps
  WorldLocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation Task
  WorldConfiguration UnscopedControl)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings GroundedTables GroundedRuns
  GroundedEveryRun NestedArithmetic EveryRunFinishes

variable {minimal : Minimal.Services} {lookup : CastLookup} {policy : Policy}

/-! ## The world machine on contextual configurations -/

/-- One step of HE's world machine (read-only world, integer host service), read on contextual
configurations. Every world configuration is one (`toFlat`). -/
abbrev WStep (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy) (x y : HEConfig) :
    Prop :=
  WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
    (WorldConfiguration.ofReadOnly x) (WorldConfiguration.ofReadOnly y)

/-- The contextual configuration of a world configuration. -/
def toFlat (w : WorldConfiguration Space Unit) : HEConfig := ⟨w.context, w.control, w.stack, w.emitted⟩

/-- Tasks the world machine runs exactly as the contextual machine does. -/
def PlainTask : Task → Prop
  | .call _ _ value .. => ¬ Minimal.HostCall heDispatch value.erase
  | .invocation _ _ _ value .. => ¬ Minimal.HostCall heDispatch value.erase
  | .minimal .. => False
  | .capture .. => False
  | .restore .. => False
  | _ => True

/-- Configurations the world machine runs exactly as the contextual machine does. -/
def Plain : HEConfig → Prop
  | ⟨_, .work task, _, _⟩ => PlainTask task
  | ⟨_, .returning _, .collect _ :: _, _⟩ => False
  | ⟨_, .returning _, _, _⟩ => True
  | ⟨_, .context .., _, _⟩ => False

/-- **On a plain configuration every world step is a contextual step.** -/
theorem world_core {x y : HEConfig} (plain : Plain x) (step : WStep minimal lookup policy x y) :
    HEStep heDispatch lookup policy x y := by
  obtain ⟨space, control, stack, emitted⟩ := x
  obtain ⟨space', control', stack', emitted'⟩ := y
  dsimp only [WStep, WorldConfiguration.ofReadOnly] at step
  cases step with
  | publish => exact .publish
  | internal l =>
      cases l with
      | core before _ inner after =>
          cases before <;> cases after <;> exact .internal inner
      | callGroundedDone erased executable => exact absurd ⟨_, _, erased, executable⟩ plain
      | callGroundedResume erased executable => exact absurd ⟨_, _, erased, executable⟩ plain
      | invocationGroundedDone erased executable => exact absurd ⟨_, _, erased, executable⟩ plain
      | invocationGroundedResume erased executable => exact absurd ⟨_, _, erased, executable⟩ plain
      | _ => exact False.elim plain

/-- A call of a head the host does not execute is plain. -/
theorem plain_call {atoms : List Atom} {f : String} {vals : List Atom}
    (head : NodeHead heDispatch atoms f) {space : Space} {live : List Atom} {scope : List String}
    {value : Entry.Value} {expected : Atom} {activation : Frame} {stack : List Continuation}
    {emitted : List Result} (erased : value.erase = .expression (.symbol f :: vals)) :
    Plain ⟨space, .work (.call live scope value expected activation), stack, emitted⟩ := by
  show ¬ Minimal.HostCall heDispatch value.erase
  rintro ⟨operator, arguments, shaped, executable⟩
  rw [erased] at shaped
  simp only [Atom.expression.injEq, List.cons.injEq] at shaped
  obtain ⟨rfl, rfl⟩ := shaped
  exact head.notHost executable

/-! ## Configurations from which every world run finishes -/

/-- **Every world run from `x` finishes**: `x` is final, or `x` can step and every successor
finishes. -/
inductive FineW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy) :
    HEConfig → Prop
  | final {space : Space} {emitted : List Result} :
      FineW minimal lookup policy ⟨space, .returning [], [], emitted⟩
  | step {x : HEConfig} : (∃ y, WStep minimal lookup policy x y) →
      (∀ y, WStep minimal lookup policy x y → FineW minimal lookup policy y) →
      FineW minimal lookup policy x

theorem final_no_stepW {space : Space} {emitted : List Result} {y : HEConfig} :
    ¬ WStep minimal lookup policy ⟨space, .returning [], [], emitted⟩ y := by
  intro step
  cases world_core (by trivial) step with
  | internal l => cases l

theorem FineW.next {x y : HEConfig} (fine : FineW minimal lookup policy x)
    (step : WStep minimal lookup policy x y) : FineW minimal lookup policy y := by
  cases fine with
  | final => exact absurd step final_no_stepW
  | step _ all => exact all y step

/-- **No infinite world run.** -/
theorem FineW.acc_world {x : HEConfig} (fine : FineW minimal lookup policy x) :
    Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy a b)
      (WorldConfiguration.ofReadOnly x) := by
  induction fine with
  | final =>
      exact Acc.intro _ fun w step =>
        absurd (show WStep minimal lookup policy _ (toFlat w) from step) final_no_stepW
  | step _ _ ih => exact Acc.intro _ fun w step => ih (toFlat w) step

/-- Every world configuration reachable from a `FineW` one is `FineW`. -/
theorem FineW.reaches_world {x : HEConfig} (fine : FineW minimal lookup policy x)
    {w : WorldConfiguration Space Unit}
    (path : WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly x) w) :
    FineW minimal lookup policy (toFlat w) := by
  induction path with
  | refl => exact fine
  | @tail b c _ step ih => exact ih.next (y := toFlat c) step

/-- **No stuck configuration.** -/
theorem FineW.progress {x : HEConfig} (fine : FineW minimal lookup policy x) :
    (∃ y, WStep minimal lookup policy x y) ∨
      ∃ (space : Space) (emitted : List Result), x = ⟨space, .returning [], [], emitted⟩ := by
  cases fine with
  | final => exact Or.inr ⟨_, _, rfl⟩
  | step moves _ => exact Or.inl moves

/-- A plain configuration with one contextual successor is `FineW` when that successor is. -/
theorem fineW_det {x y : HEConfig} (plain : Plain x) (moves : HEStep heDispatch lookup policy x y)
    (only : ∀ z, HEStep heDispatch lookup policy x z → z = y) (next : FineW minimal lookup policy y) :
    FineW minimal lookup policy x :=
  .step ⟨y, lift_step minimal moves⟩ fun z step => by
    rw [only z (world_core plain step)]
    exact next

/-- **The world machine has every infinite run of the contextual machine**: well-foundedness of the
world step relation from a configuration gives it for the contextual one. -/
theorem acc_of_world_acc {x : HEConfig}
    (acc : Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup
      policy a b) (WorldConfiguration.ofReadOnly x)) :
    Acc (fun b a => HEStep heDispatch lookup policy a b) x := by
  generalize same : WorldConfiguration.ofReadOnly x = w at acc
  induction acc generalizing x with
  | intro w _ ih =>
      subst same
      exact Acc.intro _ fun y step => ih _ (lift_step minimal step) rfl

/-- World runs keep the context. -/
theorem context_fixed {x : HEConfig} {w : WorldConfiguration Space Unit}
    (path : WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly x) w) : w.context = x.space := by
  induction path with
  | refl => rfl
  | tail _ step ih => rw [step.preserves_context, ih]

/-! ## Continuation frames -/

section Frames

variable {space : Space} {stack : List Continuation} {emitted : List Result}

theorem fine_singletonW {R : List Result}
    (next : FineW minimal lookup policy ⟨space, .returning (R.map Completed.tupleSingleton), stack,
      emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .singleton :: stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .singleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_frameW {live : List Atom} {scope : List String} {tail : List Entry.Value}
    {heads : List Result}
    (next : FineW minimal lookup policy ⟨space, .work (.branches live scope tail heads), stack,
      emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning heads, .branches live scope tail :: stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal .branches) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_tupleTailW {head : Entry.Value} {R : List Result}
    (next : FineW minimal lookup policy ⟨space, .returning (R.map (Completed.tuplePrepend head)),
      stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .tupleTail head :: stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .tupleTail) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_appendW {remaining : Task} {R : List Result}
    (next : FineW minimal lookup policy ⟨space, .work remaining, .prepend R :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .append remaining :: stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .append) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_prependW {selected R : List Result}
    (next : FineW minimal lookup policy ⟨space, .returning (selected ++ R), stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .prepend selected :: stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .prepend) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_calls_frameW {live : List Atom} {scope : List String} {expected : Atom}
    {rows : List Result}
    (next : FineW minimal lookup policy ⟨space, .work (.calls live scope expected rows), stack,
      emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning rows, .calls live scope expected :: stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal .calls) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_diagnosticsW {errors : List Atom} {activation : Frame} {R : List Result}
    (next : FineW minimal lookup policy ⟨space,
      .returning (R ++ Completed.diagnosticResults errors activation), stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .diagnostics errors activation :: stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal .diagnostics) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundaryBatch_frameW {live : List Atom} {scope : List String} {caller : Option Atom}
    {site : Completed.Boundary} {rows : List Result}
    (next : FineW minimal lookup policy ⟨space, .work (.boundaryBatch live scope caller site rows),
      stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning rows,
      .boundaryBatch live scope caller site :: stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .boundaryBatch) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

/-- The publication frame: every answer is answerable, so all are kept. -/
theorem fine_publishW {R : List Result} {original : Atom} (clean : ∀ r ∈ R, Answerable r.1.erase)
    (next : FineW minimal lookup policy ⟨space,
      .returning (R.map (Completed.publishResult policy original)), stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .returning R, .publish original :: stack, emitted⟩ := by
  have unchanged : R.map (Completed.readResult policy) = R :=
    map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (R.map (Completed.readResult policy)) R := by
    rw [unchanged]
    exact HERuns.success_all R fun r member => (clean r member).notError
  refine fineW_det (by trivial) (.internal (.publish selected)) (fun z step => ?_) next
  cases step with
  | internal l =>
      cases l with
      | publish chosen =>
          rw [Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional chosen
            selected]

/-- **The top level drains every batch.** -/
theorem fine_topW : ∀ (R emitted : List Result),
    FineW minimal lookup policy ⟨space, .returning R, [], emitted⟩
  | [], _ => .final
  | r :: rs, emitted => fineW_det (by trivial) .publish (fun z step => by
      cases step with
      | internal l => cases l
      | publish => rfl) (fine_topW rs (emitted ++ [r]))

end Frames

/-! ## Deterministic task steps -/

section Tasks

variable {space : Space} {stack : List Continuation} {emitted : List Result} {live : List Atom}
  {scope : List String}

theorem fine_tuple_singletonW {v : Entry.Value} {activation : Frame}
    (next : FineW minimal lookup policy ⟨space,
      .work (.atom live scope v Atom.undefinedType activation), .singleton :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.tuple live scope [v] activation), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .tupleSingleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_tuple_consW {head second : Entry.Value} {remaining : List Entry.Value}
    {activation : Frame}
    (next : FineW minimal lookup policy ⟨space,
      .work (.atom (.expression ((second :: remaining).map Entry.Value.erase) :: live) scope head
        Atom.undefinedType activation), .branches live scope (second :: remaining) :: stack,
        emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.tuple live scope (head :: second :: remaining)
      activation), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .tupleCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_nilW {tail : List Entry.Value}
    (next : FineW minimal lookup policy ⟨space, .returning [], stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.branches live scope tail []), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .branchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_consW {tail : List Entry.Value} {head : Result} {heads : List Result}
    (clean : ¬ IsEmptyOrErrorRel head.1.erase)
    (next : FineW minimal lookup policy ⟨space,
      .work (.tuple (head.1.erase :: live) scope tail head.2),
      .tupleTail head.1 :: .append (.branches live scope tail heads) :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.branches live scope tail (head :: heads)), stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal (.branchesContinue clean)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | branchesStopped stopped => exact absurd stopped clean
        | branchesContinue _ => rfl) next

theorem fine_calls_nilW {expected : Atom}
    (next : FineW minimal lookup policy ⟨space, .returning [], stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.calls live scope expected []), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .callsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_calls_consW {expected : Atom} {head : Result} {heads : List Result}
    (next : FineW minimal lookup policy ⟨space, .work (.call live scope head.1 expected head.2),
      .append (.calls live scope expected heads) :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.calls live scope expected (head :: heads)), stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal .callsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_equations_nilW {original : Entry.Value} {expected : Atom} {activation : Frame}
    (next : FineW minimal lookup policy ⟨space, .returning [], stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.equations live scope original expected activation []), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .equationsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundary_producerW {caller : Option Atom} {value : Entry.Value} {activation : Frame}
    (raw : ¬ Completed.FunctionPending policy value)
    (next : FineW minimal lookup policy ⟨space, .returning [(value, activation)], stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.boundary live scope caller .producer value activation), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal (.boundaryProducerRaw raw)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | boundaryProducerRaw _ => rfl
        | boundaryProducerFunction pending => exact absurd pending raw) next

theorem fine_boundaryBatch_nilW {caller : Option Atom} {site : Completed.Boundary}
    (next : FineW minimal lookup policy ⟨space, .returning [], stack, emitted⟩) :
    FineW minimal lookup policy ⟨space, .work (.boundaryBatch live scope caller site []), stack,
      emitted⟩ :=
  fineW_det (by trivial) (.internal .boundaryBatchNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundaryBatch_consW {caller : Option Atom} {site : Completed.Boundary} {head : Result}
    {heads : List Result}
    (next : FineW minimal lookup policy ⟨space,
      .work (.boundary live scope caller site head.1 head.2),
      .append (.boundaryBatch live scope caller site heads) :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.boundaryBatch live scope caller site (head :: heads)), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .boundaryBatchCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundary_returnedW {caller : Option Atom} {original value : Entry.Value}
    {expected : Atom} {activation : Frame}
    (next : FineW minimal lookup policy ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.boundary live scope caller (.returned original expected) value activation), stack,
        emitted⟩ :=
  fineW_det (by trivial) (.internal .boundaryReturned) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_returned_evaluateW {original value : Entry.Value} {expected : Atom}
    {activation : Frame}
    (notRefused : value.erase ≠ Atom.notReducible) (notStopped : ¬ IsEmptyOrErrorRel value.erase)
    (next : FineW minimal lookup policy ⟨space,
      .work (.atom live scope value expected activation), stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal (.returnEvaluate notRefused notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | returnRefused refused => exact absurd refused notRefused
        | returnStopped stopped => exact absurd stopped notStopped
        | returnEvaluate _ _ => rfl) next

/-- The native boundary of an emitted value under a return demand. -/
theorem fine_native_emitted_returnW {caller : Option Atom} {original value : Entry.Value}
    {expected : Atom} {activation : Frame}
    (next : FineW minimal lookup policy ⟨space,
      .work (.boundary (expected :: live) scope (some original.erase) .producer value activation),
      .boundaryBatch live scope caller (.returned original expected) :: stack, emitted⟩) :
    FineW minimal lookup policy ⟨space,
      .work (.boundary live scope caller (.native original (some expected) .emitted) value
        activation), stack, emitted⟩ :=
  fineW_det (by trivial) (.internal .boundaryNativeEmittedReturn) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

end Tasks

/-! ## The logical relation on the world machine -/

/-- **Every world run from pending work on `v` finishes, with answers `L`.** -/
def FineRunsW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    (∀ R : List Result, R.map (fun r => r.1.erase) = L →
      FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
    FineW minimal lookup policy ⟨Space.ofList atoms,
      .work (.atom live scope v Atom.undefinedType activation), stack, emitted⟩

/-- **Every marked presentation of `t` runs finely to `L` on the world machine.** -/
def FineEvalW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked heDispatch atoms v → FineRunsW minimal lookup policy atoms v L

/-- **Every query of `(f vals)`, on every call value, runs finely to `A` on the world machine.** -/
def FineQueryW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (f : String) (vals A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) →
    ∀ (stack : List Continuation) (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = A →
        FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      FineW minimal lookup policy ⟨Space.ofList atoms,
        .work (.call live scope value Atom.undefinedType activation), stack, emitted⟩

/-- **A data atom**: its cast is the only step, and every cast result is the atom. -/
theorem fine_dataW (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    FineEvalW minimal lookup policy atoms d [d] := by
  intro v erased _ live scope activation stack emitted cont
  rw [value_of_data data erased]
  have entry : Entry.Rel policy.reentry (activation.read policy (Entry.Value.ofAtom d)).status
      (activation.read policy (Entry.Value.ofAtom d)).erase Atom.undefinedType .cast := by
    simp only [CompleteRun.read_data policy activation data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  refine .step ⟨_, lift_step minimal (CompleteRun.cast_step_frame (dispatch := heDispatch)
    (policy := policy) answers (Space.ofList atoms) data activation live scope stack emitted)⟩ ?_
  intro y step
  replace step := world_core (by trivial) step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered batch related =>
          have derived : Completed.AtomRel (Space.ofList atoms) heDispatch lookup _ _ _ _ _ _
              (policy := policy) := .cast entered batch related
          obtain ⟨after, rfl⟩ := data_source contract data derived
          exact cont _ (by simp)
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-- **A held expression under reuse is delivered**, the only step. -/
theorem fine_heldW (atoms : List Atom) {children : List Entry.Value}
    (reuses : policy.reentry = .reuse)
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (children.map Entry.Value.erase)) name)
    (notStopped : ¬ IsEmptyOrErrorRel (.expression (children.map Entry.Value.erase))) :
    FineRunsW minimal lookup policy atoms (.expression .held children)
      [.expression (children.map Entry.Value.erase)] := by
  intro live scope activation stack emitted cont
  have eraseV : (Entry.Value.expression .held children).erase =
      .expression (children.map Entry.Value.erase) := by
    simp only [Entry.Value.erase]
  have readV := read_closed_value policy activation (v := .expression .held children)
    (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression .held children)).status
      (activation.read policy (.expression .held children)).erase Atom.undefinedType .deliver := by
    rw [readV, eraseV]
    exact .held notStopped undefined_not_raw reuses rfl
  refine .step ⟨_, lift_step minimal (.internal (.delivered entry))⟩ ?_
  intro y step
  replace step := world_core (by trivial) step
  cases step with
  | internal l =>
      cases l with
      | delivered _ =>
          apply cont
          rw [readV]
          simp only [List.map_cons, List.map_nil, eraseV]
      | cast entered => cases Entry.functional entered entry
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-- **The branches of a tuple's head**, for every successor. -/
theorem fine_branchesW (atoms : List Atom) {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ts : List (List Atom)}
    (tailFine : ∀ (live' : List Atom) (activation : Frame) (stack : List Continuation)
      (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = Ts.map Atom.expression →
        FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      FineW minimal lookup policy ⟨Space.ofList atoms, .work (.tuple live' scope tail activation),
        stack, emitted⟩)
    (tailClean : ∀ c ∈ Ts, ∃ c0 cs, c = c0 :: cs ∧ Answerable c0) :
    ∀ (heads : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            heads.flatMap (fun h => Ts.map fun c => Atom.expression (h.1.erase :: c)) →
          FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        FineW minimal lookup policy ⟨Space.ofList atoms, .work (.branches live scope tail heads),
          stack, emitted⟩
  | [], _, stack, emitted, cont => fine_branches_nilW (cont [] rfl)
  | h :: hs, clean, stack, emitted, cont => by
      have hClean := clean h List.mem_cons_self
      apply fine_branches_consW hClean.notStopped
      apply tailFine (h.1.erase :: live) h.2
        (.tupleTail h.1 :: .append (.branches live scope tail hs) :: stack) emitted
      intro Rt eraseRt
      apply fine_tupleTailW
      apply fine_appendW
      apply fine_branchesW atoms tailFine tailClean hs
        (fun x member => clean x (List.mem_cons_of_mem _ member))
        (.prepend (Rt.map (Completed.tuplePrepend h.1)) :: stack) emitted
      intro Rh eraseRh
      apply fine_prependW
      apply cont
      have pointwise : ∀ r ∈ Rt, (Completed.tuplePrepend h.1 r).1.erase =
          HENested.prependAtom h.1.erase r.1.erase := by
        intro r member
        have inTs : r.1.erase ∈ Ts.map Atom.expression := by
          rw [← eraseRt]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        obtain ⟨c, cMem, cEq⟩ := List.mem_map.mp inTs
        obtain ⟨c0, cs, rfl, clean0⟩ := tailClean c cMem
        rw [tuplePrepend_erase_any h.1 cEq.symm clean0, ← cEq]
        rfl
      rw [List.map_append, eraseRh, List.flatMap_cons, List.map_map]
      congr 1
      have mapped : (Rt.map ((fun r : Result => r.1.erase) ∘ Completed.tuplePrepend h.1)) =
          (Rt.map fun r => r.1.erase).map (HENested.prependAtom h.1.erase) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro r member
        exact pointwise r member
      rw [mapped, eraseRt, List.map_map]
      rfl

/-- **The tuple traversal of marked values**, for every successor. -/
theorem fine_tupleW (atoms : List Atom) :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)), vs ≠ [] →
      List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧ ∀ a ∈ L, Answerable a)
        vs Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression →
          FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        FineW minimal lookup policy ⟨Space.ofList atoms, .work (.tuple live scope vs activation),
          stack, emitted⟩
  | [], _, nonempty, _ => absurd rfl nonempty
  | [v], Ls, _, related => by
      intro live scope activation stack emitted cont
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          apply fine_tuple_singletonW
          apply here.1 live scope activation (.singleton :: stack) emitted
          intro R eraseR
          apply fine_singletonW
          apply cont
          have clean := HENested.clean_of_erase eraseR here.2
          have singled : ∀ r ∈ R, Completed.tupleSingleton r = (.expression .active [r.1], r.2) := by
            intro r member
            unfold Completed.tupleSingleton
            rw [HENested.emptyOrError_false (clean r member)]
            rfl
          rw [List.map_map]
          have mapped : R.map ((fun r : Result => r.1.erase) ∘ Completed.tupleSingleton) =
              (R.map fun r => r.1.erase).map fun a => Atom.expression [a] := by
            rw [List.map_map]
            apply List.map_congr_left
            intro r member
            simp only [Function.comp_apply, singled r member, Entry.Value.erase, List.map_cons,
              List.map_nil]
          rw [mapped, eraseR, combos_singleton, List.map_map]
          rfl
  | v :: v2 :: rest, Ls, _, related => by
      intro live scope activation stack emitted cont
      cases related with
      | cons here later =>
          rename_i L Ls'
          have tailFine := fine_tupleW atoms (v2 :: rest) Ls' (List.cons_ne_nil _ _) later
          have tailClean : ∀ c ∈ combos Ls', ∃ c0 cs, c = c0 :: cs ∧ Answerable c0 := by
            intro c member
            have lengths := combos_length member
            have positive : Ls'.length = (v2 :: rest).length := (List.Forall₂.length_eq later).symm
            obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, c = c0 :: cs := by
              cases c with
              | nil =>
                  simp only [List.length_nil] at lengths
                  simp only [List.length_cons] at positive
                  omega
              | cons c0 cs => exact ⟨c0, cs, rfl⟩
            refine ⟨c0, cs, rfl, ?_⟩
            have allClean : ∀ L' ∈ Ls', ∀ a ∈ L', Answerable a := by
              intro L' member' a inside
              obtain ⟨t', both⟩ := forall₂_right_exists later L' member'
              exact both.2 a inside
            exact combos_answerable allClean _ member c0 List.mem_cons_self
          apply fine_tuple_consW
          apply here.1 _ scope activation (.branches live scope (v2 :: rest) :: stack) emitted
          intro R eraseR
          apply fine_branches_frameW
          apply fine_branchesW atoms (live := live) (fun live' activation' stack' emitted' cont' =>
            tailFine live' scope activation' stack' emitted' cont') tailClean R
            (HENested.clean_of_erase eraseR here.2) stack emitted
          intro R' eraseR'
          apply cont
          rw [eraseR']
          have flat : R.flatMap (fun h => (combos Ls').map fun c => Atom.expression (h.1.erase :: c)) =
              (R.map fun h => h.1.erase).flatMap
                (fun a => (combos Ls').map fun c => Atom.expression (a :: c)) := by
            rw [List.flatMap_map]
          rw [flat, eraseR]
          simp only [combos, List.map_flatMap, List.map_map]
          rfl

/-- **The calls continuation over rows**, for every successor. -/
theorem fine_callsW (atoms : List Atom) {live : List Atom} {scope : List String} {f : String}
    (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQueryW minimal lookup policy atoms f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) →
          FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        FineW minimal lookup policy ⟨Space.ofList atoms,
          .work (.calls live scope Atom.undefinedType rows), stack, emitted⟩
  | [], _, stack, emitted, cont => fine_calls_nilW (cont [] rfl)
  | r :: rs, queries, stack, emitted, cont => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      apply fine_calls_consW
      apply query live scope r.2 r.1 erased (.append (.calls live scope Atom.undefinedType rs) :: stack)
        emitted
      intro Qr eraseQr
      apply fine_appendW
      apply fine_callsW atoms Q rs (fun x member => queries x (List.mem_cons_of_mem _ member))
        (.prepend Qr :: stack) emitted
      intro Rs eraseRs
      apply fine_prependW
      apply cont
      rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
      rfl

/-- **The equation loop**, for every unifier output of every work. -/
theorem fine_equationsW (atoms : List Atom) {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEvalW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = Ls.flatten →
          FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        FineW minimal lookup policy ⟨Space.ofList atoms,
          .work (.equations live scope original Atom.undefinedType activation works), stack, emitted⟩
  | [], Ls, _, related, stack, emitted, cont => by
      cases related
      exact fine_equations_nilW (cont [] rfl)
  | work :: works, Ls, unifiers, related, stack, emitted, cont => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨i, readsAs, fineI, facts⟩ := here
          obtain ⟨output₀, sameBindings₀, unified₀⟩ := unifiers work List.mem_cons_self
          refine .step ⟨_, lift_step minimal (.internal (.equationsCons sameBindings₀ unified₀))⟩ ?_
          intro y step
          replace step := world_core (by trivial) step
          cases step with
          | internal l =>
              cases l with
              | equationsCons sameBindings _ =>
                  obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings
                  apply fine_boundary_producerW (not_pending facts readErase)
                  apply fine_boundaryBatch_frameW
                  apply fine_boundaryBatch_consW
                  apply fine_boundary_returnedW
                  apply fine_returned_evaluateW (by rw [readErase]; exact facts.notRefused)
                    (by rw [readErase]; exact facts.notStopped)
                  refine fineI _ readErase readMarked _ _ _ _ _ ?_
                  intro Rb eraseRb
                  apply fine_appendW
                  apply fine_boundaryBatch_nilW
                  apply fine_prependW
                  apply fine_appendW
                  apply fine_equationsW atoms works Ls'
                    (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
                    (.prepend (Rb ++ []) :: stack) emitted
                  intro Rs eraseRs
                  apply fine_prependW
                  apply cont
                  rw [List.append_nil, List.map_append, eraseRb, eraseRs, List.flatten_cons]

/-- **A query with an empty region**: `callAbsent` is the only step, returning the call. -/
theorem fine_query_absentW {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead heDispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (empty : regionBodies atoms f vals = []) :
    FineQueryW minimal lookup policy atoms f vals [.expression (.symbol f :: vals)] := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  have noBodies : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [empty]
    intro b member
    cases member
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies := HERuns.frontier_bodies ground activation.certified.satisfiable program noBodies frontier
  rw [empty] at bodies
  have none : works = [] := List.map_eq_nil_iff.mp bodies
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings [] := by
    rw [erased]
    exact frontier
  refine .step ⟨_, lift_step minimal (.internal (.callAbsent (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier'))⟩ ?_
  intro y step
  replace step := world_core (plain_call head erased) step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed (HERuns.value_not_error head.head erased)
      | callEmbedded _ _ instruction =>
          rw [erased, head.instruction vals] at instruction
          cases instruction
      | callAbsent _ _ _ =>
          apply cont
          simp [erased]
      | callEquations _ _ frontierW nonemptyW =>
          rw [erased] at frontierW
          have bodiesW := HERuns.frontier_bodies ground activation.certified.satisfiable program
            noBodies frontierW
          rw [empty] at bodiesW
          exact absurd (List.map_eq_nil_iff.mp bodiesW) nonemptyW

/-- **A query with a nonempty region of instances**: every frontier the machine may choose fires. -/
theorem fine_query_equationsW {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {vals : List Atom} (head : NodeHead heDispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value heDispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => FineEvalW minimal lookup policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    FineQueryW minimal lookup policy atoms f vals Ls.flatten := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  have fromFrontier : ∀ (works : List EquationWork),
      EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
        (.expression (.symbol f :: vals)) activation.bindings works →
      FineW minimal lookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value Atom.undefinedType activation works), stack, emitted⟩ := by
    intro works frontier
    have instances := works_instances_K policy valsValues program activation.certified.satisfiable
      frontier
    have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
        value.erase activation.bindings works := by
      rw [erased]
      exact frontier
    obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
      (policy := policy.rebuilding) activation.certified frontier'
    have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment value
          (Entry.Value.ofAtom w.pattern) output.environment := by
      intro w member
      obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
      exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
    have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
          output.bindings = work.bindings →
            (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
            Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEvalW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls :=
      (forall₂_comp instances bodies).imp fun _ _ both => by
        obtain ⟨i, ⟨_, reads⟩, fineI, facts⟩ := both
        exact ⟨i, reads, fineI, facts⟩
    exact fine_equationsW atoms works Ls unifiers related stack emitted cont
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have instances := works_instances_K policy valsValues program activation.certified.satisfiable
    frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  refine .step ⟨_, lift_step minimal (.internal (.callEquations
    (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier'
    worksNonempty))⟩ ?_
  intro y step
  replace step := world_core (plain_call head erased) step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed (HERuns.value_not_error head.head erased)
      | callEmbedded _ _ instruction =>
          rw [erased, head.instruction vals] at instruction
          cases instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have sidesEq := frontier_sides ground activation.certified.satisfiable
            (scoped_consFree program) frontierEmpty
          apply absurd _ nonempty
          rw [regionInstances_sides, ← sidesEq]
          rfl
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-! ## The host call -/

/-- **The native boundary of an integer value**: the emitted value is returned under the demand,
cast, and passed through the batch frames; every cast result is the value. -/
theorem fine_nativeW (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} {d : Atom} (data : DataAtom d) (notRefused : d ≠ Atom.notReducible)
    (live : List Atom) (scope : List String) (original : Entry.Value) (activation : Frame)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [d] →
      FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    FineW minimal lookup policy ⟨Space.ofList atoms, .work (.boundaryBatch live scope none
      (.native original (some Atom.undefinedType) .emitted) [(Entry.Value.ofAtom d, activation)]),
      stack, emitted⟩ := by
  have notFunction : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom d) := by
    rintro ⟨⟨body, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    subst same
    cases data
  apply fine_boundaryBatch_consW
  apply fine_native_emitted_returnW
  apply fine_boundary_producerW notFunction
  apply fine_boundaryBatch_frameW
  apply fine_boundaryBatch_consW
  apply fine_boundary_returnedW
  apply fine_returned_evaluateW (by rw [Entry.Value.erase_ofAtom]; exact notRefused)
    (by rw [Entry.Value.erase_ofAtom]; exact data.not_stopped)
  refine fine_dataW answers contract atoms data (Entry.Value.ofAtom d) (Entry.Value.erase_ofAtom d)
    (marked_ofAtom d) live scope activation _ emitted ?_
  intro R eraseR
  apply fine_appendW
  apply fine_boundaryBatch_nilW
  apply fine_prependW
  apply fine_appendW
  apply fine_boundaryBatch_nilW
  apply fine_prependW
  apply cont
  simpa using eraseR

/-- **An integer operation on every call value**: the host step is the only step, its plan resumes
with the one value under whatever frame the merge renews, and the native boundary finishes. -/
theorem fine_grounded_query (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} {op : String} (known : IntOp op) (a b : Int) :
    FineQueryW minimal lookup policy atoms op [num a, num b] [intValue op a b] := by
  intro live scope activation value erased stack emitted cont
  have host : Minimal.HostCall heDispatch value.erase :=
    ⟨.symbol op, [num a, num b], erased, he_executable known⟩
  have rData := intValue_dataAtom known a b
  have outcomeOf : ∀ {frame : Frame} {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (services minimal).groundedAt (Space.ofList atoms) w₃ live scope frame value outcome w₄ →
      outcome = .ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)] := by
    intro frame outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [erased] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    rw [(he_outcome_exact known a b raw).mp executed]
    rfl
  have produced : (services minimal).groundedAt (Space.ofList atoms) () live scope activation value
      (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)]) () :=
    ⟨.symbol op, [num a, num b], .ok [(intValue op a b, Bindings.empty)], erased,
      (he_outcome_exact known a b _).mpr rfl, rfl⟩
  have rows : Completed.NativeOutcomeRel policy heDispatch (.symbol op) [num a, num b] value
      (some Atom.undefinedType) activation
      (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)])
      (.resume [(Entry.Value.ofAtom (intValue op a b), activation)]) :=
    .success (.cons (Frame.NativeRenewRel.empty policy activation) .nil)
  have notError : ¬ IsErrorRel value.erase := HERuns.value_not_error (intOp_head known) erased
  refine .step ⟨⟨Space.ofList atoms, .work (.boundaryBatch live scope none
      (.native value (some Atom.undefinedType) .emitted)
      [(Entry.Value.ofAtom (intValue op a b), activation)]), stack, emitted⟩,
    .internal (WorldLocalStepWith.callGroundedResume erased (he_executable known) notError produced
      rows)⟩ ?_
  intro y step
  obtain ⟨space', control', stack', emitted'⟩ := y
  dsimp only [WStep, WorldConfiguration.ofReadOnly] at step
  cases step with
  | internal l =>
      cases l with
      | core before _ inner _ =>
          cases before
          cases inner with
          | callError failed =>
              exact absurd failed (HERuns.value_not_error (intOp_head known) erased)
          | callEmbedded _ notHost _ => exact absurd host notHost
          | callAbsent _ nonGrounded _ => exact absurd host nonGrounded.1
          | callEquations _ nonGrounded _ _ => exact absurd host nonGrounded.1
      | callGroundedDone _ _ _ produced' planned =>
          rw [outcomeOf produced'] at planned
          cases planned
      | callGroundedResume _ _ _ produced' planned =>
          rw [outcomeOf produced'] at planned
          cases planned with
          | success prepared =>
              cases prepared with
              | rejected impossible _ =>
                  exact absurd ⟨_, ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _,
                    activation.certified.satisfiable⟩⟩ impossible
              | @cons _ _ after _ _ rest =>
                  cases rest
                  exact fine_nativeW answers contract rData (intValue_notRefused known a b) live scope
                    value after stack emitted cont

/-! ## Every marked call whose root HE interprets -/

/-- **A marked call whose root HE interprets**: the tuple entry or the fallback (with no
diagnostics), the argument product, the calls of each combination, the publication. -/
theorem fine_nodeW (contract : LookupContract lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    (headFine : FineRunsW minimal lookup policy atoms (.symbol f) [.symbol f])
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, FineQueryW minimal lookup policy atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    FineRunsW minimal lookup policy atoms (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  intro live scope activation stack emitted cont
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : activation.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy activation (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression readiness (.symbol f :: vs))).status
      (activation.read policy (.expression readiness (.symbol f :: vs))).erase
      Atom.undefinedType .interpret := by
    rw [readV, eraseV]
    exact .expression (call_not_stopped head) undefined_not_raw interpreted
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol f).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences untyped
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope
        (activation.read policy (.expression readiness (.symbol f :: vs))).erase
        (.symbol f) Atom.undefinedType activation outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      FineW minimal lookup policy ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol f :: ts)) :: stack, emitted⟩ := by
    intro R eraseR
    apply fine_publishW (HENested.clean_of_erase eraseR answerableAll)
    apply cont
    rw [publish_erase, eraseR]
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
        FineW minimal lookup policy ⟨Space.ofList atoms, .returning R, rest, emitted⟩) →
      ∀ rows : List Result, rows.map (fun r => r.1.erase) =
          (combos ([.symbol f] :: Ls)).map Atom.expression →
        FineW minimal lookup policy ⟨Space.ofList atoms, .returning rows,
          .calls live scope Atom.undefinedType :: rest, emitted⟩ := by
    intro rest restFine rows eraseRows
    rw [combos_head] at eraseRows
    apply fine_calls_frameW
    have queries : ∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQueryW minimal lookup policy atoms f vals (Q vals) := by
      intro r member
      have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
        rw [← eraseRows]
        exact List.mem_map.mpr ⟨r, member, rfl⟩
      rw [List.map_map] at inRows
      obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
      exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
    apply fine_callsW atoms Q rows queries rest emitted
    intro R eraseR
    apply restFine
    rw [eraseR]
    have viaAtoms : rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (rows.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseRows, List.map_map, List.flatMap_map]
    rfl
  have argsAll : List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) (Entry.Value.symbol f :: vs) ([.symbol f] :: Ls) :=
    .cons ⟨headFine, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args
  refine .step ⟨_, lift_step minimal (.internal (LocalStepWith.atomTuple entry readV occurrences))⟩ ?_
  intro y step
  replace step := world_core (by trivial) step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped _ =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [published]
          exact fine_tupleW atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
            argsAll _ scope activation _ emitted (afterRows _ afterPublish)
      | atomFunction _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          cases selectionExact chosen
      | atomFallback _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
          subst exhausted
          rw [published]
          refine fine_tupleW atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
            argsAll _ scope activation _ emitted (afterRows _ ?_)
          intro R eraseR
          apply fine_diagnosticsW
          simp only [Completed.diagnosticResults, List.map_nil, List.append_nil]
          exact afterPublish R eraseR
      | atomSelectionFailed _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp at exhausted

/-! ## Every settling term with arithmetic -/

/-- **Every settling term runs finely to its answers on the world machine**, on every marked
presentation, under every continuation fine on its answers. -/
theorem fine_settlesKG (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} (program : CallProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesKG atoms t L) : FineEvalW minimal lookup policy atoms t L := by
  induction settles with
  | @data d data _ => exact fine_dataW answers contract atoms data
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesKG.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          FineEvalW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesKG_shape both.1).1.answers a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      have headFine : FineRunsW minimal lookup policy atoms (.symbol f) [.symbol f] :=
        fine_dataW answers contract atoms head.head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f)
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesKG_value_self whole value]
        have runs := fine_heldW (minimal := minimal) (lookup := lookup) atoms reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rwa [eraseList] at runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact fine_nodeW contract head.head head.untyped closed headFine interpreted rfl args
          (fun vals => [.expression (.symbol f :: vals)])
          (fun vals member => ⟨fine_query_absentW (scoped_consFree program.scoped) head
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation),
            fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesKG.call R head defined length settled nonempty lengths bodies
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          FineEvalW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value heDispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesKG_shape both.1).2 a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      have headFine : FineRunsW minimal lookup policy atoms (.symbol f) [.symbol f] :=
        fine_dataW answers contract atoms head.head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f)
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim
      | active =>
          exact fine_nodeW contract head.head head.untyped closed headFine (Or.inr rfl) rfl args
            (fun vals => (R vals).flatten)
            (fun vals member => ⟨fine_query_equationsW program.scoped head
                (combos_all allValues vals member) (nonempty vals member)
                (forall₂_of_zip (lengths vals member) fun p inside =>
                  ⟨ihBodies vals member p inside, settlesKG_facts (bodies vals member p inside)⟩),
              fun a inside => by
                obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
                have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
                obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
                exact (settlesKG_shape settlesB).1.answers a inner⟩)
  | @grounded op ts Ls known untyped length settled ints ih =>
      have whole := SettlesKG.grounded known untyped length settled ints
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          FineEvalW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRunsW minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      have headFine : FineRunsW minimal lookup policy atoms (.symbol op) [.symbol op] :=
        fine_dataW answers contract atoms (intOp_head known) (.symbol op)
          (by simp only [Entry.Value.erase]) (.symbol op)
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          cases value with
          | data data => cases data
          | node head _ => exact (intOp_not_constructor known head).elim
      | active =>
          exact fine_nodeW contract (intOp_head known) untyped closed headFine (Or.inr rfl) rfl args
            (fun vals => [arith op vals])
            (fun vals member => by
              obtain ⟨a, b, rfl⟩ := ints vals member
              refine ⟨?_, fun x inside => ?_⟩
              · rw [arith_num]
                exact fine_grounded_query answers contract known a b
              · rw [List.mem_singleton] at inside
                subst inside
                rw [arith_num]
                exact answerable_of_data (intValue_dataAtom known a b))

/-- **The entry of a settling term is `FineW`.** -/
theorem fine_entryW (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} (program : CallProgram atoms) {c : Atom} {L : List Atom}
    (settles : SettlesKG atoms c L) :
    FineW minimal lookup policy (load (Space.ofList atoms) c Atom.undefinedType) :=
  fine_settlesKG answers contract program settles (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
    (marked_ofAtom c) [] [] Completed.Frame.empty [] [] (fun R _ => fine_topW R [])

/-- **Every run of HE's world machine on a settling term with arithmetic finishes, and every
finished run publishes PeTTa's answers.** From the entry (historical lookup, any policy, any minimal
services): the world step relation is well founded (no infinite run), and every reachable world
configuration either has a step or is final, and a final one publishes exactly `L`, which PeTTa's
run yields from some fuel on. -/
theorem every_run_finishes_kg (minimal : Minimal.Services) (policy : Policy) {atoms : List Atom}
    (program : CallProgram atoms) {c : Atom} {L : List Atom} (settles : SettlesKG atoms c L) :
    Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
        Completed.rawLookup policy a b)
        (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) ∧
      (∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) w →
        (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy w w') ∨
          ∃ emitted : List Result,
            w = WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = L) ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  have fine := fine_entryW (minimal := minimal) (policy := policy) raw_answers raw_contract program
    settles
  obtain ⟨_, N, every⟩ := every_complete_run_kg minimal policy program settles
  refine ⟨fine.acc_world, fun w path => ?_, N, fun n bigger => (every n bigger).1⟩
  rcases (fine.reaches_world path).progress with ⟨y, moves⟩ | ⟨space, emitted, same⟩
  · exact Or.inl ⟨_, moves⟩
  · have sameSpace := context_fixed path
    obtain ⟨world, context, control, stack, emitted'⟩ := w
    simp only [toFlat, HEOnTheStep.HEConfig,
      Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.mk.injEq] at same
    obtain ⟨sameContext, rfl, rfl, sameEmitted⟩ := same
    subst sameContext sameEmitted
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    cases world
    exact Or.inr ⟨emitted', rfl, (every N le_rfl).2 emitted' path⟩

/-- **The whole result under any lookup meeting the contract**: a complete world run exists, the
world step relation is well founded from the entry, every reachable world configuration steps or is
final, every final one publishes exactly `L`, and PeTTa's run yields `L` from some fuel on. -/
theorem every_run_finishes_kg_under (minimal : Minimal.Services) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (contract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} (program : CallProgram atoms) {c : Atom} {L : List Atom}
    (settles : SettlesKG atoms c L) :
    (∃ heAnswers : List Result,
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
        (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], heAnswers⟩)) ∧
      Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy a b)
        (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) ∧
      (∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) w →
        (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy w w') ∨
          ∃ emitted : List Result,
            w = WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = L) ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  obtain ⟨he, petta⟩ := settlesKG_agree minimal (lookup := lookup) (policy := policy) answers program
    settles
  have shape := (settlesKG_shape settles).1
  obtain ⟨R, _, path⟩ := he (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c) (marked_ofAtom c)
    [] [] Completed.Frame.empty [] []
  obtain ⟨N, stable⟩ := petta_complete shape.answerable.ground shape.answers
    (over_root_K petta fun σ => shows_ground_K shape.tree shape.answerable)
  have determined := settlesKG_determined (minimal := minimal) (lookup := lookup) (policy := policy)
    contract program settles
  have fine := fine_entryW (minimal := minimal) (policy := policy) answers contract program settles
  refine ⟨⟨R, path.trans (lift_path minimal (HERuns.publish_all _ R []))⟩, fine.acc_world,
    fun w reached => ?_, N, stable⟩
  rcases (fine.reaches_world reached).progress with ⟨y, moves⟩ | ⟨space, emitted, same⟩
  · exact Or.inl ⟨_, moves⟩
  · have sameSpace := context_fixed reached
    obtain ⟨world, context, control, stack, emitted'⟩ := w
    simp only [toFlat, HEOnTheStep.HEConfig,
      Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.mk.injEq] at same
    obtain ⟨sameContext, rfl, rfl, sameEmitted⟩ := same
    subst sameContext sameEmitted
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    cases world
    exact Or.inr ⟨emitted', rfl, determined (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
      (marked_ofAtom c) _ _ _ _ _ _ (complete_source_W reached)⟩

/-- **With either of HE's own lookups** (the historical list storage and the scoped fresh
variants): a complete world run exists, no world run is infinite or stuck, and every finished run
publishes PeTTa's answers. -/
theorem every_run_finishes_kg_with_he_lookups (minimal : Minimal.Services) (policy : Policy)
    {atoms : List Atom} (program : CallProgram atoms) {c : Atom} {L : List Atom}
    (settles : SettlesKG atoms c L) :
    ∀ lookup ∈ [Completed.rawLookup, Completed.scopedLookup],
      (∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], heAnswers⟩)) ∧
        Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          a b) (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) ∧
        (∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
            (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType)) w →
          (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy w w') ∨
            ∃ emitted : List Result,
              w = WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
              emitted.map (fun r => r.1.erase) = L) ∧
        ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } c)) = L := by
  intro lookup member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact every_run_finishes_kg_under minimal raw_answers raw_contract policy program settles
  · exact every_run_finishes_kg_under minimal scoped_answers scoped_contract policy program settles

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app)
open NestedArithmetic.Controls (quadRows quad_program quad_four toIntRows toInt_program toInt_ssz
  empty_program arith_seven)

/-- **Positive control: every world run of `(quad 4)` finishes with `16`.** -/
theorem quad_every_run_finishes (minimal : Minimal.Services) (policy : Policy) :
    Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
        Completed.rawLookup policy a b)
        (WorldConfiguration.ofReadOnly
          (load (Space.ofList quadRows) (app "quad" [num 4]) Atom.undefinedType)) ∧
      ∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy (WorldConfiguration.ofReadOnly
            (load (Space.ofList quadRows) (app "quad" [num 4]) Atom.undefinedType)) w →
        (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy w w') ∨
          ∃ emitted : List Result,
            w = WorldConfiguration.ofReadOnly ⟨Space.ofList quadRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [num 16] := by
  obtain ⟨acc, every, _⟩ := every_run_finishes_kg minimal policy quad_program quad_four
  exact ⟨acc, every⟩

/-- **Positive control: every world run of `(toInt (S (S Z)))` finishes with `2`.** -/
theorem toInt_every_run_finishes (minimal : Minimal.Services) (policy : Policy) :
    Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
        Completed.rawLookup policy a b)
        (WorldConfiguration.ofReadOnly (load (Space.ofList toIntRows)
          (app "toInt" [app "S" [app "S" [sym "Z"]]]) Atom.undefinedType)) ∧
      ∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy (WorldConfiguration.ofReadOnly (load (Space.ofList toIntRows)
            (app "toInt" [app "S" [app "S" [sym "Z"]]]) Atom.undefinedType)) w →
        (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy w w') ∨
          ∃ emitted : List Result,
            w = WorldConfiguration.ofReadOnly ⟨Space.ofList toIntRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [num 2] := by
  obtain ⟨acc, every, _⟩ := every_run_finishes_kg minimal policy toInt_program toInt_ssz
  exact ⟨acc, every⟩

/-- **Positive control: every world run of `(+ (* 2 3) 1)` finishes with `7`.** -/
theorem arith_every_run_finishes (minimal : Minimal.Services) (policy : Policy) :
    Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
        Completed.rawLookup policy a b)
        (WorldConfiguration.ofReadOnly
          (load (Space.ofList []) (app "+" [app "*" [num 2, num 3], num 1]) Atom.undefinedType)) ∧
      ∀ w, WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy (WorldConfiguration.ofReadOnly
            (load (Space.ofList []) (app "+" [app "*" [num 2, num 3], num 1]) Atom.undefinedType)) w →
        (∃ w', WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup
          policy w w') ∨
          ∃ emitted : List Result,
            w = WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [num 7] := by
  obtain ⟨acc, every, _⟩ := every_run_finishes_kg minimal policy empty_program arith_seven
  exact ⟨acc, every⟩

/-- **The extension is needed**: the host call `(+ 4 4)`, which has no step on the contextual
machine, steps on the world machine. -/
theorem host_steps_on_world (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}
    (atoms : List Atom) (live : List Atom) (scope : List String) (activation : Frame)
    (stack : List Continuation) (emitted : List Result) :
    (¬ ∃ next, HEStep heDispatch lookup policy ⟨Space.ofList atoms,
      .work (.call live scope (callValue "+" [num 4, num 4]) Atom.undefinedType activation), stack,
        emitted⟩ next) ∧
      ∃ y, WStep minimal lookup policy ⟨Space.ofList atoms,
        .work (.call live scope (callValue "+" [num 4, num 4]) Atom.undefinedType activation), stack,
          emitted⟩ y := by
  refine ⟨GroundedRuns.Controls.contextual_stuck _ live scope _ activation stack emitted, ?_⟩
  have produced : (services minimal).groundedAt (Space.ofList atoms) () live scope activation
      (callValue "+" [num 4, num 4]) (.ok [(Entry.Value.ofAtom (intValue "+" 4 4), Bindings.empty)])
      () :=
    ⟨.symbol "+", [num 4, num 4], .ok [(intValue "+" 4 4, Bindings.empty)],
      callValue_erase "+" [num 4, num 4], (he_outcome_exact .plus 4 4 _).mpr rfl, rfl⟩
  have rows : Completed.NativeOutcomeRel policy heDispatch (.symbol "+") [num 4, num 4]
      (callValue "+" [num 4, num 4]) (some Atom.undefinedType) activation
      (.ok [(Entry.Value.ofAtom (intValue "+" 4 4), Bindings.empty)])
      (.resume [(Entry.Value.ofAtom (intValue "+" 4 4), activation)]) :=
    .success (.cons (Frame.NativeRenewRel.empty policy activation) .nil)
  exact ⟨⟨Space.ofList atoms, .work (.boundaryBatch live scope none
      (.native (callValue "+" [num 4, num 4]) (some Atom.undefinedType) .emitted)
      [(Entry.Value.ofAtom (intValue "+" 4 4), activation)]), stack, emitted⟩,
    .internal (WorldLocalStepWith.callGroundedResume (callValue_erase "+" [num 4, num 4])
      (he_executable .plus) (HERuns.value_not_error (intOp_head .plus)
        (callValue_erase "+" [num 4, num 4])) produced rows)⟩

/-- **Negative control: the world machine diverges outside the class.** On `{(= (loop) (loop))}`
the world step relation is not well founded from the entry of `(loop)`, so `(loop)` is not `FineW`;
it is not a settling term either. -/
theorem loop_diverges_world (minimal : Minimal.Services) (policy : Policy) :
    ¬ Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
        Completed.rawLookup policy a b)
        (WorldConfiguration.ofReadOnly
          (load (Space.ofList AnswerBags.Controls.loopRows) (app "loop" []) Atom.undefinedType)) ∧
      ¬ FineW minimal Completed.rawLookup policy
        (load (Space.ofList AnswerBags.Controls.loopRows) (app "loop" []) Atom.undefinedType) := by
  have diverges : ¬ Acc (fun b a => WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch
      Completed.rawLookup policy a b)
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList AnswerBags.Controls.loopRows) (app "loop" []) Atom.undefinedType)) :=
    fun acc => EveryRunFinishes.Controls.loop_diverges_on
      (NestedArithmetic.Controls.not_host "loop" (by decide)) policy (acc_of_world_acc acc)
  exact ⟨diverges, fun fine => diverges fine.acc_world⟩

end Controls

#print axioms world_core
#print axioms acc_of_world_acc
#print axioms FineW.acc_world
#print axioms FineW.reaches_world
#print axioms FineW.progress
#print axioms fine_dataW
#print axioms fine_tupleW
#print axioms fine_equationsW
#print axioms fine_query_equationsW
#print axioms fine_nativeW
#print axioms fine_grounded_query
#print axioms fine_nodeW
#print axioms fine_settlesKG
#print axioms fine_entryW
#print axioms every_run_finishes_kg
#print axioms every_run_finishes_kg_under
#print axioms every_run_finishes_kg_with_he_lookups
#print axioms Controls.quad_every_run_finishes
#print axioms Controls.toInt_every_run_finishes
#print axioms Controls.arith_every_run_finishes
#print axioms Controls.host_steps_on_world
#print axioms Controls.loop_diverges_world

end EveryRunFinishesW

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
