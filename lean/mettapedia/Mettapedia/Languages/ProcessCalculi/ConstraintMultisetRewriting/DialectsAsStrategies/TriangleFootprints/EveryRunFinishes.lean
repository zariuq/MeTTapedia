import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.CompoundBindings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedRuns

/-!
# Every run of HE on a settling term finishes

The every-run theorems so far are about *complete* runs: every run of HE's machine that reaches a
completed phase publishes PeTTa's answers. HE's machine is a relation, so two more things could go
wrong: a run could get stuck before completing, or run forever. Here neither happens.

**`Fine x`** (inductive): `x` is final (`.returning []` with an empty stack), or `x` can step and
every successor is `Fine`. So from a `Fine` configuration no run gets stuck (`Fine.progress`,
`Fine.reaches`) and no run is infinite (`Fine.acc`, well-foundedness of the step relation from `x`).

The proof is a logical relation in continuation-passing form, the termination counterpart of
PeTTa's `Delivers`: `FineRuns v L` says that pending work on `v` is `Fine` under **every**
continuation stack that is `Fine` on every batch whose atoms are `L`. HE's choice points on the
fragment (tuple entry or fallback, cast frames, alpha variants of the frontier, unifier
environments) are all quantified: every successor is shown `Fine`, by inversion of the step. The
continuation frames compose (`fine_publish`, `fine_singleton`, `fine_append`, `fine_prepend`, …), and
the tasks are handled by the same inductions as the runs of `MarkedValues` (`fine_tuple`,
`fine_branches`, `fine_calls`, `fine_equations`, `fine_query_equations`, `fine_node`).

## Results

* `fine_settlesK`: every settling term of `CompoundBindings.SettlesK` is `FineEval` (every marked
  presentation, under every continuation fine on its answers).
* `every_run_finishes_k`: from the entry of a settling term (historical lookup, any policy), the step
  relation is well founded (no infinite run), and every reachable configuration either steps or is
  final, and then it publishes the term's answers. Together with `every_complete_run_k`: **every run
  completes, and every completed run publishes PeTTa's answers.**

## Controls

* `Controls.add_every_run_finishes` (positive): every run of `(add (S (S Z)) (S Z))` finishes with
  `(S (S (S Z)))`.
* `Controls.host_call_not_fine` (negative): on this machine a host call `(+ 4 4)` is stuck, so it is
  not `Fine`; the class excludes host heads (`NodeHead.notHost`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace EveryRunFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom isEmptyOrError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-! ## Configurations from which every run finishes -/

/-- **Every run from `x` finishes**: `x` is final, or `x` can step and every successor finishes. -/
inductive Fine (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    HEConfig → Prop
  | final {space : Space} {emitted : List Result} :
      Fine dispatch lookup policy ⟨space, .returning [], [], emitted⟩
  | step {x : HEConfig} : (∃ y, HEStep dispatch lookup policy x y) →
      (∀ y, HEStep dispatch lookup policy x y → Fine dispatch lookup policy y) →
      Fine dispatch lookup policy x

/-- A final configuration has no step. -/
theorem final_no_step {space : Space} {emitted : List Result} {y : HEConfig} :
    ¬ HEStep dispatch lookup policy ⟨space, .returning [], [], emitted⟩ y := by
  intro step
  cases step with
  | internal l => cases l

theorem Fine.next {x y : HEConfig} (fine : Fine dispatch lookup policy x)
    (step : HEStep dispatch lookup policy x y) : Fine dispatch lookup policy y := by
  cases fine with
  | final => exact absurd step final_no_step
  | step _ all => exact all y step

/-- **No infinite run**: the step relation is well founded from a `Fine` configuration. -/
theorem Fine.acc {x : HEConfig} (fine : Fine dispatch lookup policy x) :
    Acc (fun b a => HEStep dispatch lookup policy a b) x := by
  induction fine with
  | final => exact Acc.intro _ fun y step => absurd step final_no_step
  | step _ _ ih => exact Acc.intro _ fun y step => ih y step

/-- Every configuration reachable from a `Fine` one is `Fine`. -/
theorem Fine.reaches {x y : HEConfig} (fine : Fine dispatch lookup policy x)
    (path : Relation.ReflTransGen (HEStep dispatch lookup policy) x y) :
    Fine dispatch lookup policy y := by
  induction path with
  | refl => exact fine
  | tail _ step ih => exact ih.next step

/-- **No stuck configuration**: a `Fine` configuration steps or is final. -/
theorem Fine.progress {x : HEConfig} (fine : Fine dispatch lookup policy x) :
    (∃ y, HEStep dispatch lookup policy x y) ∨
      ∃ (space : Space) (emitted : List Result), x = ⟨space, .returning [], [], emitted⟩ := by
  cases fine with
  | final => exact Or.inr ⟨_, _, rfl⟩
  | step moves _ => exact Or.inl moves

/-- A configuration with one successor is `Fine` when that successor is. -/
theorem fine_det {x y : HEConfig} (moves : HEStep dispatch lookup policy x y)
    (only : ∀ z, HEStep dispatch lookup policy x z → z = y) (next : Fine dispatch lookup policy y) :
    Fine dispatch lookup policy x :=
  .step ⟨y, moves⟩ fun z step => by rw [only z step]; exact next

/-- Steps keep the space. -/
theorem space_fixed {x y : HEConfig}
    (path : Relation.ReflTransGen (HEStep dispatch lookup policy) x y) : y.space = x.space := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
      cases step with
      | internal _ => exact ih
      | publish => exact ih

/-! ## Continuation frames -/

section Frames

variable {space : Space} {stack : List Continuation} {emitted : List Result}

theorem fine_singleton {R : List Result}
    (next : Fine dispatch lookup policy ⟨space, .returning (R.map Completed.tupleSingleton), stack,
      emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .singleton :: stack, emitted⟩ :=
  fine_det (.internal .singleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_frame {live : List Atom} {scope : List String} {tail : List Entry.Value}
    {heads : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.branches live scope tail heads), stack,
      emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning heads, .branches live scope tail :: stack,
      emitted⟩ :=
  fine_det (.internal .branches) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_tupleTail {head : Entry.Value} {R : List Result}
    (next : Fine dispatch lookup policy ⟨space, .returning (R.map (Completed.tuplePrepend head)),
      stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .tupleTail head :: stack, emitted⟩ :=
  fine_det (.internal .tupleTail) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_append {remaining : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Task}
    {R : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work remaining, .prepend R :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .append remaining :: stack, emitted⟩ :=
  fine_det (.internal .append) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_prepend {selected R : List Result}
    (next : Fine dispatch lookup policy ⟨space, .returning (selected ++ R), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .prepend selected :: stack, emitted⟩ :=
  fine_det (.internal .prepend) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_calls_frame {live : List Atom} {scope : List String} {expected : Atom}
    {rows : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.calls live scope expected rows), stack,
      emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning rows, .calls live scope expected :: stack,
      emitted⟩ :=
  fine_det (.internal .calls) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_diagnostics {errors : List Atom} {activation : Frame} {R : List Result}
    (next : Fine dispatch lookup policy ⟨space,
      .returning (R ++ Completed.diagnosticResults errors activation), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .diagnostics errors activation :: stack,
      emitted⟩ :=
  fine_det (.internal .diagnostics) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundaryBatch_frame {live : List Atom} {scope : List String} {caller : Option Atom}
    {site : Completed.Boundary} {rows : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.boundaryBatch live scope caller site rows),
      stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning rows,
      .boundaryBatch live scope caller site :: stack, emitted⟩ :=
  fine_det (.internal .boundaryBatch) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

/-- The publication frame: every answer is answerable, so all are kept. -/
theorem fine_publish {R : List Result} {original : Atom} (clean : ∀ r ∈ R, Answerable r.1.erase)
    (next : Fine dispatch lookup policy ⟨space,
      .returning (R.map (Completed.publishResult policy original)), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .publish original :: stack, emitted⟩ := by
  have unchanged : R.map (Completed.readResult policy) = R :=
    map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (R.map (Completed.readResult policy)) R := by
    rw [unchanged]
    exact HERuns.success_all R fun r member => (clean r member).notError
  refine fine_det (.internal (.publish selected)) (fun z step => ?_) next
  cases step with
  | internal l =>
      cases l with
      | publish chosen =>
          rw [Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional chosen
            selected]

/-- **The top level drains every batch**: the publication rule moves the answers one by one. -/
theorem fine_top : ∀ (R emitted : List Result), Fine dispatch lookup policy ⟨space, .returning R, [],
    emitted⟩
  | [], _ => .final
  | r :: rs, emitted => fine_det .publish (fun z step => by
      cases step with
      | internal l => cases l
      | publish => rfl) (fine_top rs (emitted ++ [r]))

end Frames

/-! ## Deterministic task steps -/

section Tasks

variable {space : Space} {stack : List Continuation} {emitted : List Result} {live : List Atom}
  {scope : List String}

theorem fine_tuple_singleton {v : Entry.Value} {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.atom live scope v Atom.undefinedType activation), .singleton :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.tuple live scope [v] activation), stack, emitted⟩ :=
  fine_det (.internal .tupleSingleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_tuple_cons {head second : Entry.Value} {remaining : List Entry.Value} {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.atom (.expression ((second :: remaining).map Entry.Value.erase) :: live) scope head
        Atom.undefinedType activation), .branches live scope (second :: remaining) :: stack,
        emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.tuple live scope (head :: second :: remaining)
      activation), stack, emitted⟩ :=
  fine_det (.internal .tupleCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_nil {tail : List Entry.Value}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.branches live scope tail []), stack, emitted⟩ :=
  fine_det (.internal .branchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_branches_cons {tail : List Entry.Value} {head : Result} {heads : List Result}
    (clean : ¬ IsEmptyOrErrorRel head.1.erase)
    (next : Fine dispatch lookup policy ⟨space, .work (.tuple (head.1.erase :: live) scope tail head.2),
      .tupleTail head.1 :: .append (.branches live scope tail heads) :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.branches live scope tail (head :: heads)), stack,
      emitted⟩ :=
  fine_det (.internal (.branchesContinue clean)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | branchesStopped stopped => exact absurd stopped clean
        | branchesContinue _ => rfl) next

theorem fine_calls_nil {expected : Atom}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.calls live scope expected []), stack, emitted⟩ :=
  fine_det (.internal .callsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_calls_cons {expected : Atom} {head : Result} {heads : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.call live scope head.1 expected head.2),
      .append (.calls live scope expected heads) :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.calls live scope expected (head :: heads)), stack,
      emitted⟩ :=
  fine_det (.internal .callsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_equations_nil {original : Entry.Value} {expected : Atom} {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.equations live scope original expected activation []),
      stack, emitted⟩ :=
  fine_det (.internal .equationsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundary_producer {caller : Option Atom} {value : Entry.Value} {activation : Frame}
    (raw : ¬ Completed.FunctionPending policy value)
    (next : Fine dispatch lookup policy ⟨space, .returning [(value, activation)], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.boundary live scope caller .producer value activation),
      stack, emitted⟩ :=
  fine_det (.internal (.boundaryProducerRaw raw)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | boundaryProducerRaw _ => rfl
        | boundaryProducerFunction pending => exact absurd pending raw) next

theorem fine_boundaryBatch_nil {caller : Option Atom} {site : Completed.Boundary}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.boundaryBatch live scope caller site []), stack,
      emitted⟩ :=
  fine_det (.internal .boundaryBatchNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundaryBatch_cons {caller : Option Atom} {site : Completed.Boundary} {head : Result}
    {heads : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.boundary live scope caller site head.1 head.2),
      .append (.boundaryBatch live scope caller site heads) :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.boundaryBatch live scope caller site (head :: heads)),
      stack, emitted⟩ :=
  fine_det (.internal .boundaryBatchCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_boundary_returned {caller : Option Atom} {original value : Entry.Value} {expected : Atom}
    {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.boundary live scope caller (.returned original expected) value activation), stack,
        emitted⟩ :=
  fine_det (.internal .boundaryReturned) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_returned_evaluate {original value : Entry.Value} {expected : Atom} {activation : Frame}
    (notRefused : value.erase ≠ Atom.notReducible) (notStopped : ¬ IsEmptyOrErrorRel value.erase)
    (next : Fine dispatch lookup policy ⟨space,
      .work (.atom live scope value expected activation), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩ :=
  fine_det (.internal (.returnEvaluate notRefused notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | returnRefused refused => exact absurd refused notRefused
        | returnStopped stopped => exact absurd stopped notStopped
        | returnEvaluate _ _ => rfl) next

end Tasks

/-! ## The logical relation -/

/-- **Every run from pending work on `v` finishes, with answers `L`**: under every continuation stack
that is `Fine` on every batch whose atoms are `L`, pending work on `v` is `Fine`. -/
def FineRuns (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    (∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
    Fine dispatch lookup policy ⟨Space.ofList atoms,
      .work (.atom live scope v Atom.undefinedType activation), stack, emitted⟩

/-- **Every marked presentation of `t` runs finely to `L`.** -/
def FineEval (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v → FineRuns dispatch lookup policy atoms v L

/-- **Every query of `(f vals)`, on every call value, runs finely to `A`.** -/
def FineQuery (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (f : String) (vals A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) →
    ∀ (stack : List Continuation) (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = A →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      Fine dispatch lookup policy ⟨Space.ofList atoms,
        .work (.call live scope value Atom.undefinedType activation), stack, emitted⟩

/-- **A data atom**: its cast is the only step, and every cast result is the atom. -/
theorem fine_data (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    (atoms : List Atom) {d : Atom} (data : DataAtom d) : FineEval dispatch lookup policy atoms d [d] := by
  intro v erased _ live scope activation stack emitted cont
  rw [value_of_data data erased]
  have entry : Entry.Rel policy.reentry (activation.read policy (Entry.Value.ofAtom d)).status
      (activation.read policy (Entry.Value.ofAtom d)).erase Atom.undefinedType .cast := by
    simp only [CompleteRun.read_data policy activation data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  refine .step ⟨_, CompleteRun.cast_step_frame (dispatch := dispatch) (policy := policy) answers
    (Space.ofList atoms) data activation live scope stack emitted⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered batch related =>
          have derived : Completed.AtomRel (Space.ofList atoms) dispatch lookup _ _ _ _ _ _
              (policy := policy) := .cast entered batch related
          obtain ⟨after, rfl⟩ := data_source contract data derived
          exact cont _ (by simp)
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-- **A held expression under reuse is delivered**, the only step. -/
theorem fine_held (atoms : List Atom) {children : List Entry.Value}
    (reuses : policy.reentry = .reuse)
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (children.map Entry.Value.erase)) name)
    (notStopped : ¬ IsEmptyOrErrorRel (.expression (children.map Entry.Value.erase))) :
    FineRuns dispatch lookup policy atoms (.expression .held children)
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
  refine .step ⟨_, .internal (.delivered entry)⟩ ?_
  intro y step
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

/-- `tuplePrepend` on a row that is an expression, whatever its mark. -/
theorem tuplePrepend_erase_any (head : Entry.Value) {r : Result} {c0 : Atom} {cs : List Atom}
    (erased : r.1.erase = .expression (c0 :: cs)) (clean : Answerable c0) :
    (Completed.tuplePrepend head r).1.erase = .expression (head.erase :: c0 :: cs) := by
  obtain ⟨value, frame⟩ := r
  simp only at erased ⊢
  cases value with
  | symbol _ => simp [Entry.Value.erase] at erased
  | var _ => simp [Entry.Value.erase] at erased
  | grounded _ => simp [Entry.Value.erase] at erased
  | expression readiness children =>
      have stopped : isEmptyOrError (Entry.Value.expression readiness children).erase = false := by
        rw [erased]
        exact HENested.expression_clean clean
      have unfolded : Completed.tuplePrepend head (Entry.Value.expression readiness children, frame) =
          (.expression .active (head :: children), frame) := by
        unfold Completed.tuplePrepend
        simp [stopped]
      rw [unfolded]
      simp only [Entry.Value.erase, Atom.expression.injEq] at erased ⊢
      rw [List.map_cons, erased]

/-- **The branches of a tuple's head**, for every successor: each answer's tail is a fine tuple. -/
theorem fine_branches (atoms : List Atom) {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ts : List (List Atom)}
    (tailFine : ∀ (live' : List Atom) (activation : Frame) (stack : List Continuation)
      (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = Ts.map Atom.expression →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      Fine dispatch lookup policy ⟨Space.ofList atoms, .work (.tuple live' scope tail activation),
        stack, emitted⟩)
    (tailClean : ∀ c ∈ Ts, ∃ c0 cs, c = c0 :: cs ∧ Answerable c0) :
    ∀ (heads : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            heads.flatMap (fun h => Ts.map fun c => Atom.expression (h.1.erase :: c)) →
          Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .work (.branches live scope tail heads),
          stack, emitted⟩
  | [], _, stack, emitted, cont => fine_branches_nil (cont [] rfl)
  | h :: hs, clean, stack, emitted, cont => by
      have hClean := clean h List.mem_cons_self
      apply fine_branches_cons hClean.notStopped
      apply tailFine (h.1.erase :: live) h.2
        (.tupleTail h.1 :: .append (.branches live scope tail hs) :: stack) emitted
      intro Rt eraseRt
      apply fine_tupleTail
      apply fine_append
      apply fine_branches atoms tailFine tailClean hs
        (fun x member => clean x (List.mem_cons_of_mem _ member))
        (.prepend (Rt.map (Completed.tuplePrepend h.1)) :: stack) emitted
      intro Rh eraseRh
      apply fine_prepend
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
theorem fine_tuple (atoms : List Atom) :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)), vs ≠ [] →
      List.Forall₂ (fun v L => FineRuns dispatch lookup policy atoms v L ∧ ∀ a ∈ L, Answerable a)
        vs Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression →
          Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .work (.tuple live scope vs activation),
          stack, emitted⟩
  | [], _, nonempty, _ => absurd rfl nonempty
  | [v], Ls, _, related => by
      intro live scope activation stack emitted cont
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          apply fine_tuple_singleton
          apply here.1 live scope activation (.singleton :: stack) emitted
          intro R eraseR
          apply fine_singleton
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
          have tailFine := fine_tuple atoms (v2 :: rest) Ls' (List.cons_ne_nil _ _) later
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
          apply fine_tuple_cons
          apply here.1 _ scope activation (.branches live scope (v2 :: rest) :: stack) emitted
          intro R eraseR
          apply fine_branches_frame
          apply fine_branches atoms (live := live) (fun live' activation' stack' emitted' cont' =>
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
theorem fine_calls (atoms : List Atom) {live : List Atom} {scope : List String} {f : String}
    (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQuery dispatch lookup policy atoms f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) →
          Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch lookup policy ⟨Space.ofList atoms,
          .work (.calls live scope Atom.undefinedType rows), stack, emitted⟩
  | [], _, stack, emitted, cont => fine_calls_nil (cont [] rfl)
  | r :: rs, queries, stack, emitted, cont => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      apply fine_calls_cons
      apply query live scope r.2 r.1 erased (.append (.calls live scope Atom.undefinedType rs) :: stack)
        emitted
      intro Qr eraseQr
      apply fine_append
      apply fine_calls atoms Q rs (fun x member => queries x (List.mem_cons_of_mem _ member))
        (.prepend Qr :: stack) emitted
      intro Rs eraseRs
      apply fine_prepend
      apply cont
      rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
      rfl

/-- **The equation loop**, for every unifier output of every work. -/
theorem fine_equations (atoms : List Atom) {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEval dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = Ls.flatten →
          Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch lookup policy ⟨Space.ofList atoms,
          .work (.equations live scope original Atom.undefinedType activation works), stack, emitted⟩
  | [], Ls, _, related, stack, emitted, cont => by
      cases related
      exact fine_equations_nil (cont [] rfl)
  | work :: works, Ls, unifiers, related, stack, emitted, cont => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨i, readsAs, fineI, facts⟩ := here
          obtain ⟨output₀, sameBindings₀, unified₀⟩ := unifiers work List.mem_cons_self
          refine .step ⟨_, .internal (.equationsCons sameBindings₀ unified₀)⟩ ?_
          intro y step
          cases step with
          | internal l =>
              cases l with
              | equationsCons sameBindings _ =>
                  obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings
                  apply fine_boundary_producer (not_pending facts readErase)
                  apply fine_boundaryBatch_frame
                  apply fine_boundaryBatch_cons
                  apply fine_boundary_returned
                  apply fine_returned_evaluate (by rw [readErase]; exact facts.notRefused)
                    (by rw [readErase]; exact facts.notStopped)
                  refine fineI _ readErase readMarked _ _ _ _ _ ?_
                  intro Rb eraseRb
                  apply fine_append
                  apply fine_boundaryBatch_nil
                  apply fine_prepend
                  apply fine_append
                  apply fine_equations atoms works Ls'
                    (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
                    (.prepend (Rb ++ []) :: stack) emitted
                  intro Rs eraseRs
                  apply fine_prepend
                  apply cont
                  rw [List.append_nil, List.map_append, eraseRb, eraseRs, List.flatten_cons]

/-- **A query with an empty region**: `callAbsent` is the only step, returning the call. -/
theorem fine_query_absent {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (empty : regionBodies atoms f vals = []) :
    FineQuery dispatch lookup policy atoms f vals [.expression (.symbol f :: vals)] := by
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
  refine .step ⟨_, .internal (.callAbsent (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier')⟩ ?_
  intro y step
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

/-- **A query with a nonempty region of instances**: every frontier the machine may choose fires,
and each work's body is read as a marked value of its instance. -/
theorem fine_query_equations {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value dispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => FineEval dispatch lookup policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    FineQuery dispatch lookup policy atoms f vals Ls.flatten := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  -- the queries every frontier gives
  have fromFrontier : ∀ (works : List EquationWork),
      EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
        (.expression (.symbol f :: vals)) activation.bindings works →
      Fine dispatch lookup policy ⟨Space.ofList atoms,
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
            Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEval dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls :=
      (forall₂_comp instances bodies).imp fun _ _ both => by
        obtain ⟨i, ⟨_, reads⟩, fineI, facts⟩ := both
        exact ⟨i, reads, fineI, facts⟩
    exact fine_equations atoms works Ls unifiers related stack emitted cont
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
  refine .step ⟨_, .internal (.callEquations (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier'
    worksNonempty)⟩ ?_
  intro y step
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

/-- **A marked call whose root HE interprets**: the tuple entry or the fallback (with no
diagnostics), the argument product, the calls of each combination, the publication. -/
theorem fine_node (contract : LookupContract lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    (headFine : FineRuns dispatch lookup policy atoms (.symbol f) [.symbol f])
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => FineRuns dispatch lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, FineQuery dispatch lookup policy atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    FineRuns dispatch lookup policy atoms (.expression readiness (.symbol f :: vs))
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
  -- the publication, then the caller's continuation
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol f :: ts)) :: stack, emitted⟩ := by
    intro R eraseR
    apply fine_publish (HENested.clean_of_erase eraseR answerableAll)
    apply cont
    rw [publish_erase, eraseR]
  -- the rows of the argument product, then their calls
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .returning R, rest, emitted⟩) →
      ∀ rows : List Result, rows.map (fun r => r.1.erase) =
          (combos ([.symbol f] :: Ls)).map Atom.expression →
        Fine dispatch lookup policy ⟨Space.ofList atoms, .returning rows,
          .calls live scope Atom.undefinedType :: rest, emitted⟩ := by
    intro rest restFine rows eraseRows
    rw [combos_head] at eraseRows
    apply fine_calls_frame
    have queries : ∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQuery dispatch lookup policy atoms f vals (Q vals) := by
      intro r member
      have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
        rw [← eraseRows]
        exact List.mem_map.mpr ⟨r, member, rfl⟩
      rw [List.map_map] at inRows
      obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
      exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
    apply fine_calls atoms Q rows queries rest emitted
    intro R eraseR
    apply restFine
    rw [eraseR]
    have viaAtoms : rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (rows.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseRows, List.map_map, List.flatMap_map]
    rfl
  have argsAll : List.Forall₂ (fun v L => FineRuns dispatch lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) (Entry.Value.symbol f :: vs) ([.symbol f] :: Ls) :=
    .cons ⟨headFine, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args
  refine .step ⟨_, .internal (LocalStepWith.atomTuple entry readV occurrences)⟩ ?_
  intro y step
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
          exact fine_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _) argsAll
            _ scope activation _ emitted (afterRows _ afterPublish)
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
          refine fine_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _) argsAll
            _ scope activation _ emitted (afterRows _ ?_)
          intro R eraseR
          apply fine_diagnostics
          simp only [Completed.diagnosticResults, List.map_nil, List.append_nil]
          exact afterPublish R eraseR
      | atomSelectionFailed _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp at exhausted

/-! ## Every settling term -/

/-- **Every settling term runs finely to its answers**, on every marked presentation, under every
continuation fine on its answers. -/
theorem fine_settlesK (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} (program : CallProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) : FineEval dispatch lookup policy atoms t L := by
  induction settles with
  | @data d data _ => exact fine_data answers contract atoms data
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesK.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          FineEval dispatch lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesK_shape both.1).1.answers a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRuns dispatch lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape both.1).1.answers⟩
      have headFine : FineRuns dispatch lookup policy atoms (.symbol f) [.symbol f] :=
        fine_data answers contract atoms head.head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f)
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesK_value_self whole value]
        have runs := fine_held (dispatch := dispatch) (lookup := lookup) atoms reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rwa [eraseList] at runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact fine_node contract head.head head.untyped closed headFine interpreted rfl args
          (fun vals => [.expression (.symbol f :: vals)])
          (fun vals member => ⟨fine_query_absent (scoped_consFree program.scoped) head
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation),
            fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesK.call R head defined length settled nonempty lengths bodies
      have argsT : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          FineEval dispatch lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesK_shape both.1).2 a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRuns dispatch lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape both.1).1.answers⟩
      have headFine : FineRuns dispatch lookup policy atoms (.symbol f) [.symbol f] :=
        fine_data answers contract atoms head.head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f)
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim
      | active =>
          exact fine_node contract head.head head.untyped closed headFine (Or.inr rfl) rfl args
            (fun vals => (R vals).flatten)
            (fun vals member => ⟨fine_query_equations program.scoped head
                (combos_all allValues vals member) (nonempty vals member)
                (forall₂_of_zip (lengths vals member) fun p inside =>
                  ⟨ihBodies vals member p inside, settlesK_facts (bodies vals member p inside)⟩),
              fun a inside => by
                obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
                have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
                obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
                exact (settlesK_shape settlesB).1.answers a inner⟩)

/-- **The entry of a settling term is `Fine`.** -/
theorem fine_entry (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} (program : CallProgram atoms) {c : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms c L) :
    Fine dispatch lookup policy (load (Space.ofList atoms) c Atom.undefinedType) :=
  fine_settlesK answers contract program settles (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
    (marked_ofAtom c) [] [] Completed.Frame.empty [] [] (fun R _ => fine_top R [])

/-- **Every run of HE on a settling term finishes, and every finished run publishes PeTTa's
answers.** For a settling term (historical lookup, any policy): the step relation is well founded
from the entry (no infinite run), and every configuration reachable from the entry either has a
step or is final, and a final one publishes exactly `L`, which PeTTa's run yields from some fuel
on. -/
theorem every_run_finishes_k (policy : Policy) {atoms : List Atom} (program : CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : SettlesK dispatch atoms c L) :
    Acc (fun b a => HEStep dispatch Completed.rawLookup policy a b)
        (load (Space.ofList atoms) c Atom.undefinedType) ∧
      (∀ y, Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType) y →
        (∃ z, HEStep dispatch Completed.rawLookup policy y z) ∨
          ∃ emitted : List Result, y = ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = L) ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  have fine := fine_entry (policy := policy) raw_answers raw_contract program settles
  obtain ⟨_, N, every⟩ := every_complete_run_k policy program settles
  refine ⟨fine.acc, fun y path => ?_, N, fun n bigger => (every n bigger).1⟩
  rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
  · exact Or.inl moves
  · have sameSpace := space_fixed path
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    exact Or.inr ⟨emitted, rfl, (every N le_rfl).2 emitted path⟩

/-- **A cycle defeats well-foundedness**: if every configuration satisfying `P` reaches another one
in at least one step, then no configuration from which the step relation is well founded reaches a
configuration satisfying `P`. -/
theorem not_acc_of_cycle {P : HEConfig → Prop}
    (cycle : ∀ x, P x → ∃ y, Relation.TransGen (HEStep dispatch lookup policy) x y ∧ P y) :
    ∀ x, Acc (fun b a => HEStep dispatch lookup policy a b) x →
      ∀ y, Relation.ReflTransGen (HEStep dispatch lookup policy) x y → ¬ P y := by
  intro x acc
  induction acc with
  | intro x _ ih =>
      intro y path py
      rcases Relation.ReflTransGen.cases_head path with same | ⟨c, first, rest⟩
      · subst same
        obtain ⟨y', trans, py'⟩ := cycle _ py
        obtain ⟨y1, first, rest⟩ := Relation.TransGen.head'_iff.mp trans
        exact ih y1 first y' rest py'
      · exact ih c first y rest py

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule loopRows)
open WholeRunWords.Double (noHost)
open CompoundBindings.Controls (peanoRows peano_program add_ssz_sz SSZ SZ SSSZ)

/-- **Positive control: every run of Peano addition finishes.** `(add (S (S Z)) (S Z))`: no run of
HE's machine is infinite, every reachable configuration steps or is final, and every final one
publishes `(S (S (S Z)))`, under every policy. -/
theorem add_every_run_finishes (policy : Policy) :
    Acc (fun b a => HEStep noHost Completed.rawLookup policy a b)
        (load (Space.ofList peanoRows) (app "add" [SSZ, SZ]) Atom.undefinedType) ∧
      ∀ y, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList peanoRows) (app "add" [SSZ, SZ]) Atom.undefinedType) y →
        (∃ z, HEStep noHost Completed.rawLookup policy y z) ∨
          ∃ emitted : List Result, y = ⟨Space.ofList peanoRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [SSSZ] := by
  obtain ⟨acc, every, _⟩ := every_run_finishes_k policy peano_program add_ssz_sz
  exact ⟨acc, every⟩

/-- **Negative control: a stuck configuration is not `Fine`.** On HE's contextual machine with the
integer dispatch, the host call `(+ 4 4)` has no step and is not final. -/
theorem host_call_not_fine {lookup : CastLookup} {policy : Policy} (space : Space)
    (live : List Atom) (scope : List String) (expected : Atom) (activation : Frame)
    (stack : List Continuation) (emitted : List Result) :
    ¬ Fine GroundedTables.heDispatch lookup policy ⟨space,
      .work (.call live scope (callValue "+" [GroundedTables.num 4, GroundedTables.num 4]) expected
        activation), stack, emitted⟩ := by
  intro fine
  rcases fine.progress with moves | ⟨_, _, same⟩
  · exact GroundedRuns.Controls.contextual_stuck space live scope expected activation stack emitted
      moves
  · cases same

/-- Pending work on `(loop)`, anywhere. -/
def LoopEntry (x : HEConfig) : Prop :=
  ∃ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result), x = ⟨Space.ofList loopRows,
      .work (.atom live scope (Entry.Value.ofAtom (app "loop" [])) Atom.undefinedType activation),
      stack, emitted⟩

/-- **`(loop)` comes back to itself**: from pending work on `(loop)`, HE's machine enters the call,
fires the query, reads the body `(loop)` and evaluates it again, under a longer stack. This holds
under every dispatch that does not execute `loop`. -/
theorem loop_cycle_on {dispatch : GroundedDispatch} (notHost : ¬ dispatch.executable (.symbol "loop"))
    (policy : Policy) : ∀ x, LoopEntry x →
    ∃ y, Relation.TransGen (HEStep dispatch Completed.rawLookup policy) x y ∧ LoopEntry y := by
  rintro x ⟨live, scope, activation, stack, emitted, rfl⟩
  have loopHead : DataAtom (.symbol "loop") := .symbol (by decide) (by decide)
  have loopData : ∀ a ∈ Atom.symbol "loop" :: ([] : List Atom), DataAtom a := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact loopHead
  have untyped : (Space.ofList loopRows).atoms.filter (typeRegion (.symbol "loop")) = [] := by
    decide +kernel
  have entry := HERuns.call_entry_steps (dispatch := dispatch) (lookup := Completed.rawLookup)
    (policy := policy) raw_answers loopData untyped live scope activation stack emitted
  have program : ∀ row ∈ loopRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [loopRows, List.mem_singleton] at member
    subst member
    exact AnswerBags.Controls.rule_consFree fun a member => by cases member
  have bodies : regionBodies loopRows "loop" [] = [app "loop" []] := by decide +kernel
  have loopFixed : ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename
        (app "loop" []) = app "loop" [] := by
    intro rename
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  have fixed : ∀ b ∈ regionBodies loopRows "loop" [], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [bodies]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    exact loopFixed rename
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList loopRows) (Atom.undefinedType :: live)
    (app "loop" []) activation.bindings
  have bodiesEq := HERuns.frontier_bodies (fun v member => by cases member)
    activation.certified.satisfiable program fixed frontier
  rw [bodies] at bodiesEq
  obtain ⟨w, rfl⟩ : ∃ w, works = [w] := by
    cases works with
    | nil => simp at bodiesEq
    | cons w rest =>
        cases rest with
        | nil => exact ⟨w, rfl⟩
        | cons _ _ => simp at bodiesEq
  have body : w.body = app "loop" [] := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
    exact bodiesEq
  have frontier' : EquationFrontierRel (Space.ofList loopRows) (Atom.undefinedType :: live)
      (callValue "loop" []).erase activation.bindings [w] := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
  let output : Frame := ⟨w.bindings, after, certificate⟩
  have closedLoop : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (app "loop" []) name := (call_answerable loopHead fun _ member => by cases member).closed
  have readBody : output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom (app "loop" []) := by
    rw [body]
    exact HERuns.read_closed policy output closedLoop
  have notFunction : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom (app "loop" [])) := by
    rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    simp at same
  have callStep : HEStep dispatch Completed.rawLookup policy
      ⟨Space.ofList loopRows, .work (.call live scope (callValue "loop" []) Atom.undefinedType
        activation), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩
      ⟨Space.ofList loopRows, .work (.equations live scope (callValue "loop" []) Atom.undefinedType
        activation [w]), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩ :=
    .internal (.callEquations (HERuns.value_not_error loopHead (callValue_erase "loop" []))
      (HERuns.value_nonGrounded notHost (by decide)
        (callValue_erase "loop" [])) frontier' (List.cons_ne_nil _ _))
  have rest : Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
      ⟨Space.ofList loopRows, .work (.equations live scope (callValue "loop" []) Atom.undefinedType
        activation [w]), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩
      ⟨Space.ofList loopRows, .work (.atom live scope (Entry.Value.ofAtom (app "loop" []))
        Atom.undefinedType output),
        .append (.boundaryBatch live scope none (.returned (callValue "loop" []) Atom.undefinedType)
          []) :: .append (.equations live scope (callValue "loop" []) Atom.undefinedType activation
          []) :: .append (.calls live scope Atom.undefinedType []) :: .publish (app "loop" []) ::
          stack, emitted⟩ := by
    refine .head (.internal (.equationsCons (output := output) rfl unified)) ?_
    rw [readBody]
    refine .head (.internal (.boundaryProducerRaw notFunction)) ?_
    refine .head (.internal .boundaryBatch) ?_
    refine .head (.internal .boundaryBatchCons) ?_
    refine .head (.internal .boundaryReturned) ?_
    refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
    · rw [Entry.Value.erase_ofAtom]
      intro same
      cases same
    · rw [Entry.Value.erase_ofAtom]
      exact call_not_stopped loopHead
    exact .refl
  exact ⟨_, Relation.TransGen.trans_left (Relation.TransGen.tail' entry callStep) rest,
    ⟨_, _, _, _, _, rfl⟩⟩

/-- `loop_cycle_on` for the dispatch that executes nothing. -/
theorem loop_cycle (policy : Policy) : ∀ x, LoopEntry x →
    ∃ y, Relation.TransGen (HEStep noHost Completed.rawLookup policy) x y ∧ LoopEntry y :=
  loop_cycle_on (fun impossible => impossible) policy

/-- **`(loop)` diverges under every dispatch that does not execute `loop`.** -/
theorem loop_diverges_on {dispatch : GroundedDispatch}
    (notHost : ¬ dispatch.executable (.symbol "loop")) (policy : Policy) :
    ¬ Acc (fun b a => HEStep dispatch Completed.rawLookup policy a b)
        (load (Space.ofList loopRows) (app "loop" []) Atom.undefinedType) := fun acc =>
  not_acc_of_cycle (loop_cycle_on notHost policy) _ acc _ .refl
    ⟨[], [], Completed.Frame.empty, [], [], rfl⟩

/-- **Negative control: the theorem has content; HE's machine diverges outside the class.** On
`{(= (loop) (loop))}` the step relation is not well founded from the entry of `(loop)`: HE has an
infinite run, so `(loop)` is not `Fine`. -/
theorem loop_diverges (policy : Policy) :
    ¬ Acc (fun b a => HEStep noHost Completed.rawLookup policy a b)
        (load (Space.ofList loopRows) (app "loop" []) Atom.undefinedType) ∧
      ¬ Fine noHost Completed.rawLookup policy
        (load (Space.ofList loopRows) (app "loop" []) Atom.undefinedType) := by
  have diverges := loop_diverges_on (dispatch := noHost) (fun impossible => impossible) policy
  exact ⟨diverges, fun fine => diverges fine.acc⟩

/-- **Negative control: `(loop)` lies outside the class.** No settling derivation exists for it,
whatever the answers. -/
theorem loop_not_settlesK (L : List Atom) : ¬ SettlesK noHost loopRows (app "loop" []) L := by
  have instances : regionInstances loopRows "loop" [] = [app "loop" []] := by decide +kernel
  intro settles
  generalize same : app "loop" [] = t at settles
  induction settles with
  | data data _ =>
      subst same
      cases data
  | build _ noEquation _ _ _ =>
      have defined : (loopRows.filterMap LiveEquations.equationOfRow).all
          (fun equation => equation.head != "loop") = false := by decide +kernel
      simp only [app, Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [defined] at noEquation
      cases noEquation
  | call R _ _ length _ _ lengths _ _ ihBodies =>
      simp only [app, Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have noArgs : combos [] = [[]] := rfl
      cases (List.length_eq_zero_iff.mp length.symm)
      have inner := ihBodies [] (by rw [noArgs]; exact List.mem_singleton_self _)
      have one := lengths [] (by rw [noArgs]; exact List.mem_singleton_self _)
      rw [instances] at inner one
      obtain ⟨Lb, hLb⟩ : ∃ Lb, R [] = [Lb] := by
        cases hR : R [] with
        | nil => rw [hR] at one; simp at one
        | cons Lb rest =>
            cases rest with
            | nil => exact ⟨Lb, rfl⟩
            | cons _ _ => rw [hR] at one; simp at one
      rw [hLb] at inner
      exact inner (app "loop" [], Lb) (by simp) rfl

end Controls

#print axioms Fine.acc
#print axioms Fine.progress
#print axioms fine_publish
#print axioms fine_top
#print axioms fine_data
#print axioms fine_held
#print axioms fine_branches
#print axioms fine_tuple
#print axioms fine_calls
#print axioms fine_equations
#print axioms fine_query_absent
#print axioms fine_query_equations
#print axioms fine_node
#print axioms fine_settlesK
#print axioms fine_entry
#print axioms every_run_finishes_k
#print axioms not_acc_of_cycle
#print axioms Controls.add_every_run_finishes
#print axioms Controls.host_call_not_fine
#print axioms Controls.loop_cycle_on
#print axioms Controls.loop_cycle
#print axioms Controls.loop_diverges_on
#print axioms Controls.loop_diverges
#print axioms Controls.loop_not_settlesK

end EveryRunFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
