import Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations
import Mettapedia.Languages.MeTTa.HE.EquationFrontierExtension
import Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.HETypedReplacement

/-!
# Replacing a snapshot in HE

An invocation retains its selected body and competing occurrences.
For a fresh invocation, extending a space by independently rejected
atoms preserves its complete frontier in both directions. A new
matching occurrence is not an irrelevant extension. A typed call
also needs its type queries protected; rejection from a function
frontier alone does not supply that evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEObservationReplacement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (WorldEnvironment Policy Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation WorldConfiguration)
open Mettapedia.GSLT.Contracts.OccurrenceObservers (Demand)
open Mettapedia.GSLT.Contracts.OccurrenceExecution (completed completed_iff_chain readCompleted reports ofTerm reports_congr)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open EvaluationObservations (heView heEmit)
open HEInvocationEntry (Input Mode Request Reply Licensed)
open HEFocused (Focus Parent NativeRequest)

private theorem no_work_of_rejected {live : List Atom} {query declaration : Atom} {incoming : Bindings}
    {ordinal : Nat} {work : List EquationWork}
    (rejected : EquationRowResultsRel live query incoming ordinal declaration [])
    (covered : EquationRowResultsRel live query incoming ordinal declaration work) : work = [] := by
  cases covered with
  | irrelevant | miss => rfl
  | hit left right pattern body matched output fresh matching merged =>
    cases rejected with
    | irrelevant _ notDefinition => exact (notDefinition left right rfl).elim
    | miss _ _ _ _ _ absent => exact (absent pattern body fresh matched output ⟨matching, merged⟩).elim

private theorem rejected_flatten {live : List Atom} {query : Atom} {incoming : Bindings}
    {entries : List (Atom × Nat)} {blocks : List (List EquationWork)}
    (checked : List.Forall₂ (fun e b => EquationRowResultsRel live query incoming e.2 e.1 b) entries blocks)
    (rejected : ∀ e ∈ entries, EquationRowResultsRel live query incoming e.2 e.1 []) :
    blocks.flatten = [] := by
  induction checked with
  | nil => rfl
  | @cons entry work entries blocks covered remaining ih =>
    have noneHere := no_work_of_rejected (rejected entry List.mem_cons_self) covered
    have noneLater := ih fun e found => rejected e (List.mem_cons_of_mem _ found)
    simp only [List.flatten_cons, noneHere, noneLater, List.nil_append]

/-- Rejected appended atoms contribute no additional alternatives, and
the existing alternatives retain their authored order and positions. -/
theorem frontier_append_iff (base : Space) (extra live : List Atom) (query : Atom) (incoming : Bindings)
    (rejected : ∀ a ∈ extra, ∀ ordinal, EquationRowResultsRel live query incoming ordinal a [])
    (work : List EquationWork) :
    EquationFrontierRel (Space.ofList (base.atoms ++ extra)) live query incoming work ↔
      EquationFrontierRel base live query incoming work := by
  constructor
  · intro frontier
    cases frontier with
    | @completed blocks checked =>
      change List.Forall₂ _ (base.atoms ++ extra).zipIdx blocks at checked
      rw [List.zipIdx_append] at checked
      let n := base.atoms.length
      have first := List.forall₂_take n checked
      have rest := List.forall₂_drop n checked
      have baseLen : base.atoms.zipIdx.length = n := List.length_zipIdx
      rw [List.take_left' baseLen] at first
      rw [List.drop_left' baseLen] at rest
      have empty := rejected_flatten rest fun entry present => by
        have serves := (List.mem_zipIdx_iff_le_and_getElem?_sub.mp present).2
        exact rejected entry.1 (List.mem_iff_getElem?.mpr ⟨_, serves⟩) entry.2
      have partition := congrArg List.flatten (List.take_append_drop n blocks)
      rw [List.flatten_append, empty, List.append_nil] at partition
      exact partition ▸ EquationFrontierRel.completed first
  · intro frontier
    exact EquationFrontierRel.append_rejected base live query incoming work extra frontier rejected

variable {Context World : Type}

/-- At an invocation, authority for native work stays with the actual
world. Only the equation lookup changes between these views. -/
theorem invocation_append_iff (env : WorldEnvironment Context World)
    (other : World → Context → Space) (p : Policy) (q : Input) (mode : Mode)
    (world : World) (scope : Context) (extra : List Atom)
    (appended : other world scope = Space.ofList ((env.view world scope).atoms ++ extra))
    (rejected : ∀ a ∈ extra, ∀ ordinal, EquationRowResultsRel (mode.protect q.live)
      q.value.erase q.frame.bindings ordinal a [])
    (stack : List Continuation) (parents : List (Parent Context)) (published : List Result)
    (target : Focus Context World) :
    let source : Focus Context World := ⟨world, scope, .work (Request.task (.invoke q mode)), stack,
      parents, published⟩
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p source target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p source target := by
  let extended : WorldEnvironment Context World := {env with view := other}
  change HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
    ⟨world, scope, .work (Request.task (.invoke q mode)), stack, parents, published⟩ target ↔
    HEFocused.Move extended.arguments extended.view extended.services extended.dispatch extended.lookup p
    ⟨world, scope, .work (Request.task (.invoke q mode)), stack, parents, published⟩ target
  rw [HEInvocationEntry.step_iff env, HEInvocationEntry.step_iff extended]
  have same (reply : Reply) (next : World) :
      Licensed env p world scope (.invoke q mode) reply next ↔
        Licensed extended p world scope (.invoke q mode) reply next := by
    cases reply with
    | query work =>
      simp only [Licensed, extended, appended]
      rw [frontier_append_iff _ _ _ _ _ rejected work]
    | error | embedded | native | exhausted | use => rfl
  constructor
  · rintro ⟨reply, next, body, frames, licensed, phase, result⟩
    exact ⟨reply, next, body, frames, (same reply next).mp licensed, phase, result⟩
  · rintro ⟨reply, next, body, frames, licensed, phase, result⟩
    exact ⟨reply, next, body, frames, (same reply next).mpr licensed, phase, result⟩

/-- The snapshots may have different rejected suffixes. In particular
the compiled snapshot can be older than the live one. All retained
occurrences have the same position in their common prefix. -/
def InvocationAgreement (first second : Space) (q : Input) (mode : Mode) : Prop :=
  ∃ common : Space, ∃ left right,
    first = Space.ofList (common.atoms ++ left) ∧ second = Space.ofList (common.atoms ++ right) ∧
    ∀ atom ∈ left ++ right, ∀ ordinal, EquationRowResultsRel (mode.protect q.live)
      q.value.erase q.frame.bindings ordinal atom []

theorem invocation_iff (env : WorldEnvironment Context World)
    (other : World → Context → Space) (p : Policy) (q : Input) (mode : Mode)
    (world : World) (scope : Context)
    (agrees : InvocationAgreement (env.view world scope) (other world scope) q mode)
    (stack : List Continuation) (parents : List (Parent Context)) (published : List Result)
    (target : Focus Context World) :
    let source : Focus Context World := ⟨world, scope, .work (Request.task (.invoke q mode)), stack, parents, published⟩
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p source target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p source target := by
  obtain ⟨common, left, right, first, second, rejected⟩ := agrees
  let prefixEnv : WorldEnvironment Context World := {env with view := fun _ _ => common}
  have toFirst := invocation_append_iff prefixEnv env.view p q mode world scope left first
    (fun a member n => rejected a (List.mem_append_left right member) n) stack parents published target
  have toSecond := invocation_append_iff prefixEnv other p q mode world scope right second
    (fun a member n => rejected a (List.mem_append_right left member) n) stack parents published target
  exact toFirst.symm.trans toSecond

/-- These phases may use host services and change the world. They have
no dependency on the definition view substituted by this theorem. -/
inductive Independent : Focus Context World → Prop where
  | returning (world : World) (scope : Context) (answers : List Result) (stack parents published) :
      Independent ⟨world, scope, .returning answers, stack, parents, published⟩
  | native (r : NativeRequest) (world : World) (scope : Context) (stack parents published) :
      Independent ⟨world, scope, .work r.task, stack, parents, published⟩
  | context (r : HEContextEntry.Request) (world : World) (scope : Context) (stack parents published) :
      Independent ⟨world, scope, .work r.task, stack, parents, published⟩
  | application (task : Task) (world : World) (scope : Context) (stack parents published) :
      HEApplicationEntry.covered task = true →
      Independent ⟨world, scope, .work task, stack, parents, published⟩
  | bindings (task : Task) (world : World) (scope : Context) (stack parents published) :
      HESnapshotEntry.covered task = true →
      Independent ⟨world, scope, .work task, stack, parents, published⟩
  | primitive (task : Task) (world : World) (scope : Context) (stack parents published) :
      HEMinimalEntry.covered task = true →
      NativeRequest.recognize task = none → HEContextEntry.Request.recognize task = none →
      HESnapshotEntry.covered task = false →
      Independent ⟨world, scope, .work task, stack, parents, published⟩

theorem independent_move (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy)
    {before target : Focus Context World} (independent : Independent before) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p before target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p before target := by
  let alternative : WorldEnvironment Context World := {env with view := other}
  cases independent with
  | returning world scope answers stack parents published =>
    cases stack with
    | nil =>
      exact (HEFocused.return_step_iff (view := env.view) world scope answers parents published target).trans
        (HEFocused.return_step_iff (view := other) world scope answers parents published target).symm
    | cons frame stack =>
      exact (HESnapshotEntry.return_iff env p frame answers world scope stack parents published target).trans
        (HESnapshotEntry.return_iff alternative p frame answers world scope stack parents published target).symm
  | native request world scope stack parents published =>
    exact (HEFocused.native_step_iff (view := env.view) request world scope stack parents published target).trans
      (HEFocused.native_step_iff (view := other) request world scope stack parents published target).symm
  | context request world scope stack parents published =>
    exact (HEContextEntry.step_iff (view := env.view) request world scope stack parents published target).trans
      (HEContextEntry.step_iff (view := other) request world scope stack parents published target).symm
  | application task world scope stack parents published covered =>
    exact (HEApplicationEntry.step_iff env p task covered world scope stack parents published target).trans
      (HEApplicationEntry.step_iff alternative p task covered world scope stack parents published target).symm
  | bindings task world scope stack parents published covered =>
    exact (HESnapshotEntry.step_iff env p task covered world scope stack parents published target).trans
      (HESnapshotEntry.step_iff alternative p task covered world scope stack parents published target).symm
  | primitive task world scope stack parents published covered noNative noContext noBindings =>
    exact (HEMinimalEntry.step_iff env p task covered noNative noContext noBindings
      world scope stack parents published target).trans
      (HEMinimalEntry.step_iff alternative p task covered noNative noContext noBindings
        world scope stack parents published target).symm

/-- A replacement holds the reached, phase-specific definition or type
observations, not a global approval to reuse a space. A retained call
needs no new lookup. An unrelated append is certified at a fresh entry,
and typed uses check their own read support. -/
inductive ProtectedAt (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy) :
    WorldConfiguration Context World → Prop where
  | effective {current} :
      (∀ name ∈ current.context :: current.control.contexts, env.view current.world name = other current.world name) →
      ProtectedAt env other p current
  | invoking {q : Input} {mode : Mode} {world scope stack parents published} :
      InvocationAgreement (env.view world scope) (other world scope) q mode →
      ProtectedAt env other p
        (HEFocused.restore ⟨world, scope, .work (Request.task (.invoke q mode)), stack, parents, published⟩)
  | entered (q : Input) (mode : Option Atom) (work : List EquationWork) (world scope stack parents published) :
      ProtectedAt env other p
        (HEFocused.restore ⟨world, scope, .work (Request.task (.retained q mode work)), stack, parents, published⟩)
  | typed (q : HEAtomEntry.Request) (world scope stack parents published) :
      HETypedReplacement.EntryAgreement env.arguments (env.view world scope) (other world scope) env.lookup p q →
      ProtectedAt env other p
        (HEFocused.restore ⟨world, scope, .work q.task, stack, parents, published⟩)
  | body (task : Task) (world scope stack parents published) :
      HEBodyEntry.covered task = true →
      HETypedReplacement.BodyAgreement (env.view world scope) (other world scope) env.lookup task →
      ProtectedAt env other p
        (HEFocused.restore ⟨world, scope, .work task, stack, parents, published⟩)
  | independent {current : Focus Context World} :
      Independent current → ProtectedAt env other p (HEFocused.restore current)

theorem protected_step (env : WorldEnvironment Context World)
    (other : World → Context → Space) (p : Policy) {current target : WorldConfiguration Context World}
    (held : ProtectedAt env other p current) :
    (HEControlOnTransform.source env p).Step current target ↔
      (HEControlOnTransform.source {env with view := other} p).Step current target := by
  let alternative : WorldEnvironment Context World := {env with view := other}
  refine (HEControlOnTransform.source_step_iff env p current target).trans
    (Iff.trans ?_ (HEControlOnTransform.source_step_iff alternative p current target).symm)
  cases held with
  | effective held =>
    exact HEExecution.world_rewrite_iff_of_same_snapshot held
  | @invoking q mode world scope stack parents published agrees =>
    refine (HEFocused.focus_step_iff _ _).symm.trans (Iff.trans ?_ (HEFocused.focus_step_iff _ _))
    rw [HEFocused.focus_restore]
    exact invocation_iff env other p q mode world scope agrees stack parents published _
  | entered q mode work world scope stack parents published =>
    refine (HEFocused.focus_step_iff _ _).symm.trans (Iff.trans ?_ (HEFocused.focus_step_iff _ _))
    rw [HEFocused.focus_restore]
    exact HEInvocationEntry.retained_step_of_another_view env other p q mode work world scope stack parents published _
  | typed q world scope stack parents published same =>
    refine (HEFocused.focus_step_iff _ _).symm.trans (Iff.trans ?_ (HEFocused.focus_step_iff _ _))
    rw [HEFocused.focus_restore]
    exact HETypedReplacement.entry_step_iff env other p q world scope same stack parents published _
  | body task world scope stack parents published covered same =>
    refine (HEFocused.focus_step_iff _ _).symm.trans (Iff.trans ?_ (HEFocused.focus_step_iff _ _))
    rw [HEFocused.focus_restore]
    exact HETypedReplacement.body_step_iff env other p task covered world scope same stack parents published _
  | independent free =>
    refine (HEFocused.focus_step_iff _ _).symm.trans (Iff.trans ?_ (HEFocused.focus_step_iff _ _))
    rw [HEFocused.focus_restore]
    exact independent_move env other p free

private theorem protected_chain (env : WorldEnvironment Context World)
    (other : World → Context → Space) (p : Policy) (current : WorldConfiguration Context World)
    (kept : ∀ reached, (HEControlOnTransform.source {env with view := other} p).MultiStep current reached →
      ProtectedAt env other p reached)
    (tail : List (WorldConfiguration Context World)) :
    (current :: tail).IsChain (HEControlOnTransform.source env p).Step ↔
      (current :: tail).IsChain (HEControlOnTransform.source {env with view := other} p).Step := by
  change (current :: tail).IsChain
    (fun a b : WorldConfiguration Context World => (HEControlOnTransform.source env p).Step a b) ↔
    (current :: tail).IsChain
      (fun a b : WorldConfiguration Context World => (HEControlOnTransform.source {env with view := other} p).Step a b)
  induction tail generalizing current with
  | nil => simp
  | cons next tail ih =>
    simp only [List.isChain_cons_cons]
    have here := protected_step env other p (target := next) (kept current (.refl _))
    constructor
    · rintro ⟨first, tailPath⟩
      have fixed := here.mp first
      exact ⟨fixed, (ih next (fun reached rest => kept reached (.step fixed rest))).mp tailPath⟩
    · rintro ⟨first, tailPath⟩
      exact ⟨here.mpr first, (ih next (fun reached rest => kept reached (.step first rest))).mpr tailPath⟩

/-- Replace only the source lookups certified at the current phase. The
compiled segment keeps the actual world, saved continuations and all
publications, so the result applies even to the timed observer. -/
theorem protected_reports_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy)
    (code : HENativeOnTransform.Presentation Context World)
    {current : WorldConfiguration Context World} {start : SState O}
    (shown : HEControlOnTransform.Shows code current start)
    (kept : ∀ reached, (HEControlOnTransform.source {env with view := other} p).MultiStep current reached →
      ProtectedAt env other p reached)
    (demand : Demand) (answer : Mettapedia.GSLT.Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEControlOnTransform.source env p) heView (·.finished = true) heEmit current)
      demand answer ↔
    reports (readCompleted (sys := HEControlOnTransform.theory O code {env with view := other} p)
      (ofTerm (HEControlOnTransform.Shows code) heView) (·.finished = true) heEmit start) demand answer := by
  refine Iff.trans ?_ (EvaluationObservations.he_reports_iff {env with view := other} p code shown demand answer)
  apply reports_congr
  intro trace
  refine (completed_iff_chain (sys := HEControlOnTransform.source env p) heView _ heEmit current trace).trans
    (Iff.trans ?_ (completed_iff_chain (sys := HEControlOnTransform.source {env with view := other} p)
      heView _ heEmit current trace).symm)
  constructor
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    exact ⟨tail, finish, (protected_chain env other p current kept tail).mp chain, last, ended, batches⟩
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    exact ⟨tail, finish, (protected_chain env other p current kept tail).mpr chain, last, ended, batches⟩

section Controls

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (context work)

private def note : Atom := .symbol "note"

theorem harmless_append_keeps_both_copies :
    EquationFrontierRel (Space.ofList (context.atoms ++ [note])) []
      (.symbol "a") Bindings.empty [work 0, work 3] := by
  refine (frontier_append_iff context [note] [] (.symbol "a") Bindings.empty ?_ _).mpr
    Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls.complete
  intro a present ordinal
  obtain rfl := List.mem_singleton.mp present
  exact .irrelevant ordinal note (by intro left right impossible; cases impossible)

theorem same_definitions_do_not_keep_ordinal_evidence :
    ¬EquationFrontierRel (Space.ofList (note :: context.atoms)) []
      (.symbol "a") Bindings.empty [work 0, work 3] := by
  intro invalid
  obtain ⟨_, actual⟩ := invalid.occurrence (work := work 0) List.mem_cons_self
  have impossible := actual.stored
  change some note = some (.expression [.symbol "=", .symbol "a", .symbol "result"]) at impossible
  cases impossible

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.HEObservationReplacement
