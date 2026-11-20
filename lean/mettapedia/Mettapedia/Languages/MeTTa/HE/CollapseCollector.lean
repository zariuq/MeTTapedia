import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# The `collapse` collector

`collapse` evaluates its operand as a child computation and packs every
completed child result into one expression. This module gives the collector
two layers of meaning.

* **Readback.** A completed child supplies an ordered list of rows; each row
  has an optional value and its binding snapshot. `results` keeps the rows
  whose value is present and not `Empty`; `pack` encodes them in order. The
  packed expression is the minimal-instruction `collapse-bind` result
  (`completed_core_step`). Reordering the child alternatives permutes the
  packed occurrences (`results_perm`, `scan_perm`), and duplicate occurrences
  are kept (`duplicate_retained`).
* **Retained child.** As a handled machine (`handled`), the collector keeps
  the whole child configuration while the child runs. Partial child output is
  published as child events and never closes the parent
  (`paused_child_exact`); only a completed reply followed by the collector's
  own closing step yields the aggregate (`complete_after_child`). Cancellation
  closes without an aggregate (`cancellation_no_aggregate`), and resuming a
  paused run equals running uninterrupted (`resume_after_prefix`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.CollapseCollector

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Spec.Eval Spec.Eval.Minimal

/-! ## Readback of a completed child -/

/-- Materialization may return no atom. Its absence is distinct from the
binding snapshot, which remains present for every child row. -/
structure MaterializedOutcome where
  value : Option Atom
  bindings : Bindings
  deriving DecidableEq, Repr

def MaterializedOutcome.kept (row : MaterializedOutcome) : Option ResultPair :=
  match row.value with
  | none => none
  | some value => if value == Atom.empty then none else some (value, row.bindings)

/-- The collected results: every child row with a retained, non-`Empty` value, in order. -/
def results (rows : List MaterializedOutcome) : ResultSet :=
  rows.filterMap MaterializedOutcome.kept

/-- The collector's accumulation loop, starting from an existing prefix of encoded pairs. -/
def scan (services : Services) : List MaterializedOutcome → List Atom → List Atom
  | [], pairs => pairs
  | row :: rest, pairs =>
      match row.kept with
      | none => scan services rest pairs
      | some result => scan services rest (pairs ++ [encodeResult services result])

theorem scan_exact (services : Services) (rows : List MaterializedOutcome)
    (pairs : List Atom) :
    scan services rows pairs = pairs ++ (results rows).map (encodeResult services) := by
  induction rows generalizing pairs with
  | nil => simp [scan, results]
  | cons row rows ih =>
      cases found : row.kept <;> simp [scan, results, found, ih, List.append_assoc]

def pack (services : Services) (rows : List MaterializedOutcome) : Atom :=
  .expression (scan services rows [])

theorem pack_exact (services : Services) (rows : List MaterializedOutcome) :
    pack services rows = encodeResults services (results rows) := by
  simp [pack, scan_exact, encodeResults]

/-- Reordering child alternatives transports to a permutation of the collected
occurrences; it does not erase multiplicity or choose one global MeTTa order. -/
theorem results_perm {left right : List MaterializedOutcome} (permutation : left.Perm right) :
    (results left).Perm (results right) :=
  permutation.filterMap MaterializedOutcome.kept

theorem scan_perm (services : Services) {left right : List MaterializedOutcome}
    (permutation : (results left).Perm (results right)) :
    (scan services left []).Perm (scan services right []) := by
  simpa only [scan_exact, List.nil_append] using permutation.map (encodeResult services)

theorem kept_nonempty (rows : List MaterializedOutcome) (pair : ResultPair)
    (member : pair ∈ results rows) : pair.1 ≠ Atom.empty := by
  simp only [results, List.mem_filterMap] at member
  obtain ⟨row, _, kept⟩ := member
  rcases row with ⟨value, bindings⟩
  cases value with
  | none => simp [MaterializedOutcome.kept] at kept
  | some value =>
      simp only [MaterializedOutcome.kept] at kept
      split at kept
      · cases kept
      · cases kept
        simpa using ‹¬ (value == Atom.empty) = true›

theorem encodeResult_injective (services : Services) (laws : ServiceLaws services) :
    Function.Injective (encodeResult services) := by
  rintro ⟨left, leftBindings⟩ ⟨right, rightBindings⟩ equal
  simp only [encodeResult, Atom.expression.injEq, List.cons.injEq,
    Atom.grounded.injEq, and_true] at equal
  exact Prod.ext equal.1 (laws.bindingPayload_injective equal.2)

theorem pack_eq_iff (services : Services) (laws : ServiceLaws services)
    (left right : List MaterializedOutcome) :
    pack services left = pack services right ↔ results left = results right := by
  simp only [pack_exact, encodeResults, Atom.expression.injEq]
  exact (List.map_injective_iff.mpr (encodeResult_injective services laws)).eq_iff

/-- List equality here observes occurrences and bindings; equal values are
not deduplicated by the encoding. -/
theorem duplicate_retained (services : Services) (value : Atom) (bindings : Bindings)
    (nonempty : value ≠ Atom.empty) :
    pack services [⟨some value, bindings⟩, ⟨some value, bindings⟩] =
      .expression [encodeResult services (value, bindings),
        encodeResult services (value, bindings)] := by
  simp [pack_exact, results, MaterializedOutcome.kept, nonempty, encodeResults]

/-- This local closing square uses an independently supplied *complete*
child enumeration. Mere support or a partial child prefix is insufficient. -/
theorem completed_core_step (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (space : Space) (body : Atom) (caller : Bindings) (rows : List MaterializedOutcome)
    (host : dispatch.minimal = some ⟨services, enumeration⟩)
    (child : enumeration.minimalResults space body caller (results rows)) :
    CoreStepRel space dispatch live (typing := typing)
      (.expression [.symbol "collapse-bind", body]) caller
      (pack services rows, caller) := by
  rw [pack_exact]
  exact .collapseBind space body caller (results rows) services enumeration host rfl child

/-- The existing may-level law checks support, while the collector's list
itself continues to supply the additional order and multiplicity observation. -/
theorem completed_support (services : Services) (enumeration : Enumeration)
    (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    (space : Space) (body : Atom) (caller : Bindings) (rows : List MaterializedOutcome)
    (child : enumeration.minimalResults space body caller (results rows))
    (pair : ResultPair) :
    pair ∈ results rows ↔
      MinimalResultRel services dispatch live typing enumeration space body caller pair :=
  laws.support_exact space body caller (results rows) child pair

/-! ## The collector as a handled machine -/

/-- A completed child owns its reached world and its full ordered row list. -/
structure Completed (World : Type) where
  world : World
  rows : List MaterializedOutcome
  deriving DecidableEq, Repr

/-- The caller parameter is the complete saved caller state, including its
delivery target and any surrounding continuation. -/
inductive Parent (Caller World Failure : Type) where
  | enter (caller : Caller)
  | waiting (caller : Caller)
  | returned (caller : Caller) (reply : Reply (Completed World) Failure)

inductive Event (Caller World Receipt Failure : Type) where
  | entered (caller : Caller)
  | child (receipt : Receipt)
  | replied (reply : Reply (Completed World) Failure)

/-- Closing a collector is different from cancellation or a child's failure.
Neither stopped outcome carries a fabricated aggregate. -/
inductive Verdict (Caller World Failure : Type) where
  | aggregate (caller : Caller) (world : World) (result : ResultPair)
  | failed (caller : Caller) (failure : Failure)
  | cancelled (caller : Caller)

variable {Caller World Receipt Failure Child External : Type}

def Parent.caller : Parent Caller World Failure → Caller
  | .enter caller | .waiting caller | .returned caller _ => caller

def parent (services : Services) (bindings : Caller → Bindings) :
    Machine (Parent Caller World Failure) (Event Caller World Receipt Failure)
      (Verdict Caller World Failure) Caller where
  step
    | .enter caller => some (.call caller (.waiting caller))
    | .waiting _ => none
    | .returned caller (.returned done) =>
        some (.finish (.aggregate caller done.world (pack services done.rows, bindings caller)))
    | .returned caller (.faulted failure) => some (.finish (.failed caller failure))
    | .returned caller .cancelled => some (.finish (.cancelled caller))

def callback : Callback (Parent Caller World Failure)
    (Event Caller World Receipt Failure) Caller (Completed World) Failure where
  callEvent := Event.entered
  replyEvent := Event.replied
  resume saved reply := .returned saved.caller reply

def handled (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) :
    Machine (HandledState (Parent Caller World Failure) Child Caller)
      (Event Caller World Receipt Failure) (Verdict Caller World Failure) External :=
  (parent services bindings).handle callback
    (child.relabel Event.child id id) load

/-- A whole child configuration, rather than its already received answers,
is the retained service state. -/
def active (caller : Caller) (child : Child) :
    HandledState (Parent Caller World Failure) Child Caller :=
  .handling caller (.waiting caller) child

theorem before_reply (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state : Child)
    (events : List Receipt) (outcome : Outcome Child (Reply (Completed World) Failure) External)
    (ran : child.run fuel state = (events, outcome))
    (unfinished : ∀ reply, outcome ≠ .finished reply) :
    (handled services bindings child load).run fuel (active caller state) =
      (events.map Event.child,
        Machine.handlerOutcome (callback (Receipt := Receipt)) caller (.waiting caller) outcome) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  have run' : (child.relabel
      (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id).run fuel state =
      (events.map Event.child, outcome) := by
    simpa only [Outcome.relabel_id] using lifted
  exact (parent services bindings).handle_run_of_no_reply callback
    (child.relabel Event.child id id) load fuel caller (.waiting caller)
      state _ outcome run' unfinished

theorem paused_child_exact (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state residual : Child)
    (events : List Receipt)
    (ran : child.run fuel state = (events, .exhausted residual)) :
    (handled services bindings child load).run fuel (active caller state) =
      (events.map Event.child, .exhausted (active caller residual)) := by
  exact before_reply services bindings child load fuel caller state events
    (.exhausted residual) ran (by intro reply; simp)

/-- Even an empty or duplicate-filled partial row list cannot close the parent:
a completed reply, followed by the collector's own closing step, is required. -/
theorem complete_after_child (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (fuel : Nat) (caller : Caller) (state : Child)
    (events : List Receipt) (done : Completed World)
    (ran : child.run fuel state = (events, .finished (.returned done))) :
    ∃ used ≤ fuel + 1,
      (handled services bindings child load).run used (active caller state) =
        (events.map Event.child ++ [Event.replied (.returned done)],
          .finished (.aggregate caller done.world (pack services done.rows, bindings caller))) := by
  have lifted := child.run_relabel
    (Event.child (Caller := Caller) (World := World) (Failure := Failure)) id id fuel state
  rw [ran] at lifted
  obtain ⟨used, bound, reached⟩ := (parent services bindings).handle_run_of_reply callback
    (child.relabel Event.child id id) load fuel caller (.waiting caller) state
      (events.map Event.child) (.returned done) lifted
  refine ⟨used + 1, Nat.add_le_add_right bound 1, ?_⟩
  change (handled services bindings child load).run (used + 1)
    (.handling caller (.waiting caller) state) = _
  rw [Machine.run_add]
  change (handled services bindings child load).continueRun 1
    ((parent services bindings).handle callback (child.relabel Event.child id id) load |>.run used
      (.handling caller (.waiting caller) state)) = _
  rw [reached]
  simp [Machine.continueRun, Machine.run, handled, Machine.handle, parent, callback, Parent.caller]

/-- The same retained interface supplies exact scheduler resumption; this
law does not grant permission to restart a cancelled child. -/
theorem resume_after_prefix (services : Services) (bindings : Caller → Bindings)
    (child : Machine Child Receipt (Reply (Completed World) Failure) External)
    (load : Caller → Child) (first second : Nat)
    (state residual : HandledState (Parent Caller World Failure) Child Caller)
    (events : List (Event Caller World Receipt Failure))
    (paused : (handled services bindings child load).run first state =
      (events, .exhausted residual)) :
    (handled services bindings child load).run (first + second) state =
      (events ++ ((handled services bindings child load).run second residual).1,
        ((handled services bindings child load).run second residual).2) :=
  (handled services bindings child load).established_and_pending first second state residual events paused

/-- A cancelled reply closes with its explicit interruption verdict. -/
theorem cancellation_no_aggregate (services : Services) (bindings : Caller → Bindings)
    (caller : Caller) :
    (parent (World := World) (Receipt := Receipt) (Failure := Failure) services bindings).step
      (.returned caller .cancelled) = some (.finish (.cancelled caller)) := rfl

/-! ## Controls -/

namespace Controls

private def services : Services where
  bindingPayload bindings := .custom "Bindings" (reprStr bindings)
  contextPayload _ := .custom "Context" "test"
  nativeCall _ _ _ _ _ := False

private def original (caller : Nat) : Bindings :=
  ⟨[("caller", .grounded (.int caller))], []⟩
private def captured : Bindings := ⟨[("x", .symbol "A")], []⟩
private def rows : List MaterializedOutcome :=
  [⟨some (.symbol "token"), captured⟩, ⟨none, {}⟩,
   ⟨some Atom.empty, {}⟩, ⟨some (.symbol "token"), captured⟩]

private def rowA : MaterializedOutcome := ⟨some (.symbol "A"), captured⟩
private def rowB : MaterializedOutcome := ⟨some (.symbol "B"), captured⟩

/-- A representation whose binding payload forgets the bindings. It violates
`ServiceLaws.bindingPayload_injective`. -/
private def forgetful : Services where
  bindingPayload _ := .custom "Bindings" ""
  contextPayload _ := .custom "Context" ""
  nativeCall _ _ _ _ _ := False

/-- The child enumeration that reports exactly `expected` as complete. -/
private def exactly (expected : ResultSet) : Enumeration where
  results _ _ _ _ _ := False
  minimalResults _ _ _ found := found = expected

/-! ### Readback -/

/-- `scan_exact`, `pack_exact`: absent and `Empty` rows are omitted and the
survivors keep their order and bindings. -/
example : results rows = [(.symbol "token", captured), (.symbol "token", captured)] := by
  decide

/-- The readback is not a row-for-row image: two of the four rows are dropped. -/
example : (results rows).length ≠ rows.length := by decide

/-- `scan_exact` with a nonempty prefix: the prefix is kept in front. -/
example : scan services [rowA] [.symbol "seed"] =
    [.symbol "seed", encodeResult services (.symbol "A", captured)] := by
  rw [scan_exact]
  rfl

/-- `results_perm`, `scan_perm`: swapping two alternatives permutes the packed list. -/
example : (scan services [rowA, rowB] []).Perm (scan services [rowB, rowA] []) :=
  scan_perm services (results_perm (List.Perm.swap rowB rowA []))

/-- Permutation, not equality: the packed list records the child's order. -/
example : scan services [rowA, rowB] [] ≠ scan services [rowB, rowA] [] := by
  simp [scan, MaterializedOutcome.kept, rowA, rowB, encodeResult, Atom.empty]

/-- Without a permutation of the rows, the results need not be permutations:
dropping one surviving row changes the multiset. -/
example : ¬ (results rows).Perm (results rows.tail) := by
  intro perm
  have := perm.length_eq
  revert this
  decide

/-- `kept_nonempty`: no collected result is `Empty` ... -/
example : ∀ pair ∈ results rows, pair.1 ≠ Atom.empty := kept_nonempty rows

/-- ... although the child rows themselves do contain an `Empty` value. -/
example : ∃ row ∈ rows, row.value = some Atom.empty :=
  ⟨⟨some Atom.empty, {}⟩, by decide, rfl⟩

/-- `encodeResult_injective`, `pack_eq_iff`: under the service laws, different
binding snapshots of one value stay distinguishable in the packed result. -/
example (services : Services) (laws : ServiceLaws services) :
    pack services [rowA] ≠ pack services [⟨some (.symbol "A"), {}⟩] := by
  rw [Ne, pack_eq_iff services laws]
  decide

/-- Without injective binding payloads the two packs coincide although their
results differ: the law is needed. -/
example : pack forgetful [rowA] = pack forgetful [⟨some (.symbol "A"), {}⟩] ∧
    results [rowA] ≠ results [⟨some (.symbol "A"), {}⟩] := by
  constructor
  · rfl
  · decide

/-- `duplicate_retained`: two equal occurrences stay two. -/
example : pack services [rowA, rowA] =
    .expression [encodeResult services (.symbol "A", captured),
      encodeResult services (.symbol "A", captured)] :=
  duplicate_retained services (.symbol "A") captured (by decide)

/-- The `value ≠ Empty` hypothesis is needed: duplicated `Empty` rows pack to nothing. -/
example : pack services [⟨some Atom.empty, captured⟩, ⟨some Atom.empty, captured⟩] =
    .expression [] := by
  rw [pack_exact]
  rfl

/-- `completed_core_step`: a host whose enumeration reports the complete
results makes the packed rows the `collapse-bind` step result. -/
example (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (space : Space) (body : Atom) (caller : Bindings)
    (host : dispatch.minimal = some ⟨services, exactly (results rows)⟩) :
    CoreStepRel space dispatch live (typing := typing)
      (.expression [.symbol "collapse-bind", body]) caller (pack services rows, caller) :=
  completed_core_step services _ dispatch live typing space body caller rows host rfl

/-- A strict prefix of the child rows is not the complete enumeration, so
`completed_core_step` does not apply to a partial readback. -/
example (space : Space) (body : Atom) (caller : Bindings) :
    ¬ (exactly (results rows)).minimalResults space body caller (results (rows.take 1)) := by
  change ¬ results (rows.take 1) = results rows
  decide

/-- `completed_support`: an `Empty` pair is never a minimal result of a
completed child, whatever the enumeration laws. -/
example (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (enumeration : Enumeration)
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    (space : Space) (body : Atom) (caller : Bindings)
    (child : enumeration.minimalResults space body caller (results rows)) (bindings : Bindings) :
    ¬ MinimalResultRel services dispatch live typing enumeration space body caller
      (BindingFrame.historicalResult (Atom.empty, bindings)) := fun related =>
  kept_nonempty rows _
    ((completed_support services enumeration dispatch live typing laws space body caller
      rows child (Atom.empty, bindings)).mpr related) rfl

/-- ... while the surviving occurrences are minimal results. -/
example (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom) (typing : EvalTypeService)
    (enumeration : Enumeration)
    (laws : MinimalEnumerationLaws services dispatch live typing enumeration)
    (space : Space) (body : Atom) (caller : Bindings)
    (child : enumeration.minimalResults space body caller (results rows)) :
    MinimalResultRel services dispatch live typing enumeration space body caller
      (BindingFrame.historicalResult (.symbol "token", captured)) :=
  (completed_support services enumeration dispatch live typing laws space body caller
    rows child (.symbol "token", captured)).mp (by decide)

/-! ### The handled machine -/

/-- This control child commits before its retained administrative step. -/
private def child : Machine (Nat × Nat) Nat (Reply (Completed Nat) Empty) Empty where
  step state := some <| match state.1 with
    | 0 => .publish [state.2 + 1] (1, state.2 + 1)
    | 1 => .silent (2, state.2)
    | _ => .finish (.returned ⟨state.2, rows⟩)

private def machine := handled services original child (fun _ => (0, 0))

/-- `paused_child_exact`, `before_reply`: a paused child publishes only its
own events and keeps the whole parent retained. -/
example : machine.run 1 (active 7 (0, 0)) =
    ([Event.child 1], .exhausted (active 7 (1, 1))) := by rfl

example : machine.run 2 (active 7 (0, 0)) =
    ([Event.child 1], .exhausted (active 7 (2, 1))) := by rfl

/-- Once the child finishes, the reply is published: the `unfinished`
hypothesis of `before_reply` is needed, and the parent has not yet closed. -/
example : machine.run 3 (active 7 (0, 0)) =
    ([Event.child 1, Event.replied (.returned ⟨1, rows⟩)],
      .exhausted (.running (.returned 7 (.returned ⟨1, rows⟩)))) := by rfl

/-- `complete_after_child`: the closing step after the reply yields the aggregate. -/
example : machine.run 4 (active 7 (0, 0)) =
    ([Event.child 1, Event.replied (.returned ⟨1, rows⟩)],
      .finished (.aggregate 7 1 (pack services rows, original 7))) := by rfl

/-- `resume_after_prefix`: resuming from the paused residual equals the
uninterrupted run. -/
example : machine.run (1 + 3) (active 7 (0, 0)) =
    ([Event.child 1] ++ (machine.run 3 (active 7 (1, 1))).1,
      (machine.run 3 (active 7 (1, 1))).2) :=
  resume_after_prefix services original child (fun _ => (0, 0)) 1 3 _ _ _ rfl

/-- Resuming from the initial state instead of the residual repeats the
first publication: the `paused` hypothesis is needed. -/
example : ([Event.child 1] ++ (machine.run 3 (active 7 (0, 0))).1).length ≠
    (machine.run 4 (active 7 (0, 0))).1.length := by
  decide

#guard (results rows).length == 2
#guard (results rows).map Prod.snd == [captured, captured]
#guard pack services rows != pack services [⟨some (.symbol "token"), captured⟩]
#guard pack services rows != pack services [⟨some (.symbol "token"), {}⟩,
  ⟨some (.symbol "token"), {}⟩]

/-- Restarting the child from its reached world repeats the effect. -/
example : machine.run 1 (active 7 (0, 1)) =
    ([Event.child 2], .exhausted (active 7 (1, 2))) := by rfl

/- Deleting pending work admits an empty aggregate in the raw state, which
is observably different from the actual finished child. Such a state is not
reachable by the retained execution above. -/
#guard pack services [] != pack services rows

private def stalled : Machine Nat Nat (Reply (Completed Nat) Empty) Empty where
  step n := some (.silent (n + 1))

example : (handled services original stalled id).run 12 (active 7 0) =
    ([], .exhausted (active 7 12)) := by rfl

private def cancelled : Machine Nat Nat (Reply (Completed Nat) Empty) Empty where
  step _ := some (.finish .cancelled)

/-- `cancellation_no_aggregate`: a cancelled child closes the collector
without an aggregate, unlike the returned child above. -/
example : (handled services original cancelled id).run 2 (active 7 0) =
    ([Event.replied .cancelled], .finished (.cancelled 7)) := by rfl

/-- A collector can itself be a retained child of another collector. -/
private def outerChild := machine.relabel id
  (fun verdict => (match verdict with
    | .aggregate _ world result =>
        Reply.returned (Completed.mk world [⟨some result.1, result.2⟩])
    | .failed _ impossible => nomatch impossible
    | .cancelled _ => Reply.cancelled : Reply (Completed Nat) Empty)) id
private def nested := handled services original outerChild (fun _ => active 7 (0, 0))

example : nested.run 1 (active 9 (active 7 (0, 0))) =
    ([Event.child (Event.child 1)], .exhausted (active 9 (active 7 (1, 1)))) := by rfl

example : nested.run 5 (active 9 (active 7 (0, 0))) =
    ([Event.child (Event.child 1),
      Event.child (Event.replied (.returned ⟨1, rows⟩)),
      Event.replied (.returned ⟨1, [⟨some (pack services rows), original 7⟩]⟩)],
      .finished (.aggregate 9 1
        (pack services [⟨some (pack services rows), original 7⟩], original 9))) := by rfl

end Controls

end Mettapedia.Languages.MeTTa.HE.CollapseCollector
