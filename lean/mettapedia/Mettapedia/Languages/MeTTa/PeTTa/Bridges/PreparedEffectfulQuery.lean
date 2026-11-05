import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryReadStability
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource

/-!
# Prepared nested reads with source-ordered effects

Prepared rows are reused across nested matches when their ordered query
views remain valid. The store itself may grow. Execution keeps every source
binding occurrence and runs effectful bodies in authored order.

The source uses captured, quoted handles. This is a completed-execution law
for the existing evaluator, not a claim of arbitrary open-fact unification,
concurrent publication, a set-space constructor, or `once` semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

structure Leg where
  handle : Handle
  pattern : Atom
  rows : List Atom

def prepare (state : Effects.State) : List (Handle × Atom) → Option (List Leg)
  | [] => some []
  | (handle, pattern) :: rest => do
      let rows ← state.read handle
      let later ← prepare state rest
      return ⟨handle, pattern, rows⟩ :: later

def inputs (legs : List Leg) : List (Handle × Atom) := legs.map fun leg => (leg.handle, leg.pattern)

def Valid (legs : List Leg) (state : Effects.State) : Prop :=
  ∀ leg ∈ legs, ∀ bindings, QueryReadStability.view state leg.handle bindings leg.pattern =
    some (choices bindings leg.pattern leg.rows)

theorem prepare_exact (state : Effects.State) (requested : List (Handle × Atom)) (legs : List Leg)
    (prepared : prepare state requested = some legs) : inputs legs = requested ∧ Valid legs state := by
  induction requested generalizing legs with
  | nil =>
      cases prepared
      exact ⟨rfl, by intro leg member; cases member⟩
  | cons request rest ih =>
      rcases request with ⟨handle, pattern⟩
      obtain ⟨rows, snapshot, remaining⟩ := Option.bind_eq_some_iff.mp prepared
      obtain ⟨later, ready, same⟩ := Option.bind_eq_some_iff.mp remaining
      cases Option.some.inj same
      obtain ⟨erases, valid⟩ := ih later ready
      constructor
      · simpa [inputs] using congrArg (List.cons (handle, pattern)) erases
      · intro leg member bindings
        rcases List.mem_cons.mp member with same | member
        · subst leg
          simp [QueryReadStability.view, snapshot]
        · exact valid leg member bindings

def source (legs : List Leg) (body : Atom) : Atom :=
  NestedQuerySource.source (inputs legs) body

/-- The prepared worker never reads a space while traversing a query leg.
Only the declared leaf body may inspect or update the current world. -/
def run (body : Body) : List Leg → Body
  | [], bindings, state => body bindings state
  | leg :: rest, bindings, state =>
      traverse (run body rest) (choices bindings leg.pattern leg.rows) (state, [])

#print axioms run.eq_1
#print axioms run.eq_2
#print axioms run.eq_def

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

/-- An invariant is passed through each real body execution, rather than
requiring a body theorem for arbitrary unreachable intermediate worlds. -/
theorem sequence_returns_invariant (program : Program) (expression : Atom) (body : Body)
    (invariant : Effects.State → Prop) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before after answers, invariant before →
      body bindings before = some (after, answers) →
      Returns program bindings before expression after answers ∧ invariant after)
    (before after : Effects.State) (collected result : List Atom) (valid : invariant before)
    (completed : traverse body captured (before, collected) = some (after, result)) :
    (theory program).MultiStep
      {state := before, control := .sequence (captured.map (fun bindings => .evaluate bindings expression)) collected}
      (finished after result [] []) ∧ invariant after := by
  induction captured generalizing before collected with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact ⟨.step (step_transition rfl) (.refl _), valid⟩
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨returned, middleValid⟩ := law bindings List.mem_cons_self before next.1 next.2 valid first
      obtain ⟨continued, finalValid⟩ := ih
        (fun bound member => law bound (List.mem_cons_of_mem _ member)) next.1 (collected ++ next.2) middleValid later
      refine ⟨?_, finalValid⟩
      exact sequence_cons_answers program before next.1 after (.evaluate bindings expression)
        (rest.map fun bound => .evaluate bound expression) collected next.2 result returned continued

theorem match_returns_invariant (program : Program) (caller : Subst) (before after : Effects.State)
    (space pattern expression : Atom) (handle : Handle) (captured : List Subst)
    (body : Body) (answers : List Atom) (invariant : Effects.State → Prop)
    (spaceReturn : PureReturns program caller before space before (Effects.handleValue handle))
    (complete : QueryReadStability.view before handle caller pattern = some captured)
    (law : ∀ bindings ∈ captured, ∀ current next values, invariant current →
      body bindings current = some (next, values) →
      Returns program bindings current expression next values ∧ invariant next)
    (valid : invariant before)
    (completed : traverse body captured (before, []) = some (after, answers)) :
    Returns program caller before (.expression [.symbol "match", space, pattern, expression]) after answers ∧
      invariant after := by
  obtain ⟨rows, snapshot, same⟩ := QueryReadStability.complete_view_has_read complete
  have reading : (Effects.readHandle (Effects.handleValue handle) >>= before.read) = some rows := by
    simp [snapshot]
  obtain ⟨bodies, finalValid⟩ := sequence_returns_invariant program expression body invariant captured
    law before after [] answers valid completed
  refine ⟨?_, finalValid⟩
  refine .step (step_transition rfl) (path_trans
    (path_with_caller_frames program [.query caller pattern expression] spaceReturn) ?_)
  refine .step (step_transition rfl) ?_
  simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, queryAlternatives, reading]
  rw [← choices_controls, same]
  exact bodies

/-- Independent source execution is reconstructed through each nested
query, while the prepared worker uses its retained reads. -/
theorem run_returns (program : Program) (expression : Atom) (body : Body) (footprint : List Leg)
    (leaf : ∀ bindings before after answers, Valid footprint before →
      body bindings before = some (after, answers) →
      Returns program bindings before expression after answers ∧ Valid footprint after)
    (legs : List Leg) (within : ∀ leg ∈ legs, leg ∈ footprint)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (valid : Valid footprint before) (completed : run body legs caller before = some (after, answers)) :
    Returns program caller before (source legs expression) after answers ∧ Valid footprint after := by
  induction legs generalizing caller before after answers with
  | nil => exact leaf caller before after answers valid completed
  | cons leg rest ih =>
      apply match_returns_invariant program caller before after
        (.expression [.symbol "quote", Effects.handleValue leg.handle]) leg.pattern (source rest expression)
        leg.handle (choices caller leg.pattern leg.rows) (run body rest) answers (Valid footprint)
      · have pure := quote_returns program caller before (Effects.handleValue leg.handle)
        have fixed : applySubst caller (Effects.handleValue leg.handle) = Effects.handleValue leg.handle := by
          cases leg.handle <;> rfl
        simpa only [fixed] using pure
      · exact valid leg (within leg List.mem_cons_self) caller
      · intro bindings _ current next values currentValid returned
        exact ih (fun member present => within member (List.mem_cons_of_mem _ present))
          bindings current next values currentValid returned
      · exact valid
      · exact completed

theorem insertion_preserves_valid (legs : List Leg) (target : Handle) (row : Atom)
    (before after : Effects.State) (valid : Valid legs before)
    (irrelevant : ∀ leg ∈ legs, ∀ bindings, leg.handle ≠ target ∨ matchValue bindings leg.pattern row = none)
    (updated : GuardedInsertionSource.update before target row = some after) : Valid legs after := by
  intro leg member bindings
  rw [QueryReadStability.guarded_insert_stable bindings updated (irrelevant leg member bindings)]
  exact valid leg member bindings

/-- Collapse counts the complete ordered answer list, not the number of
distinct payloads or newly inserted rows. -/
theorem counted_run_returns (program : Program) (expression : Atom) (body : Body) (footprint : List Leg)
    (leaf : ∀ bindings before after answers, Valid footprint before →
      body bindings before = some (after, answers) →
      Returns program bindings before expression after answers ∧ Valid footprint after)
    (legs : List Leg) (within : ∀ leg ∈ legs, leg ∈ footprint)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (valid : Valid footprint before) (completed : run body legs caller before = some (after, answers)) :
    PureReturns program caller before
      (.expression [.symbol "size-atom", .expression [.symbol "collapse", source legs expression]])
      after (.grounded (.int answers.length)) ∧ Valid footprint after := by
  obtain ⟨returned, finalValid⟩ := run_returns program expression body footprint leaf legs within
    caller before after answers valid completed
  have collected := collapse_returns program caller before after _ _ returned
  refine ⟨?_, finalValid⟩
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PreparedEffectfulQuery
