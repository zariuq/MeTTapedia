import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

/-!
# Nested source queries with current-state reads

Each match captures its choices when that match is entered. Inner matches
therefore see effects performed by preceding bodies; they are not silently
replaced with a round-entry snapshot. The existing source evaluator and
ordered traversal remain the authority.

This is a completed-execution law for the effectful evaluator profile, not
an identification with the separate scoped raw-template/once profile. A
failed private worker alone does not authorize rollback after publication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

abbrev Leg := Handle × Atom

def source : List Leg → Atom → Atom
  | [], body => body
  | (handle, pattern) :: rest, body =>
      .expression [.symbol "match", .expression [.symbol "quote", Effects.handleValue handle], pattern, source rest body]

def run (body : Body) : List Leg → Body
  | [], bindings, state => body bindings state
  | (handle, pattern) :: rest, bindings, state => do
      let rows ← state.read handle
      traverse (run body rest) (choices bindings pattern rows) (state, [])

/-- An invariant on bindings is propagated by actual matching, not by a
fresh substitution chosen independently at each query leg. -/
theorem run_returns (program : Program) (expression : Atom) (body : Body)
    (invariant : Subst → Prop)
    (leaf : ∀ bindings before after answers, invariant bindings →
      body bindings before = some (after, answers) →
      Returns program bindings before expression after answers)
    (legs : List Leg)
    (stable : ∀ leg ∈ legs, ∀ bindings rows bound,
      invariant bindings → bound ∈ choices bindings leg.2 rows → invariant bound)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (valid : invariant caller) (completed : run body legs caller before = some (after, answers)) :
    Returns program caller before (source legs expression) after answers := by
  induction legs generalizing caller before after answers with
  | nil => exact leaf caller before after answers valid completed
  | cons leg rest ih =>
      rcases leg with ⟨handle, pattern⟩
      obtain ⟨rows, snapshot, traversed⟩ := Option.bind_eq_some_iff.mp completed
      apply EffectfulQuerySource.match_returns program caller before after
        (.expression [.symbol "quote", Effects.handleValue handle]) (Effects.handleValue handle)
        pattern (source rest expression) rows (run body rest) answers
      · have returned := quote_returns program caller before (Effects.handleValue handle)
        have closed : applySubst caller (Effects.handleValue handle) = Effects.handleValue handle := by
          cases handle <;> rfl
        simpa only [closed] using returned
      · simp [snapshot]
      · intro bound member current next values result
        exact ih (fun item included => stable item (List.mem_cons_of_mem _ included))
          bound current next values (stable (handle, pattern) List.mem_cons_self caller rows bound valid member) result
      · exact traversed

theorem counted_returns (program : Program) (expression : Atom) (body : Body)
    (invariant : Subst → Prop)
    (leaf : ∀ bindings before after answers, invariant bindings →
      body bindings before = some (after, answers) →
      Returns program bindings before expression after answers)
    (legs : List Leg)
    (stable : ∀ leg ∈ legs, ∀ bindings rows bound,
      invariant bindings → bound ∈ choices bindings leg.2 rows → invariant bound)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (valid : invariant caller) (completed : run body legs caller before = some (after, answers)) :
    PureReturns program caller before
      (.expression [.symbol "size-atom", .expression [.symbol "collapse", source legs expression]])
      after (.grounded (.int answers.length)) := by
  have returned := run_returns program expression body invariant leaf legs stable caller before after answers valid completed
  have collected := collapse_returns program caller before after _ _ returned
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

def silent (body : Body) : Prop :=
  ∀ bindings before after, body bindings before = some (after, []) → before = after

theorem traverse_silent (body : Body) (quiet : silent body) (captured : List Subst)
    (before after : Effects.State) (completed : traverse body captured (before, []) = some (after, [])) :
    before = after := by
  induction captured generalizing before with
  | nil => exact (Prod.mk.inj (Option.some.inj completed)).1
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      have empty := empty_result_has_empty_prefix body rest next.1 after ([] ++ next.2) later
      have noAnswers : next.2 = [] := by simpa using empty
      have noOutput : body bindings before = some (next.1, []) :=
        first.trans (congrArg some (Prod.ext rfl noAnswers))
      have same := quiet bindings before next.1 noOutput
      have tail := ih next.1 (by simpa only [noAnswers, List.nil_append] using later)
      exact same.trans tail

theorem run_silent (body : Body) (quiet : silent body) (legs : List Leg) : silent (run body legs) := by
  induction legs with
  | nil => exact quiet
  | cons leg rest ih =>
      intro bindings before after completed
      obtain ⟨rows, _, traversed⟩ := Option.bind_eq_some_iff.mp completed
      exact traverse_silent (run body rest) ih (choices bindings leg.2 rows) before after traversed

theorem traverse_empty_iff (body : Body) (quiet : silent body) (captured : List Subst)
    (state : Effects.State) :
    traverse body captured (state, []) = some (state, []) ↔
      ∀ bindings ∈ captured, body bindings state = some (state, []) := by
  induction captured with
  | nil => simp [EffectfulQuerySource.traverse]
  | cons first rest ih =>
      constructor
      · intro completed
        obtain ⟨next, firstRun, later⟩ := Option.bind_eq_some_iff.mp completed
        have empty := empty_result_has_empty_prefix body rest next.1 state ([] ++ next.2) later
        have noAnswers : next.2 = [] := by simpa using empty
        have noOutput : body first state = some (next.1, []) :=
          firstRun.trans (congrArg some (Prod.ext rfl noAnswers))
        have same := quiet first state next.1 noOutput
        have firstExact : body first state = some (state, []) := by simpa [← same] using noOutput
        have restExact : traverse body rest (state, []) = some (state, []) := by
          simpa [noAnswers, ← same] using later
        intro bindings member
        rcases List.mem_cons.mp member with equal | member
        · simpa [equal] using firstExact
        · exact ih.mp restExact bindings member
      · intro all
        have firstRun := all first List.mem_cons_self
        have later := ih.mpr (fun bindings member => all bindings (List.mem_cons_of_mem _ member))
        simpa [EffectfulQuerySource.traverse, firstRun] using later

/-- At zero progress, the dynamic source execution is characterized by
complete reads in one unchanged state and no-op leaves for every match.
An unvisited inner space need not be allocated when an earlier leg is empty. -/
def QuietAt (body : Body) (state : Effects.State) : List Leg → Subst → Prop
  | [], bindings => body bindings state = some (state, [])
  | (handle, pattern) :: rest, bindings =>
      ∃ rows, state.read handle = some rows ∧
        ∀ bound ∈ choices bindings pattern rows, QuietAt body state rest bound

theorem run_empty_iff (body : Body) (quiet : silent body) (state : Effects.State)
    (legs : List Leg) (caller : Subst) :
    run body legs caller state = some (state, []) ↔ QuietAt body state legs caller := by
  induction legs generalizing caller with
  | nil => rfl
  | cons leg rest ih =>
      rcases leg with ⟨handle, pattern⟩
      cases snapshot : state.read handle with
      | none => simp [run, QuietAt, snapshot]
      | some rows =>
          simp only [run, snapshot, bind, Option.bind, QuietAt, Option.some.injEq,
            exists_eq_left']
          rw [traverse_empty_iff _ (run_silent body quiet rest)]
          exact forall_congr' fun bound => imp_congr_right fun _ => ih bound

def Growth (target : Handle) (body : Body) : Prop :=
  ∀ bindings before after answers rows, before.read target = some rows →
    body bindings before = some (after, answers) →
    ∃ result, after.read target = some result ∧ result.length = rows.length + answers.length

theorem traverse_growth (target : Handle) (body : Body) (growth : Growth target body)
    (captured : List Subst) (before after : Effects.State) (rows collected answers : List Atom)
    (snapshot : before.read target = some rows)
    (completed : traverse body captured (before, collected) = some (after, answers)) :
    ∃ result, after.read target = some result ∧ result.length + collected.length = rows.length + answers.length := by
  induction captured generalizing before rows collected with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact ⟨rows, snapshot, rfl⟩
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨middleRows, middleRead, increased⟩ := growth bindings before next.1 next.2 rows snapshot first
      obtain ⟨result, finalRead, balance⟩ := ih next.1 middleRows (collected ++ next.2) middleRead later
      refine ⟨result, finalRead, ?_⟩
      simp only [List.length_append] at balance
      omega

theorem run_growth (target : Handle) (body : Body) (growth : Growth target body)
    (legs : List Leg) : Growth target (run body legs) := by
  induction legs with
  | nil => exact growth
  | cons leg rest ih =>
      intro bindings before after answers rows snapshot completed
      obtain ⟨input, _, traversed⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨result, finalRead, balance⟩ := traverse_growth target (run body rest) ih
        (choices bindings leg.2 input) before after rows [] answers snapshot traversed
      exact ⟨result, finalRead, by simpa using balance⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource
