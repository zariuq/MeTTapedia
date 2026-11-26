import Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms
import Mettapedia.Machines.TIsa.Derivation.Contents
import Mettapedia.Machines.TIsa.StoreInstructions.FiringLoop

/-!
# The derived machine on a multiset store: a positive and a negative example

One first-order program over four atoms, on a multiset store. `split` takes a `token` and makes a
`half`; `join` takes two `half`s and makes a `whole`. The store starts with two `token`s and a
`mark`.

## Positive: the machine, the evaluator, t-ISA and the step theory agree

* `machine_runs`: the derived machine, run by the bounded driver, halts quiescent with a `mark`
  and a `whole`; `evaluator_runs`: so does the evaluator, as the derivation proves it must.
* `final_reached`, `final_terminal`: this store is an outcome of the step theory: reached by its
  steps from the start, with no step left.
* `outcome_unique`: it is the step theory's only outcome: every store the step theory reaches from
  the start and cannot leave has exactly these values. The proof is a counting invariant
  (`balanced_reached`) and the progress of `split` and `join` (`step_of_token`, `step_of_halves`).
* `tisa_fires`, `tisa_run`: the compiled t-ISA firing loop publishes the same first firing, and
  invoked once per firing it reaches the same final store, then refuses.

## Negative: a plausible wrong `make` changes the outcome

A `make` that adds a value only when the store does not already carry it (`Store.addUnique`), as a
set store would, gives a machine (`stepDedup`) that halts with a `mark` and one `half`
(`dedup_runs`): the second `half` was absorbed, so `join` never fires. That outcome differs
(`dedup_differs`), and no store the step theory reaches has its values (`dedup_unreachable`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.Examples

open Mettapedia.Logic.LP
open Mettapedia.Machines.TIsa
open FirstOrderTerms

/-! ## The program -/

/-- Four atoms. -/
inductive Atom where
  | token | half | whole | mark
  deriving DecidableEq, Repr

/-- The signature: the atoms as constants, natural-number variables, no function symbols. -/
def sig : LPSignature where
  constants := Atom
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := fun _ => 0

instance : DecidableEq sig.constants := inferInstanceAs (DecidableEq Atom)
instance : DecidableEq sig.vars := inferInstanceAs (DecidableEq ℕ)
instance : DecidableEq sig.functionSymbols := inferInstanceAs (DecidableEq Empty)
instance : Inhabited (Term sig) := ⟨.var (0 : ℕ)⟩

/-- An atom as a value. -/
def value (x : Atom) : GroundTerm sig := .const x

/-- An atom as a term. -/
def term (x : Atom) : Term sig := .const x

/-- A rule that takes some atoms and makes others. -/
def rule (take produce : List Atom) : Rule (Term sig) :=
  ⟨PUnit.unit, ⟨take.map term, [], [], [], produce.map term⟩, []⟩

/-- Take a `token`, make a `half`. -/
def split : Rule (Term sig) := rule [.token] [.half]

/-- Take two `half`s, make a `whole`. -/
def join : Rule (Term sig) := rule [.half, .half] [.whole]

/-- The program. -/
def program : List (Rule (Term sig)) := [split, join]

/-- Two `token`s and a `mark`. -/
def start : Store (GroundTerm sig) := ⟨[(0, value .token), (1, value .token), (2, value .mark)], 3⟩

/-- A `mark` and a `whole`. -/
def final : Store (GroundTerm sig) := ⟨[(2, value .mark), (5, value .whole)], 6⟩

/-- The matcher and its laws. -/
abbrev M : Matcher (Term sig) (GroundTerm sig) (Bindings sig) := matcher
abbrev Sem : Semantics (Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder.action sig) M :=
  semantics

/-! ## Positive: the machine and the evaluator -/

/-- **The derived machine runs the program to quiescence.** -/
theorem machine_runs :
    (BoundedDeterministicRun.run (step M program) 200 (.run 5 start)).outcome? =
      some (.quiescent final) := by
  decide +kernel

/-- The evaluator's run is the machine's. -/
theorem evaluator_runs : run M program 5 start = .quiescent final :=
  (driver_sound M program 5 200 start _ machine_runs).symm

theorem start_wellFormed : start.WellFormed := ⟨by decide, by decide⟩

theorem ranged : ∀ r ∈ program, RangeRestricted M r := by
  intro r member
  apply rangeRestricted_of_scoped
  intro t inside x mentions
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [groundedTerms, split, join, rule, term] at inside <;> subst inside <;>
    simp [Term.freeVars] at mentions

/-! ## Positive: the step theory -/

/-- **The machine's outcome is reached by the step theory.** -/
theorem final_reached : Relation.ReflTransGen (Sem.GroundStep program) start final :=
  (Sem.run_quiescent_sound program 5 start final start_wellFormed evaluator_runs).1

/-- **The machine's outcome is terminal in the step theory.** -/
theorem final_terminal : ∀ st', ¬ Sem.GroundStep program final st' :=
  (Sem.firings_eq_nil_iff program final ⟨by decide, by decide⟩ ranged).mp
    (Sem.run_quiescent_sound program 5 start final start_wellFormed evaluator_runs).2

/-- The counting invariant: tokens, halves and twice the wholes make two; one mark. -/
def Balanced (st : Store (GroundTerm sig)) : Prop :=
  st.values.count (value .token) + st.values.count (value .half) +
      2 * st.values.count (value .whole) = 2 ∧
    st.values.count (value .mark) = 1

/-- The rules' take values and made values. -/
def takeValues (r : Rule (Term sig)) : List (GroundTerm sig) := r.body.take.filterMap (instantiate [])
def madeValues (r : Rule (Term sig)) : List (GroundTerm sig) := r.body.produce.filterMap (instantiate [])

theorem ground : ∀ r ∈ program, r.body.take = (takeValues r).map Sem.embed ∧
    r.body.produce = (madeValues r).map Sem.embed := by
  intro r member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem count_eq (st st' : Store (GroundTerm sig)) (taken made : List (GroundTerm sig))
    (law : st'.values + (taken : Multiset (GroundTerm sig)) = st.values + (made : Multiset (GroundTerm sig)))
    (x : GroundTerm sig) :
    st'.values.count x + taken.count x = st.values.count x + made.count x := by
  have counted := congrArg (Multiset.count x) law
  simpa [Multiset.count_add, Multiset.coe_count] using counted

/-- **Every step keeps the balance.** -/
theorem balanced_step {st st' : Store (GroundTerm sig)} (distinct : st.Distinct) (balanced : Balanced st)
    (stepped : Sem.GroundStep program st st') : Balanced st' := by
  obtain ⟨r, member, law⟩ := Sem.groundStep_ground_values program takeValues madeValues ground
    distinct ranged stepped
  have counts := count_eq st st' (takeValues r) (madeValues r) law
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨balance, marks⟩ := balanced
  unfold Balanced
  simp only [value] at balance marks ⊢
  have t := counts (.const .token)
  have h := counts (.const .half)
  have w := counts (.const .whole)
  have k := counts (.const .mark)
  rcases member with rfl | rfl
  · simp (config := { decide := true }) [takeValues, madeValues, split, rule, term, instantiate]
      at t h w k
    constructor <;> omega
  · simp (config := { decide := true }) [takeValues, madeValues, join, rule, term, instantiate]
      at t h w k
    constructor <;> omega

/-- **Every store the step theory reaches is balanced**, with distinct identities. -/
theorem balanced_reached {st : Store (GroundTerm sig)}
    (reached : Relation.ReflTransGen (Sem.GroundStep program) start st) : Balanced st ∧ st.Distinct := by
  induction reached with
  | refl => exact ⟨by unfold Balanced; decide, by unfold Store.Distinct; decide⟩
  | tail _ stepped ih =>
      obtain ⟨_, _, reads⟩ := stepped
      exact ⟨balanced_step ih.2 ih.1 ⟨_, ‹_›, reads⟩, reads.1⟩

theorem collect_same (x : Atom) : collectBindingsList [term x] [value x] = some [] := by
  cases x <;> decide +kernel

theorem extend_same (x : Atom) : extend (σ := sig) [] (term x) (value x) = some [] := by
  simp [extend, collectBindings, collect_same, bindingsConsistent?]

/-- **`split` fires wherever a `token` is.** -/
theorem step_of_token {st : Store (GroundTerm sig)} (distinct : st.Distinct) {o : ℕ}
    (inside : (o, value .token) ∈ st.occurrences) : ∃ st', Sem.GroundStep program st st' := by
  have firing : (split, (⟨[], [o], [], [], [value .half]⟩ : Match (GroundTerm sig) (Bindings sig))) ∈
      firings M program st := by
    apply (mem_firings program st _ _).mpr
    refine ⟨by simp [program], (mem_solve_goals st split _).mpr ?_⟩
    refine ⟨[(o, value .token)], [], ⟨[], [o], [], [], []⟩, ⟨[], [o], [], [], []⟩, ?_, by simp, ?_, rfl, ?_⟩
    · intro x member
      simp only [List.mem_singleton] at member
      exact member ▸ inside
    · simp [attemptAll, attempt, Role.allows, Match.start, M, matcher, Match.select, split, rule,
        extend_same]
    · simp [applyAll, determinates, split, rule, Determinate.apply, M, matcher, instantiate, term, value]
  exact Sem.exists_groundStep program distinct firing

/-- **`join` fires wherever two `half`s are.** -/
theorem step_of_halves {st : Store (GroundTerm sig)} (distinct : st.Distinct) {o o' : ℕ}
    (different : o ≠ o') (inside : (o, value .half) ∈ st.occurrences)
    (inside' : (o', value .half) ∈ st.occurrences) : ∃ st', Sem.GroundStep program st st' := by
  have firing : (join, (⟨[], [o, o'], [], [], [value .whole]⟩ : Match (GroundTerm sig) (Bindings sig))) ∈
      firings M program st := by
    apply (mem_firings program st _ _).mpr
    refine ⟨by simp [program], (mem_solve_goals st join _).mpr ?_⟩
    refine ⟨[(o, value .half), (o', value .half)], [], ⟨[], [o, o'], [], [], []⟩, ⟨[], [o, o'], [], [], []⟩,
      ?_, by simp, ?_, rfl, ?_⟩
    · intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact inside
      · exact inside'
    · simp [attemptAll, attempt, Role.allows, Match.start, M, matcher, Match.select, join, rule,
        extend_same, Ne.symm different]
    · simp [applyAll, determinates, join, rule, Determinate.apply, M, matcher, instantiate, term, value]
  exact Sem.exists_groundStep program distinct firing

/-- Two occurrences of a value counted twice. -/
theorem two_of_count {st : Store (GroundTerm sig)} (distinct : st.Distinct) (x : GroundTerm sig)
    (twice : 2 ≤ st.values.count x) :
    ∃ o o', o ≠ o' ∧ (o, x) ∈ st.occurrences ∧ (o', x) ∈ st.occurrences := by
  have counted : 2 ≤ (st.occurrences.filter fun y => y.2 == x).length := by
    simp only [Store.values, Multiset.coe_count, List.count_eq_countP, List.countP_map] at twice
    rw [List.countP_eq_length_filter] at twice
    simpa [Function.comp_def] using twice
  obtain ⟨first, second, rest, split⟩ : ∃ first second rest,
      st.occurrences.filter (fun y => y.2 == x) = first :: second :: rest := by
    match h : st.occurrences.filter (fun y => y.2 == x) with
    | [] => rw [h] at counted; simp at counted
    | [_] => rw [h] at counted; simp at counted
    | first :: second :: rest => exact ⟨first, second, rest, h⟩
  have firstIn : first ∈ st.occurrences.filter (fun y => y.2 == x) := by rw [split]; simp
  have secondIn : second ∈ st.occurrences.filter (fun y => y.2 == x) := by rw [split]; simp
  have nodup : (st.occurrences.filter fun y => y.2 == x).Nodup :=
    (List.Nodup.of_map Prod.fst distinct).filter _
  rw [split] at nodup
  have firstNe : first ≠ second := fun same => (List.nodup_cons.mp nodup).1 (by simp [same])
  obtain ⟨firstOcc, firstValue⟩ := List.mem_filter.mp firstIn
  obtain ⟨secondOcc, secondValue⟩ := List.mem_filter.mp secondIn
  simp only [beq_iff_eq] at firstValue secondValue
  refine ⟨first.1, second.1, ?_, ?_, ?_⟩
  · intro same
    apply firstNe
    exact Prod.ext same (firstValue.trans secondValue.symm)
  · rw [← firstValue]
    exact firstOcc
  · rw [← secondValue]
    exact secondOcc

theorem values_eq_of_counts (st st' : Store (GroundTerm sig))
    (counts : ∀ x : Atom, st.values.count (value x) = st'.values.count (value x)) :
    st.values = st'.values := by
  ext v
  cases v with
  | const x => exact counts x
  | app f _ => exact f.elim

/-- **The step theory has one outcome from the start**: the machine's. -/
theorem outcome_unique {st : Store (GroundTerm sig)}
    (reached : Relation.ReflTransGen (Sem.GroundStep program) start st)
    (terminal : ∀ st', ¬ Sem.GroundStep program st st') : st.values = final.values := by
  obtain ⟨⟨balance, marks⟩, distinct⟩ := balanced_reached reached
  have noToken : st.values.count (value .token) = 0 := by
    by_contra present
    obtain ⟨o, inside⟩ : ∃ o, (o, value .token) ∈ st.occurrences := by
      have positive : 0 < st.values.count (value .token) := Nat.pos_of_ne_zero present
      obtain ⟨y, member, same⟩ := List.mem_map.mp (Multiset.count_pos.mp positive)
      exact ⟨y.1, same ▸ member⟩
    obtain ⟨st', stepped⟩ := step_of_token distinct inside
    exact terminal st' stepped
  have fewHalves : st.values.count (value .half) ≤ 1 := by
    by_contra many
    obtain ⟨o, o', different, inside, inside'⟩ := two_of_count distinct (value .half) (by omega)
    obtain ⟨st', stepped⟩ := step_of_halves distinct different inside inside'
    exact terminal st' stepped
  apply values_eq_of_counts
  intro x
  cases x <;> simp (config := { decide := true }) [final, Store.values, value]
    at balance marks noToken fewHalves ⊢ <;> omega

/-! ## Positive: t-ISA -/

/-- A p1 machine state with an allowance of ten units. -/
def machine₀ : P1WordExecution.State :=
  ⟨fun _ => 0, fun _ => ⟨0, 0, .absent⟩, fun _ => 0, fun _ => none, 10, 0⟩

/-- The t-ISA state holding the start store. -/
def tisaStart : StoreInstructions.State (GroundTerm sig) (Bindings sig) :=
  ⟨machine₀, start, fun _ => Match.start M⟩

/-- The store of a `FIRED` return. -/
def firedStore? : StoreInstructions.Flow (GroundTerm sig) (Bindings sig) → Option (Store (GroundTerm sig))
  | .returned .completed _ st => some st.store
  | _ => none

/-- **The compiled firing loop publishes the machine's first firing.** -/
theorem tisa_fires :
    firedStore? (StoreInstructions.execute M tisaStart (StoreInstructions.program 16 program)) =
      some ⟨[(1, value .token), (2, value .mark), (3, value .half)], 4⟩ := by
  decide +kernel

/-- Invoke the compiled program once per firing, until it refuses. -/
def invokeAll : ℕ → StoreInstructions.State (GroundTerm sig) (Bindings sig) → Option (Store (GroundTerm sig))
  | 0, _ => none
  | n + 1, st =>
      match StoreInstructions.execute M st (StoreInstructions.program 16 program) with
      | .returned .completed _ after => invokeAll n after
      | .returned .refused _ after => some after.store
      | _ => none

/-- **Invoked once per firing, the compiled program reaches the machine's outcome.** -/
theorem tisa_run : invokeAll 5 tisaStart = some final := by
  decide +kernel

/-! ## Negative: a `make` that deduplicates -/

/-- Add a value only when the store does not already carry it. -/
def Store.addUnique (st : Store (GroundTerm sig)) (w : GroundTerm sig) : Store (GroundTerm sig) :=
  if st.occurrences.any (fun x => decide (x.2 = w)) then st else st.add w

/-- **The machine with a deduplicating `make`.** -/
def stepDedup : Config (Term sig) (GroundTerm sig) (Bindings sig) →
    Option (Config (Term sig) (GroundTerm sig) (Bindings sig))
  | .making a st (w :: ws) => some (.making a (Store.addUnique st w) ws)
  | c => step M program c

/-- A `mark` and one `half`. -/
def dedupFinal : Store (GroundTerm sig) := ⟨[(2, value .mark), (3, value .half)], 4⟩

/-- **The deduplicating machine halts with a `mark` and one `half`.** -/
theorem dedup_runs :
    (BoundedDeterministicRun.run stepDedup 200 (.run 5 start)).outcome? = some (.quiescent dedupFinal) := by
  decide +kernel

/-- Its outcome differs from the machine's. -/
theorem dedup_differs : dedupFinal.values ≠ final.values := by decide

/-- **No store the step theory reaches has the deduplicating machine's values.** -/
theorem dedup_unreachable {st : Store (GroundTerm sig)}
    (reached : Relation.ReflTransGen (Sem.GroundStep program) start st) : st.values ≠ dedupFinal.values := by
  intro same
  obtain ⟨⟨balance, _⟩, _⟩ := balanced_reached reached
  rw [same] at balance
  simp (config := { decide := true }) at balance

end Mettapedia.Machines.TIsa.Derivation.Examples
