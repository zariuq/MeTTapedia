import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.ConcurrencySeparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# PeTTa and HE: a strategy and an observation over the step

## The strategy

* **Effects are sequenced within a branch.** A branch runs its single-atom operations in order
  (`Concurrency.Op`, `runOps`), as the body of a `let*`, of a function, or of one `match` answer.
* **Branches are unordered.** `superpose` and `match` produce alternatives in an order no program may
  rely on: spaces are unordered and a `collapse` is any permutation of its bag. `sequential` runs the
  branches one after another, in every order.
* **`hyperpose`** (SWI-PeTTa, CeTTa's PeTTa lane) is modelled as threads interleaving on one shared
  store: `hyperpose`. That is the interleaving reading; the tree's PLeaTTa compiler reads hyperpose
  sequentially (`Goal.amb`), and no theorem here relates the two readings. HE has no threads.
  `mutexed` is this hyperpose with a lock around every branch, each branch one sequence of
  operations.

## The observation

The possible outcomes: the answer bag and the store reached, over all orders (`sequential`) or all
interleavings (`hyperpose`). The two engines differ in removal (`pettaRemoval`: every copy, with an
answer saying whether one was there; `heRemoval`: one copy, unit either way).

## Where the narrowing from the step is open

The step's side is the atomic take (`Concurrency.Take`), a bag model of one firing; the dialect's
side is its encoding as a match then removals and additions. A ground firing of the step that reads
distinct occurrences is such a take (`Concurrency.firing_is_take`); the converse is not proved, so
the results below are about the bag model of firings.

* **Sequential evaluation: open.** `sequential_open`: with HE's removal and takes of distinct atoms,
  the identity is a functional bisimulation (`TransitionMaps.FunctionalBisimulation`, the
  path-lifting `Zag` of open maps) between the atomic serial steps and the sequential steps of the
  encodings. With PeTTa's removal each block is exact on stores where every taken atom is single
  (`Concurrency.sequential_exact`) and `Concurrency.Controls.remove_all_loses_copy` is the failure
  otherwise; a bisimulation under PeTTa's removal needs that condition kept along the run, which is
  not proved here.
* **A lock around each branch: the sequential outcomes.** `mutexed_eq_sequential`
  (`Concurrency.lock_exact`); with HE's removal (one copy) and takes of distinct atoms, the outcomes
  of the atomic takes (`Concurrency.global_lock_exact`). Each branch is one sequence of operations
  and answers at most once, so a lock that keeps every branch and a lock committed to the first
  answer coincide on it.
* **PeTTa's lock is committed-choice.** SWI's `with_mutex/2` and `transaction/1` run their goal as
  `once/1`, and SWI-PeTTa dispatches to them directly. Around a nondeterministic producer the lock
  keeps its first answer only (`onceLocked`): `Controls.once_lock_loses_answers`, two branches that
  both answer give both answers sequentially and at most one under the committed lock, as
  `superpose` gives 2 answers and `with_mutex` or `transaction` around it gives 1 on SWI-PeTTa.
  `transaction/1` also rolls back the database writes of a goal that fails; that is not modelled.
* **Hyperpose without a lock: not open.** `hyperpose_not_open`: a path of the interleaved encodings
  out of the image of a configuration reaches a final configuration that no atomic path reaches.
  `hyperpose_no_zag` follows, but it holds already by granularity, since one interleaved operation is
  not a whole atomic take, even for a single thread (`Controls.no_lift_single_thread`); the race is
  `hyperpose_not_open`. Every
  sequential outcome is a hyperpose outcome (`sequential_sub_hyperpose`), so hyperpose adds outcomes
  and loses none.
* **Host effects: off the step.** A branch's host effects (output, files, foreign calls) are not
  firings. `Controls.host_log_off_step`: two runs with the same answer bag and store write the host
  log in two orders; the log is an observation the step does not carry, and seeing it sees order.

## Snapshots, checked in the engines' sources

* SWI-PeTTa: a space is a family of dynamic predicates, and `match` calls them by backtracking, so
  SWI-Prolog's logical update view gives each call the clauses of its pre-state
  (`ISOProlog.DB.view_stable`). A conjunctive pattern calls its later conjuncts again for every
  solution of the earlier ones, so each conjunct sees the store as the earlier bodies left it.
* CeTTa: an open reader keeps its rows: a removal detaches the space before rewriting it, and an
  addition lands beyond the reader's ceiling. A call reads its pre-state.
* HE: `match` collects every binding of the query before any template is evaluated: one match reads
  its pre-state.
* `Controls.snapshot_granularity`: SWI's per-conjunct reading and HE's per-match reading give
  different answer bags for one program; the per-match reading is one firing reading its pre-state,
  the per-conjunct one a chain of reads.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

namespace PeTTaHE

open Concurrency
open FragmentsOfTheStep.TransitionMaps

variable {α : Type*} [DecidableEq α] {β : Type*}

/-- **PeTTa's removal** (SWI-PeTTa and CeTTa's PeTTa lane): every copy; `checked` when the program
tests the answer. -/
def pettaRemoval (checked : Bool) : Removal := ⟨true, checked⟩

/-- **HE's removal**: one copy, unit either way. -/
def heRemoval : Removal := ⟨false, false⟩

/-- **The sequential strategy**: each branch's operations in order, the branches in every order. -/
def sequential (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  serialOutcomes (bodies pol) Prod.snd s branches

/-- **Hyperpose**: the branches as threads on one store. -/
def hyperpose (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  interleavedOutcomes pol s branches

/-- **Hyperpose with a lock around every branch**, each branch one sequence of operations, so it
answers at most once: committing to its first answer loses nothing here. -/
def mutexed (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  lockedOutcomes pol s branches

/-- **A lock around each branch gives the sequential outcomes.** The lock is around each
single-sequence branch, not around a nondeterministic producer (for that, `onceLocked`). -/
theorem mutexed_eq_sequential (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    mutexed pol s branches = sequential pol s branches :=
  lock_exact pol s branches

/-! ## A lock around a nondeterministic producer, committed to its first answer -/

/-- **The once-committed lock around a producer**, as SWI's `with_mutex/2` and `transaction/1` run
their goal (`once/1`): the producer's branches are tried one after another until one finishes; its
answer is the only answer, and the branches after it never run. The effects of branches that die
before it stay, as with `with_mutex`; the rollback of `transaction/1` is not modelled. -/
def onceRun (pol : Removal) : List (List (Op α) × β) → Multiset α → Multiset β × Multiset α
  | [], s => (0, s)
  | (code, b) :: rest, s =>
      if (runOps pol code s).2 then ({b}, (runOps pol code s).1)
      else onceRun pol rest (runOps pol code s).1

/-- **The outcomes of the once-committed lock**: the producer offers its branches in some order. -/
def onceLocked (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  {o | ∃ order : List (List (Op α) × β), order.Perm branches ∧ onceRun pol order s = o}

theorem onceRun_card (pol : Removal) : ∀ (branches : List (List (Op α) × β)) (s : Multiset α),
    Multiset.card (onceRun pol branches s).1 ≤ 1
  | [], _ => by simp [onceRun]
  | (code, b) :: rest, s => by
      by_cases fired : (runOps pol code s).2 = true
      · show Multiset.card (if (runOps pol code s).2 = true then ({b}, (runOps pol code s).1)
          else onceRun pol rest (runOps pol code s).1).1 ≤ 1
        rw [if_pos fired]
        simp
      · show Multiset.card (if (runOps pol code s).2 = true then ({b}, (runOps pol code s).1)
          else onceRun pol rest (runOps pol code s).1).1 ≤ 1
        rw [if_neg fired]
        exact onceRun_card pol rest _

/-- **The once-committed lock answers at most once**, whatever the producer. -/
theorem onceLocked_at_most_one (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    ∀ o ∈ onceLocked pol s branches, Multiset.card o.1 ≤ 1 := by
  rintro o ⟨order, _, rfl⟩
  exact onceRun_card pol order s

/-- **Every sequential outcome is a hyperpose outcome.** -/
theorem sequential_sub_hyperpose (pol : Removal) (s : Multiset α) (branches : List (List (Op α) × β)) :
    sequential pol s branches ⊆ hyperpose pol s branches := by
  intro o path
  have interleaved : ∀ {x y : SConfig α (List (Op α) × β) β},
      Relation.ReflTransGen (Serial (bodies pol) Prod.snd) x y →
      Relation.ReflTransGen (Interleave pol) ⟨x.store, x.pending, x.answers⟩
        ⟨y.store, y.pending, y.answers⟩ := by
    intro x y path
    induction path with
    | refl => exact .refl
    | tail _ step earlier =>
        refine earlier.trans ?_
        cases step with
        | shuffle perm => exact .single (.shuffle perm)
        | @run s t ts ans => exact interleave_block pol t.1 s t.2 ts ans
  exact interleaved path

/-! ## Open in the sequential evaluator -/

/-- Configurations whose pending takes take and read distinct atoms. -/
def Linear (x : SConfig α (Take α × β) β) : Prop := ∀ t ∈ x.pending, (t.1.take ++ t.1.read).Nodup

/-- The step's side: atomic takes, from linear configurations. -/
def atomicStep (x y : SConfig α (Take α × β) β) : Prop := Serial atomic Prod.snd x y ∧ Linear x

/-- The dialect's side: the encodings run sequentially, from linear configurations. -/
def sequentialStep (pol : Removal) (x y : SConfig α (Take α × β) β) : Prop :=
  Serial (locked pol) Prod.snd x y ∧ Linear x

omit [DecidableEq α] in
/-- One serial move depends on the blocks of the threads it holds only. -/
theorem serial_step_congr {γ : Type*} {block₁ block₂ : γ → Multiset α → Multiset α × Bool}
    {answer : γ → β} {x y : SConfig α γ β} (step : Serial block₁ answer x y)
    (agree : ∀ t ∈ x.pending, block₁ t = block₂ t) : Serial block₂ answer x y := by
  cases step with
  | shuffle perm => exact .shuffle perm
  | @run s t ts ans =>
      have same := agree t List.mem_cons_self
      rw [same]
      exact .run

/-- **The narrowing is open in the sequential evaluator**: with one-copy removal, on linear
configurations, the identity carries atomic steps to sequential steps of the encodings and lifts
every sequential step back. -/
theorem sequential_open (pol : Removal) (one : pol.all = false) :
    FunctionalBisimulation (atomicStep (α := α) (β := β)) (sequentialStep pol) id := by
  have agree : ∀ (x : SConfig α (Take α × β) β), Linear x → ∀ t ∈ x.pending, atomic t = locked pol t :=
    fun x linear t member => by
      funext s
      exact (sequential_exact pol t.1 s (linear t member)
        (fun all => absurd (one.symm.trans all) (by decide))).symm
  refine ⟨fun {x y} step => ⟨serial_step_congr step.1 (agree x step.2), step.2⟩,
    fun {x y'} step => ⟨y', ⟨serial_step_congr step.1 fun t member => (agree x step.2 t member).symm,
      step.2⟩, rfl⟩⟩

/-! ## Not open under hyperpose -/

/-- **The narrowing into hyperpose is not open**: a path of the interleaved encodings out of the
image of a configuration reaches a final configuration that no atomic path reaches. -/
theorem hyperpose_not_open (pol : Removal) :
    ∃ (x : SConfig ℕ (Take ℕ × ℕ) ℕ) (y : Config ℕ ℕ),
      Relation.ReflTransGen (Interleave pol) (embed x) y ∧ y.threads = [] ∧
        ¬ ∃ x', Relation.ReflTransGen (Serial atomic Prod.snd) x x' ∧ embed x' = y := by
  obtain ⟨o, interleaved, notSerial⟩ := race pol
  refine ⟨⟨both, threads, 0⟩, ⟨o.2, [], o.1⟩, interleaved, rfl, ?_⟩
  rintro ⟨⟨store, pending, answers⟩, path, mapped⟩
  have hp : pending = [] := by
    have := congrArg Config.threads mapped
    simpa [embed] using this
  have hs : store = o.2 := congrArg Config.store mapped
  have ha : answers = o.1 := congrArg Config.answers mapped
  subst hp hs ha
  exact notSerial path

/-- **No path lifting**: the atomic steps do not lift the interleaving steps through `embed`. This
holds already by granularity, since one interleaved operation is not a whole atomic take, even for a
single thread (`Controls.no_lift_single_thread`); it is not itself evidence of the race, which is
`hyperpose_not_open`. -/
theorem hyperpose_no_zag (pol : Removal) :
    ¬ Zag (Serial (atomic (α := ℕ) (β := ℕ)) Prod.snd) (Interleave pol) embed := by
  intro zag
  obtain ⟨x, y, path, _, noLift⟩ := hyperpose_not_open pol
  exact noLift (Zag.path zag path x rfl)

/-! ## Controls -/

namespace Controls

/-- Serial runs that keep the order in which branches finish: a host log. -/
inductive SerialLog {γ : Type*} (block : γ → Multiset α → Multiset α × Bool) (answer : γ → β) :
    Multiset α × List γ × List β → Multiset α × List γ × List β → Prop
  | shuffle {s : Multiset α} {ts ts' : List γ} {log : List β} :
      ts.Perm ts' → SerialLog block answer (s, ts, log) (s, ts', log)
  | run {s : Multiset α} {t : γ} {ts : List γ} {log : List β} :
      SerialLog block answer (s, t :: ts, log)
        ((block t s).1, ts, if (block t s).2 then log ++ [answer t] else log)

omit [DecidableEq α] in
/-- The answer bag is the host log forgotten. -/
theorem log_forgets {γ : Type*} {block : γ → Multiset α → Multiset α × Bool} {answer : γ → β}
    {x y : Multiset α × List γ × List β} (path : Relation.ReflTransGen (SerialLog block answer) x y) :
    Relation.ReflTransGen (Serial block answer) ⟨x.1, x.2.1, (x.2.2 : Multiset β)⟩
      ⟨y.1, y.2.1, (y.2.2 : Multiset β)⟩ := by
  induction path with
  | refl => exact .refl
  | tail _ step earlier =>
      refine earlier.trans ?_
      cases step with
      | shuffle perm => exact .single (.shuffle perm)
      | @run s t ts log =>
          have step := Serial.run (block := block) (answer := answer) (s := s) (t := t) (ts := ts)
            (ans := (log : Multiset β))
          by_cases fired : (block t s).2 = true
          · simp only [fired, if_true] at step ⊢
            rw [← Multiset.coe_add, Multiset.coe_singleton, add_comm, Multiset.singleton_add]
            exact .single step
          · simp only [fired] at step ⊢
            exact .single step

/-- **Control: host effects are off the step.** Two branches that touch no atom and answer `1` and
`2`: the runs in the two orders reach the same answer bag and store, and write the host log in two
orders. -/
theorem host_log_off_step :
    Relation.ReflTransGen (SerialLog (bodies (α := ℕ) heRemoval) Prod.snd)
        ((0 : Multiset ℕ), [([], 1), ([], 2)], ([] : List ℕ)) (0, [], [1, 2]) ∧
      Relation.ReflTransGen (SerialLog (bodies (α := ℕ) heRemoval) Prod.snd)
        ((0 : Multiset ℕ), [([], 1), ([], 2)], ([] : List ℕ)) (0, [], [2, 1]) ∧
      (([1, 2] : List ℕ) : Multiset ℕ) = ([2, 1] : List ℕ) ∧ ([1, 2] : List ℕ) ≠ [2, 1] :=
  ⟨.head .run (.single .run), .head (.shuffle (.swap _ _ _)) (.head .run (.single .run)),
    by decide, by decide⟩

/-- **HE reads per match**: every solution of `(, (p $x) q)` is found on the pre-state, then the body
(remove `q`, answer `x`) runs for each. Atoms: `p 1`, `p 2` are `1`, `2`; `q` is `9`. -/
def perMatch (s : Multiset ℕ) : List ℕ × Multiset ℕ :=
  let solutions := ([1, 2] : List ℕ).filter fun x => decide (x ∈ s) && decide (9 ∈ s)
  (solutions, solutions.foldl (fun store _ => store.erase 9) s)

/-- **SWI-PeTTa reads per conjunct**: the first conjunct's solutions are found once; the second is
called again for each, on the store the earlier bodies left. -/
def perConjunct (s : Multiset ℕ) : List ℕ × Multiset ℕ :=
  (([1, 2] : List ℕ).filter fun x => decide (x ∈ s)).foldl
    (fun acc x => if 9 ∈ acc.2 then (acc.1 ++ [x], acc.2.erase 9) else acc) ([], s)

/-- **Control: snapshot granularity.** On `{p 1, p 2, q}` the per-match reading answers twice, the
per-conjunct reading once. -/
theorem snapshot_granularity :
    perMatch {1, 2, 9} = ([1, 2], {1, 2}) ∧ perConjunct {1, 2, 9} = ([1], {1, 2}) := by
  constructor <;> decide

/-- **Control: `hyperpose_no_zag` holds by granularity.** One thread taking `0` from the store
`{0}`, with no second thread and no race: its first interleaved operation, the query, has no atomic
lift through `embed`. -/
theorem no_lift_single_thread (pol : Removal) :
    Interleave pol (embed (⟨{0}, [(⟨[0], [], []⟩, 1)], 0⟩ : SConfig ℕ (Take ℕ × ℕ) ℕ))
        ⟨{0}, [([.remove 0], 1)], 0⟩ ∧
      ¬ ∃ x', Serial (atomic (α := ℕ) (β := ℕ)) Prod.snd
          (⟨{0}, [(⟨[0], [], []⟩, 1)], 0⟩ : SConfig ℕ (Take ℕ × ℕ) ℕ) x' ∧
        embed x' = ⟨{0}, [([.remove 0], 1)], 0⟩ := by
  refine ⟨.op (run_query_pass pol (by decide)), ?_⟩
  rintro ⟨x', step, mapped⟩
  have threads := congrArg Config.threads mapped
  cases step with
  | shuffle perm =>
      obtain rfl := List.perm_singleton.mp perm.symm
      simp [embed, Take.encode] at threads
  | run => simp [embed] at threads

/-- Two branches that both answer, with no effects: `superpose (1 2)`. -/
def twoAnswers : List (List (Op ℕ) × ℕ) := [([], 1), ([], 2)]

/-- **Control: the once-committed lock loses answers that the sequential semantics keeps.** Run
sequentially, the two branches give both answers; under a lock committed to the producer's first
answer every outcome has at most one, as on SWI-PeTTa `superpose` gives 2 answers and `with_mutex`
or `transaction` around it gives 1. -/
theorem once_lock_loses_answers (pol : Removal) (s : Multiset ℕ) :
    ((2 ::ₘ 1 ::ₘ 0 : Multiset ℕ), s) ∈ sequential pol s twoAnswers ∧
      (({1} : Multiset ℕ), s) ∈ onceLocked pol s twoAnswers ∧
      ∀ o ∈ onceLocked pol s twoAnswers, Multiset.card o.1 ≤ 1 := by
  refine ⟨?_, ⟨twoAnswers, List.Perm.refl _, rfl⟩, onceLocked_at_most_one pol s twoAnswers⟩
  have first : Serial (bodies pol) Prod.snd
      (⟨s, twoAnswers, 0⟩ : SConfig ℕ (List (Op ℕ) × ℕ) ℕ) ⟨s, [([], 2)], 1 ::ₘ 0⟩ :=
    serial_run_eq (block := bodies pol) (answer := Prod.snd) (t := ([], 1)) (ts := [([], 2)])
      (ans := 0) (s := s) (s' := s) (fired := true) rfl
  have second : Serial (bodies pol) Prod.snd
      (⟨s, [([], 2)], 1 ::ₘ 0⟩ : SConfig ℕ (List (Op ℕ) × ℕ) ℕ) ⟨s, [], 2 ::ₘ 1 ::ₘ 0⟩ :=
    serial_run_eq (block := bodies pol) (answer := Prod.snd) (t := ([], 2)) (ts := [])
      (ans := 1 ::ₘ 0) (s := s) (s' := s) (fired := true) rfl
  show Relation.ReflTransGen (Serial (bodies pol) Prod.snd) ⟨s, twoAnswers, 0⟩ ⟨s, [], 2 ::ₘ 1 ::ₘ 0⟩
  exact .tail (.single first) second

end Controls

#print axioms mutexed_eq_sequential
#print axioms onceLocked_at_most_one
#print axioms Controls.once_lock_loses_answers
#print axioms sequential_sub_hyperpose
#print axioms sequential_open
#print axioms hyperpose_not_open
#print axioms hyperpose_no_zag
#print axioms Controls.no_lift_single_thread
#print axioms Controls.log_forgets
#print axioms Controls.host_log_off_step
#print axioms Controls.snapshot_granularity

end PeTTaHE

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
