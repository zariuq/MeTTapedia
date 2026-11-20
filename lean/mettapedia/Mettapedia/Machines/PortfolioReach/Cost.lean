import Mettapedia.Machines.PortfolioReach.Reads

/-!
# Cost of the portfolio on the widened fragment

**The unit.** In the model a unit is one expansion of a state of the search, or one change of
bound: the entry of a call, a primitive, a test, the fan-out of a read over its rows, the return
of an answer. Arithmetic and reads are counted as work. A unit is not a time bound: what one
expansion costs (a unification, a big-integer operation, a fan-out over many rows) is not
counted, nor is the scheduler's own work.

* `portfolio_cost`: on a quiet root, under quanta `first, 2 first, 4 first, …`, a portfolio that
  has published has spent at most `2 w - 1` when the walk needs `w`, at most `3 d + first` when
  deepening needs `d`, and at most `3 (idWork + target) + first` when the bound `target` settles
  the demand.
* `portfolio_under_four`: hence less than four times the faster strategy's need, once that need
  is at least the first quantum (`Controls.small_need_pays_first_quantum` shows the condition is
  needed).
* `portfolio_cost_publishes`: such a publication exists whenever some bound settles the demand.
* `program_cost`: the same for an admitted program, arithmetic and reads included.

**An inline superpose and an anonymous relation.** In the program model a call branches into
its equations in one expansion, which is exactly the branch an inline `superpose` makes: the two
are the same state. When a call costs an expansion of its own before the branch (`prefixed`), it
adds one level and one unit to each round and changes no answer and no batch
(`prefixed_bounded`, `prefixed_work`, `prefixed_batch`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (Step Space Reaches IsAnswer bounded
  boundedWork idWork)
open Mettapedia.Machines.BoundedSearchPortfolio (Origin Task Cursor Status status ready
  expandOne children Iteration beginIteration nextIteration BatchMeaning start)

universe u v w x

section Cost

variable {σ : Type x} {S : Type u} {A : Type v} {E : Type w}

/-- **Cost on a quiet root.** -/
theorem portfolio_cost (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) (demand first count : Nat) (log : List E)
    (published :
      (portfolio sys root demand (rounds (doubling first) count) store log).published.isSome =
        true) :
    (∀ need, (walkResumable (sys.space store) demand).ready
        ((walkResumable (sys.space store) demand).step^[need] ⟨[root], []⟩) = true →
      (portfolio sys root demand (rounds (doubling first) count) store log).spent ≤
        2 * need - 1) ∧
    (∀ need, (deepenResumable (sys.space store) root demand).ready
        ((deepenResumable (sys.space store) root demand).step^[need] (beginIteration root 0)) =
          true →
      (portfolio sys root demand (rounds (doubling first) count) store log).spent ≤
        3 * need + first) ∧
    (∀ target, Decides (sys.space store) root demand target →
      (portfolio sys root demand (rounds (doubling first) count) store log).spent ≤
        3 * (idWork (sys.space store) root 0 target + target) + first) := by
  have same : portfolio sys root demand (rounds (doubling first) count) store log =
      race (walkResumable (sys.space store) demand) (deepenResumable (sys.space store) root demand)
        (doubling first) (⟨store, log, none⟩ : World σ E) ⟨[root], []⟩ (beginIteration root 0)
        count :=
    (portfolio_quiet sys quiet demand _ log).1
  rw [same] at published ⊢
  refine ⟨fun need outcome => race_first_cost _ _ _ _ _ _ published outcome,
    fun need outcome => (doubling_second_cost _ _ _ _ _ _ published outcome).1,
    fun target decides => ?_⟩
  obtain ⟨units, within, outcome⟩ := deepen_need (sys.space store) root demand target decides
  have cost := (doubling_second_cost _ _ _ _ _ _ published outcome).1
  omega

/-- **Under four times the faster strategy**, once its need is at least the first quantum. -/
theorem portfolio_under_four (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) (demand first count : Nat) (log : List E)
    (published :
      (portfolio sys root demand (rounds (doubling first) count) store log).published.isSome =
        true) :
    (∀ need, 0 < need → (walkResumable (sys.space store) demand).ready
        ((walkResumable (sys.space store) demand).step^[need] ⟨[root], []⟩) = true →
      (portfolio sys root demand (rounds (doubling first) count) store log).spent < 4 * need) ∧
    (∀ need, first ≤ need → 0 < need → (deepenResumable (sys.space store) root demand).ready
        ((deepenResumable (sys.space store) root demand).step^[need] (beginIteration root 0)) =
          true →
      (portfolio sys root demand (rounds (doubling first) count) store log).spent < 4 * need) := by
  have same : portfolio sys root demand (rounds (doubling first) count) store log =
      race (walkResumable (sys.space store) demand) (deepenResumable (sys.space store) root demand)
        (doubling first) (⟨store, log, none⟩ : World σ E) ⟨[root], []⟩ (beginIteration root 0)
        count :=
    (portfolio_quiet sys quiet demand _ log).1
  rw [same] at published ⊢
  refine ⟨fun need positive outcome => ?_, fun need large positive outcome =>
    doubling_under_four _ _ _ _ _ _ published outcome large positive⟩
  have cost := race_first_cost _ _ _ _ _ _ published outcome
  omega

/-- **A publication exists** under any positive first quantum, whenever some bound settles the
demand. -/
theorem portfolio_cost_publishes (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) (demand target : Nat)
    (decides : Decides (sys.space store) root demand target) {first : Nat} (positive : 0 < first)
    (log : List E) :
    ∃ count,
      (portfolio sys root demand (rounds (doubling first) count) store log).published.isSome =
        true := by
  obtain ⟨units, _, outcome⟩ := deepen_need (sys.space store) root demand target decides
  refine ⟨units + 1, ?_⟩
  rw [(portfolio_quiet sys quiet demand _ log).1]
  exact race_publishes_second _ _ _ _ _ _ (doubling_pos positive) outcome

end Cost

/-- **The cost bound for an admitted program**, arithmetic and reads counted. -/
theorem program_cost {program : Program} {rowKind : Nat → Bool} {entry : Nat}
    {arguments : List Val} {store : Store} (admitted : admits program rowKind entry arguments = true)
    (rows : RowsInt rowKind store) (demand first count target : Nat)
    (decides : Decides ((system program).space store) (root entry arguments) demand target)
    (log : List Event)
    (published : (portfolio (system program) (root entry arguments) demand
      (rounds (doubling first) count) store log).published.isSome = true) :
    (portfolio (system program) (root entry arguments) demand (rounds (doubling first) count)
        store log).spent ≤
      3 * (idWork ((system program).space store) (root entry arguments) 0 target + target) +
        first :=
  (portfolio_cost _ (admits_quiet admitted rows) demand first count log published).2.2 target
    decides

/-! ## An inline superpose and an anonymous relation -/

section Prefixed

variable {S : Type u} {A : Type v}

/-- The search with one expansion in front of the root. -/
def prefixed (space : Space S A) (root : S) : Space (Option S) A where
  expand
    | none => .branch [some root]
    | some state =>
        match space.expand state with
        | .answer value => .answer value
        | .branch states => .branch (states.map some)

theorem prefixed_none (space : Space S A) (root : S) :
    (prefixed space root).expand none = .branch [some root] := rfl

theorem prefixed_answer (space : Space S A) (root : S) {state : S} {value : A}
    (expansion : space.expand state = .answer value) :
    (prefixed space root).expand (some state) = .answer value := by
  simp [prefixed, expansion]

theorem prefixed_branch (space : Space S A) (root : S) {state : S} {states : List S}
    (expansion : space.expand state = .branch states) :
    (prefixed space root).expand (some state) = .branch (states.map some) := by
  simp [prefixed, expansion]

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (bounded_answer bounded_zero_branch
  bounded_succ_branch)

theorem prefixed_some (space : Space S A) (root : S) : ∀ (depth : Nat) (state : S),
    bounded (prefixed space root) depth (some state) = bounded space depth state
  | depth, state => by
      cases expansion : space.expand state with
      | answer value =>
          rw [bounded_answer _ (prefixed_answer space root expansion),
            bounded_answer _ expansion]
      | branch states =>
          cases depth with
          | zero =>
              rw [bounded_zero_branch _ (prefixed_branch space root expansion),
                bounded_zero_branch _ expansion]
              simp
          | succ depth =>
              rw [bounded_succ_branch _ (prefixed_branch space root expansion),
                bounded_succ_branch _ expansion]
              simp only [List.map_map, Function.comp_def, prefixed_some space root depth]

/-- One more level: the bounded run of the prefixed search at `depth + 1` is the bounded run of
the search at `depth`, answers and cut alike. -/
theorem prefixed_bounded (space : Space S A) (root : S) (depth : Nat) :
    bounded (prefixed space root) (depth + 1) none = bounded space depth root := by
  rw [bounded_succ_branch _ (prefixed_none space root)]
  simp [prefixed_some space root depth]

theorem prefixed_work_some (space : Space S A) (root : S) : ∀ (depth : Nat) (state : S),
    boundedWork (prefixed space root) depth (some state) = boundedWork space depth state
  | 0, _ => rfl
  | depth + 1, state => by
      cases expansion : space.expand state with
      | answer value =>
          simp only [boundedWork, prefixed_answer space root expansion, expansion]
      | branch states =>
          simp only [boundedWork, prefixed_branch space root expansion, expansion, List.map_map,
            Function.comp_def, prefixed_work_some space root depth]

/-- One more unit per round. -/
theorem prefixed_work (space : Space S A) (root : S) (depth : Nat) :
    boundedWork (prefixed space root) (depth + 1) none = 1 + boundedWork space depth root := by
  simp only [boundedWork, prefixed_none space root, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, prefixed_work_some space root depth, Nat.add_zero]

/-- The same batches. -/
theorem prefixed_batch (space : Space S A) (root : S) (demand : Nat) (batch : List A) :
    BatchMeaning (prefixed space root) none demand batch ↔ BatchMeaning space root demand batch := by
  constructor
  · rintro ⟨depth, suffix, joined, limited, complete⟩
    cases depth with
    | zero =>
        have empty : bounded (prefixed space root) 0 none = ([], true) := rfl
        simp only [empty] at joined complete
        have none : batch = [] := (List.append_eq_nil_iff.mp joined).1
        subst none
        rcases complete with full | ⟨_, uncut⟩
        · exact ⟨0, (bounded space 0 root).1, rfl, limited, Or.inl full⟩
        · cases uncut
    | succ depth =>
        rw [prefixed_bounded] at joined complete
        exact ⟨depth, suffix, joined, limited, complete⟩
  · rintro ⟨depth, suffix, joined, limited, complete⟩
    refine ⟨depth + 1, suffix, ?_, limited, ?_⟩
    · rw [prefixed_bounded]; exact joined
    · rw [prefixed_bounded]; exact complete

end Prefixed

namespace Controls

/-- **Cost of the measured loop.** The arithmetic loop is answered after `28` units, within the
bound `3 * (idWork + target) + first = 52` that `program_cost` gives for the settling bound `2`. -/
theorem arithmetic_loop_cost :
    (portfolio (system arithmeticLoop) (root 1 []) 1 (rounds (doubling 1) 4) emptyStore []).spent =
        28 ∧
      Decides ((system arithmeticLoop).space emptyStore) (root 1 []) 1 2 ∧
      idWork ((system arithmeticLoop).space emptyStore) (root 1 []) 0 2 = 15 := by
  unfold Decides
  decide

theorem arithmetic_loop_within_bound :
    (portfolio (system arithmeticLoop) (root 1 []) 1 (rounds (doubling 1) 4) emptyStore []).spent ≤
      3 * (idWork ((system arithmeticLoop).space emptyStore) (root 1 []) 0 2 + 2) + 1 := by
  obtain ⟨_, decides, _⟩ := arithmetic_loop_cost
  have admitted : admits arithmeticLoop noRows 1 [] = true := arithmetic_loop.1
  exact program_cost admitted (fun _ known => by cases known) 1 1 4 2 decides []
    (by decide)

end Controls

#print axioms portfolio_cost
#print axioms portfolio_under_four
#print axioms portfolio_cost_publishes
#print axioms program_cost
#print axioms prefixed_bounded
#print axioms prefixed_work
#print axioms prefixed_batch
#print axioms Controls.arithmetic_loop_cost
#print axioms Controls.arithmetic_loop_within_bound

end Mettapedia.Machines.PortfolioReach
