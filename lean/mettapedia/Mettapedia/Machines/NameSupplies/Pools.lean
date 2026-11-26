import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.Range
import Mathlib.Data.Set.Finite.Basic

/-!
# Name supplies shared out among parallel holders

A *name supply* gives names one at a time: drawing a name returns it together with the supply that
gives the next ones (Augustsson, Rittri and Synek, *On generating unique names*, 1994).  A
computation with parallel parts holds one supply per live part, and the supplies are reshaped by
three operations that consult nothing but the supplies they are given (`Discipline`):

* **fork** (`Discipline.piece`): a holder that splits into `k` parts hands part `i` the piece
  `piece s k i` of its supply `s`, and its own supply ends with it;
* **join** (`Discipline.join`): two holders that end together hand their one successor the join of
  their supplies;
* **draw** (`Discipline.draw`): a holder draws its next name.

A **pool** is the multiset of live supplies with the names drawn so far.  A pool run applies the
operations one at a time, together with the release of a supply whose holder ends (`Pool.step`,
`Pool.run`, `Pool.Valid`).  A discipline is **exact** from a pool when no valid run from it draws a
name twice (`Exact`).  For a step of the transform calculus this is the conclusion
`issuedAlong_nodup` of its issuing discipline (`NamesOnTheStep.IssuedNames`); here it is reached
without a shared ledger.

## Exactness against bounded supplies

A discipline is **local** by construction: its operations are functions of the supplies they are
given, never of other holders or of the order in which holders run.  Consider a supply that keeps
forking in two, keeping the first piece and releasing the second at once (`eagerForks`): at most two
supplies are ever live (`eager_forks_live`).  The run that keeps the released pieces instead
(`lazyForks`) holds all of them live at once, and every live supply may draw; so exactness makes
the pieces pairwise distinct (`exact_forking_injective`), and locality makes them the same pieces in
both runs.  Hence, for every measure with finitely many supplies of each size, **an exact local
discipline hands out pieces of unbounded size while never holding more than two supplies**
(`exact_forking_unbounded`).  A local discipline is therefore never both exact and bounded;
`SharedSupplies` has one that is local and exact, and one that is local and bounded.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-! ## Two elements of a multiset -/

section Pairs

variable {α : Type} [DecidableEq α]

theorem pair_le_cons {a b x : α} {rest : Multiset α} (pair : {a, b} ≤ x ::ₘ rest) :
    {a, b} ≤ rest ∨ (a = x ∧ b ∈ rest) ∨ (b = x ∧ a ∈ rest) := by
  by_cases ax : a = x
  · subst ax
    rw [Multiset.insert_eq_cons, Multiset.cons_le_cons_iff, Multiset.singleton_le] at pair
    exact Or.inr (Or.inl ⟨rfl, pair⟩)
  · by_cases bx : b = x
    · subst bx
      rw [Multiset.pair_comm, Multiset.insert_eq_cons, Multiset.cons_le_cons_iff,
        Multiset.singleton_le] at pair
      exact Or.inr (Or.inr ⟨rfl, pair⟩)
    · refine Or.inl ((Multiset.le_cons_of_notMem ?_).mp pair)
      simp [Ne.symm ax, Ne.symm bx]

theorem pair_le_add {a b : α} {first second : Multiset α} (pair : {a, b} ≤ first + second) :
    {a, b} ≤ first ∨ {a, b} ≤ second ∨ (a ∈ first ∧ b ∈ second) ∨ (b ∈ first ∧ a ∈ second) := by
  induction first using Multiset.induction_on with
  | empty => rw [zero_add] at pair; exact Or.inr (Or.inl pair)
  | cons x first ih =>
      rw [Multiset.cons_add] at pair
      rcases pair_le_cons pair with rest | ⟨rfl, inRest⟩ | ⟨rfl, inRest⟩
      · rcases ih rest with inFirst | inSecond | ⟨ha, hb⟩ | ⟨hb, ha⟩
        · exact Or.inl (inFirst.trans (Multiset.le_cons_self _ _))
        · exact Or.inr (Or.inl inSecond)
        · exact Or.inr (Or.inr (Or.inl ⟨Multiset.mem_cons_of_mem ha, hb⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨Multiset.mem_cons_of_mem hb, ha⟩))
      · rcases Multiset.mem_add.mp inRest with inFirst | inSecond
        · refine Or.inl ?_
          rw [Multiset.insert_eq_cons]
          exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr inFirst)
        · exact Or.inr (Or.inr (Or.inl ⟨Multiset.mem_cons_self _ _, inSecond⟩))
      · rcases Multiset.mem_add.mp inRest with inFirst | inSecond
        · refine Or.inl ?_
          rw [Multiset.pair_comm, Multiset.insert_eq_cons]
          exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr inFirst)
        · exact Or.inr (Or.inr (Or.inr ⟨Multiset.mem_cons_self _ _, inSecond⟩))

theorem pairs_of_mem_sub {s r b : α} {tasks : Multiset α} (pair : {s, r} ≤ tasks)
    (member : b ∈ tasks - {s, r}) : {s, b} ≤ tasks ∧ {r, b} ≤ tasks := by
  have whole : {s, r} + {b} ≤ tasks :=
    (le_tsub_iff_left pair).mp (Multiset.singleton_le.mpr member)
  have spread : ({s, r} : Multiset α) + {b} = s ::ₘ r ::ₘ {b} := by
    simp [Multiset.insert_eq_cons, Multiset.singleton_add]
  rw [spread] at whole
  refine ⟨le_trans ?_ whole, le_trans ?_ whole⟩
  · rw [Multiset.insert_eq_cons]
    exact Multiset.cons_le_cons _ (Multiset.le_cons_self _ _)
  · rw [Multiset.insert_eq_cons, Multiset.cons_swap]
    exact Multiset.cons_le_cons _ (Multiset.le_cons_self _ _)

theorem pair_of_mem_erase {t b : α} {tasks : Multiset α} (present : t ∈ tasks)
    (member : b ∈ tasks.erase t) : {t, b} ≤ tasks := by
  rw [Multiset.insert_eq_cons, ← Multiset.cons_erase present]
  exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr member)

theorem pair_of_pairwise {R : α → α → Prop} (symmetric : ∀ {a b}, R a b → R b a) :
    ∀ {list : List α}, list.Pairwise R → ∀ {a b : α}, {a, b} ≤ (list : Multiset α) → R a b
  | [], _, a, b, pair => by
      have := Multiset.card_le_card pair
      simp at this
  | x :: rest, pairwise, a, b, pair => by
      rw [← Multiset.cons_coe] at pair
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp pairwise
      rcases pair_le_cons pair with inRest | ⟨rfl, inRest⟩ | ⟨rfl, inRest⟩
      · exact pair_of_pairwise symmetric tail inRest
      · exact head b (Multiset.mem_coe.mp inRest)
      · exact symmetric (head a (Multiset.mem_coe.mp inRest))

/-- Two copies of one element in a multiset leave one copy after erasing it. -/
theorem mem_erase_of_twice {t : α} {tasks : Multiset α} (twice : {t, t} ≤ tasks) :
    t ∈ tasks.erase t := by
  have := Multiset.erase_le_erase t twice
  rw [Multiset.insert_eq_cons, Multiset.erase_cons_head] at this
  exact Multiset.singleton_le.mp this

end Pairs

/-! ## Disciplines, pools and runs -/

/-- **A local discipline of name supplies**: what a supply draws, the pieces of a fork, and the
join of two supplies. -/
structure Discipline (S N : Type) where
  /-- The next name of a supply, and the supply after giving it. -/
  draw : S → N × S
  /-- `piece s k i`: the piece of `s` handed to part `i` of a fork into `k` parts. -/
  piece : S → ℕ → ℕ → S
  /-- The supply handed to the one successor of two holders that end together. -/
  join : S → S → S

variable {S N : Type}

/-- The pieces of a fork of `supply` into `parts` parts. -/
def Discipline.pieces (D : Discipline S N) (supply : S) (parts : ℕ) : List S :=
  (List.range parts).map (D.piece supply parts)

/-- The live supplies of a computation and the names drawn so far, oldest first. -/
structure Pool (S N : Type) where
  live : Multiset S
  drawn : List N

/-- An operation on the live supplies. -/
inductive Operation (S : Type) where
  /-- The holder of `supply` splits into `parts` parts. -/
  | fork (supply : S) (parts : ℕ)
  /-- The holders of two supplies end together, leaving one successor. -/
  | join (first second : S)
  /-- The holder of `supply` ends, leaving no successor. -/
  | release (supply : S)
  /-- The holder of `supply` draws a name. -/
  | draw (supply : S)

/-- The supplies an operation consumes. -/
def Operation.consumed : Operation S → Multiset S
  | .fork supply _ => {supply}
  | .join first second => {first, second}
  | .release supply => {supply}
  | .draw supply => {supply}

/-- An operation can happen when the supplies it consumes are live. -/
def Operation.Enabled (live : Multiset S) (operation : Operation S) : Prop :=
  operation.consumed ≤ live

/-- The supplies an operation produces. -/
def Operation.produced (D : Discipline S N) : Operation S → Multiset S
  | .fork supply parts => D.pieces supply parts
  | .join first second => {D.join first second}
  | .release _ => 0
  | .draw supply => {(D.draw supply).2}

/-- The names an operation draws. -/
def Operation.names (D : Discipline S N) : Operation S → List N
  | .draw supply => [(D.draw supply).1]
  | _ => []

variable [DecidableEq S]

/-- One operation on a pool. -/
def Pool.step (D : Discipline S N) (pool : Pool S N) (operation : Operation S) : Pool S N :=
  ⟨operation.produced D + (pool.live - operation.consumed), pool.drawn ++ operation.names D⟩

/-- A run of operations. -/
def Pool.run (D : Discipline S N) (pool : Pool S N) (operations : List (Operation S)) : Pool S N :=
  operations.foldl (Pool.step D) pool

/-- A run is valid when every operation can happen when it comes. -/
def Pool.Valid (D : Discipline S N) : Pool S N → List (Operation S) → Prop
  | _, [] => True
  | pool, operation :: rest =>
      operation.Enabled pool.live ∧ Pool.Valid D (pool.step D operation) rest

@[simp] theorem Pool.run_nil (D : Discipline S N) (pool : Pool S N) : pool.run D [] = pool := rfl

@[simp] theorem Pool.run_cons (D : Discipline S N) (pool : Pool S N) (operation : Operation S)
    (rest : List (Operation S)) :
    pool.run D (operation :: rest) = (pool.step D operation).run D rest := rfl

theorem Pool.run_append (D : Discipline S N) (pool : Pool S N) (first second : List (Operation S)) :
    pool.run D (first ++ second) = (pool.run D first).run D second := by
  simp [Pool.run, List.foldl_append]

theorem Pool.valid_append (D : Discipline S N) (pool : Pool S N)
    (first second : List (Operation S)) :
    Pool.Valid D pool (first ++ second) ↔
      Pool.Valid D pool first ∧ Pool.Valid D (pool.run D first) second := by
  induction first generalizing pool with
  | nil => simp [Pool.Valid]
  | cons operation rest ih => simp [Pool.Valid, ih, and_assoc]

/-- **Exactness**: no valid run from the pool draws a name twice. -/
def Exact (D : Discipline S N) (pool : Pool S N) : Prop :=
  ∀ operations, Pool.Valid D pool operations → (pool.run D operations).drawn.Nodup

/-! ## A supply that keeps forking -/

/-- The supply kept after `k` forks of `root`: the first piece each time. -/
def kept (D : Discipline S N) (root : S) : ℕ → S
  | 0 => root
  | k + 1 => D.piece (kept D root k) 2 0

/-- The piece forked off by fork number `k`: the second piece. -/
def forkedOff (D : Discipline S N) (root : S) (k : ℕ) : S := D.piece (kept D root k) 2 1

/-- The forks that keep every forked-off piece. -/
def lazyForks (D : Discipline S N) (root : S) : ℕ → List (Operation S)
  | 0 => []
  | k + 1 => lazyForks D root k ++ [.fork (kept D root k) 2]

/-- The forks that release every forked-off piece at once. -/
def eagerForks (D : Discipline S N) (root : S) : ℕ → List (Operation S)
  | 0 => []
  | k + 1 => eagerForks D root k ++ [.fork (kept D root k) 2] ++ [.release (forkedOff D root k)]

omit [DecidableEq S] in
theorem pieces_two (D : Discipline S N) (supply : S) :
    (D.pieces supply 2 : Multiset S) = {D.piece supply 2 0, D.piece supply 2 1} := rfl

/-- The lazy run: the kept supply beside every piece forked off. -/
theorem lazy_forks_run (D : Discipline S N) (root : S) (k : ℕ) :
    (Pool.mk {root} [] : Pool S N).run D (lazyForks D root k) =
      ⟨kept D root k ::ₘ (Multiset.range k).map (forkedOff D root), []⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [lazyForks, Pool.run_append, ih, Pool.run_cons, Pool.run_nil]
      simp only [Pool.step, Operation.produced, Operation.consumed, Operation.names, pieces_two,
        List.append_nil, Multiset.range_succ, Multiset.map_cons, Multiset.sub_singleton,
        Multiset.erase_cons_head, Multiset.insert_eq_cons, Multiset.cons_add,
        Multiset.singleton_add]
      rfl

theorem lazy_forks_valid (D : Discipline S N) (root : S) (k : ℕ) :
    Pool.Valid D (Pool.mk {root} [] : Pool S N) (lazyForks D root k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      rw [lazyForks, Pool.valid_append, lazy_forks_run]
      exact ⟨ih, by simp [Operation.Enabled, Operation.consumed], trivial⟩

/-- The eager run: only the kept supply. -/
theorem eager_forks_run (D : Discipline S N) (root : S) (k : ℕ) :
    (Pool.mk {root} [] : Pool S N).run D (eagerForks D root k) = ⟨{kept D root k}, []⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [eagerForks, Pool.run_append, Pool.run_append, ih]
      simp only [Pool.run_cons, Pool.run_nil, Pool.step, Operation.produced, Operation.consumed,
        Operation.names, pieces_two, List.append_nil, Multiset.sub_singleton,
        Multiset.erase_singleton, add_zero, forkedOff]
      rw [Multiset.pair_comm, Multiset.insert_eq_cons, Multiset.erase_cons_head]
      rfl

theorem eager_forks_valid (D : Discipline S N) (root : S) (k : ℕ) :
    Pool.Valid D (Pool.mk {root} [] : Pool S N) (eagerForks D root k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      rw [eagerForks, List.append_assoc, Pool.valid_append, eager_forks_run]
      refine ⟨ih, by simp [Operation.Enabled, Operation.consumed], ?_, trivial⟩
      simp [Pool.step, Operation.Enabled, Operation.consumed, Operation.produced, pieces_two,
        Multiset.insert_eq_cons, forkedOff]

/-- **The eager run never holds more than two live supplies.** -/
theorem eager_forks_live (D : Discipline S N) (root : S) (k : ℕ) (operations : List (Operation S))
    (isPrefix : operations <+: eagerForks D root k) :
    ((Pool.mk {root} [] : Pool S N).run D operations).live.card ≤ 2 := by
  induction k generalizing operations with
  | zero =>
      rw [List.prefix_nil.mp isPrefix]
      simp
  | succ k ih =>
      rw [eagerForks] at isPrefix
      rcases List.prefix_concat_iff.mp isPrefix with whole | earlier
      · have whole' := eager_forks_run D root (k + 1)
        rw [eagerForks] at whole'
        rw [whole, whole']; simp
      rcases List.prefix_concat_iff.mp earlier with whole | earlier
      · rw [whole, Pool.run_append, eager_forks_run]
        simp [Pool.step, Operation.produced, Operation.consumed, pieces_two]
      · exact ih operations earlier

/-- The piece forked off by fork number `k` is live right after that fork in the eager run. -/
theorem eager_forkedOff_live (D : Discipline S N) (root : S) (k : ℕ) :
    forkedOff D root k ∈
      ((Pool.mk {root} [] : Pool S N).run D (eagerForks D root k ++ [.fork (kept D root k) 2])).live := by
  rw [Pool.run_append, eager_forks_run]
  simp [Pool.step, Operation.produced, Operation.consumed, pieces_two, forkedOff]

/-- **Exactness separates the forked-off pieces**: an exact local discipline forks off pairwise
distinct pieces. -/
theorem exact_forking_injective (D : Discipline S N) (root : S)
    (exact : Exact D (Pool.mk {root} [] : Pool S N)) : Function.Injective (forkedOff D root) := by
  intro i j same
  by_contra distinct
  let k := max i j + 1
  let lazy := (Pool.mk {root} [] : Pool S N).run D (lazyForks D root k)
  have twice : {forkedOff D root i, forkedOff D root i} ≤ lazy.live := by
    have indices : ({i, j} : Multiset ℕ) ≤ Multiset.range k := by
      rw [Multiset.le_iff_subset (by simp [distinct])]
      intro index member
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
      simp only [Multiset.mem_range, k]
      omega
    have mapped := Multiset.map_le_map (f := forkedOff D root) indices
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, ← same] at mapped
    simp only [lazy, lazy_forks_run]
    exact mapped.trans (Multiset.le_cons_self _ _)
  have valid : Pool.Valid D (Pool.mk {root} [] : Pool S N)
      (lazyForks D root k ++ [.draw (forkedOff D root i), .draw (forkedOff D root i)]) := by
    rw [Pool.valid_append]
    refine ⟨lazy_forks_valid D root k, ?_, ?_, trivial⟩
    · exact Multiset.singleton_le.mpr (Multiset.mem_of_le twice (by simp))
    · simp only [Pool.step, Operation.Enabled, Operation.consumed, Operation.produced]
      exact Multiset.singleton_le.mpr (Multiset.mem_add.mpr (Or.inr (by
        rw [Multiset.sub_singleton]; exact mem_erase_of_twice twice)))
  have nodup := exact _ valid
  rw [Pool.run_append, lazy_forks_run] at nodup
  simp [Pool.step, Operation.names] at nodup

omit [DecidableEq S] in
/-- An injective sequence in a type with finitely many elements of each size exceeds every size. -/
theorem unbounded_of_injective {T : Type} (size : T → ℕ)
    (finite : ∀ bound, {x | size x ≤ bound}.Finite) {sequence : ℕ → T}
    (injective : Function.Injective sequence) (bound : ℕ) : ∃ k, bound < size (sequence k) := by
  by_contra small
  simp only [not_exists, not_lt] at small
  exact Set.infinite_range_of_injective injective
    ((finite bound).subset (by rintro _ ⟨k, rfl⟩; exact small k))

/-- **An exact local discipline is not bounded.**  If no valid run from a single supply draws a
name twice, then the supply that keeps forking in two and releasing the second piece — never more
than two live supplies — hands out pieces of unbounded size, for every measure with finitely many
supplies of each size. -/
theorem exact_forking_unbounded (D : Discipline S N) (root : S)
    (exact : Exact D (Pool.mk {root} [] : Pool S N))
    (size : S → ℕ) (finite : ∀ bound, {s | size s ≤ bound}.Finite) :
    (∀ k (operations : List (Operation S)), operations <+: eagerForks D root k →
      ((Pool.mk {root} [] : Pool S N).run D operations).live.card ≤ 2) ∧
    ∀ bound, ∃ k, ∃ operations : List (Operation S), operations <+: eagerForks D root k ∧
      ∃ s ∈ ((Pool.mk {root} [] : Pool S N).run D operations).live, bound < size s := by
  refine ⟨eager_forks_live D root, fun bound => ?_⟩
  obtain ⟨k, large⟩ := unbounded_of_injective size finite (exact_forking_injective D root exact) bound
  refine ⟨k + 1, _, ?_, _, eager_forkedOff_live D root k, large⟩
  rw [eagerForks]
  exact List.prefix_append _ _

end Mettapedia.Machines.NameSupplies
