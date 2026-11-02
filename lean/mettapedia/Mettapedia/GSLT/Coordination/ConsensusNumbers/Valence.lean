import Mettapedia.GSLT.Coordination.ConsensusNumbers.Framework

/-!
# The valence argument: which objects cannot reach consensus

Herlihy's impossibility proofs, once, for every deterministic object.

## Hiding the order of two operations

Let processes `p` and `q` be about to apply operations `a` and `b` at the object's state `s`.
`OrderHidden T s a b` says that one of the two cannot tell whether `a` went first:

* `noChange`: `a` leaves `s` as it was (a read, or a failed removal). Then `q` sees the same state
  whether or not `p` moved first.
  Example: `a` reads a register, `b` writes it.
* `overwritten`: applying `b` after `a` gives what `b` alone gives, state and answer.
  Then `q`'s view after `a, b` equals its view after `b`.
  Example: `a` and `b` write the same register.
* `commutes`: the two orders end in the same state and `a` gets the same answer in both. Then `p`
  cannot tell the orders apart.
  Example: `a` and `b` write different registers.

`PairCannotOrder` is `OrderHidden` in one direction or the other. `BystanderCannotOrder` adds the
case in which only the state is the same in both orders: then a third process, which sees only the
state, cannot tell the orders apart.
Example: two test-and-set operations on a fresh flag (`Controls.testAndSet_bystander`): both orders
end with the flag set, and the two answers are swapped, so only a third process is blind
(`Controls.testAndSet_pair_sees`).

## The theorems

* **No two-process consensus** (`not_solvable_of_pairCannotOrder`): over an object in which every
  pair of operations at every state is `PairCannotOrder`, no wait-free protocol solves binary
  consensus for two or more processes.
* **No three-process consensus** (`not_solvable_of_bystanderCannotOrder`): the same for
  `BystanderCannotOrder` and three or more processes.
* Both hold for consensus over any type with two distinct values
  (`not_solvable_of_pairCannotOrder'`, `not_solvable_of_bystanderCannotOrder'`).
* Both conditions survive taking any family of objects as one (`pi_pairCannotOrder`,
  `pi_bystanderCannotOrder`), so they bound protocols using any number of such objects.

## The proof

* Some initial configuration is **bivalent**: both decisions are reachable
  (`Solves.initial_bivalent`). A process running alone from the start decides its own input,
  since the run is the same as in the configuration where every input equals its own.
* Some reachable configuration is **critical**: bivalent, and every single step leads to a
  configuration that is not (`Solves.exists_critical`). Otherwise an execution staying bivalent
  forever would exist; some process is scheduled infinitely often in it and never decides.
* At a critical configuration two processes `p` and `q` have steps leading to opposite decisions
  (`Solves.critical_pair`). If some process cannot tell the two orders apart, its solo run from
  the two configurations is the same and decides the same value, which is impossible
  (`Solves.no_split`, `Solves.no_hidden_order`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-! ## Order hiding -/

/-- The process of `a` or of `b` cannot tell whether `a` went first. -/
inductive OrderHidden (T : DetObject) (s : T.State) (a b : T.Op) : Prop
  | noChange : (T.apply s a).1 = s → OrderHidden T s a b
  | overwritten : T.apply (T.apply s a).1 b = T.apply s b → OrderHidden T s a b
  | commutes : (T.apply (T.apply s a).1 b).1 = (T.apply (T.apply s b).1 a).1 →
      (T.apply (T.apply s b).1 a).2 = (T.apply s a).2 → OrderHidden T s a b

/-- One of the two processes cannot tell which of `a` and `b` went first. -/
def PairCannotOrder (T : DetObject) (s : T.State) (a b : T.Op) : Prop :=
  OrderHidden T s a b ∨ OrderHidden T s b a

/-- A third process, seeing only the state, cannot tell which of `a` and `b` went first; or one of
the pair cannot. -/
def BystanderCannotOrder (T : DetObject) (s : T.State) (a b : T.Op) : Prop :=
  PairCannotOrder T s a b ∨ (T.apply (T.apply s a).1 b).1 = (T.apply (T.apply s b).1 a).1

theorem PairCannotOrder.symm {T : DetObject} {s : T.State} {a b : T.Op}
    (h : PairCannotOrder T s a b) : PairCannotOrder T s b a := Or.symm h

theorem BystanderCannotOrder.symm {T : DetObject} {s : T.State} {a b : T.Op}
    (h : BystanderCannotOrder T s a b) : BystanderCannotOrder T s b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem PairCannotOrder.bystander {T : DetObject} {s : T.State} {a b : T.Op}
    (h : PairCannotOrder T s a b) : BystanderCannotOrder T s a b := Or.inl h

/-! ## Deterministic steps -/

namespace Protocol

variable {T : DetObject} {n : ℕ} {V : Type} {P : Protocol T.toObject n V}

variable (P) in
/-- The step of process `i`, as a function: an object that always fires gives one step. -/
def go (C : P.Config) (i : Fin n) : P.Config :=
  match P.action i (C.loc i) with
  | .decide _ => C
  | .invoke op =>
      ⟨(T.apply C.obj op).1, Function.update C.loc i (P.next i (C.loc i) (T.apply C.obj op).2)⟩

theorem go_of_decide {C : P.Config} {i : Fin n} {v : V} (h : P.action i (C.loc i) = .decide v) :
    P.go C i = C := by
  simp [go, h]

theorem go_of_invoke {C : P.Config} {i : Fin n} {op : T.Op} (h : P.action i (C.loc i) = .invoke op) :
    P.go C i =
      ⟨(T.apply C.obj op).1, Function.update C.loc i (P.next i (C.loc i) (T.apply C.obj op).2)⟩ := by
  simp [go, h]

theorem step_iff_go {C D : P.Config} {i : Fin n} : P.Step C i D ↔ D = P.go C i := by
  constructor
  · intro step
    cases step with
    | decided h => exact (go_of_decide h).symm
    | fires h fires =>
        rw [go_of_invoke h]
        have fires' : T.apply _ _ = _ := fires
        rw [fires']
    | waits h never =>
        exact absurd rfl (never (T.apply _ _).1 (T.apply _ _).2)
  · rintro rfl
    cases h : P.action i (C.loc i) with
    | decide v => rw [go_of_decide h]; exact Step.decided h
    | invoke op => rw [go_of_invoke h]; exact Step.fires h rfl

theorem go_loc_of_ne {C : P.Config} {i j : Fin n} (ne : j ≠ i) : (P.go C i).loc j = C.loc j :=
  (step_iff_go.mpr rfl : P.Step C i (P.go C i)).loc_of_ne ne

variable (P) in
/-- A run, as a function. -/
def run : P.Config → List (Fin n) → P.Config
  | C, [] => C
  | C, i :: σ => run (P.go C i) σ

theorem run_iff {C D : P.Config} {σ : List (Fin n)} : P.Run C σ D ↔ D = P.run C σ := by
  induction σ generalizing C with
  | nil => rfl
  | cons i σ ih =>
      simp only [Run, run]
      constructor
      · rintro ⟨E, step, rest⟩
        rw [step_iff_go.mp step] at rest
        exact ih.mp rest
      · intro h
        exact ⟨_, step_iff_go.mpr rfl, ih.mpr h⟩

theorem run_append' (C : P.Config) (σ τ : List (Fin n)) :
    P.run C (σ ++ τ) = P.run (P.run C σ) τ := by
  induction σ generalizing C with
  | nil => rfl
  | cons i σ ih => exact ih _

theorem reach_iff {x : Fin n → V} {C : P.Config} : P.Reach x C ↔ ∃ σ, C = P.run (P.initial x) σ :=
  ⟨fun ⟨σ, h⟩ => ⟨σ, run_iff.mp h⟩, fun ⟨σ, h⟩ => ⟨σ, run_iff.mpr h⟩⟩

theorem Reach.run {x : Fin n → V} {C : P.Config} (reach : P.Reach x C) (σ : List (Fin n)) :
    P.Reach x (P.run C σ) := by
  obtain ⟨τ, h⟩ := reach_iff.mp reach
  exact reach_iff.mpr ⟨τ ++ σ, by rw [h, run_append']⟩

theorem Reach.go {x : Fin n → V} {C : P.Config} (reach : P.Reach x C) (i : Fin n) :
    P.Reach x (P.go C i) :=
  reach.step (step_iff_go.mpr rfl)

variable (P) in
/-- The execution of an infinite schedule from `C`. -/
def runFrom (C : P.Config) (σ : ℕ → Fin n) : ℕ → P.Config
  | 0 => C
  | m + 1 => P.go (runFrom C σ m) (σ m)

theorem execution_runFrom (C : P.Config) (σ : ℕ → Fin n) : P.Execution σ (P.runFrom C σ) :=
  fun _ => step_iff_go.mpr rfl

theorem decision_run_of_decided {C : P.Config} {i : Fin n} {v : V} (decided : P.decision C i = some v)
    (σ : List (Fin n)) : P.decision (P.run C σ) i = some v := by
  induction σ generalizing C with
  | nil => exact decided
  | cons j σ ih => exact ih ((step_iff_go.mpr rfl : P.Step C j _).decision_of_decided decided)

/-! ## Valence -/

variable (P) in
/-- Some run from `C` has some process decide `v`. -/
def Decides (C : P.Config) (v : V) : Prop := ∃ σ i, P.decision (P.run C σ) i = some v

theorem decides_of_run {C : P.Config} {σ : List (Fin n)} {v : V} (h : P.Decides (P.run C σ) v) :
    P.Decides C v := by
  obtain ⟨τ, i, h⟩ := h
  exact ⟨σ ++ τ, i, by rw [run_append']; exact h⟩

theorem not_decides_go {C : P.Config} {i : Fin n} {v : V} (h : ¬ P.Decides C v) :
    ¬ P.Decides (P.go C i) v :=
  fun d => h (decides_of_run (σ := [i]) d)

/-- Agreement, read forward: once a process has decided `v`, every decision reachable is `v`. -/
theorem Solves.decides_eq (S : P.Solves) {x : Fin n → V} {C : P.Config} (reach : P.Reach x C)
    {i : Fin n} {v w : V} (decided : P.decision C i = some v) (later : P.Decides C w) : w = v := by
  obtain ⟨σ, j, h⟩ := later
  exact (S.agreement x _ (reach.run σ) i j v w (decision_run_of_decided decided σ) h).symm

theorem runFrom_take {C : P.Config} {τ : List (Fin n)} {r : Fin n} {σ : ℕ → Fin n}
    (hσ : ∀ m, σ m = if h : m < τ.length then τ[m] else r) :
    ∀ m ≤ τ.length, P.runFrom C σ m = P.run C (τ.take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro le
      have lt : m < τ.length := le
      rw [runFrom, ih (le_of_lt lt), hσ, dif_pos lt, List.take_add_one, List.getElem?_eq_getElem lt,
        Option.toList_some, run_append']
      rfl

theorem runFrom_solo {C : P.Config} {τ : List (Fin n)} {r : Fin n} {σ : ℕ → Fin n}
    (hσ : ∀ m, σ m = if h : m < τ.length then τ[m] else r) (k : ℕ) :
    P.runFrom C σ (τ.length + k) = P.run (P.run C τ) (List.replicate k r) := by
  induction k with
  | zero => simpa [run] using runFrom_take hσ τ.length le_rfl
  | succ k ih =>
      rw [← add_assoc, runFrom, ih, hσ, dif_neg (by omega), List.replicate_succ', run_append']
      rfl

/-- **A process running alone decides**, from any reachable configuration. -/
theorem Solves.solo (S : P.Solves) {x : Fin n → V} {C : P.Config} (reach : P.Reach x C)
    (r : Fin n) : ∃ k v, P.decision (P.run C (List.replicate k r)) r = some v := by
  obtain ⟨τ, rfl⟩ := reach_iff.mp reach
  let σ : ℕ → Fin n := fun m => if h : m < τ.length then τ[m] else r
  have hσ : ∀ m, σ m = if h : m < τ.length then τ[m] else r := fun _ => rfl
  have often : InfinitelyOften σ r := fun N =>
    ⟨N + τ.length, by omega, by rw [hσ, dif_neg (by omega)]⟩
  obtain ⟨m, hm⟩ := S.waitFree x σ (P.runFrom (P.initial x) σ) rfl
    (execution_runFrom _ σ) r often
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  have stays : ∀ d, P.decision (P.runFrom (P.initial x) σ (m + d)) r = some v := by
    intro d
    induction d with
    | zero => exact hv
    | succ d ih => exact (execution_runFrom _ σ (m + d)).decision_of_decided ih
  refine ⟨m, v, ?_⟩
  rw [← runFrom_solo hσ, show τ.length + m = m + τ.length by omega]
  exact stays _

/-- Two configurations that agree on the object and on `r`'s local state stay so while `r` runs
alone. -/
theorem run_solo_agree {C D : P.Config} {r : Fin n} (obj : C.obj = D.obj) (loc : C.loc r = D.loc r)
    (k : ℕ) : (P.run C (List.replicate k r)).obj = (P.run D (List.replicate k r)).obj ∧
      (P.run C (List.replicate k r)).loc r = (P.run D (List.replicate k r)).loc r := by
  induction k generalizing C D with
  | zero => exact ⟨obj, loc⟩
  | succ k ih =>
      apply ih
      · cases h : P.action r (C.loc r) with
        | decide v =>
            rw [go_of_decide h, go_of_decide (loc ▸ h)]; exact obj
        | invoke op =>
            rw [go_of_invoke h, go_of_invoke (loc ▸ h)]; simp [obj]
      · cases h : P.action r (C.loc r) with
        | decide v =>
            rw [go_of_decide h, go_of_decide (loc ▸ h)]; exact loc
        | invoke op =>
            rw [go_of_invoke h, go_of_invoke (loc ▸ h)]; simp [obj, loc]

section Binary

variable {P : Protocol T.toObject n Bool}

/-- **No split.** Two reachable configurations that agree on the object and on one process's local
state cannot be bound to opposite decisions: that process, running alone, decides the same
value from both. -/
theorem Solves.no_split (S : P.Solves) {x : Fin n → Bool} {D E : P.Config} {r : Fin n}
    (hD : P.Reach x D) (obj : D.obj = E.obj) (loc : D.loc r = E.loc r)
    {v w : Bool} (hvw : v ≠ w) (avoidD : ¬ P.Decides D w) (avoidE : ¬ P.Decides E v) : False := by
  obtain ⟨k, u, hu⟩ := S.solo hD r
  obtain ⟨-, sameLoc⟩ := run_solo_agree obj loc k
  have hu' : P.decision (P.run E (List.replicate k r)) r = some u := by
    rw [decision_eq_of_loc sameLoc.symm]; exact hu
  have notW : u ≠ w := fun h => avoidD ⟨_, r, h ▸ hu⟩
  have notV : u ≠ v := fun h => avoidE ⟨_, r, h ▸ hu'⟩
  cases u <;> cases v <;> cases w <;> simp_all

variable (P) in
/-- Both decisions are still reachable. -/
def Bivalent (C : P.Config) : Prop := P.Decides C false ∧ P.Decides C true

/-- **Some initial configuration is bivalent.** -/
theorem Solves.initial_bivalent (S : P.Solves) (two : 2 ≤ n) : ∃ x, P.Bivalent (P.initial x) := by
  let p1 : Fin n := ⟨1, by omega⟩
  let x : Fin n → Bool := fun i => decide (i = p1)
  have alone : ∀ (p : Fin n) (b : Bool), x p = b → P.Decides (P.initial x) b := by
    intro p b hp
    obtain ⟨k, u, hu⟩ := S.solo (Reach.initial (fun _ => b)) p
    obtain ⟨j, hj⟩ := S.validity (fun _ => b) _ ((Reach.initial _).run _) p u hu
    obtain ⟨-, sameLoc⟩ := run_solo_agree (C := P.initial x) (D := P.initial fun _ => b) (r := p)
      rfl (by simp [initial, hp]) k
    refine ⟨List.replicate k p, p, ?_⟩
    rw [decision_eq_of_loc sameLoc, hu, ← hj]
  exact ⟨x, alone ⟨0, by omega⟩ false (by simp [x, p1]), alone p1 true (by simp [x])⟩

/-- **A critical configuration is reachable**: bivalent, with no step to a bivalent configuration. -/
theorem Solves.exists_critical (S : P.Solves) {x : Fin n → Bool} (biv : P.Bivalent (P.initial x)) :
    ∃ C, P.Reach x C ∧ P.Bivalent C ∧ ∀ i, ¬ P.Bivalent (P.go C i) := by
  by_contra none
  have more : ∀ C, P.Reach x C → P.Bivalent C → ∃ i, P.Bivalent (P.go C i) := by
    intro C reach b
    by_contra h
    exact none ⟨C, reach, b, fun i hi => h ⟨i, hi⟩⟩
  let Good := {C : P.Config // P.Reach x C ∧ P.Bivalent C}
  let pick : Good → Fin n := fun C => Classical.choose (more C.1 C.2.1 C.2.2)
  let advance : Good → Good := fun C =>
    ⟨P.go C.1 (pick C), C.2.1.go _, Classical.choose_spec (more C.1 C.2.1 C.2.2)⟩
  let seq : ℕ → Good := fun m => advance^[m] ⟨P.initial x, Reach.initial x, biv⟩
  let σ : ℕ → Fin n := fun m => pick (seq m)
  let c : ℕ → P.Config := fun m => (seq m).1
  have exec : P.Execution σ c := by
    intro m
    apply step_iff_go.mpr
    show (advance^[m + 1] _).1 = _
    rw [Function.iterate_succ_apply']
  obtain ⟨i, infinite⟩ := Finite.exists_infinite_fiber σ
  have often : InfinitelyOften σ i := by
    intro N
    obtain ⟨m, mem, lt⟩ := (Set.infinite_coe_iff.mp infinite).exists_gt N
    exact ⟨m, le_of_lt lt, mem⟩
  obtain ⟨m, hm⟩ := S.waitFree x σ c rfl exec i often
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  have bm := (seq m).2
  have f := S.decides_eq bm.1 hv bm.2.1
  have t := S.decides_eq bm.1 hv bm.2.2
  exact absurd (f.trans t.symm) (by decide)

/-- At a bivalent configuration some process has a step after which `v` is reachable. -/
theorem Solves.first_mover (S : P.Solves) {x : Fin n → Bool} {C : P.Config} (reach : P.Reach x C)
    (biv : P.Bivalent C) (v : Bool) : ∃ p, P.Decides (P.go C p) v := by
  have dv : P.Decides C v := by cases v; exact biv.1; exact biv.2
  have dw : P.Decides C (!v) := by cases v; exact biv.2; exact biv.1
  obtain ⟨σ, j, h⟩ := dv
  cases σ with
  | nil =>
      have := S.decides_eq reach h dw
      cases v <;> simp at this
  | cons p σ => exact ⟨p, σ, j, h⟩

/-- **At a critical configuration two processes are about to move it to opposite decisions.** -/
theorem Solves.critical_pair (S : P.Solves) {x : Fin n → Bool} {C : P.Config} (reach : P.Reach x C)
    (biv : P.Bivalent C) (crit : ∀ i, ¬ P.Bivalent (P.go C i)) :
    ∃ p q a b, p ≠ q ∧ P.action p (C.loc p) = .invoke a ∧ P.action q (C.loc q) = .invoke b ∧
      ¬ P.Decides (P.go C p) true ∧ ¬ P.Decides (P.go C q) false := by
  obtain ⟨p, hp⟩ := S.first_mover reach biv false
  obtain ⟨q, hq⟩ := S.first_mover reach biv true
  have np : ¬ P.Decides (P.go C p) true := fun h => crit p ⟨hp, h⟩
  have nq : ¬ P.Decides (P.go C q) false := fun h => crit q ⟨h, hq⟩
  have invokes : ∀ i, ∃ a, P.action i (C.loc i) = .invoke a := by
    intro i
    cases h : P.action i (C.loc i) with
    | decide v => exact absurd (by rw [go_of_decide h]; exact biv) (crit i)
    | invoke a => exact ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := invokes p
  obtain ⟨b, hb⟩ := invokes q
  refine ⟨p, q, a, b, ?_, ha, hb, np, nq⟩
  rintro rfl
  exact np hq

/-- The two configurations after `p` then `q`, and after `q` alone or `q` then `p`. -/
theorem go_go_of_invoke {C : P.Config} {p q : Fin n} {a b : T.Op} (ne : p ≠ q)
    (ha : P.action p (C.loc p) = .invoke a) (hb : P.action q (C.loc q) = .invoke b) :
    (P.go (P.go C p) q).obj = (T.apply (T.apply C.obj a).1 b).1 ∧
      (P.go (P.go C p) q).loc q = P.next q (C.loc q) (T.apply (T.apply C.obj a).1 b).2 ∧
      (P.go (P.go C p) q).loc p = P.next p (C.loc p) (T.apply C.obj a).2 ∧
      ∀ r, r ≠ p → r ≠ q → (P.go (P.go C p) q).loc r = C.loc r := by
  have locq : (P.go C p).loc q = C.loc q := go_loc_of_ne (Ne.symm ne)
  have hb' : P.action q ((P.go C p).loc q) = .invoke b := by rw [locq]; exact hb
  rw [go_of_invoke hb', go_of_invoke ha]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (Ne.symm ne)]
  · simp [Function.update_of_ne ne]
  · intro r rp rq
    simp [Function.update_of_ne rp, Function.update_of_ne rq]

/-- **No hidden order at a critical pair.** -/
theorem Solves.no_hidden_order (S : P.Solves) {x : Fin n → Bool} {C : P.Config}
    (reach : P.Reach x C) {p q : Fin n} {a b : T.Op} (ne : p ≠ q)
    (ha : P.action p (C.loc p) = .invoke a) (hb : P.action q (C.loc q) = .invoke b)
    {v w : Bool} (hvw : v ≠ w) (hp : ¬ P.Decides (P.go C p) w) (hq : ¬ P.Decides (P.go C q) v)
    (hidden : OrderHidden T C.obj a b) : False := by
  obtain ⟨pqObj, pqLoc, pqLocP, -⟩ := go_go_of_invoke ne ha hb
  obtain ⟨qpObj, qpLocP, -, -⟩ := go_go_of_invoke (Ne.symm ne) hb ha
  have qObj : (P.go C q).obj = (T.apply C.obj b).1 := by rw [go_of_invoke hb]
  have qLoc : (P.go C q).loc q = P.next q (C.loc q) (T.apply C.obj b).2 := by
    rw [go_of_invoke hb]; simp
  have avoidPQ : ¬ P.Decides (P.go (P.go C p) q) w := not_decides_go hp
  have avoidQP : ¬ P.Decides (P.go (P.go C q) p) v := not_decides_go hq
  cases hidden with
  | noChange h =>
      refine S.no_split ((reach.go p).go q) ?_ ?_ hvw avoidPQ hq (r := q)
      · rw [pqObj, qObj, h]
      · rw [pqLoc, qLoc, h]
  | overwritten h =>
      refine S.no_split ((reach.go p).go q) ?_ ?_ hvw avoidPQ hq (r := q)
      · rw [pqObj, qObj, h]
      · rw [pqLoc, qLoc, h]
  | commutes h1 h2 =>
      refine S.no_split ((reach.go p).go q) ?_ ?_ hvw avoidPQ avoidQP (r := p)
      · rw [pqObj, qpObj, h1]
      · rw [pqLocP, qpLocP, h2]

/-- A bystander cannot tell the orders apart either. -/
theorem Solves.no_bystander_order (S : P.Solves) {x : Fin n → Bool} {C : P.Config}
    (reach : P.Reach x C) {p q r : Fin n} {a b : T.Op} (ne : p ≠ q) (rp : r ≠ p) (rq : r ≠ q)
    (ha : P.action p (C.loc p) = .invoke a) (hb : P.action q (C.loc q) = .invoke b)
    {v w : Bool} (hvw : v ≠ w) (hp : ¬ P.Decides (P.go C p) w) (hq : ¬ P.Decides (P.go C q) v)
    (same : (T.apply (T.apply C.obj a).1 b).1 = (T.apply (T.apply C.obj b).1 a).1) : False := by
  obtain ⟨pqObj, -, -, pqRest⟩ := go_go_of_invoke ne ha hb
  obtain ⟨qpObj, -, -, qpRest⟩ := go_go_of_invoke (Ne.symm ne) hb ha
  refine S.no_split ((reach.go p).go q) (E := P.go (P.go C q) p) ?_ ?_ hvw (not_decides_go hp)
    (not_decides_go (i := p) hq) (r := r)
  · rw [pqObj, qpObj, same]
  · rw [pqRest r rp rq, qpRest r rq rp]

end Binary

end Protocol

open Protocol

/-- **Herlihy's bound for objects whose operation orders a process of the pair cannot see**: no
wait-free protocol solves binary consensus for two or more processes. -/
theorem not_solvable_of_pairCannotOrder {T : DetObject} {n : ℕ} (two : 2 ≤ n)
    (hidden : ∀ s a b, PairCannotOrder T s a b) : ¬ Solvable T.toObject n Bool := by
  rintro ⟨P, S⟩
  obtain ⟨x, biv⟩ := S.initial_bivalent two
  obtain ⟨C, reach, bivC, crit⟩ := S.exists_critical biv
  obtain ⟨p, q, a, b, ne, ha, hb, hp, hq⟩ := S.critical_pair reach bivC crit
  rcases hidden C.obj a b with h | h
  · exact S.no_hidden_order reach ne ha hb (v := false) (w := true) (by decide) hp hq h
  · exact S.no_hidden_order reach (Ne.symm ne) hb ha (v := true) (w := false) (by decide) hq hp h

/-- Among three processes, some process is neither `p` nor `q`. -/
theorem exists_third {n : ℕ} (three : 3 ≤ n) (p q : Fin n) : ∃ r : Fin n, r ≠ p ∧ r ≠ q := by
  by_contra none
  have h : ∀ r : Fin n, r ≠ p → r = q := fun r rp => by
    by_contra rq
    exact none ⟨r, rp, rq⟩
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
  omega

/-- **Herlihy's bound for objects whose operation orders a bystander cannot see**: no wait-free
protocol solves binary consensus for three or more processes. -/
theorem not_solvable_of_bystanderCannotOrder {T : DetObject} {n : ℕ} (three : 3 ≤ n)
    (hidden : ∀ s a b, BystanderCannotOrder T s a b) : ¬ Solvable T.toObject n Bool := by
  rintro ⟨P, S⟩
  obtain ⟨x, biv⟩ := S.initial_bivalent (by omega)
  obtain ⟨C, reach, bivC, crit⟩ := S.exists_critical biv
  obtain ⟨p, q, a, b, ne, ha, hb, hp, hq⟩ := S.critical_pair reach bivC crit
  rcases hidden C.obj a b with (h | h) | same
  · exact S.no_hidden_order reach ne ha hb (v := false) (w := true) (by decide) hp hq h
  · exact S.no_hidden_order reach (Ne.symm ne) hb ha (v := true) (w := false) (by decide) hq hp h
  · obtain ⟨r, rp, rq⟩ := exists_third three p q
    exact S.no_bystander_order reach ne rp rq ha hb (v := false) (w := true) (by decide) hp hq same

/-- The two bounds hold for consensus over any type with two distinct values. -/
theorem not_solvable_of_pairCannotOrder' {T : DetObject} {n : ℕ} {V : Type} [DecidableEq V]
    {v₀ v₁ : V} (ne : v₀ ≠ v₁) (two : 2 ≤ n) (hidden : ∀ s a b, PairCannotOrder T s a b) :
    ¬ Solvable T.toObject n V :=
  fun h => not_solvable_of_pairCannotOrder two hidden (h.toBool ne)

theorem not_solvable_of_bystanderCannotOrder' {T : DetObject} {n : ℕ} {V : Type} [DecidableEq V]
    {v₀ v₁ : V} (ne : v₀ ≠ v₁) (three : 3 ≤ n) (hidden : ∀ s a b, BystanderCannotOrder T s a b) :
    ¬ Solvable T.toObject n V :=
  fun h => not_solvable_of_bystanderCannotOrder three hidden (h.toBool ne)

/-! ## Many objects as one -/

/-- A family of objects used together: the state is the tuple of their states, an operation
names its object. -/
abbrev DetObject.pi {K : Type} [DecidableEq K] (T : K → DetObject) : DetObject where
  State := (k : K) → (T k).State
  Op := Σ k, (T k).Op
  Res := Σ k, (T k).Res
  apply s op := (Function.update s op.1 ((T op.1).apply (s op.1) op.2).1,
    ⟨op.1, ((T op.1).apply (s op.1) op.2).2⟩)

section Pi

variable {K : Type} [DecidableEq K] {T : K → DetObject}

theorem pi_apply (s : (k : K) → (T k).State) (k : K) (a : (T k).Op) :
    (DetObject.pi T).apply s ⟨k, a⟩ =
      (Function.update s k ((T k).apply (s k) a).1, ⟨k, ((T k).apply (s k) a).2⟩) := rfl

theorem OrderHidden.pi {s : (DetObject.pi T).State} {k : K} {a b : (T k).Op}
    (h : OrderHidden (T k) (s k) a b) : OrderHidden (DetObject.pi T) s ⟨k, a⟩ ⟨k, b⟩ := by
  cases h with
  | noChange h =>
      exact .noChange (by rw [pi_apply, h, Function.update_eq_self])
  | overwritten h =>
      exact .overwritten (by simp only [Function.update_self, Function.update_idem, h])
  | commutes h1 h2 =>
      exact .commutes (by simp only [Function.update_self, Function.update_idem, h1])
        (by simp only [Function.update_self, h2])

/-- Operations on different objects commute, answers included. -/
theorem OrderHidden.pi_of_ne (s : (DetObject.pi T).State) {k l : K} (ne : k ≠ l) (a : (T k).Op)
    (b : (T l).Op) : OrderHidden (DetObject.pi T) s ⟨k, a⟩ ⟨l, b⟩ := by
  refine .commutes ?_ ?_
  · simp only [Function.update_of_ne (Ne.symm ne), Function.update_of_ne ne]
    exact Function.update_comm ne _ _ _
  · simp only [Function.update_of_ne ne]

theorem pi_pairCannotOrder (hidden : ∀ k s a b, PairCannotOrder (T k) s a b) :
    ∀ s a b, PairCannotOrder (DetObject.pi T) s a b := by
  rintro s ⟨k, a⟩ ⟨l, b⟩
  by_cases same : k = l
  · subst same
    rcases hidden k (s k) a b with h | h
    · exact Or.inl h.pi
    · exact Or.inr h.pi
  · exact Or.inl (OrderHidden.pi_of_ne s same a b)

theorem pi_bystanderCannotOrder (hidden : ∀ k s a b, BystanderCannotOrder (T k) s a b) :
    ∀ s a b, BystanderCannotOrder (DetObject.pi T) s a b := by
  rintro s ⟨k, a⟩ ⟨l, b⟩
  by_cases same : k = l
  · subst same
    rcases hidden k (s k) a b with (h | h) | h
    · exact Or.inl (Or.inl h.pi)
    · exact Or.inl (Or.inr h.pi)
    · exact Or.inr (by simp only [Function.update_self, Function.update_idem, h])
  · exact Or.inl (Or.inl (OrderHidden.pi_of_ne s same a b))

end Pi

/-! ## Consensus numbers one and two -/

/-- **Consensus number one**: an object whose operation orders a process of the pair cannot see. -/
theorem hasConsensusNumber_one {T : DetObject} (s : T.State)
    (hidden : ∀ s a b, PairCannotOrder T s a b) : HasConsensusNumber T.toObject 1 := by
  intro n
  constructor
  · intro solvable
    by_contra big
    exact not_solvable_of_pairCannotOrder (by
      have : ¬ n ≤ 1 := fun h => big (by exact_mod_cast h)
      omega) hidden solvable
  · intro small
    exact solvable_of_le_one _ s (by exact_mod_cast small) Bool

/-- **Consensus number two**: two processes reach consensus, and a bystander cannot see the order
of any two operations. -/
theorem hasConsensusNumber_two {T : DetObject} (s : T.State)
    (hidden : ∀ s a b, BystanderCannotOrder T s a b) (two : Solvable T.toObject 2 Bool) :
    HasConsensusNumber T.toObject 2 := by
  intro n
  constructor
  · intro solvable
    by_contra big
    exact not_solvable_of_bystanderCannotOrder (by
      have : ¬ n ≤ 2 := fun h => big (by exact_mod_cast h)
      omega) hidden solvable
  · intro small
    have small : n ≤ 2 := by exact_mod_cast small
    rcases Nat.lt_or_ge n 2 with lt | ge
    · exact solvable_of_le_one _ s (by omega) Bool
    · obtain rfl : n = 2 := by omega
      exact two

/-! ## Controls -/

namespace Controls

/-- A test-and-set flag: setting it answers what it held. -/
def testAndSet : DetObject := ⟨Bool, Unit, Bool, fun s _ => (true, s)⟩

/-- **Positive control**: two test-and-sets on a fresh flag are hidden from a bystander. -/
theorem testAndSet_bystander : BystanderCannotOrder testAndSet false () () :=
  Or.inr rfl

/-- **Negative control**: neither of the two test-and-set processes is blind: the first answers
`false`, the second `true`, and the state changed. -/
theorem testAndSet_pair_sees : ¬ PairCannotOrder testAndSet false () () := by
  have hidden : ¬ OrderHidden testAndSet false () () := by
    rintro (h | h | ⟨-, h⟩) <;> simp [testAndSet] at h
  exact fun h => h.elim hidden hidden

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
