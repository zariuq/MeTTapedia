import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Wait-free consensus from shared objects

Herlihy's framework (*Wait-free synchronization*, TOPLAS 1991), as small as it can be while saying
the real thing.

## Objects

A **shared object** (`ObjectType`) is given by its atomic operations: `Fires s op s' r` says that
the operation `op`, applied at state `s`, can take effect, leaving `s'` and answering `r`.
Example: a register holding `3`; the operation "read" fires leaving `3` and answering `3`.
An operation may be unable to fire at a state; then the process that invoked it **waits** (a rho
receive on a channel with no message waits). Herlihy considers only operations that always fire
(p. 128 of the paper); those are the **deterministic objects** (`DetObject`), given by a function
`apply : State → Op → State × Res`. Counting a process that waits forever as a process that never
finishes is the natural reading of wait-freedom for operations that can wait, and it agrees with
Herlihy's on deterministic objects.

## Protocols

`n` processes share one object (several objects are one object whose state is the tuple of their
states; `Valence.pi`). Each process is a deterministic automaton (`Protocol`): from its local state
it either **decides** a value, and stays decided, or **invokes** an operation and moves to a local
state that depends on the answer. The protocol also chooses the object's initial state.

A **step** of process `i` (`Protocol.Step`): if `i` has decided, nothing changes; otherwise its
operation fires (any one of the ways it can fire) and `i` reads the answer, or the operation cannot
fire and `i` waits, changing nothing. A **run** is a finite list of process names
(`Protocol.Run`), an **execution** an infinite one (`Protocol.Execution`); any process may be
scheduled at any time, as often as the adversary likes.

## Consensus

A protocol **solves `n`-process consensus** (`Protocol.Solves`) when, for every assignment of
inputs `x : Fin n → V`:

* **agreement**: no reachable configuration has two processes decided on different values;
* **validity**: a decided value is the input of some process;
* **wait-freedom**: in every execution, a process that is scheduled infinitely often decides.
  Example: in an execution that schedules only process `0`, process `0` must decide, whatever the
  others have done before and however long they stay silent.

`Solvable T n V` when some protocol over `T` solves it.

## Consensus numbers

`HasConsensusNumber T k` (`k : ℕ∞`): binary consensus is solvable over `T` for exactly the
numbers of processes `n ≤ k`. The consensus number is unique when it exists
(`HasConsensusNumber.unique`). Every object with a state solves consensus for zero processes and
for one (`solvable_of_le_one`: the lone process decides its own input), so a consensus number is
at least `1`.

Binary consensus is the weakest (`Solvable.toBool`): a protocol for any type with two distinct
values gives one for booleans, so the impossibility theorems, stated for booleans, hold for every
such type.

## Tools for the possibility proofs

* `waitFree_of_measure`: a process decides in every execution that schedules it infinitely often
  when a measure of its local state never grows and drops at each of its own steps until it has
  decided.

## Controls

* `Controls.ownInput_solves_one`: deciding one's own input solves consensus for one process.
* `Controls.ownInput_disagrees_two`: for two processes with inputs `false` and `true`, the same
  protocol violates agreement at the start.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- A shared object: `Fires s op s' r` when the operation `op` can take effect at `s`, leaving
`s'` and answering `r`. -/
structure ObjectType where
  State : Type
  Op : Type
  Res : Type
  Fires : State → Op → State → Res → Prop

/-- A deterministic object whose operations always take effect: Herlihy's objects. -/
structure DetObject where
  State : Type
  Op : Type
  Res : Type
  apply : State → Op → State × Res

/-- A deterministic object as a shared object. -/
abbrev DetObject.toObject (T : DetObject) : ObjectType where
  State := T.State
  Op := T.Op
  Res := T.Res
  Fires s op s' r := T.apply s op = (s', r)

/-- What a process does next: decide a value, or invoke an operation. -/
inductive Action (Op V : Type) where
  | decide (v : V)
  | invoke (op : Op)

/-- A protocol for `n` processes with inputs and outputs in `V`, over the object `T`. -/
structure Protocol (T : ObjectType) (n : ℕ) (V : Type) where
  /-- Local states of a process. -/
  Local : Type
  /-- The local state of process `i` with input `v`. -/
  start : Fin n → V → Local
  /-- The object's initial state. -/
  init : T.State
  /-- What a process does at a local state. -/
  action : Fin n → Local → Action T.Op V
  /-- The local state after an operation, from the answer. -/
  next : Fin n → Local → T.Res → Local

namespace Protocol

variable {T : ObjectType} {n : ℕ} {V : Type}

/-- A configuration: the object's state and every process's local state. -/
@[ext]
structure Config (P : Protocol T n V) where
  obj : T.State
  loc : Fin n → P.Local

variable (P : Protocol T n V)

/-- The value process `i` has decided at `C`, if any. -/
def decision (C : P.Config) (i : Fin n) : Option V :=
  match P.action i (C.loc i) with
  | .decide v => some v
  | .invoke _ => none

/-- The initial configuration for the inputs `x`. -/
def initial (x : Fin n → V) : P.Config := ⟨P.init, fun i => P.start i (x i)⟩

/-- One step of process `i`. -/
inductive Step : P.Config → Fin n → P.Config → Prop
  | decided {C : P.Config} {i : Fin n} {v : V} :
      P.action i (C.loc i) = .decide v → Step C i C
  | fires {C : P.Config} {i : Fin n} {op : T.Op} {s : T.State} {r : T.Res} :
      P.action i (C.loc i) = .invoke op → T.Fires C.obj op s r →
      Step C i ⟨s, Function.update C.loc i (P.next i (C.loc i) r)⟩
  | waits {C : P.Config} {i : Fin n} {op : T.Op} :
      P.action i (C.loc i) = .invoke op → (∀ s r, ¬ T.Fires C.obj op s r) → Step C i C

/-- A run: the steps of a finite schedule. -/
def Run : P.Config → List (Fin n) → P.Config → Prop
  | C, [], D => D = C
  | C, i :: σ, D => ∃ E, P.Step C i E ∧ Run E σ D

/-- `C` is reachable from the initial configuration for `x`. -/
def Reach (x : Fin n → V) (C : P.Config) : Prop := ∃ σ, P.Run (P.initial x) σ C

/-- An execution: an infinite schedule and its configurations. -/
def Execution (σ : ℕ → Fin n) (c : ℕ → P.Config) : Prop := ∀ m, P.Step (c m) (σ m) (c (m + 1))

/-- A schedule names `i` infinitely often. -/
def InfinitelyOften (σ : ℕ → Fin n) (i : Fin n) : Prop := ∀ N, ∃ m, N ≤ m ∧ σ m = i

/-- **The protocol solves `n`-process consensus**: agreement, validity and wait-freedom. -/
structure Solves : Prop where
  agreement : ∀ x C, P.Reach x C → ∀ i j v w, P.decision C i = some v → P.decision C j = some w →
    v = w
  validity : ∀ x C, P.Reach x C → ∀ i v, P.decision C i = some v → ∃ j, x j = v
  waitFree : ∀ x σ c, c 0 = P.initial x → P.Execution σ c → ∀ i, InfinitelyOften σ i →
    ∃ m, (P.decision (c m) i).isSome

/-! ### Runs -/

variable {P}

theorem run_append {C E : P.Config} (σ τ : List (Fin n)) :
    P.Run C (σ ++ τ) E ↔ ∃ D, P.Run C σ D ∧ P.Run D τ E := by
  induction σ generalizing C with
  | nil => simp [Run]
  | cons i σ ih =>
      simp only [List.cons_append, Run]
      constructor
      · rintro ⟨F, step, rest⟩
        obtain ⟨D, first, second⟩ := ih.mp rest
        exact ⟨D, ⟨F, step, first⟩, second⟩
      · rintro ⟨D, ⟨F, step, first⟩, second⟩
        exact ⟨F, step, ih.mpr ⟨D, first, second⟩⟩

theorem Reach.step {x : Fin n → V} {C D : P.Config} {i : Fin n} (reach : P.Reach x C)
    (step : P.Step C i D) : P.Reach x D := by
  obtain ⟨σ, run⟩ := reach
  exact ⟨σ ++ [i], (run_append σ [i]).mpr ⟨C, run, D, step, rfl⟩⟩

theorem Reach.initial (x : Fin n → V) : P.Reach x (P.initial x) := ⟨[], rfl⟩

/-- Every configuration of an execution from an initial configuration is reachable. -/
theorem Execution.reach {x : Fin n → V} {σ : ℕ → Fin n} {c : ℕ → P.Config}
    (start : c 0 = P.initial x) (exec : P.Execution σ c) (m : ℕ) : P.Reach x (c m) := by
  induction m with
  | zero => rw [start]; exact Reach.initial x
  | succ m ih => exact ih.step (exec m)

/-! ### Steps change only the stepping process -/

theorem Step.loc_of_ne {C D : P.Config} {i j : Fin n} (step : P.Step C i D) (ne : j ≠ i) :
    D.loc j = C.loc j := by
  cases step with
  | decided _ => rfl
  | fires _ _ => exact Function.update_of_ne ne _ _
  | waits _ _ => rfl

theorem Step.eq_of_decide {C D : P.Config} {i : Fin n} {v : V} (step : P.Step C i D)
    (decided : P.action i (C.loc i) = .decide v) : D = C := by
  cases step with
  | decided _ => rfl
  | fires h _ => rw [decided] at h; cases h
  | waits _ _ => rfl

theorem decision_eq_of_loc {C D : P.Config} {i : Fin n} (same : D.loc i = C.loc i) :
    P.decision D i = P.decision C i := by
  unfold decision; rw [same]

theorem decision_eq_some_iff {C : P.Config} {i : Fin n} {v : V} :
    P.decision C i = some v ↔ P.action i (C.loc i) = .decide v := by
  unfold decision
  cases P.action i (C.loc i) <;> simp

/-- **A decided process stays decided.** -/
theorem Step.decision_of_decided {C D : P.Config} {i j : Fin n} {v : V} (step : P.Step C j D)
    (decided : P.decision C i = some v) : P.decision D i = some v := by
  by_cases same : i = j
  · subst same
    rw [step.eq_of_decide (decision_eq_some_iff.mp decided)]
    exact decided
  · rw [decision_eq_of_loc (step.loc_of_ne same)]
    exact decided

/-! ### Wait-freedom from a measure -/

/-- **Wait-freedom from a measure.** If a measure `μ i` of the configuration never grows along
steps from reachable configurations, and drops at every step of `i` while `i` has not decided,
then every execution that schedules `i` infinitely often has `i` decide. -/
theorem waitFree_of_measure (μ : Fin n → P.Config → ℕ)
    (mono : ∀ x C i j D, P.Reach x C → P.Step C j D → μ i D ≤ μ i C)
    (drops : ∀ x C i D, P.Reach x C → P.Step C i D → P.decision C i = none → μ i D < μ i C) :
    ∀ x σ c, c 0 = P.initial x → P.Execution σ c → ∀ i, InfinitelyOften σ i →
      ∃ m, (P.decision (c m) i).isSome := by
  intro x σ c start exec i often
  by_contra never
  have undecided : ∀ m, P.decision (c m) i = none := fun m => by
    simpa using not_exists.mp never m
  have reach := Execution.reach start exec
  have stays : ∀ m d, μ i (c (m + d)) ≤ μ i (c m) := by
    intro m d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
        exact (mono x _ i _ _ (reach (m + d)) (exec (m + d))).trans ih
  have descends : ∀ K, ∃ m, μ i (c m) + K ≤ μ i (c 0) := by
    intro K
    induction K with
    | zero => exact ⟨0, le_rfl⟩
    | succ K ih =>
        obtain ⟨m, hm⟩ := ih
        obtain ⟨m', later, named⟩ := often m
        have fall := drops x _ i _ (reach m') (named ▸ exec m') (undecided m')
        have kept := stays m (m' - m)
        rw [Nat.add_sub_cancel' later] at kept
        exact ⟨m' + 1, by omega⟩
  obtain ⟨m, hm⟩ := descends (μ i (c 0) + 1)
  omega

/-! ### Solvability and consensus numbers -/

end Protocol

/-- `n`-process consensus over `V` is solvable from the object `T`. -/
def Solvable (T : ObjectType) (n : ℕ) (V : Type) : Prop := ∃ P : Protocol T n V, P.Solves

/-- **The consensus number of `T` is `k`**: binary consensus is solvable from `T` for exactly the
numbers of processes up to `k`. -/
def HasConsensusNumber (T : ObjectType) (k : ℕ∞) : Prop :=
  ∀ n : ℕ, Solvable T n Bool ↔ (n : ℕ∞) ≤ k

/-- **The consensus number is unique.** -/
theorem HasConsensusNumber.unique {T : ObjectType} {k k' : ℕ∞} (first : HasConsensusNumber T k)
    (second : HasConsensusNumber T k') : k = k' := by
  apply le_antisymm
  · exact ENat.forall_natCast_le_iff_le.mp fun a h => (second a).mp ((first a).mpr h)
  · exact ENat.forall_natCast_le_iff_le.mp fun a h => (first a).mp ((second a).mpr h)

/-- The protocol in which every process decides its own input at once. -/
def ownInput (T : ObjectType) (s : T.State) (n : ℕ) (V : Type) : Protocol T n V where
  Local := V
  start _ v := v
  init := s
  action _ v := .decide v
  next _ v _ := v

/-- Under `ownInput` nothing ever changes. -/
theorem ownInput_run {T : ObjectType} {s : T.State} {n : ℕ} {V : Type}
    {C D : (ownInput T s n V).Config} {σ : List (Fin n)} (run : (ownInput T s n V).Run C σ D) :
    D = C := by
  induction σ generalizing C with
  | nil => exact run
  | cons i σ ih =>
      obtain ⟨E, step, rest⟩ := run
      rw [ih rest]
      exact step.eq_of_decide rfl

theorem fin_eq_of_le_one {n : ℕ} (small : n ≤ 1) (i j : Fin n) : i = j :=
  Fin.ext (by have := i.isLt; have := j.isLt; omega)

/-- **Consensus for at most one process is solvable from any object**: the lone process decides
its own input. -/
theorem solvable_of_le_one (T : ObjectType) (s : T.State) {n : ℕ} (small : n ≤ 1) (V : Type) :
    Solvable T n V := by
  refine ⟨ownInput T s n V, ⟨?_, ?_, ?_⟩⟩
  · rintro x C ⟨σ, run⟩ i j v w hv hw
    rw [ownInput_run run] at hv hw
    rw [fin_eq_of_le_one small i j] at hv
    exact Option.some.inj (hv.symm.trans hw)
  · rintro x C ⟨σ, run⟩ i v hv
    rw [ownInput_run run] at hv
    exact ⟨i, Option.some.inj hv⟩
  · intro x σ c start _ i _
    exact ⟨0, by rw [start]; rfl⟩

/-! ### Binary consensus is the weakest -/

section Binary

variable {T : ObjectType} {n : ℕ} {V : Type}

/-- A decision read as whether it is `v₁`. -/
def boolAction [DecidableEq V] (v₁ : V) : Action T.Op V → Action T.Op Bool
  | .decide v => .decide (decide (v = v₁))
  | .invoke a => .invoke a

/-- Read a protocol for values in `V` as a protocol for booleans: input `b` is `v₁` if `b` and
`v₀` otherwise, and a decided value is read as whether it is `v₁`. -/
def Protocol.toBool (P : Protocol T n V) (v₀ v₁ : V) [DecidableEq V] : Protocol T n Bool where
  Local := P.Local
  start i b := P.start i (if b then v₁ else v₀)
  init := P.init
  action i l := boolAction v₁ (P.action i l)
  next := P.next

variable [DecidableEq V] {P : Protocol T n V} {v₀ v₁ : V}

/-- The same configuration, read by the original protocol. -/
def Protocol.ofBool (C : (P.toBool v₀ v₁).Config) : P.Config := ⟨C.obj, C.loc⟩

theorem toBool_decision (C : (P.toBool v₀ v₁).Config) (i : Fin n) :
    (P.toBool v₀ v₁).decision C i = (P.decision (Protocol.ofBool C) i).map (fun v => decide (v = v₁)) := by
  unfold Protocol.decision
  have act : (P.toBool v₀ v₁).action i (C.loc i) = boolAction v₁ (P.action i (C.loc i)) := rfl
  rw [act]
  dsimp only [Protocol.ofBool]
  cases P.action i (C.loc i) <;> rfl

theorem toBool_step {C D : (P.toBool v₀ v₁).Config} {i : Fin n}
    (step : (P.toBool v₀ v₁).Step C i D) : P.Step (Protocol.ofBool C) i (Protocol.ofBool D) := by
  have act : (P.toBool v₀ v₁).action i (C.loc i) = boolAction v₁ (P.action i (C.loc i)) := rfl
  cases step with
  | decided h =>
      rw [act] at h
      cases hP : P.action i (C.loc i) with
      | decide v => exact .decided hP
      | invoke a => rw [hP] at h; cases h
  | fires h fires =>
      rw [act] at h
      cases hP : P.action i (C.loc i) with
      | decide v => rw [hP] at h; cases h
      | invoke a =>
          rw [hP] at h
          cases h
          exact .fires hP fires
  | waits h never =>
      rw [act] at h
      cases hP : P.action i (C.loc i) with
      | decide v => rw [hP] at h; cases h
      | invoke a =>
          rw [hP] at h
          cases h
          exact .waits hP never

theorem toBool_run {C D : (P.toBool v₀ v₁).Config} {σ : List (Fin n)}
    (run : (P.toBool v₀ v₁).Run C σ D) : P.Run (Protocol.ofBool C) σ (Protocol.ofBool D) := by
  induction σ generalizing C with
  | nil => rw [run]; rfl
  | cons i σ ih =>
      obtain ⟨E, step, rest⟩ := run
      exact ⟨_, toBool_step step, ih rest⟩

/-- **Binary consensus is no harder than consensus over any type with two values**: an
impossibility for booleans is an impossibility for every such type. -/
theorem Solvable.toBool {v₀ v₁ : V} (ne : v₀ ≠ v₁) (solvable : Solvable T n V) :
    Solvable T n Bool := by
  obtain ⟨P, S⟩ := solvable
  let embed : Bool → V := fun b => if b then v₁ else v₀
  have reach : ∀ x C, (P.toBool v₀ v₁).Reach x C → P.Reach (embed ∘ x) (Protocol.ofBool C) := by
    rintro x C ⟨σ, run⟩
    exact ⟨σ, toBool_run run⟩
  refine ⟨P.toBool v₀ v₁, ⟨?_, ?_, ?_⟩⟩
  · intro x C hC i j v w hv hw
    rw [toBool_decision] at hv hw
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [S.agreement _ _ (reach x C hC) i j v' w' hv' hw']
  · intro x C hC i v hv
    rw [toBool_decision] at hv
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨j, hj⟩ := S.validity _ _ (reach x C hC) i v' hv'
    refine ⟨j, ?_⟩
    subst hj
    cases hx : x j <;> simp [embed, hx, ne]
  · intro x σ c start exec i often
    have exec' : P.Execution σ (fun m => Protocol.ofBool (c m)) := fun m => toBool_step (exec m)
    obtain ⟨m, hm⟩ := S.waitFree (embed ∘ x) σ _ (by rw [start]; rfl) exec' i often
    exact ⟨m, by rw [toBool_decision]; simpa using hm⟩

end Binary

namespace Controls

/-- One register with one value, as the shared object of the controls. -/
def unitObject : ObjectType := ⟨Unit, Unit, Unit, fun _ _ _ _ => True⟩

/-- **Positive control**: deciding one's own input solves consensus for one process. -/
theorem ownInput_solves_one : (ownInput unitObject () 1 Bool).Solves := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x C ⟨σ, run⟩ i j v w hv hw
    rw [ownInput_run run] at hv hw
    rw [fin_eq_of_le_one (le_refl 1) i j] at hv
    exact Option.some.inj (hv.symm.trans hw)
  · rintro x C ⟨σ, run⟩ i v hv
    rw [ownInput_run run] at hv
    exact ⟨i, Option.some.inj hv⟩
  · intro x σ c start _ i _
    exact ⟨0, by rw [start]; rfl⟩

/-- **Negative control**: for two processes with inputs `false` and `true`, deciding one's own
input violates agreement in the initial configuration. -/
theorem ownInput_disagrees_two : ¬ (ownInput unitObject () 2 Bool).Solves := by
  intro solves
  have := solves.agreement ![false, true] _ (Protocol.Reach.initial _) 0 1 false true rfl rfl
  exact absurd this (by decide)

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
