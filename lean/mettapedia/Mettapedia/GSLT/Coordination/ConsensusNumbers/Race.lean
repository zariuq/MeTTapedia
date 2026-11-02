import Mettapedia.GSLT.Coordination.ConsensusNumbers.Valence

/-!
# Consensus for any number of processes from one race

Herlihy's protocol from compare-and-swap, for every object that offers the same race.

## The race

A `Race` over an object is: a starting state, an operation `claim v` for each value, an operation
`read`, and for each value `w` a settled state `settled w`, such that

* a claim at the starting state settles the object on its own value;
* a claim at a settled state changes nothing and reports that it lost;
* a read at a settled state changes nothing and tells the settled value.

Example: a compare-and-swap register (`casRegister`) starting empty; `claim v` swaps `none` for
`some v`; `read` reads.

## The protocol

Each process claims its input; if the claim reports a win it decides its input, otherwise it reads
and decides what it reads (`Race.protocol`). At every reachable configuration the object is either
at its start with no process moved, or settled on the input of the first claimer, and every
process that decided decided that input (`Race.inv_go`). Each process decides after at most two
of its own steps.

* **Every race solves consensus for every number of processes** (`Race.solvable`), so an object
  with a race has an infinite consensus number (`Race.hasConsensusNumber_top`).
* The compare-and-swap register has a race (`casRegister_race`), hence an infinite consensus number
  (`casRegister_hasConsensusNumber_top`).

## Controls

* `Controls.cas_not_hidden`: two claims with different values on an empty compare-and-swap
  register are seen by everyone: the two orders end in different states. So the bound of
  `Valence` does not apply, as it must not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- A race on an object: claims that settle it once, and a read of the settled value. -/
structure Race (T : DetObject) (V : Type) where
  start : T.State
  claim : V → T.Op
  read : T.Op
  settled : V → T.State
  won : T.Res → Bool
  learn : T.Res → V → V
  claim_start : ∀ v, (T.apply start (claim v)).1 = settled v
  claim_settled : ∀ v w, (T.apply (settled w) (claim v)).1 = settled w ∧
    won (T.apply (settled w) (claim v)).2 = false
  read_settled : ∀ v w, (T.apply (settled w) read).1 = settled w ∧
    learn (T.apply (settled w) read).2 v = w

/-- A process of the race protocol: about to claim, lost and about to read, or decided. -/
inductive RaceLocal (V : Type) where
  | start (v : V)
  | lost (v : V)
  | done (v : V)

namespace Race

variable {T : DetObject} {V : Type} (R : Race T V)

/-- Claim; on a win decide your input, otherwise read and decide what you read. -/
abbrev protocol (n : ℕ) : Protocol T.toObject n V where
  Local := RaceLocal V
  start _ v := .start v
  init := R.start
  action _
    | .start v => .invoke (R.claim v)
    | .lost _ => .invoke R.read
    | .done v => .decide v
  next _
    | .start v, r => if R.won r then .done v else .lost v
    | .lost v, r => .done (R.learn r v)
    | .done v, _ => .done v

variable {R} {n : ℕ}

theorem go_start {C : (R.protocol n).Config} {i : Fin n} {v : V} (hc : C.loc i = .start v) :
    (R.protocol n).go C i = ⟨(T.apply C.obj (R.claim v)).1, Function.update C.loc i
      (if R.won (T.apply C.obj (R.claim v)).2 then .done v else .lost v)⟩ := by
  rw [Protocol.go_of_invoke (op := R.claim v) (by rw [hc]), hc]

theorem go_lost {C : (R.protocol n).Config} {i : Fin n} {v : V} (hc : C.loc i = .lost v) :
    (R.protocol n).go C i = ⟨(T.apply C.obj R.read).1, Function.update C.loc i
      (.done (R.learn (T.apply C.obj R.read).2 v))⟩ := by
  rw [Protocol.go_of_invoke (op := R.read) (by rw [hc]), hc]

theorem go_done {C : (R.protocol n).Config} {i : Fin n} {v : V} (hc : C.loc i = .done v) :
    (R.protocol n).go C i = C :=
  Protocol.go_of_decide (v := v) (by rw [hc])

/-- The reachable configurations: nothing moved yet, or settled on the first claimer's input. -/
def Inv (x : Fin n → V) (C : (R.protocol n).Config) : Prop :=
  (C.obj = R.start ∧ ∀ i, C.loc i = .start (x i)) ∨
    ∃ j, C.obj = R.settled (x j) ∧
      ∀ i, C.loc i = .start (x i) ∨ C.loc i = .lost (x i) ∨ C.loc i = .done (x j)

theorem inv_go {x : Fin n → V} {C : (R.protocol n).Config} (inv : Inv x C) (i : Fin n) :
    Inv x ((R.protocol n).go C i) := by
  rcases inv with ⟨obj, locs⟩ | ⟨j, obj, locs⟩
  · -- the first claim settles the object on the claimer's input
    rw [go_start (locs i)]
    refine Or.inr ⟨i, by simp only [obj, R.claim_start], fun k => ?_⟩
    by_cases same : k = i
    · subst same
      simp only [Function.update_self]
      split <;> simp
    · simp only [Function.update_of_ne same]
      exact Or.inl (locs k)
  · refine Or.inr ⟨j, ?_⟩
    rcases locs i with hi | hi | hi
    · rw [go_start hi]
      refine ⟨by simp only [obj, (R.claim_settled (x i) (x j)).1], fun k => ?_⟩
      by_cases same : k = i
      · subst same
        simp [obj, (R.claim_settled (x k) (x j)).2]
      · simp only [Function.update_of_ne same]
        exact locs k
    · rw [go_lost hi]
      refine ⟨by simp only [obj, (R.read_settled (x i) (x j)).1], fun k => ?_⟩
      by_cases same : k = i
      · subst same
        simp [obj, (R.read_settled (x k) (x j)).2]
      · simp only [Function.update_of_ne same]
        exact locs k
    · rw [go_done hi]
      exact ⟨obj, locs⟩

theorem inv_of_reach {x : Fin n → V} {C : (R.protocol n).Config}
    (reach : (R.protocol n).Reach x C) : Inv x C := by
  obtain ⟨σ, rfl⟩ := Protocol.reach_iff.mp reach
  clear reach
  suffices ∀ D, Inv x D → Inv x ((R.protocol n).run D σ) from
    this _ (Or.inl ⟨rfl, fun _ => rfl⟩)
  induction σ with
  | nil => exact fun D h => h
  | cons i σ ih => exact fun D h => ih _ (inv_go h i)

theorem decision_eq_some {C : (R.protocol n).Config} {i : Fin n} {v : V}
    (h : (R.protocol n).decision C i = some v) : C.loc i = .done v := by
  have h := Protocol.decision_eq_some_iff.mp h
  cases hc : C.loc i with
  | start w => rw [hc] at h; cases h
  | lost w => rw [hc] at h; cases h
  | done w => rw [hc] at h; cases h; rfl

/-- The rank of a process: steps left before it decides. -/
def rank : RaceLocal V → ℕ
  | .start _ => 2
  | .lost _ => 1
  | .done _ => 0

theorem rank_go_le (C : (R.protocol n).Config) (i j : Fin n) :
    rank (((R.protocol n).go C j).loc i) ≤ rank (C.loc i) := by
  by_cases same : i = j
  · subst same
    cases hc : C.loc i with
    | start v =>
        rw [go_start hc]; simp only [Function.update_self]; split <;> simp [rank]
    | lost v => rw [go_lost hc]; simp [rank]
    | done v => rw [go_done hc, hc]
  · rw [Protocol.go_loc_of_ne same]

theorem rank_go_lt (C : (R.protocol n).Config) (i : Fin n)
    (undecided : (R.protocol n).decision C i = none) :
    rank (((R.protocol n).go C i).loc i) < rank (C.loc i) := by
  cases hc : C.loc i with
  | start v =>
      rw [go_start hc]; simp only [Function.update_self]; split <;> simp [rank]
  | lost v => rw [go_lost hc]; simp [rank]
  | done v =>
      have : (R.protocol n).decision C i = some v := by
        unfold Protocol.decision; rw [hc]
      rw [this] at undecided; cases undecided

theorem value_of_done {x : Fin n → V} {C : (R.protocol n).Config} {j : Fin n}
    (locs : ∀ i, C.loc i = .start (x i) ∨ C.loc i = .lost (x i) ∨ C.loc i = .done (x j))
    {i : Fin n} {v : V} (h : C.loc i = .done v) : v = x j := by
  rcases locs i with h' | h' | h' <;> rw [h'] at h <;> cases h
  rfl

/-- **Every race solves consensus for every number of processes.** -/
theorem solvable (R : Race T V) (n : ℕ) : Solvable T.toObject n V := by
  refine ⟨R.protocol n, ⟨?_, ?_, ?_⟩⟩
  · intro x C reach i k v w hv hw
    have hv := decision_eq_some hv
    have hw := decision_eq_some hw
    rcases inv_of_reach reach with ⟨-, locs⟩ | ⟨j, -, locs⟩
    · rw [locs i] at hv; cases hv
    · rw [value_of_done locs hv, value_of_done locs hw]
  · intro x C reach i v hv
    have hv := decision_eq_some hv
    rcases inv_of_reach reach with ⟨-, locs⟩ | ⟨j, -, locs⟩
    · rw [locs i] at hv; cases hv
    · exact ⟨j, (value_of_done locs hv).symm⟩
  · refine Protocol.waitFree_of_measure (fun i C => rank (C.loc i)) ?_ ?_
    · intro x C i j D _ step
      rw [Protocol.step_iff_go.mp step]
      exact rank_go_le C i j
    · intro x C i D _ step undecided
      rw [Protocol.step_iff_go.mp step]
      exact rank_go_lt C i undecided

/-- **An object with a race has an infinite consensus number.** -/
theorem hasConsensusNumber_top (R : Race T Bool) : HasConsensusNumber T.toObject ⊤ :=
  fun n => ⟨fun _ => le_top, fun _ => R.solvable n⟩

end Race

/-! ## Compare-and-swap -/

/-- Operations of a compare-and-swap register. -/
inductive CasOp (V : Type) where
  /-- Replace the content by `new` if it is `expected`. -/
  | cas (expected new : Option V)
  | read

/-- A compare-and-swap register: each operation answers the old content and whether it changed
or read. -/
def casRegister (V : Type) [DecidableEq V] : DetObject where
  State := Option V
  Op := CasOp V
  Res := Option V × Bool
  apply s
    | .cas expected new => if s = expected then (new, (s, true)) else (s, (s, false))
    | .read => (s, (s, true))

/-- The race of a compare-and-swap register. -/
def casRegister_race (V : Type) [DecidableEq V] : Race (casRegister V) V where
  start := none
  claim v := .cas none (some v)
  read := .read
  settled v := some v
  won r := r.2
  learn r v := r.1.getD v
  claim_start _ := rfl
  claim_settled _ _ := ⟨rfl, rfl⟩
  read_settled _ _ := ⟨rfl, rfl⟩

/-- **A compare-and-swap register has an infinite consensus number** (Herlihy 1991, Theorem 7). -/
theorem casRegister_hasConsensusNumber_top : HasConsensusNumber (casRegister Bool).toObject ⊤ :=
  (casRegister_race Bool).hasConsensusNumber_top

namespace Controls

/-- **Negative control for the bound**: two claims of different values on an empty
compare-and-swap register are hidden from nobody. -/
theorem cas_not_hidden :
    ¬ BystanderCannotOrder (casRegister Bool) none (.cas none (some true)) (.cas none (some false)) := by
  have one : ¬ OrderHidden (casRegister Bool) none (.cas none (some true)) (.cas none (some false)) := by
    rintro (h | h | ⟨h, -⟩) <;> simp [casRegister] at h
  have two : ¬ OrderHidden (casRegister Bool) none (.cas none (some false)) (.cas none (some true)) := by
    rintro (h | h | ⟨h, -⟩) <;> simp [casRegister] at h
  rintro ((h | h) | h)
  · exact one h
  · exact two h
  · simp [casRegister] at h

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
