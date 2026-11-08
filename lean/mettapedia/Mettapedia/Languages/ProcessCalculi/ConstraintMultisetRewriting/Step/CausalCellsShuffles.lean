import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalCells
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalHistories

/-!
# The independent case: R103's shuffle identity from the cell identity

Two rate systems run side by side (`CausalHistories.par`). A run of each side is a **chain of
cells**: the `k`-th cell of a side is the whole race at the state its run reached after `k` moves,
one event per candidate of that race, counted with multiplicity (`system`). A cell of a side is
enabled when that side has fired exactly `k` moves; nothing of one side enables or disables the
other.

* The history of the two runs (`history`) is conflict-free, maximal, persistent and positive
  (`history_isHistory`), and reachable (`reach_cfg`).
* Its linearizations are the shuffles: the sum over the linearizations from the configuration
  "`k` moves of one side, `k'` of the other" is the sum over the shuffles of the two remaining runs
  (`lins_sum_cfg`), by the same first-move recursion.
* So the cell identity (`CausalCells.CellSystem.History.race_identity`) gives back R103's race
  identity, with the same statement (`sum_shuffles_of_race_identity`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalCellsShuffles

open CausalHistories (total pathProb IsRun endState shuffles schedProb Positive)
open Mettapedia.GSLT.GradedSupport (IsNormal)
open CausalCells

universe u v

/-! ## Runs read position by position -/

section Runs

variable {S : Type u} (step : S → List (S × ℝ))

/-- The state a run has reached after `k` moves. -/
def stateAt (s : S) (α : List (S × ℝ)) (k : ℕ) : S := endState s (α.take k)

/-- The weight of the `j`-th candidate of a state, `0` past the end. -/
def candWeight (s : S) (j : ℕ) : ℝ := (((step s)[j]?).map Prod.snd).getD 0

open Classical in
/-- A position, among its state's candidates, of the `k`-th move of a run. -/
def moveIndex (s : S) (α : List (S × ℝ)) (k : ℕ) : ℕ :=
  if h : ∃ j, ∃ _ : j < (step (stateAt s α k)).length, ∃ hk : k < α.length,
      (step (stateAt s α k))[j] = α[k] then Classical.choose h else 0

/-- The likelihood factor of the `k`-th move of a run. -/
def moveFactor (s : S) (α : List (S × ℝ)) (k : ℕ) : ℝ :=
  ((α[k]?).map Prod.snd).getD 0 / total step (stateAt s α k)

theorem stateAt_zero (s : S) (α : List (S × ℝ)) : stateAt s α 0 = s := by
  simp [stateAt, endState]

theorem stateAt_cons_succ (s : S) (p : S × ℝ) (rest : List (S × ℝ)) (k : ℕ) :
    stateAt s (p :: rest) (k + 1) = stateAt p.1 rest k := by
  simp [stateAt, endState]

theorem stateAt_length (s : S) (α : List (S × ℝ)) : stateAt s α α.length = endState s α := by
  rw [stateAt, List.take_of_length_le (le_refl _)]

theorem stateAt_succ : ∀ {s : S} {α : List (S × ℝ)} (k : ℕ) (h : k < α.length),
    stateAt s α (k + 1) = (α[k]).1
  | _, [], _, h => absurd h (by simp)
  | s, p :: rest, 0, _ => by simp [stateAt, endState]
  | _, p :: rest, k + 1, h => by
      rw [stateAt_cons_succ]
      simpa using stateAt_succ (s := p.1) k (by simpa using h)

variable {step}

theorem mem_step_of_isRun : ∀ {s : S} {α : List (S × ℝ)}, IsRun step s α →
    ∀ (k : ℕ) (h : k < α.length), α[k] ∈ step (stateAt s α k)
  | _, [], _, _, h => absurd h (by simp)
  | _, _ :: _, .cons member _, 0, _ => by simpa [stateAt, endState] using member
  | _, p :: _, .cons _ later, k + 1, h => by
      rw [stateAt_cons_succ]
      simpa using mem_step_of_isRun later k (by simpa using h)

theorem moveIndex_spec {s : S} {α : List (S × ℝ)} (run : IsRun step s α) {k : ℕ}
    (h : k < α.length) : ∃ below : moveIndex step s α k < (step (stateAt s α k)).length,
      (step (stateAt s α k))[moveIndex step s α k] = α[k] := by
  have found : ∃ j, ∃ _ : j < (step (stateAt s α k)).length, ∃ hk : k < α.length,
      (step (stateAt s α k))[j] = α[k] := by
    obtain ⟨j, below, same⟩ := List.getElem_of_mem (mem_step_of_isRun run k h)
    exact ⟨j, below, h, same⟩
  unfold moveIndex
  rw [dif_pos found]
  obtain ⟨below, _, same⟩ := Classical.choose_spec found
  exact ⟨below, same⟩

theorem moveIndex_lt {s : S} {α : List (S × ℝ)} (run : IsRun step s α) {k : ℕ}
    (h : k < α.length) : moveIndex step s α k < (step (stateAt s α k)).length :=
  (moveIndex_spec run h).1

theorem candWeight_moveIndex {s : S} {α : List (S × ℝ)} (run : IsRun step s α) {k : ℕ}
    (h : k < α.length) : candWeight step (stateAt s α k) (moveIndex step s α k) = (α[k]).2 := by
  obtain ⟨below, same⟩ := moveIndex_spec run h
  unfold candWeight
  rw [List.getElem?_eq_getElem below, same]
  rfl

variable (step)

theorem sum_range_candWeight (l : List (S × ℝ)) :
    ∑ j ∈ Finset.range l.length, ((l[j]?).map Prod.snd).getD 0 = (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
      simp only [Option.map_some, Option.getD_some]
      ring

/-- A run's likelihood is the product of its moves' factors. -/
theorem pathProb_eq_prod : ∀ (s : S) (α : List (S × ℝ)),
    pathProb step s α = ∏ k ∈ Finset.range α.length, moveFactor step s α k
  | _, [] => by simp [pathProb]
  | s, p :: rest => by
      rw [List.length_cons, Finset.prod_range_succ', pathProb, pathProb_eq_prod p.1 rest, mul_comm]
      congr 1

end Runs

/-! ## Two runs as chains of cells -/

section Chains

variable {A : Type u} {B : Type v} (stepA : A → List (A × ℝ)) (stepB : B → List (B × ℝ))
  (a : A) (b : B) (α : List (A × ℝ)) (β : List (B × ℝ))

/-- An event: a side, a move number and a candidate position. -/
abbrev Event := (ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- A cell: a side and a move number. -/
abbrev Cell := ℕ ⊕ ℕ

/-- The cell of an event. -/
def eventCell : Event → Cell
  | .inl e => .inl e.1
  | .inr e => .inr e.1

/-- The number of moves of the first side in a configuration. -/
def leftCount (x : Finset Event) : ℕ := (x.filter fun e => e.isLeft).card

/-- The number of moves of the second side in a configuration. -/
def rightCount (x : Finset Event) : ℕ := (x.filter fun e => e.isRight).card

/-- **Two runs as a cell system**: the `k`-th cell of a side is the race at the state its run
reached after `k` moves, enabled when that side has fired `k` moves. -/
def system : CellSystem Event Cell where
  cell := eventCell
  members c := match c with
    | .inl k => (Finset.range (stepA (stateAt a α k)).length).image fun j => .inl (k, j)
    | .inr k => (Finset.range (stepB (stateAt b β k)).length).image fun j => .inr (k, j)
  cell_of_mem := by
    intro e c member
    cases c with
    | inl k =>
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
        rfl
    | inr k =>
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
        rfl
  weight e := match e with
    | .inl e => candWeight stepA (stateAt a α e.1) e.2
    | .inr e => candWeight stepB (stateAt b β e.1) e.2
  enabled x :=
    (if leftCount x < α.length then {.inl (leftCount x)} else ∅) ∪
      (if rightCount x < β.length then {.inr (rightCount x)} else ∅)

/-- The `k`-th move of the first run, as an event. -/
def evA (k : ℕ) : Event := .inl (k, moveIndex stepA a α k)

/-- The `k`-th move of the second run, as an event. -/
def evB (k : ℕ) : Event := .inr (k, moveIndex stepB b β k)

/-- The configuration after `k` moves of the first run and `k'` of the second. -/
def cfg (k k' : ℕ) : Finset Event :=
  (Finset.range k).image (evA stepA a α) ∪ (Finset.range k').image (evB stepB b β)

/-- **The history of the two runs.** -/
def history : Finset Event := cfg stepA stepB a b α β α.length β.length

theorem evA_injective : Function.Injective (evA stepA a α) := by
  intro k k' same
  simp only [evA, Sum.inl.injEq, Prod.mk.injEq] at same
  exact same.1

theorem evB_injective : Function.Injective (evB stepB b β) := by
  intro k k' same
  simp only [evB, Sum.inr.injEq, Prod.mk.injEq] at same
  exact same.1

theorem evA_ne_evB (k k' : ℕ) : evA stepA a α k ≠ evB stepB b β k' := by
  simp [evA, evB]

theorem mem_cfg_evA {k k' j : ℕ} : evA stepA a α j ∈ cfg stepA stepB a b α β k k' ↔ j < k := by
  simp only [cfg, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, lt, same⟩ | ⟨i, _, same⟩)
    · rw [← evA_injective stepA a α same]
      exact lt
    · exact absurd same.symm (evA_ne_evB stepA stepB a b α β j i)
  · intro lt
    exact Or.inl ⟨j, lt, rfl⟩

theorem mem_cfg_evB {k k' j : ℕ} : evB stepB b β j ∈ cfg stepA stepB a b α β k k' ↔ j < k' := by
  simp only [cfg, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, _, same⟩ | ⟨i, lt, same⟩)
    · exact absurd same (evA_ne_evB stepA stepB a b α β i j)
    · rw [← evB_injective stepB b β same]
      exact lt
  · intro lt
    exact Or.inr ⟨j, lt, rfl⟩

theorem mem_cfg {k k' : ℕ} {e : Event} : e ∈ cfg stepA stepB a b α β k k' ↔
    (∃ j < k, e = evA stepA a α j) ∨ ∃ j < k', e = evB stepB b β j := by
  simp only [cfg, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨j, lt, rfl⟩ | ⟨j, lt, rfl⟩)
    · exact Or.inl ⟨j, lt, rfl⟩
    · exact Or.inr ⟨j, lt, rfl⟩
  · rintro (⟨j, lt, rfl⟩ | ⟨j, lt, rfl⟩)
    · exact Or.inl ⟨j, lt, rfl⟩
    · exact Or.inr ⟨j, lt, rfl⟩

theorem leftCount_cfg (k k' : ℕ) : leftCount (cfg stepA stepB a b α β k k') = k := by
  unfold leftCount cfg
  rw [Finset.filter_union, Finset.filter_true_of_mem, Finset.filter_false_of_mem,
    Finset.union_empty, Finset.card_image_of_injective _ (evA_injective stepA a α),
    Finset.card_range]
  · intro e member
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    simp [evB]
  · intro e member
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    simp [evA]

theorem rightCount_cfg (k k' : ℕ) : rightCount (cfg stepA stepB a b α β k k') = k' := by
  unfold rightCount cfg
  rw [Finset.filter_union, Finset.filter_false_of_mem, Finset.filter_true_of_mem,
    Finset.empty_union, Finset.card_image_of_injective _ (evB_injective stepB b β),
    Finset.card_range]
  · intro e member
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    simp [evB]
  · intro e member
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    simp [evA]

theorem insert_evA (k k' : ℕ) :
    insert (evA stepA a α k) (cfg stepA stepB a b α β k k') = cfg stepA stepB a b α β (k + 1) k' := by
  unfold cfg
  rw [Finset.range_add_one, Finset.image_insert, Finset.insert_union]

theorem insert_evB (k k' : ℕ) :
    insert (evB stepB b β k') (cfg stepA stepB a b α β k k') = cfg stepA stepB a b α β k (k' + 1) := by
  unfold cfg
  rw [Finset.range_add_one, Finset.image_insert, Finset.union_insert]

theorem cfg_zero : cfg stepA stepB a b α β 0 0 = ∅ := by
  simp [cfg]

theorem cellTotal_inl (k : ℕ) :
    (system stepA stepB a b α β).cellTotal (.inl k) = total stepA (stateAt a α k) := by
  unfold CellSystem.cellTotal
  show ∑ e ∈ (Finset.range (stepA (stateAt a α k)).length).image (fun j => (.inl (k, j) : Event)),
    (system stepA stepB a b α β).weight e = _
  rw [Finset.sum_image (fun _ _ _ _ same => by simpa using same)]
  exact sum_range_candWeight (stepA (stateAt a α k))

theorem cellTotal_inr (k : ℕ) :
    (system stepA stepB a b α β).cellTotal (.inr k) = total stepB (stateAt b β k) := by
  unfold CellSystem.cellTotal
  show ∑ e ∈ (Finset.range (stepB (stateAt b β k)).length).image (fun j => (.inr (k, j) : Event)),
    (system stepA stepB a b α β).weight e = _
  rw [Finset.sum_image (fun _ _ _ _ same => by simpa using same)]
  exact sum_range_candWeight (stepB (stateAt b β k))

theorem enabled_cfg (k k' : ℕ) :
    (system stepA stepB a b α β).enabled (cfg stepA stepB a b α β k k') =
      (if k < α.length then {.inl k} else ∅) ∪ (if k' < β.length then {.inr k'} else ∅) := by
  show (if leftCount _ < α.length then _ else _) ∪ (if rightCount _ < β.length then _ else _) = _
  rw [leftCount_cfg, rightCount_cfg]

theorem mem_enabled {x : Finset Event} {c : Cell} :
    c ∈ (system stepA stepB a b α β).enabled x ↔
      (leftCount x < α.length ∧ c = Sum.inl (leftCount x)) ∨
        (rightCount x < β.length ∧ c = Sum.inr (rightCount x)) := by
  show c ∈ (if leftCount x < α.length then ({Sum.inl (leftCount x)} : Finset Cell) else ∅) ∪
    (if rightCount x < β.length then ({Sum.inr (rightCount x)} : Finset Cell) else ∅) ↔ _
  by_cases first : leftCount x < α.length <;> by_cases second : rightCount x < β.length <;>
    simp [first, second]

variable {stepA stepB a b α β}
variable (runA : IsRun stepA a α) (runB : IsRun stepB b β)
  (deadA : IsNormal stepA (endState a α)) (deadB : IsNormal stepB (endState b β))

include runA in
theorem evA_candidate {k k' : ℕ} (h : k < α.length) :
    evA stepA a α k ∈ (system stepA stepB a b α β).candidates (cfg stepA stepB a b α β k k') := by
  rw [CellSystem.mem_candidates]
  refine ⟨?_, ?_⟩
  · rw [enabled_cfg, if_pos h]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  · show evA stepA a α k ∈ (Finset.range (stepA (stateAt a α k)).length).image fun j => _
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (moveIndex_lt runA h), rfl⟩

include runB in
theorem evB_candidate {k k' : ℕ} (h : k' < β.length) :
    evB stepB b β k' ∈ (system stepA stepB a b α β).candidates (cfg stepA stepB a b α β k k') := by
  rw [CellSystem.mem_candidates]
  refine ⟨?_, ?_⟩
  · rw [enabled_cfg, if_pos h]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · show evB stepB b β k' ∈ (Finset.range (stepB (stateAt b β k')).length).image fun j => _
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (moveIndex_lt runB h), rfl⟩

include deadA deadB in
/-- **The race total of the composition is the sum of the two sides' totals.** -/
theorem total_cfg {k k' : ℕ} (hk : k ≤ α.length) (hk' : k' ≤ β.length) :
    (system stepA stepB a b α β).total (cfg stepA stepB a b α β k k') =
      total stepA (stateAt a α k) + total stepB (stateAt b β k') := by
  unfold CellSystem.total
  rw [enabled_cfg]
  have zeroA : k = α.length → total stepA (stateAt a α k) = 0 := by
    rintro rfl
    rw [stateAt_length]
    exact CausalHistories.total_eq_zero_of_normal deadA
  have zeroB : k' = β.length → total stepB (stateAt b β k') = 0 := by
    rintro rfl
    rw [stateAt_length]
    exact CausalHistories.total_eq_zero_of_normal deadB
  by_cases lt : k < α.length <;> by_cases lt' : k' < β.length
  · rw [if_pos lt, if_pos lt', Finset.sum_union (by simp), Finset.sum_singleton,
      Finset.sum_singleton, cellTotal_inl, cellTotal_inr]
  · rw [if_pos lt, if_neg lt', Finset.union_empty, Finset.sum_singleton, cellTotal_inl,
      zeroB (by omega), add_zero]
  · rw [if_neg lt, if_pos lt', Finset.empty_union, Finset.sum_singleton, cellTotal_inr,
      zeroA (by omega), zero_add]
  · rw [if_neg lt, if_neg lt', Finset.union_empty, Finset.sum_empty, zeroA (by omega),
      zeroB (by omega), add_zero]

include runA runB in
/-- **The candidates of the history** at a configuration are the next move of each side. -/
theorem onHistory_cfg {k k' : ℕ} (hk : k ≤ α.length) (hk' : k' ≤ β.length) :
    (system stepA stepB a b α β).onHistory (history stepA stepB a b α β)
        (cfg stepA stepB a b α β k k') =
      (if k < α.length then {evA stepA a α k} else ∅) ∪
        (if k' < β.length then {evB stepB b β k'} else ∅) := by
  ext e
  simp only [CellSystem.onHistory, Finset.mem_filter, Finset.mem_sdiff, history,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨inX, notIn⟩, cand⟩
    have cell := ((system stepA stepB a b α β).mem_candidates.mp cand).1
    rw [enabled_cfg] at cell
    rcases (mem_cfg stepA stepB a b α β).mp inX with ⟨j, _, rfl⟩ | ⟨j, _, rfl⟩
    · have same : j = k ∧ k < α.length := by
        rcases Finset.mem_union.mp cell with inl | inr
        · by_cases lt : k < α.length
          · rw [if_pos lt, Finset.mem_singleton] at inl
            exact ⟨Sum.inl.inj inl, lt⟩
          · rw [if_neg lt] at inl
            simp at inl
        · by_cases lt : k' < β.length
          · rw [if_pos lt, Finset.mem_singleton] at inr
            exact absurd inr (by simp [system, evA, eventCell])
          · rw [if_neg lt] at inr
            simp at inr
      obtain ⟨rfl, lt⟩ := same
      left
      rw [if_pos lt]
      exact Finset.mem_singleton_self _
    · have same : j = k' ∧ k' < β.length := by
        rcases Finset.mem_union.mp cell with inl | inr
        · by_cases lt : k < α.length
          · rw [if_pos lt, Finset.mem_singleton] at inl
            exact absurd inl (by simp [system, evB, eventCell])
          · rw [if_neg lt] at inl
            simp at inl
        · by_cases lt : k' < β.length
          · rw [if_pos lt, Finset.mem_singleton] at inr
            exact ⟨Sum.inr.inj inr, lt⟩
          · rw [if_neg lt] at inr
            simp at inr
      obtain ⟨rfl, lt⟩ := same
      right
      rw [if_pos lt]
      exact Finset.mem_singleton_self _
  · rintro (inl | inr)
    · by_cases lt : k < α.length
      · rw [if_pos lt, Finset.mem_singleton] at inl
        subst inl
        refine ⟨⟨(mem_cfg_evA stepA stepB a b α β).mpr lt,
          fun h => absurd ((mem_cfg_evA stepA stepB a b α β).mp h) (lt_irrefl k)⟩, ?_⟩
        exact evA_candidate runA lt
      · rw [if_neg lt] at inl
        simp at inl
    · by_cases lt : k' < β.length
      · rw [if_pos lt, Finset.mem_singleton] at inr
        subst inr
        refine ⟨⟨(mem_cfg_evB stepA stepB a b α β).mpr lt,
          fun h => absurd ((mem_cfg_evB stepA stepB a b α β).mp h) (lt_irrefl k')⟩, ?_⟩
        exact evB_candidate runB lt
      · rw [if_neg lt] at inr
        simp at inr

include runA runB in
/-- **The history of two runs is reachable.** -/
theorem reach_cfg : ∀ (N k k' : ℕ), k ≤ α.length → k' ≤ β.length →
    (α.length - k) + (β.length - k') = N →
      (system stepA stepB a b α β).Reach (history stepA stepB a b α β)
        (cfg stepA stepB a b α β k k')
  | 0, k, k', hk, hk', count => by
      have ek : k = α.length := by omega
      have ek' : k' = β.length := by omega
      subst ek ek'
      exact ⟨[], CellSystem.IsLin.nil⟩
  | N + 1, k, k', hk, hk', count => by
      by_cases lt : k < α.length
      · obtain ⟨l, lin⟩ := reach_cfg N (k + 1) k' lt hk' (by omega)
        refine ⟨evA stepA a α k :: l, CellSystem.IsLin.cons (evA_candidate runA lt)
          (fun h => absurd ((mem_cfg_evA stepA stepB a b α β).mp h) (lt_irrefl k)) ?_⟩
        rw [insert_evA]
        exact lin
      · have lt' : k' < β.length := by omega
        obtain ⟨l, lin⟩ := reach_cfg N k (k' + 1) hk lt' (by omega)
        refine ⟨evB stepB b β k' :: l, CellSystem.IsLin.cons (evB_candidate runB lt')
          (fun h => absurd ((mem_cfg_evB stepA stepB a b α β).mp h) (lt_irrefl k')) ?_⟩
        rw [insert_evB]
        exact lin

include runA runB deadA deadB in
/-- **The linearizations are the shuffles**: from the configuration after `k` and `k'` moves, the
sum over the linearizations is the sum over the shuffles of the two remaining runs. -/
theorem lins_sum_cfg : ∀ (N k k' : ℕ), k ≤ α.length → k' ≤ β.length →
    (α.length - k) + (β.length - k') = N →
      ∑ l ∈ (system stepA stepB a b α β).lins (history stepA stepB a b α β)
          (cfg stepA stepB a b α β k k'),
          (system stepA stepB a b α β).pathProb (cfg stepA stepB a b α β k k') l =
        ((shuffles (α.drop k) (β.drop k')).map
          (schedProb stepA stepB (stateAt a α k) (stateAt b β k'))).sum
  | 0, k, k', hk, hk', count => by
      have ek : k = α.length := by omega
      have ek' : k' = β.length := by omega
      subst ek ek'
      rw [show cfg stepA stepB a b α β α.length β.length = history stepA stepB a b α β from rfl,
        CellSystem.lins_self]
      simp [CellSystem.pathProb, shuffles, schedProb]
  | N + 1, k, k', hk, hk', count => by
      have away : cfg stepA stepB a b α β k k' ≠ history stepA stepB a b α β := by
        intro same
        by_cases lt : k < α.length
        · have inX : evA stepA a α k ∈ history stepA stepB a b α β :=
            (mem_cfg_evA stepA stepB a b α β).mpr lt
          rw [← same] at inX
          exact lt_irrefl k ((mem_cfg_evA stepA stepB a b α β).mp inX)
        · have lt' : k' < β.length := by omega
          have inX : evB stepB b β k' ∈ history stepA stepB a b α β :=
            (mem_cfg_evB stepA stepB a b α β).mpr lt'
          rw [← same] at inX
          exact lt_irrefl k' ((mem_cfg_evB stepA stepB a b α β).mp inX)
      rw [CellSystem.sum_lins_of_ne _ away, onHistory_cfg runA runB hk hk',
        total_cfg deadA deadB hk hk']
      by_cases lt : k < α.length <;> by_cases lt' : k' < β.length
      · have ihA := lins_sum_cfg N (k + 1) k' lt hk' (by omega)
        have ihB := lins_sum_cfg N k (k' + 1) hk lt' (by omega)
        have wA : (system stepA stepB a b α β).weight (evA stepA a α k) = (α[k]).2 :=
          candWeight_moveIndex runA lt
        have wB : (system stepA stepB a b α β).weight (evB stepB b β k') = (β[k']).2 :=
          candWeight_moveIndex runB lt'
        rw [if_pos lt, if_pos lt', Finset.sum_union (by simp [evA_ne_evB]), Finset.sum_singleton,
          Finset.sum_singleton, insert_evA, insert_evB, ihA, ihB, wA, wB,
          stateAt_succ (s := a) k lt, stateAt_succ (s := b) k' lt',
          List.drop_eq_getElem_cons lt, List.drop_eq_getElem_cons lt']
        simp only [shuffles, List.map_append, List.map_map, List.sum_append]
        rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
        rfl
      · have ek' : k' = β.length := by omega
        have ihA := lins_sum_cfg N (k + 1) k' lt hk' (by omega)
        have wA : (system stepA stepB a b α β).weight (evA stepA a α k) = (α[k]).2 :=
          candWeight_moveIndex runA lt
        rw [if_pos lt, if_neg lt', Finset.union_empty, Finset.sum_singleton, insert_evA, ihA, wA,
          stateAt_succ (s := a) k lt, List.drop_eq_getElem_cons lt, ek', List.drop_length,
          CausalHistories.shuffles_nil_right, CausalHistories.shuffles_nil_right]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rfl
      · have ek : k = α.length := by omega
        have ihB := lins_sum_cfg N k (k' + 1) hk lt' (by omega)
        have wB : (system stepA stepB a b α β).weight (evB stepB b β k') = (β[k']).2 :=
          candWeight_moveIndex runB lt'
        rw [if_neg lt, if_pos lt', Finset.empty_union, Finset.sum_singleton, insert_evB, ihB, wB,
          stateAt_succ (s := b) k' lt', List.drop_eq_getElem_cons lt', ek, List.drop_length]
        simp only [shuffles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rfl
      · exact absurd count (by omega)

include runA runB in
theorem history_isHistory (positiveA : Positive stepA) (positiveB : Positive stepB) :
    (system stepA stepB a b α β).History (history stepA stepB a b α β) where
  conflictFree := by
    intro e inX e' inX' same
    rcases (mem_cfg stepA stepB a b α β).mp inX with ⟨j, _, rfl⟩ | ⟨j, _, rfl⟩ <;>
      rcases (mem_cfg stepA stepB a b α β).mp inX' with ⟨j', _, rfl⟩ | ⟨j', _, rfl⟩
    · have : j = j' := Sum.inl.inj same
      rw [this]
    · exact absurd same (by simp [system, evA, evB, eventCell])
    · exact absurd same (by simp [system, evA, evB, eventCell])
    · have : j = j' := Sum.inr.inj same
      rw [this]
  maximal := by
    show (system stepA stepB a b α β).enabled (cfg stepA stepB a b α β α.length β.length) = ∅
    rw [enabled_cfg, if_neg (lt_irrefl _), if_neg (lt_irrefl _), Finset.union_empty]
  persistent := by
    intro x _ c e enabled cand _ _ different
    have cellE := (mem_enabled stepA stepB a b α β).mp
      ((system stepA stepB a b α β).mem_candidates.mp cand).1
    rw [mem_enabled] at enabled ⊢
    rcases e with e | e
    · -- a move of the first side fires: the enabled cell of the second side stays
      have rightSame : rightCount (insert (Sum.inl e) x) = rightCount x := by
        unfold rightCount
        rw [Finset.filter_insert, if_neg (by simp)]
      rw [rightSame]
      rcases enabled with ⟨_, rfl⟩ | ⟨lt, rfl⟩
      · exfalso
        apply different
        rcases cellE with ⟨_, same⟩ | ⟨_, same⟩
        · exact same
        · simp [system, eventCell] at same
      · exact Or.inr ⟨lt, rfl⟩
    · have leftSame : leftCount (insert (Sum.inr e) x) = leftCount x := by
        unfold leftCount
        rw [Finset.filter_insert, if_neg (by simp)]
      rw [leftSame]
      rcases enabled with ⟨lt, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl ⟨lt, rfl⟩
      · exfalso
        apply different
        rcases cellE with ⟨_, same⟩ | ⟨_, same⟩
        · simp [system, eventCell] at same
        · exact same
  positive := by
    intro x _ c enabled
    rcases (mem_enabled stepA stepB a b α β).mp enabled with ⟨lt, rfl⟩ | ⟨lt, rfl⟩
    · rw [cellTotal_inl]
      exact CausalHistories.total_pos positiveA (mem_step_of_isRun runA _ lt)
    · rw [cellTotal_inr]
      exact CausalHistories.total_pos positiveB (mem_step_of_isRun runB _ lt)

include runA runB in
/-- The cell product of the history is the product of the two runs' likelihoods. -/
theorem history_product :
    ∏ e ∈ history stepA stepB a b α β,
        (system stepA stepB a b α β).weight e /
          (system stepA stepB a b α β).cellTotal ((system stepA stepB a b α β).cell e) =
      pathProb stepA a α * pathProb stepB b β := by
  have disjoint : Disjoint ((Finset.range α.length).image (evA stepA a α))
      ((Finset.range β.length).image (evB stepB b β)) := by
    rw [Finset.disjoint_left]
    intro e inA inB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp inA
    obtain ⟨j', _, same⟩ := Finset.mem_image.mp inB
    exact evA_ne_evB stepA stepB a b α β j j' same.symm
  unfold history cfg
  rw [Finset.prod_union disjoint,
    Finset.prod_image (fun _ _ _ _ same => evA_injective stepA a α same),
    Finset.prod_image (fun _ _ _ _ same => evB_injective stepB b β same),
    pathProb_eq_prod stepA a α, pathProb_eq_prod stepB b β]
  congr 1
  · refine Finset.prod_congr rfl fun k member => ?_
    have lt := Finset.mem_range.mp member
    show candWeight stepA (stateAt a α k) (moveIndex stepA a α k) /
      (system stepA stepB a b α β).cellTotal (.inl k) = _
    rw [candWeight_moveIndex runA lt, cellTotal_inl, moveFactor, List.getElem?_eq_getElem lt]
    rfl
  · refine Finset.prod_congr rfl fun k member => ?_
    have lt := Finset.mem_range.mp member
    show candWeight stepB (stateAt b β k) (moveIndex stepB b β k) /
      (system stepA stepB a b α β).cellTotal (.inr k) = _
    rw [candWeight_moveIndex runB lt, cellTotal_inr, moveFactor, List.getElem?_eq_getElem lt]
    rfl

end Chains

section Rederived

variable {A : Type u} {B : Type v} (stepA : A → List (A × ℝ)) (stepB : B → List (B × ℝ))

/-- **R103's race identity, rederived as the independent case of the cell identity**: the
statement of `CausalHistories.sum_shuffles`, proved through
`CausalCells.CellSystem.History.race_identity`. -/
theorem sum_shuffles_of_race_identity (positiveA : Positive stepA) (positiveB : Positive stepB)
    (α : List (A × ℝ)) (β : List (B × ℝ)) (a : A) (b : B)
    (runA : IsRun stepA a α) (runB : IsRun stepB b β)
    (deadA : IsNormal stepA (endState a α)) (deadB : IsNormal stepB (endState b β)) :
    ((shuffles α β).map (schedProb stepA stepB a b)).sum =
      pathProb stepA a α * pathProb stepB b β := by
  have shuffleSum := lins_sum_cfg runA runB deadA deadB _ 0 0 (Nat.zero_le _) (Nat.zero_le _) rfl
  rw [List.drop_zero, List.drop_zero, stateAt_zero, stateAt_zero, cfg_zero] at shuffleSum
  have reach := reach_cfg runA runB _ 0 0 (Nat.zero_le _) (Nat.zero_le _) rfl
  rw [cfg_zero] at reach
  rw [← shuffleSum, (history_isHistory runA runB positiveA positiveB).race_identity reach]
  exact history_product runA runB

end Rederived

#print axioms stateAt_succ
#print axioms candWeight_moveIndex
#print axioms pathProb_eq_prod
#print axioms total_cfg
#print axioms onHistory_cfg
#print axioms reach_cfg
#print axioms lins_sum_cfg
#print axioms history_isHistory
#print axioms history_product
#print axioms sum_shuffles_of_race_identity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalCellsShuffles

end
