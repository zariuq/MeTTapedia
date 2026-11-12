import Mathlib.Data.List.Nodup
import Mathlib.Order.Basic

/-!
# Rearrangements: interchange cells that keep their events

A run of a deterministic step is a word of labels. An **interchange cell** between two runs from one
state is a derivation by swaps of adjacent firings, each swap made at the state where the pair
fires and justified there by an admissibility relation. A cell is data: it records where each
swap happens, at which state, and so where each event of the first run goes in the second.

* `Rearrangement`: the cells, with `refl` and `swap`; `trans` composes them vertically, and
  `whiskerLeft`, `whiskerRight` put a run before or after a cell.
* `events`: the **event map** of a cell, a map of positions. `events_label`: every event keeps its
  label. `events_trans`, `events_whiskerLeft`, `events_whiskerRight`: the event map is
  functorial for the three compositions.
* `events_eq_of_nodup`: **coherence where events are distinct**: two cells between the same runs
  move every event alike when the target run has no repeated label.
* `symmetry`, `symmetry_events`: two equal labels side by side that the admissibility relation
  allows to swap give a cell from a run to itself whose event map is not the identity. Cells
  keep event identity; the swap relation of traces forgets it.
* `Rearrangement.runs`: where admissible pairs run in both orders to one state and the step is
  deterministic, a cell carries the runs of its source word to runs of its target word, to the
  same final state.
* `Rearrangement.mapAlong`: a map of states that keeps the step carries a cell to a cell with the
  same event map, at every state where each of its swaps stays admissible (`Survives`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

universe uS uL

variable {S : Type uS} {L : Type uL}

/-! ## Runs of a step -/

section Steps

variable (step : S → L → S → Prop)

/-- The runs of a word of labels. -/
inductive Runs : S → List L → S → Prop
  | nil (s : S) : Runs s [] s
  | cons {s t u : S} {a : L} {w : List L} : step s a t → Runs t w u → Runs s (a :: w) u

/-- Two labels fire in both orders from a state, to one state. -/
def Square (s : S) (a b : L) : Prop :=
  ∃ t : S, Runs step s [a, b] t ∧ Runs step s [b, a] t

/-- A step is deterministic when a label fires to at most one state. -/
def Deterministic : Prop :=
  ∀ {s t t' : S} {a : L}, step s a t → step s a t' → t = t'

end Steps

namespace Runs

variable {step : S → L → S → Prop}

theorem append {s t u : S} {first second : List L} (one : Runs step s first t)
    (two : Runs step t second u) : Runs step s (first ++ second) u := by
  induction one with
  | nil s => exact two
  | cons fires _ ih => exact Runs.cons fires (ih two)

theorem split : ∀ (first : List L) {second : List L} {s u : S},
    Runs step s (first ++ second) u → ∃ t : S, Runs step s first t ∧ Runs step t second u
  | [], _, s, _, run => ⟨s, Runs.nil s, run⟩
  | a :: rest, _, _, _, run => by
      cases run with
      | cons fires later =>
          obtain ⟨t, early, late⟩ := split rest later
          exact ⟨t, Runs.cons fires early, late⟩

theorem unique (deterministic : Deterministic step) {s t : S} {w : List L}
    (one : Runs step s w t) : ∀ {t' : S}, Runs step s w t' → t = t' := by
  induction one with
  | nil s =>
      intro t' two
      cases two
      rfl
  | cons fires _ ih =>
      intro t' two
      cases two with
      | cons fires' later' =>
          obtain rfl := deterministic fires fires'
          exact ih later'

end Runs

/-! ## Swapping positions -/

/-- The transposition of the positions `i` and `i + 1`. -/
def swapAt (i j : Nat) : Nat :=
  if j = i then i + 1 else if j = i + 1 then i else j

theorem swapAt_swapAt (i j : Nat) : swapAt i (swapAt i j) = j := by
  unfold swapAt
  split_ifs <;> omega

theorem getElem?_swapAt (before after : List L) (a b : L) (j : Nat) :
    (before ++ b :: a :: after)[swapAt before.length j]? = (before ++ a :: b :: after)[j]? := by
  unfold swapAt
  split_ifs with here next
  · subst here
    rw [List.getElem?_append_right (Nat.le_succ _), List.getElem?_append_right (Nat.le_refl _)]
    simp
  · subst next
    rw [List.getElem?_append_right (Nat.le_refl _), List.getElem?_append_right (Nat.le_succ _)]
    simp
  · rcases Nat.lt_or_ge j before.length with small | large
    · rw [List.getElem?_append_left small, List.getElem?_append_left small]
    · have far : before.length + 2 ≤ j := by omega
      rw [List.getElem?_append_right large, List.getElem?_append_right large]
      obtain ⟨m, hm⟩ : ∃ m, j - before.length = m + 2 := ⟨j - before.length - 2, by omega⟩
      rw [hm]
      rfl

/-! ## Cells -/

section Cells

variable (step : S → L → S → Prop) (adm : S → L → L → Prop)

/-- **An interchange cell** from a word to a word, at a state: a derivation by swaps of adjacent
labels, each made at the state its prefix reaches and allowed there by `adm`. -/
inductive Rearrangement : S → List L → List L → Type (max uS uL)
  | refl (s : S) (w : List L) : Rearrangement s w w
  | swap {s : S} {w' : List L} (before : List L) (mid : S) (a b : L) (after : List L)
      (reach : Runs step s before mid) (admissible : adm mid a b)
      (rest : Rearrangement s (before ++ b :: a :: after) w') :
      Rearrangement s (before ++ a :: b :: after) w'

variable {step adm}

namespace Rearrangement

/-- **The event map** of a cell: where each position of the source word goes in the target word. -/
def events {s : S} : {w w' : List L} → Rearrangement step adm s w w' → Nat → Nat
  | _, _, .refl _ _ => id
  | _, _, .swap before _ _ _ _ _ _ rest => fun j => events rest (swapAt before.length j)
termination_by structural _ _ cell => cell

/-- The number of swaps of a cell. -/
def swaps {s : S} : {w w' : List L} → Rearrangement step adm s w w' → Nat
  | _, _, .refl _ _ => 0
  | _, _, .swap _ _ _ _ _ _ _ rest => swaps rest + 1
termination_by structural _ _ cell => cell

/-- **Every event keeps its label.** -/
theorem events_label : ∀ {s : S} {w w' : List L} (cell : Rearrangement step adm s w w') (j : Nat),
    w'[cell.events j]? = w[j]?
  | _, _, _, .refl _ _, _ => rfl
  | _, _, _, .swap before _ a b after _ _ rest, j =>
      (events_label rest (swapAt before.length j)).trans (getElem?_swapAt before after a b j)

/-- Transport of a cell along equations of its state and words. -/
def cast {s s' : S} {w v w' v' : List L} (hs : s = s') (hw : w = v) (hw' : w' = v')
    (cell : Rearrangement step adm s w w') : Rearrangement step adm s' v v' := by
  subst hs hw hw'
  exact cell

theorem events_cast {s s' : S} {w v w' v' : List L} (hs : s = s') (hw : w = v) (hw' : w' = v')
    (cell : Rearrangement step adm s w w') : (cell.cast hs hw hw').events = cell.events := by
  subst hs hw hw'
  rfl

/-- **Vertical composition** of cells. -/
def trans {s : S} : {w w' w'' : List L} → Rearrangement step adm s w w' →
    Rearrangement step adm s w' w'' → Rearrangement step adm s w w''
  | _, _, _, .refl _ _, second => second
  | _, _, _, .swap before mid a b after reach admissible rest, second =>
      .swap before mid a b after reach admissible (trans rest second)
termination_by structural _ _ _ cell => cell

theorem events_trans : ∀ {s : S} {w w' w'' : List L} (first : Rearrangement step adm s w w')
    (second : Rearrangement step adm s w' w''), (first.trans second).events =
      second.events ∘ first.events
  | _, _, _, _, .refl _ _, _ => rfl
  | _, _, _, _, .swap before _ _ _ _ _ _ rest, second => by
      funext j
      show (rest.trans second).events (swapAt before.length j) =
        second.events (rest.events (swapAt before.length j))
      rw [events_trans rest second]
      rfl

/-- **Whiskering on the left**: a run before a cell. -/
def whiskerLeft {s mid : S} (pre : List L) (reach : Runs step s pre mid) :
    {w w' : List L} → Rearrangement step adm mid w w' →
      Rearrangement step adm s (pre ++ w) (pre ++ w')
  | _, _, .refl _ w => .refl s (pre ++ w)
  | _, _, .swap before mid' a b after reach' admissible rest =>
      Rearrangement.cast rfl (List.append_assoc pre before (a :: b :: after)) rfl
        (.swap (pre ++ before) mid' a b after (reach.append reach') admissible
          (Rearrangement.cast rfl (List.append_assoc pre before (b :: a :: after)).symm rfl
            (whiskerLeft pre reach rest)))
termination_by structural _ _ cell => cell

/-- **Whiskering on the right**: a run after a cell. -/
def whiskerRight {s : S} (post : List L) : {w w' : List L} → Rearrangement step adm s w w' →
    Rearrangement step adm s (w ++ post) (w' ++ post)
  | _, _, .refl _ w => .refl s (w ++ post)
  | _, _, .swap before mid a b after reach admissible rest =>
      Rearrangement.cast rfl (by simp only [List.append_assoc, List.cons_append]) rfl
        (.swap before mid a b (after ++ post) reach admissible
          (Rearrangement.cast rfl (by simp only [List.append_assoc, List.cons_append]) rfl
            (whiskerRight post rest)))
termination_by structural _ _ cell => cell

theorem events_whiskerLeft {s mid : S} (pre : List L) (reach : Runs step s pre mid) :
    ∀ {w w' : List L} (cell : Rearrangement step adm mid w w') (j : Nat),
      (cell.whiskerLeft pre reach).events j =
        if j < pre.length then j else pre.length + cell.events (j - pre.length)
  | _, _, .refl _ _, j => by
      show j = if j < pre.length then j else pre.length + (j - pre.length)
      split_ifs <;> omega
  | _, _, .swap before mid' a b after reach' admissible rest, j => by
      unfold whiskerLeft
      rw [events_cast]
      show (Rearrangement.cast rfl _ rfl (whiskerLeft pre reach rest)).events
          (swapAt (pre ++ before).length j) = _
      rw [events_cast, events_whiskerLeft pre reach rest, List.length_append]
      show _ = if j < pre.length then j else pre.length + rest.events (swapAt before.length (j - pre.length))
      unfold swapAt
      split_ifs <;> first | omega | (congr 1; omega) | (congr 2; omega)

theorem events_whiskerRight {s : S} (post : List L) :
    ∀ {w w' : List L} (cell : Rearrangement step adm s w w'),
      (cell.whiskerRight post).events = cell.events
  | _, _, .refl _ _ => rfl
  | _, _, .swap before mid a b after reach admissible rest => by
      unfold whiskerRight
      rw [events_cast]
      funext j
      show (Rearrangement.cast rfl _ rfl (whiskerRight post rest)).events (swapAt before.length j) =
        rest.events (swapAt before.length j)
      rw [events_cast, events_whiskerRight post rest]

/-! ### Coherence where events are distinct -/

/-- Positions of a list without repetitions are determined by their entries. -/
theorem index_eq_of_nodup {w : List L} (distinct : w.Nodup) {i j : Nat} {x : L}
    (first : w[i]? = some x) (second : w[j]? = some x) : i = j := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp first
  obtain ⟨hj, hy⟩ := List.getElem?_eq_some_iff.mp second
  exact (List.Nodup.getElem_inj_iff distinct).mp (hx.trans hy.symm)

/-- **Coherence where events are distinct**: two cells between the same words, whose target has no
repeated label, move every event of the source alike. -/
theorem events_eq_of_nodup {s : S} {w w' : List L} (distinct : w'.Nodup)
    (one two : Rearrangement step adm s w w') {j : Nat} (inside : j < w.length) :
    one.events j = two.events j := by
  obtain ⟨x, hx⟩ : ∃ x, w[j]? = some x := ⟨w[j], List.getElem?_eq_getElem inside⟩
  exact index_eq_of_nodup distinct ((one.events_label j).trans hx) ((two.events_label j).trans hx)

/-! ### Symmetries -/

/-- **A symmetry**: two equal labels side by side, allowed to swap, give a cell from a run to itself. -/
def symmetry {s mid : S} (before : List L) (reach : Runs step s before mid) (a : L)
    (after : List L) (admissible : adm mid a a) :
    Rearrangement step adm s (before ++ a :: a :: after) (before ++ a :: a :: after) :=
  .swap before mid a a after reach admissible (.refl s _)

/-- **A symmetry moves its two events**: its event map exchanges them, so it is not the identity
cell although its source and target agree. -/
theorem symmetry_events {s mid : S} (before : List L) (reach : Runs step s before mid) (a : L)
    (after : List L) (admissible : adm mid a a) :
    (symmetry before reach a after admissible).events before.length = before.length + 1 ∧
      (Rearrangement.refl s (before ++ a :: a :: after) : Rearrangement step adm s _ _).events
        before.length = before.length := by
  constructor
  · show swapAt before.length before.length = before.length + 1
    simp [swapAt]
  · rfl

/-! ### Cells carry runs -/

/-- **A cell carries the runs of its source to runs of its target**, to the same final state, where
admissible pairs run in both orders to one state and the step is deterministic. -/
theorem runs (deterministic : Deterministic step)
    (square : ∀ {s : S} {a b : L}, adm s a b → Square step s a b) :
    ∀ {s : S} {w w' : List L} (_ : Rearrangement step adm s w w') {t : S},
      Runs step s w t → Runs step s w' t
  | _, _, _, .refl _ _, _, run => run
  | _, _, _, .swap before mid a b after reach admissible rest, t, run => by
      apply runs deterministic square rest
      obtain ⟨mid', early, late⟩ := Runs.split before run
      obtain rfl := Runs.unique (step := step) deterministic reach early
      obtain ⟨t₁, pair, tail⟩ := Runs.split [a, b] (second := after) late
      obtain ⟨t₂, straight, swapped⟩ := square admissible
      obtain rfl := Runs.unique (step := step) deterministic straight pair
      exact early.append (swapped.append tail)

/-! ### Cells along maps of states -/

/-- A cell **survives** a map of states when each of its swaps stays admissible at the image of
the state where it is made. -/
def Survives (place : S → S) {s : S} : {w w' : List L} → Rearrangement step adm s w w' → Prop
  | _, _, .refl _ _ => True
  | _, _, .swap _ mid a b _ _ _ rest => adm (place mid) a b ∧ Survives place rest
termination_by structural _ _ cell => cell

/-- **A cell along a map of states** that keeps the step, where each swap survives. -/
def mapAlong (place : S → S) (keeps : ∀ {s t : S} {a : L}, step s a t → step (place s) a (place t))
    {s : S} : {w w' : List L} → (cell : Rearrangement step adm s w w') → cell.Survives place →
      Rearrangement step adm (place s) w w'
  | _, _, .refl _ w, _ => .refl (place s) w
  | _, _, .swap before mid a b after reach _ rest, survives =>
      .swap before (place mid) a b after (Runs.map place keeps reach) survives.1
        (mapAlong place keeps rest survives.2)
termination_by structural _ _ cell => cell
where
  /-- Runs along a map of states that keeps the step. -/
  Runs.map (place : S → S) (keeps : ∀ {s t : S} {a : L}, step s a t → step (place s) a (place t))
      {s t : S} {w : List L} (run : Runs step s w t) : Runs step (place s) w (place t) := by
    induction run with
    | nil s => exact Runs.nil (place s)
    | cons fires _ ih => exact Runs.cons (keeps fires) ih

theorem events_mapAlong (place : S → S)
    (keeps : ∀ {s t : S} {a : L}, step s a t → step (place s) a (place t)) :
    ∀ {s : S} {w w' : List L} (cell : Rearrangement step adm s w w') (survives : cell.Survives place),
      (cell.mapAlong place keeps survives).events = cell.events
  | _, _, _, .refl _ _, _ => rfl
  | _, _, _, .swap before _ _ _ _ _ _ rest, survives => by
      funext j
      show (rest.mapAlong place keeps survives.2).events (swapAt before.length j) =
        rest.events (swapAt before.length j)
      rw [events_mapAlong place keeps rest survives.2]

/-- Where admissibility is kept by the map, every cell survives it. -/
theorem survives_of_keeps (place : S → S) (keepsAdm : ∀ {s : S} {a b : L}, adm s a b → adm (place s) a b) :
    ∀ {s : S} {w w' : List L} (cell : Rearrangement step adm s w w'), cell.Survives place
  | _, _, _, .refl _ _ => True.intro
  | _, _, _, .swap _ _ _ _ _ _ admissible rest => ⟨keepsAdm admissible, survives_of_keeps place keepsAdm rest⟩

/-! ### The first swap of a cell -/

/-- **A cell between different words begins with a swap**, made where its prefix leads and allowed
there. -/
theorem first_swap {s : S} {w w' : List L} (cell : Rearrangement step adm s w w') (different : w ≠ w') :
    ∃ (before : List L) (mid : S) (a b : L) (after : List L),
      w = before ++ a :: b :: after ∧ Runs step s before mid ∧ adm mid a b := by
  cases cell with
  | refl => exact absurd rfl different
  | swap before mid a b after reach admissible _ => exact ⟨before, mid, a, b, after, rfl, reach, admissible⟩

/-- The positions of two adjacent labels in a word of two. -/
theorem split_two {before after : List L} {a b x y : L} (shape : before ++ a :: b :: after = [x, y]) :
    before = [] ∧ a = x ∧ b = y ∧ after = [] := by
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at shape
      exact ⟨rfl, shape.1, shape.2.1, shape.2.2⟩
  | cons c rest =>
      have lengths := congrArg List.length shape
      simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil] at lengths
      omega

/-- The positions of two adjacent labels in a word of three. -/
theorem split_three {before after : List L} {a b x y z : L}
    (shape : before ++ a :: b :: after = [x, y, z]) :
    (before = [] ∧ a = x ∧ b = y ∧ after = [z]) ∨ (before = [x] ∧ a = y ∧ b = z ∧ after = []) := by
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at shape
      exact Or.inl ⟨rfl, shape.1, shape.2.1, shape.2.2⟩
  | cons c rest =>
      simp only [List.cons_append, List.cons.injEq] at shape
      obtain ⟨rfl, inner⟩ := shape
      obtain ⟨rfl, ha, hb, hafter⟩ := split_two inner
      exact Or.inr ⟨rfl, ha, hb, hafter⟩

/-! ### The interchange law of cells -/

/-- A cell fixes every position beyond its word. -/
theorem events_beyond : ∀ {s : S} {w w' : List L} (cell : Rearrangement step adm s w w') {j : Nat},
    w.length ≤ j → cell.events j = j
  | _, _, _, .refl _ _, _, _ => rfl
  | _, _, _, .swap before _ a b after _ _ rest, j, beyond => by
      have long : (before ++ a :: b :: after).length = before.length + after.length + 2 := by
        simp only [List.length_append, List.length_cons]
        omega
      have fixed : swapAt before.length j = j := by
        unfold swapAt
        split_ifs <;> omega
      show rest.events (swapAt before.length j) = j
      rw [fixed]
      exact events_beyond rest (by
        simp only [List.length_append, List.length_cons] at long beyond ⊢
        omega)

/-- A cell keeps the positions of its word inside the word. -/
theorem events_inside {s : S} {w w' : List L} (cell : Rearrangement step adm s w w') {j : Nat}
    (inside : j < w.length) : cell.events j < w.length := by
  have label := cell.events_label j
  rw [List.getElem?_eq_getElem inside] at label
  have bound := (List.getElem?_eq_some_iff.mp label).1
  rwa [← List.Perm.length_eq (perm cell)] at bound
where
  /-- A cell permutes its word. -/
  perm : ∀ {s : S} {w w' : List L}, Rearrangement step adm s w w' → w.Perm w'
    | _, _, _, .refl _ w => List.Perm.refl w
    | _, _, _, .swap before _ a b after _ _ rest =>
        (List.Perm.append_left before (List.Perm.swap b a after)).trans (perm rest)

/-- **The interchange law of cells**: for a cell `first` from `w₁` to `w₁'` and a cell `second` from
`w₂` to `w₂'` after it, the two horizontal composites, first-then-second and second-then-first,
move every event alike. -/
theorem events_interchange {s mid : S} {w₁ w₁' w₂ w₂' : List L}
    (reach : Runs step s w₁ mid) (reach' : Runs step s w₁' mid)
    (first : Rearrangement step adm s w₁ w₁') (second : Rearrangement step adm mid w₂ w₂') :
    ((first.whiskerRight w₂).trans (second.whiskerLeft w₁' reach')).events =
      ((second.whiskerLeft w₁ reach).trans (first.whiskerRight w₂')).events := by
  have same : w₁'.length = w₁.length := (List.Perm.length_eq (events_inside.perm first)).symm
  funext j
  rw [events_trans, events_trans]
  simp only [Function.comp_apply, events_whiskerRight, events_whiskerLeft, same]
  by_cases small : j < w₁.length
  · rw [if_pos (events_inside first small), if_pos small]
  · have large : w₁.length ≤ j := Nat.le_of_not_lt small
    rw [events_beyond first large, if_neg small, events_beyond first (Nat.le_add_right _ _)]

end Rearrangement

end Cells

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
