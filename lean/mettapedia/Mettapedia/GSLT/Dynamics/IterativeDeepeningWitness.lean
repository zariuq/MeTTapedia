import Mathlib.Data.Nat.Log

/-!
# Iterative deepening for a first-witness observation

A nondeterministic computation is presented as a search space: each state is
either an answer or branches into an ordered list of alternatives (an empty
list is a dead end).  A first-witness observation (`once`) asks for some
answer.  Depth-first order finds one only after exhausting every earlier
alternative, which can be unbounded work before a shallow answer is reached.

This file proves what a depth-bounded depth-first search and iterative
deepening deliver:

* every answer a bounded search reports is an answer of the unbounded search
  (`bounded_sound`);
* every answer within the bound is reported (`bounded_complete`);
* a bounded search that cut no branch has seen every answer
  (`bounded_exhaustive`), so an empty uncut search proves there is none
  (`no_answer_of_uncut_empty`);
* iterative deepening returns an answer whenever one exists within its depth
  limit, and only answers (`deepen_sound`, `deepen_complete`);
* the same holds when the bound is a grade of the states, such as the nesting
  depth of equation applications, which may rise and fall along a path: every
  answer lies within some bound (`exists_within`), and an uncut bounded search
  has every answer within its bound (`within_of_uncut`).

A portfolio then alternates two budgeted strategies with doubling budgets:
depth-first search over a stack of pending states (`dfsRun`) and iterative
deepening that pays for every state each iteration visits (`idFrom`).  Both
are sound and report exhaustion only when there is no answer.  Whenever the
search has an answer the portfolio finds one, and the rounds up to that point
spend less than eight times the work of whichever strategy succeeds sooner
(`portfolio_finds`, `portfolio_finds_of_dfs`); strategies that resume rather
than restart reach it within four times (`Portfolio.resumable_within`).

The last section is the control that fixes the scope: a node whose value
aggregates the answers of its children is not a search node, and bounding the
search below it reports a value that is not an answer (`aggregate_bounded_unsound`).
-/

namespace Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness

universe uS uA

/-- One expansion of a search state. -/
inductive Step (S : Type uS) (A : Type uA) where
  | answer : A → Step S A
  | branch : List S → Step S A

/-- A search space: the expansion of every state. -/
structure Space (S : Type uS) (A : Type uA) where
  expand : S → Step S A

variable {S : Type uS} {A : Type uA} (sp : Space S A)

/-- `a` is an answer of `s` reached through `d` branchings. -/
inductive Reaches : S → A → ℕ → Prop
  | answer {s : S} {a : A} : sp.expand s = .answer a → Reaches s a 0
  | branch {s c : S} {a : A} {d : ℕ} {cs : List S} :
      sp.expand s = .branch cs → c ∈ cs → Reaches c a d → Reaches s a (d + 1)

/-- The answers of the unbounded search from `s`. -/
def IsAnswer (s : S) (a : A) : Prop := ∃ d, Reaches sp s a d

/-- Depth-bounded depth-first search: the answers found, in depth-first order
with their multiplicity, and whether a branch was cut at the bound. -/
def bounded : ℕ → S → List A × Bool
  | 0, s =>
    match sp.expand s with
    | .answer a => ([a], false)
    | .branch cs => ([], !cs.isEmpty)
  | d + 1, s =>
    match sp.expand s with
    | .answer a => ([a], false)
    | .branch cs =>
      ((cs.map (bounded d)).flatMap Prod.fst, (cs.map (bounded d)).any Prod.snd)

theorem bounded_answer {s : S} {a : A} (h : sp.expand s = .answer a) (d : ℕ) :
    bounded sp d s = ([a], false) := by
  cases d <;> simp [bounded, h]

theorem bounded_zero_branch {s : S} {cs : List S} (h : sp.expand s = .branch cs) :
    bounded sp 0 s = ([], !cs.isEmpty) := by
  simp [bounded, h]

theorem bounded_succ_branch {s : S} {cs : List S} (h : sp.expand s = .branch cs)
    (d : ℕ) :
    bounded sp (d + 1) s =
      ((cs.map (bounded sp d)).flatMap Prod.fst,
        (cs.map (bounded sp d)).any Prod.snd) := by
  simp [bounded, h]

/-- Every answer a bounded search reports is an answer, within the bound. -/
theorem bounded_sound : ∀ (d : ℕ) {s : S} {a : A},
    a ∈ (bounded sp d s).1 → ∃ k ≤ d, Reaches sp s a k
  | 0, s, a, h => by
    cases hs : sp.expand s with
    | answer b =>
      rw [bounded_answer sp hs] at h
      simp only [List.mem_singleton] at h
      subst h
      exact ⟨0, le_rfl, .answer hs⟩
    | branch cs =>
      rw [bounded_zero_branch sp hs] at h
      simp at h
  | d + 1, s, a, h => by
    cases hs : sp.expand s with
    | answer b =>
      rw [bounded_answer sp hs] at h
      simp only [List.mem_singleton] at h
      subst h
      exact ⟨0, Nat.zero_le _, .answer hs⟩
    | branch cs =>
      rw [bounded_succ_branch sp hs] at h
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨_, ⟨c, hc, rfl⟩, ha⟩ := h
      obtain ⟨k, hk, hr⟩ := bounded_sound d ha
      exact ⟨k + 1, Nat.succ_le_succ hk, .branch hs hc hr⟩

/-- Every answer within the bound is reported. -/
theorem bounded_complete {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    ∀ {d : ℕ}, k ≤ d → a ∈ (bounded sp d s).1 := by
  induction h with
  | answer hs =>
    intro d _
    rw [bounded_answer sp hs]
    simp
  | @branch s c a k cs hs hc _ ih =>
    intro d hd
    cases d with
    | zero => omega
    | succ d =>
      rw [bounded_succ_branch sp hs]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨_, ⟨c, hc, rfl⟩, ih (by omega)⟩

/-- A bounded search that cut no branch has reported every answer. -/
theorem bounded_exhaustive {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    ∀ {d : ℕ}, (bounded sp d s).2 = false → a ∈ (bounded sp d s).1 := by
  induction h with
  | answer hs =>
    intro d _
    rw [bounded_answer sp hs]
    simp
  | @branch s c a k cs hs hc _ ih =>
    intro d huncut
    cases d with
    | zero =>
      rw [bounded_zero_branch sp hs] at huncut
      have : cs ≠ [] := List.ne_nil_of_mem hc
      simp [List.isEmpty_iff, this] at huncut
    | succ d =>
      rw [bounded_succ_branch sp hs] at huncut ⊢
      have hcut : (bounded sp d c).2 = false := by
        simp only [List.any_eq_false, List.mem_map] at huncut
        have := huncut (bounded sp d c) ⟨c, hc, rfl⟩
        simpa using this
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨_, ⟨c, hc, rfl⟩, ih hcut⟩

/-- An uncut bounded search that found nothing proves the search has no answer. -/
theorem no_answer_of_uncut_empty {s : S} {d : ℕ}
    (huncut : (bounded sp d s).2 = false) (hempty : (bounded sp d s).1 = []) :
    ∀ a, ¬ IsAnswer sp s a := by
  rintro a ⟨k, hk⟩
  have := bounded_exhaustive sp hk huncut
  simp [hempty] at this

/-! ## Graded search

A machine bounds a derivation by a grade of its states — for example the
nesting depth of equation applications — rather than by the number of
branchings on a path.  Grades may rise and fall along a path.  The bounded
search keeps the states whose grade is within the bound and prunes the rest;
it has cut something exactly when a kept state has a child above the bound. -/

section Graded

variable (grade : S → ℕ)

/-- `a` is reached from `s` through states of grade at most `d`. -/
inductive Within (d : ℕ) : S → A → Prop
  | answer {s : S} {a : A} : grade s ≤ d → sp.expand s = .answer a → Within d s a
  | branch {s c : S} {a : A} {cs : List S} :
      grade s ≤ d → sp.expand s = .branch cs → c ∈ cs → Within d c a → Within d s a

/-- `t` is reached from `s` through states of grade at most `d` (`t` itself
may lie above it). -/
inductive ReachWithin (d : ℕ) : S → S → Prop
  | refl (s : S) : ReachWithin d s s
  | step {s c t : S} {cs : List S} :
      grade s ≤ d → sp.expand s = .branch cs → c ∈ cs → ReachWithin d c t →
        ReachWithin d s t

/-- The bounded search from `s` cut nothing: every state it reaches is within
the bound. -/
def Uncut (d : ℕ) (s : S) : Prop := ∀ t, ReachWithin sp grade d s t → grade t ≤ d

theorem within_sound {d : ℕ} {s : S} {a : A} (h : Within sp grade d s a) :
    IsAnswer sp s a := by
  induction h with
  | answer _ hs => exact ⟨0, .answer hs⟩
  | branch _ hs hc _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .branch hs hc hk⟩

theorem within_mono {d e : ℕ} (hde : d ≤ e) {s : S} {a : A}
    (h : Within sp grade d s a) : Within sp grade e s a := by
  induction h with
  | answer hg hs => exact .answer (le_trans hg hde) hs
  | branch hg hs hc _ ih => exact .branch (le_trans hg hde) hs hc ih

/-- Every answer lies within some bound: the largest grade on its path. -/
theorem exists_within {s : S} {a : A} (h : IsAnswer sp s a) :
    ∃ d, Within sp grade d s a := by
  obtain ⟨k, hk⟩ := h
  induction hk with
  | @answer s a hs => exact ⟨grade s, .answer le_rfl hs⟩
  | @branch s c a k cs hs hc _ ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨max d (grade s),
      .branch (le_max_right _ _) hs hc (within_mono sp grade (le_max_left _ _) hd)⟩

/-- An uncut bounded search has every answer within its bound. -/
theorem within_of_uncut {d : ℕ} {s : S} (huncut : Uncut sp grade d s) {a : A}
    (h : IsAnswer sp s a) : Within sp grade d s a := by
  obtain ⟨k, hk⟩ := h
  induction hk with
  | @answer t b ht => exact .answer (huncut t (.refl t)) ht
  | @branch t c b k cs ht hc _ ih =>
    have hgt : grade t ≤ d := huncut t (.refl t)
    refine .branch hgt ht hc (ih ?_)
    intro u hu
    exact huncut u (.step hgt ht hc hu)

/-- An uncut bounded search that found no answer within its bound proves the
search has no answer. -/
theorem no_answer_of_uncut_none {d : ℕ} {s : S} (huncut : Uncut sp grade d s)
    (hnone : ∀ a, ¬ Within sp grade d s a) : ∀ a, ¬ IsAnswer sp s a :=
  fun a ha => hnone a (within_of_uncut sp grade huncut ha)

end Graded

/-! ## Iterative deepening -/

/-- Iterative deepening up to depth `D`: bounds `0, 1, …, D` in increasing
order, and the first answer of the first bounded search that reports one. -/
def deepen (s : S) : ℕ → Option A
  | 0 => (bounded sp 0 s).1.head?
  | D + 1 => (deepen s D).or (bounded sp (D + 1) s).1.head?

theorem mem_of_head? {l : List A} {a : A} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons b bs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp

theorem deepen_sound {s : S} : ∀ {D : ℕ} {a : A}, deepen sp s D = some a →
    IsAnswer sp s a
  | 0, a, h => by
    obtain ⟨k, _, hr⟩ := bounded_sound sp 0 (mem_of_head? h)
    exact ⟨k, hr⟩
  | D + 1, a, h => by
    unfold deepen at h
    cases hD : deepen sp s D with
    | some b =>
      rw [hD] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact deepen_sound hD
    | none =>
      rw [hD] at h
      simp only [Option.none_or] at h
      obtain ⟨k, _, hr⟩ := bounded_sound sp (D + 1) (mem_of_head? h)
      exact ⟨k, hr⟩

theorem deepen_complete {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    ∀ {D : ℕ}, k ≤ D → (deepen sp s D).isSome
  | D, hk => by
    have head_some : ∀ d, k ≤ d → a ∈ (bounded sp d s).1 →
        ((bounded sp d s).1.head?).isSome := by
      intro d _ hmem
      cases hl : (bounded sp d s).1 with
      | nil => simp [hl] at hmem
      | cons b bs => simp
    induction D with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      exact head_some 0 le_rfl (bounded_complete sp h le_rfl)
    | succ D ih =>
      unfold deepen
      rcases Nat.lt_or_ge D k with hDk | hkD
      · have hk' : k = D + 1 := by omega
        subst hk'
        cases hD : deepen sp s D with
        | some b => simp
        | none =>
          simpa [Option.none_or] using
            head_some (D + 1) le_rfl (bounded_complete sp h le_rfl)
      · cases hD : deepen sp s D with
        | some b => simp
        | none =>
          have := ih hkD
          rw [hD] at this
          simp at this

/-! ## A doubling portfolio of budgeted strategies -/

/-- The outcome of one budgeted attempt at a first-witness observation. -/
inductive Attempt (A : Type uA) where
  | found : A → Attempt A
  | exhausted : Attempt A
  | incomplete : Attempt A

/-- The budget ran out, or a bound cut a branch. -/
def Attempt.isIncomplete : Attempt A → Bool
  | .incomplete => true
  | _ => false

/-- A budgeted strategy for the observation of `s`: every answer it reports
is an answer, and it reports exhaustion only when there is none. -/
structure Strategy (s : S) where
  run : ℕ → Attempt A
  sound : ∀ b a, run b = .found a → IsAnswer sp s a
  exhausted_honest : ∀ b, run b = .exhausted → ∀ a, ¬ IsAnswer sp s a

variable {sp} in
/-- The strategy finds an answer with every budget from `w` on. -/
def Strategy.SucceedsFrom {s : S} (x : Strategy sp s) (w : ℕ) : Prop :=
  ∀ b, w ≤ b → ∃ a, x.run b = .found a

namespace Portfolio

variable {sp} {s : S}

/-- The budget of round `j`: each strategy runs with `2 ^ j`. -/
def budget (j : ℕ) : ℕ := 2 ^ j

/-- Round `j`: the first strategy's attempt unless it was incomplete, then
the second strategy's attempt. -/
def round (x y : Strategy sp s) (j : ℕ) : Attempt A :=
  if (x.run (budget j)).isIncomplete then y.run (budget j) else x.run (budget j)

theorem round_found_sound (x y : Strategy sp s) {j : ℕ} {a : A}
    (h : round x y j = .found a) : IsAnswer sp s a := by
  unfold round at h
  split_ifs at h
  · exact y.sound _ _ h
  · exact x.sound _ _ h

theorem round_exhausted_honest (x y : Strategy sp s) {j : ℕ}
    (h : round x y j = .exhausted) : ∀ a, ¬ IsAnswer sp s a := by
  unfold round at h
  split_ifs at h
  · exact y.exhausted_honest _ h
  · exact x.exhausted_honest _ h

/-- Once the budget reaches a budget from which either strategy succeeds, the
round finds an answer. -/
theorem round_found (x y : Strategy sp s) {w j : ℕ}
    (hw : x.SucceedsFrom w ∨ y.SucceedsFrom w) (hj : w ≤ budget j) :
    ∃ a, round x y j = .found a := by
  unfold round
  rcases hw with hx | hy
  · obtain ⟨a, ha⟩ := hx _ hj
    exact ⟨a, by simp [ha, Attempt.isIncomplete]⟩
  · split_ifs with hinc
    · exact hy _ hj
    · obtain ⟨a, ha⟩ := hy _ hj
      rcases hx : x.run (budget j) with b | _ | _
      · exact ⟨b, rfl⟩
      · exact absurd (y.sound _ _ ha) (x.exhausted_honest _ hx a)
      · simp [hx, Attempt.isIncomplete] at hinc

/-- The first round whose budget covers `w`. -/
def roundFor (w : ℕ) : ℕ := Nat.clog 2 w

theorem covers (w : ℕ) : w ≤ budget (roundFor w) :=
  Nat.le_pow_clog Nat.one_lt_two w

/-- The budget spent in rounds `0 .. j`: two attempts of `2 ^ i` each. -/
def spent : ℕ → ℕ
  | 0 => 2 * budget 0
  | j + 1 => spent j + 2 * budget (j + 1)

theorem spent_eq (j : ℕ) : spent j + 2 = 4 * 2 ^ j := by
  induction j with
  | zero => simp [spent, budget]
  | succ j ih =>
    show spent j + 2 * budget (j + 1) + 2 = 4 * 2 ^ (j + 1)
    unfold budget
    rw [Nat.pow_succ]
    omega

/-- Work bound: rounds `0` through the first round that covers a success
budget `w ≥ 1` spend less than `8 w`. -/
theorem spent_lt (w : ℕ) (hw : 1 ≤ w) : spent (roundFor w) < 8 * w := by
  have hlt : 2 ^ roundFor w < 2 * w := by
    unfold roundFor
    rcases Nat.lt_or_ge 1 w with h1 | h1
    · have hpred := Nat.pow_pred_clog_lt_self Nat.one_lt_two h1
      have hpos : 0 < Nat.clog 2 w := Nat.clog_pos Nat.one_lt_two h1
      obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 w = m + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hm] at hpred ⊢
      rw [Nat.pow_succ]
      simp only [Nat.pred_succ] at hpred
      omega
    · have : w = 1 := le_antisymm h1 hw
      subst this
      simp
  have := spent_eq (roundFor w)
  omega

/-! ### Resumable strategies

A strategy whose run can be continued, rather than restarted, reaches its
outcome at a cumulative budget.  Alternating two of them with quanta
`2 ^ i` gives each `2 ^ (j + 1) - 1` units by the end of round `j`; `roundAt`
reads both outcomes there. -/

/-- Both strategies' outcomes at a common budget `b`: the first unless it is
incomplete, then the second. -/
def roundAt (x y : Strategy sp s) (b : ℕ) : Attempt A :=
  if (x.run b).isIncomplete then y.run b else x.run b

theorem round_eq_roundAt (x y : Strategy sp s) (j : ℕ) :
    round x y j = roundAt x y (budget j) := rfl

theorem roundAt_found_sound (x y : Strategy sp s) {b : ℕ} {a : A}
    (h : roundAt x y b = .found a) : IsAnswer sp s a := by
  unfold roundAt at h
  split_ifs at h
  · exact y.sound _ _ h
  · exact x.sound _ _ h

theorem roundAt_exhausted_honest (x y : Strategy sp s) {b : ℕ}
    (h : roundAt x y b = .exhausted) : ∀ a, ¬ IsAnswer sp s a := by
  unfold roundAt at h
  split_ifs at h
  · exact y.exhausted_honest _ h
  · exact x.exhausted_honest _ h

theorem roundAt_found (x y : Strategy sp s) {w b : ℕ}
    (hw : x.SucceedsFrom w ∨ y.SucceedsFrom w) (hb : w ≤ b) :
    ∃ a, roundAt x y b = .found a := by
  unfold roundAt
  rcases hw with hx | hy
  · obtain ⟨a, ha⟩ := hx _ hb
    exact ⟨a, by simp [ha, Attempt.isIncomplete]⟩
  · split_ifs with hinc
    · exact hy _ hb
    · obtain ⟨a, ha⟩ := hy _ hb
      rcases hx : x.run b with c | _ | _
      · exact ⟨c, rfl⟩
      · exact absurd (y.sound _ _ ha) (x.exhausted_honest _ hx a)
      · simp [hx, Attempt.isIncomplete] at hinc

/-- The units each resumable strategy has run by the end of round `j`. -/
def cumulative (j : ℕ) : ℕ := 2 ^ (j + 1) - 1

/-- The first round by whose end each strategy has run `w` units. -/
def resumableRoundFor (w : ℕ) : ℕ := Nat.clog 2 (w + 1) - 1

/-- Work bound for resumable strategies: by the end of the first round that
gives each strategy a success budget `w ≥ 1`, the rounds have spent less
than `4 w`. -/
theorem resumable_within (w : ℕ) (hw : 1 ≤ w) :
    w ≤ cumulative (resumableRoundFor w) ∧
      2 * cumulative (resumableRoundFor w) < 4 * w := by
  have h1 : 1 < w + 1 := by omega
  have hpos : 0 < Nat.clog 2 (w + 1) := Nat.clog_pos Nat.one_lt_two h1
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (w + 1) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hge := Nat.le_pow_clog Nat.one_lt_two (w + 1)
  have hlt := Nat.pow_pred_clog_lt_self Nat.one_lt_two h1
  rw [hk] at hge hlt
  simp only [Nat.pred_succ] at hlt
  unfold cumulative resumableRoundFor
  rw [hk, Nat.add_sub_cancel]
  rw [Nat.pow_succ] at hge ⊢
  omega

end Portfolio

/-! ## The two strategies of the portfolio -/

/-- Depth-first search over a stack of pending states, one expansion per unit
of budget. -/
def dfsRun : ℕ → List S → Attempt A
  | 0, _ => .incomplete
  | _ + 1, [] => .exhausted
  | fuel + 1, t :: rest =>
    match sp.expand t with
    | .answer a => .found a
    | .branch cs => dfsRun fuel (cs ++ rest)

theorem isAnswer_of_child {t c : S} {cs : List S} {a : A}
    (ht : sp.expand t = .branch cs) (hc : c ∈ cs) (h : IsAnswer sp c a) :
    IsAnswer sp t a := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, .branch ht hc hk⟩

theorem child_of_isAnswer {t : S} {cs : List S} {a : A}
    (ht : sp.expand t = .branch cs) (h : IsAnswer sp t a) :
    ∃ c ∈ cs, IsAnswer sp c a := by
  obtain ⟨k, hk⟩ := h
  cases hk with
  | answer h' => rw [ht] at h'; cases h'
  | branch h' hc hr =>
    rw [ht] at h'
    cases h'
    exact ⟨_, hc, _, hr⟩

theorem dfsRun_sound {s : S} : ∀ (fuel : ℕ) (stack : List S) {a : A},
    (∀ t ∈ stack, ∀ b, IsAnswer sp t b → IsAnswer sp s b) →
    dfsRun sp fuel stack = .found a → IsAnswer sp s a
  | 0, _, _, _, h => by simp [dfsRun] at h
  | _ + 1, [], _, _, h => by simp [dfsRun] at h
  | fuel + 1, t :: rest, a, hbelow, h => by
    cases ht : sp.expand t with
    | answer b =>
      simp only [dfsRun, ht, Attempt.found.injEq] at h
      subst h
      exact hbelow t (by simp) _ ⟨0, .answer ht⟩
    | branch cs =>
      simp only [dfsRun, ht] at h
      refine dfsRun_sound fuel (cs ++ rest) ?_ h
      intro u hu b hb
      rcases List.mem_append.mp hu with hc | hr
      · exact hbelow t (by simp) b (isAnswer_of_child sp ht hc hb)
      · exact hbelow u (by simp [hr]) b hb

theorem dfsRun_exhausted {s : S} : ∀ (fuel : ℕ) (stack : List S),
    (∀ a, IsAnswer sp s a → ∃ t ∈ stack, IsAnswer sp t a) →
    dfsRun sp fuel stack = .exhausted → ∀ a, ¬ IsAnswer sp s a
  | 0, _, _, h => by simp [dfsRun] at h
  | _ + 1, [], hcover, _ => by
    intro a ha
    obtain ⟨t, ht, _⟩ := hcover a ha
    simp at ht
  | fuel + 1, t :: rest, hcover, h => by
    cases ht : sp.expand t with
    | answer b => simp [dfsRun, ht] at h
    | branch cs =>
      simp only [dfsRun, ht] at h
      refine dfsRun_exhausted fuel (cs ++ rest) ?_ h
      intro a ha
      obtain ⟨u, hu, hua⟩ := hcover a ha
      rcases List.mem_cons.mp hu with rfl | hr
      · obtain ⟨c, hc, hca⟩ := child_of_isAnswer sp ht hua
        exact ⟨c, List.mem_append_left _ hc, hca⟩
      · exact ⟨u, List.mem_append_right _ hr, hua⟩

theorem dfsRun_mono : ∀ (fuel : ℕ) (stack : List S) {a : A} (m : ℕ),
    dfsRun sp fuel stack = .found a → dfsRun sp (fuel + m) stack = .found a
  | 0, _, _, _, h => by simp [dfsRun] at h
  | _ + 1, [], _, _, h => by simp [dfsRun] at h
  | fuel + 1, t :: rest, a, m, h => by
    rw [show fuel + 1 + m = (fuel + m) + 1 by omega]
    cases ht : sp.expand t with
    | answer b =>
      simp only [dfsRun, ht] at h ⊢
      exact h
    | branch cs =>
      simp only [dfsRun, ht] at h ⊢
      exact dfsRun_mono fuel (cs ++ rest) m h

/-- Depth-first search as a portfolio strategy. -/
def dfsStrategy (s : S) : Strategy sp s where
  run b := dfsRun sp b [s]
  sound b _ h := dfsRun_sound sp b [s] (by
    intro t ht c hc
    simp only [List.mem_singleton] at ht
    subst ht
    exact hc) h
  exhausted_honest b h := dfsRun_exhausted sp b [s] (fun a ha => ⟨s, by simp, ha⟩) h

theorem dfsStrategy_succeeds {s : S} {w : ℕ} {a : A}
    (h : dfsRun sp w [s] = .found a) : (dfsStrategy sp s).SucceedsFrom w := by
  intro b hb
  refine ⟨a, ?_⟩
  have := dfsRun_mono sp w [s] (b - w) h
  rwa [show w + (b - w) = b by omega] at this

/-- The states a bounded search visits. -/
def boundedWork : ℕ → S → ℕ
  | 0, _ => 1
  | d + 1, s =>
    match sp.expand s with
    | .answer _ => 1
    | .branch cs => 1 + (cs.map (boundedWork d)).sum

theorem boundedWork_pos (d : ℕ) (s : S) : 0 < boundedWork sp d s := by
  cases d with
  | zero => simp [boundedWork]
  | succ d =>
    unfold boundedWork
    split <;> omega

/-- Iterative deepening from bound `d` with a work budget: each iteration pays
for the states it visits, and one that does not fit leaves the attempt
incomplete. -/
def idFrom (s : S) (budget d : ℕ) : Attempt A :=
  if _hfit : boundedWork sp d s ≤ budget then
    match (bounded sp d s).1.head? with
    | some a => .found a
    | none =>
      if (bounded sp d s).2 then idFrom s (budget - boundedWork sp d s) (d + 1)
      else .exhausted
  else .incomplete
termination_by budget
decreasing_by
  have := boundedWork_pos sp d s
  omega

theorem idFrom_sound {s : S} : ∀ (budget d : ℕ) {a : A},
    idFrom sp s budget d = .found a → IsAnswer sp s a := by
  intro budget
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
    intro d a h
    rw [idFrom] at h
    by_cases hfit : boundedWork sp d s ≤ budget
    · rw [dif_pos hfit] at h
      cases hhead : (bounded sp d s).1.head? with
      | some b =>
        simp only [hhead, Attempt.found.injEq] at h
        subst h
        obtain ⟨k, _, hr⟩ := bounded_sound sp d (mem_of_head? hhead)
        exact ⟨k, hr⟩
      | none =>
        by_cases hcut : (bounded sp d s).2 = true
        · simp only [hhead, hcut, if_true] at h
          exact ih _ (by have := boundedWork_pos sp d s; omega) (d + 1) h
        · simp [hhead, hcut] at h
    · rw [dif_neg hfit] at h
      cases h

theorem idFrom_exhausted {s : S} : ∀ (budget d : ℕ),
    idFrom sp s budget d = .exhausted → ∀ a, ¬ IsAnswer sp s a := by
  intro budget
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
    intro d h
    rw [idFrom] at h
    by_cases hfit : boundedWork sp d s ≤ budget
    · rw [dif_pos hfit] at h
      cases hhead : (bounded sp d s).1.head? with
      | some b => simp [hhead] at h
      | none =>
        by_cases hcut : (bounded sp d s).2 = true
        · simp only [hhead, hcut, if_true] at h
          exact ih _ (by have := boundedWork_pos sp d s; omega) (d + 1) h
        · have hempty : (bounded sp d s).1 = [] := by
            cases hl : (bounded sp d s).1 with
            | nil => rfl
            | cons x xs => simp [hl] at hhead
          exact no_answer_of_uncut_empty sp (by simpa using hcut) hempty
    · rw [dif_neg hfit] at h
      cases h

/-- The work iterative deepening spends on bounds `d, d + 1, …, d + n`. -/
def idWork (s : S) (d : ℕ) : ℕ → ℕ
  | 0 => boundedWork sp d s
  | n + 1 => boundedWork sp d s + idWork s (d + 1) n

theorem idFrom_succeeds {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    ∀ (n d budget : ℕ), d + n = k → idWork sp s d n ≤ budget →
      ∃ b, idFrom sp s budget d = .found b := by
  intro n
  induction n with
  | zero =>
    intro d budget hdk hwork
    simp only [Nat.add_zero] at hdk
    subst hdk
    simp only [idWork] at hwork
    have hmem := bounded_complete sp h (le_refl d)
    rw [idFrom, dif_pos hwork]
    cases hl : (bounded sp d s).1 with
    | nil => simp [hl] at hmem
    | cons x xs => exact ⟨x, by simp⟩
  | succ n ih =>
    intro d budget hdk hwork
    simp only [idWork] at hwork
    rw [idFrom, dif_pos (by omega)]
    cases hl : (bounded sp d s).1 with
    | cons x xs => exact ⟨x, by simp⟩
    | nil =>
      simp only [List.head?_nil]
      by_cases hcut : (bounded sp d s).2
      · rw [if_pos hcut]
        exact ih (d + 1) _ (by omega) (by omega)
      · exfalso
        exact no_answer_of_uncut_empty sp (by simpa using hcut) hl a ⟨k, h⟩

/-- Iterative deepening from bound zero as a portfolio strategy. -/
def idStrategy (s : S) : Strategy sp s where
  run b := idFrom sp s b 0
  sound b _ h := idFrom_sound sp b 0 h
  exhausted_honest b h := idFrom_exhausted sp b 0 h

theorem idStrategy_succeeds {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    (idStrategy sp s).SucceedsFrom (idWork sp s 0 k) := by
  intro b hb
  exact idFrom_succeeds sp h k 0 b (by omega) hb

theorem idWork_pos (s : S) (d n : ℕ) : 1 ≤ idWork sp s d n := by
  cases n with
  | zero => exact boundedWork_pos sp d s
  | succ n => simp only [idWork]; have := boundedWork_pos sp d s; omega

/-- The portfolio of depth-first search and iterative deepening finds an
answer whenever the search has one, by the round whose budget covers the work
iterative deepening needs; the rounds up to it spend less than eight times
that work. -/
theorem portfolio_finds {s : S} {a : A} {k : ℕ} (h : Reaches sp s a k) :
    (∃ b, Portfolio.round (dfsStrategy sp s) (idStrategy sp s)
        (Portfolio.roundFor (idWork sp s 0 k)) = .found b) ∧
      Portfolio.spent (Portfolio.roundFor (idWork sp s 0 k)) < 8 * idWork sp s 0 k :=
  ⟨Portfolio.round_found _ _ (Or.inr (idStrategy_succeeds sp h))
      (Portfolio.covers _),
    Portfolio.spent_lt _ (idWork_pos sp s 0 k)⟩

/-- When depth-first search finds an answer with budget `w`, the portfolio
finds one by the round covering `w`, again within eight times `w`. -/
theorem portfolio_finds_of_dfs {s : S} {w : ℕ} {a : A}
    (h : dfsRun sp w [s] = .found a) (hw : 1 ≤ w) :
    (∃ b, Portfolio.round (dfsStrategy sp s) (idStrategy sp s)
        (Portfolio.roundFor w) = .found b) ∧
      Portfolio.spent (Portfolio.roundFor w) < 8 * w :=
  ⟨Portfolio.round_found _ _ (Or.inl (dfsStrategy_succeeds sp h))
      (Portfolio.covers _),
    Portfolio.spent_lt _ hw⟩

/-! ## Scope: aggregation is not a search node -/

/-- A node that counts its children's answers.  Treating it as a leaf of a
bounded search reports the count of the bounded answers, which differs from
the count of all answers once a branch is cut. -/
def countSpace : Space ℕ ℕ where
  expand
    | 0 => .branch [1, 2]
    | 1 => .answer 7
    | 2 => .branch [3]
    | 3 => .answer 8
    | _ => .branch []

/-- The true count of answers below state `0` is two. -/
theorem countSpace_answers : IsAnswer countSpace 0 7 ∧ IsAnswer countSpace 0 8 :=
  ⟨⟨1, .branch (c := 1) (cs := [1, 2]) rfl (by simp) (.answer rfl)⟩,
    ⟨2, .branch (c := 2) (cs := [1, 2]) rfl (by simp)
      (.branch (c := 3) (cs := [3]) rfl (by simp) (.answer rfl))⟩⟩

/-- Bounded at depth one, the search reports one answer and a cut: an
aggregate computed from it (a count of `1`) is not the count of the search. -/
theorem aggregate_bounded_unsound :
    bounded countSpace 1 0 = ([7], true) := by
  rfl

end Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
