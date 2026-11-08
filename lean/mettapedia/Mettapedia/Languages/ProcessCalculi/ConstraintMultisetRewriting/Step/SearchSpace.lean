import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome
import Mathlib.Data.Set.Card

/-!
# Search spaces and the soundness of bounded search

A **search space** (`Space`) unfolds a state into finitely many alternatives, each an answer or a
further state. Its list order is the order a program presents its alternatives in; nothing below
depends on it except the policies of `SearchPolicy`.

## The unbounded semantics (`item`, `Answers`, `multiplicity`)

Positions in the search tree are **addresses**: lists of alternative indices from the root. An
answer of the unbounded semantics is an address carrying an answer; two addresses carrying one
answer are two answers. The multiplicity of an answer is the (possibly infinite) number of its
addresses.

## The budgeted run (`run`, `approx`)

`run n x` explores the tree below `x` to depth `n` and reports addressed answers; `approx n x`
forgets the addresses. It is the outcome algebra applied to the space: an answer is `pure`, an
unexplored state is `unknown`, and a state with budget left is the choice of its alternatives
(`approx_succ`).

* **Soundness**: the reported addressed answers are exactly the answer addresses of length at most
  `n`, each once (`mem_run`, `nodup_run`); hence every multiplicity is bounded by the unbounded one
  (`count_approx_le`).
* **Finished means complete**: a run is finished exactly when every state lies above depth `n`
  (`status_run_eq_finished_iff`), and then it reports every answer of the unbounded semantics with
  its multiplicity (`mem_run_of_finished`, `count_approx_eq_of_finished`).
* **Monotonicity**: runs increase in the information order as the budget grows (`run_mono`): the
  answers only grow, and a finished run stays finished with the same answers
  (`run_eq_of_finished`).
* **Incomplete is never none**: a run is cut off exactly when a state lies at depth `n` or below
  (`status_run_eq_cutOff_iff`); every answer below such a state is an answer of the unbounded
  semantics that the run does not report (`beyond_cut`). A refuted readout is sound for the
  unbounded semantics (`refuted_sound`); a commit is sound at every status (`commit_sound`); a
  definite readout never changes with more budget (`verdict_run_eq_of_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

universe u v w

/-- **A search space**: a state unfolds into finitely many alternatives, each an answer or a
further state. -/
structure Space (σ : Type u) (α : Type v) where
  unfold : σ → List (α ⊕ σ)

/-! ## Alternatives, addressed by their index -/

section Branch

variable {σ : Type u} {α : Type v} {β : Type w}

/-- The alternatives of a state, at indices from `k`, each read by `f` and addressed below its
index. -/
def branch (f : α ⊕ σ → Outcome (List ℕ × β)) : ℕ → List (α ⊕ σ) → Outcome (List ℕ × β)
  | _, [] => 0
  | k, y :: ys => (f y).map (fun p => (k :: p.1, p.2)) + branch f (k + 1) ys

theorem mem_branch (f : α ⊕ σ → Outcome (List ℕ × β)) :
    ∀ (k : ℕ) (l : List (α ⊕ σ)) (w : List ℕ) (b : β),
      (w, b) ∈ (branch f k l).answers ↔
        ∃ i w', w = (k + i) :: w' ∧ ∃ y, l[i]? = some y ∧ (w', b) ∈ (f y).answers
  | k, [], w, b => by simp [branch]
  | k, y :: ys, w, b => by
      simp only [branch, Outcome.add_answers, Outcome.map_answers, Multiset.mem_add,
        Multiset.mem_map, mem_branch f (k + 1) ys w b]
      constructor
      · rintro (⟨⟨w', b'⟩, member, same⟩ | ⟨i, w', rfl, y', get, member⟩)
        · simp only [Prod.mk.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact ⟨0, w', by simp, y, rfl, member⟩
        · exact ⟨i + 1, w', by rw [show k + (i + 1) = k + 1 + i by omega], y', get, member⟩
      · rintro ⟨i, w', rfl, y', get, member⟩
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at get
            subst get
            exact .inl ⟨(w', b), member, by simp⟩
        | succ j =>
            simp only [List.getElem?_cons_succ] at get
            exact .inr ⟨j, w', by rw [show k + (j + 1) = k + 1 + j by omega], y', get, member⟩

theorem branch_status_eq_finished_iff (f : α ⊕ σ → Outcome (List ℕ × β)) :
    ∀ (k : ℕ) (l : List (α ⊕ σ)),
      (branch f k l).status = .finished ↔ ∀ y ∈ l, (f y).status = .finished
  | k, [] => by simp [branch]
  | k, y :: ys => by
      simp [branch, Status.add_eq_finished_iff, branch_status_eq_finished_iff f (k + 1) ys]

theorem nodup_branch (f : α ⊕ σ → Outcome (List ℕ × β)) :
    ∀ (k : ℕ) (l : List (α ⊕ σ)), (∀ y ∈ l, (f y).answers.Nodup) → (branch f k l).answers.Nodup
  | k, [], _ => by simp [branch]
  | k, y :: ys, h => by
      simp only [branch, Outcome.add_answers, Outcome.map_answers]
      refine Multiset.nodup_add.mpr ⟨?_, nodup_branch f (k + 1) ys fun y' m => h y' (by simp [m]), ?_⟩
      · refine (h y (by simp)).map ?_
        rintro ⟨w, b⟩ ⟨w', b'⟩ same
        simp only [Prod.mk.injEq, List.cons.injEq, true_and] at same
        rw [same.1, same.2]
      · rw [Multiset.disjoint_left]
        rintro ⟨w, b⟩ first second
        obtain ⟨⟨w₀, b₀⟩, _, same⟩ := Multiset.mem_map.mp first
        simp only [Prod.mk.injEq] at same
        obtain ⟨i, w', address, _⟩ := (mem_branch f (k + 1) ys w b).mp second
        rw [← same.1] at address
        simp only [List.cons.injEq] at address
        omega

theorem branch_le_branch {f g : α ⊕ σ → Outcome (List ℕ × β)} (h : ∀ y, f y ≤ g y) :
    ∀ (k : ℕ) (l : List (α ⊕ σ)), branch f k l ≤ branch g k l
  | _, [] => le_rfl
  | k, y :: ys => Outcome.add_le_add' (Outcome.map_mono _ (h y)) (branch_le_branch h (k + 1) ys)

theorem branch_map_snd (f : α ⊕ σ → Outcome (List ℕ × β)) :
    ∀ (k : ℕ) (l : List (α ⊕ σ)),
      (branch f k l).map Prod.snd = (l.map fun y => (f y).map Prod.snd).sum
  | _, [] => rfl
  | k, y :: ys => by
      rw [branch, Outcome.map_add, branch_map_snd f (k + 1) ys, List.map_cons, List.sum_cons]
      congr 1
      ext1
      · simp [Outcome.map, Multiset.map_map]
      · rfl

end Branch

namespace Space

variable {σ : Type u} {α : Type v} (S : Space σ α)

/-! ## The unbounded semantics -/

/-- The item at an address below an item. -/
def item : α ⊕ σ → List ℕ → Option (α ⊕ σ)
  | x, [] => some x
  | .inl _, _ :: _ => none
  | .inr s, i :: w => (S.unfold s)[i]?.bind fun y => item y w

@[simp] theorem item_nil (x : α ⊕ σ) : S.item x [] = some x := by cases x <;> rfl
@[simp] theorem item_inl_cons (a : α) (i : ℕ) (w : List ℕ) : S.item (.inl a) (i :: w) = none := rfl
theorem item_inr_cons (s : σ) (i : ℕ) (w : List ℕ) :
    S.item (.inr s) (i :: w) = (S.unfold s)[i]?.bind fun y => S.item y w := rfl

/-- Addresses compose. -/
theorem item_append : ∀ (x : α ⊕ σ) (w w' : List ℕ),
    S.item x (w ++ w') = (S.item x w).bind fun y => S.item y w'
  | x, [], w' => by simp
  | .inl a, i :: w, w' => rfl
  | .inr s, i :: w, w' => by
      rw [List.cons_append, item_inr_cons, item_inr_cons, Option.bind_assoc]
      congr 1
      funext y
      exact item_append y w w'

/-- **The answers of the unbounded semantics**: addresses carrying an answer. -/
def Answers (x : α ⊕ σ) : Set (List ℕ × α) := {p | S.item x p.1 = some (.inl p.2)}

theorem mem_Answers {x : α ⊕ σ} {p : List ℕ × α} :
    p ∈ S.Answers x ↔ S.item x p.1 = some (.inl p.2) := Iff.rfl

/-- **The multiplicity of an answer** in the unbounded semantics: the number of its addresses. -/
noncomputable def multiplicity (x : α ⊕ σ) (a : α) : ℕ∞ :=
  {w : List ℕ | S.item x w = some (.inl a)}.encard

/-! ## The budgeted run -/

/-- **The budget-`n` run**: the tree below an item explored to depth `n`, with addressed answers. -/
def run : ℕ → α ⊕ σ → Outcome (List ℕ × α)
  | _, .inl a => Outcome.pure ([], a)
  | 0, .inr _ => Outcome.unknown
  | n + 1, .inr s => branch (run n) 0 (S.unfold s)

/-- The budget-`n` run without addresses. -/
def approx (n : ℕ) (x : α ⊕ σ) : Outcome α := (S.run n x).map Prod.snd

@[simp] theorem run_inl (n : ℕ) (a : α) : S.run n (.inl a) = Outcome.pure ([], a) := by
  cases n <;> rfl
@[simp] theorem run_zero (s : σ) : S.run 0 (.inr s) = Outcome.unknown := rfl
theorem run_succ (n : ℕ) (s : σ) : S.run (n + 1) (.inr s) = branch (S.run n) 0 (S.unfold s) := rfl

/-- **A bounded search is the outcome algebra applied to the space.** -/
theorem approx_inl (n : ℕ) (a : α) : S.approx n (.inl a) = Outcome.pure a := by
  rw [approx, run_inl, Outcome.map_pure]

theorem approx_zero (s : σ) : S.approx 0 (.inr s) = Outcome.unknown := by
  rw [approx, run_zero, Outcome.map_unknown]

theorem approx_succ (n : ℕ) (s : σ) :
    S.approx (n + 1) (.inr s) = ((S.unfold s).map (S.approx n)).sum := by
  rw [approx, run_succ, branch_map_snd]
  rfl

/-- **Soundness, exactly**: the run reports the answer addresses of length at most the budget. -/
theorem mem_run : ∀ (n : ℕ) (x : α ⊕ σ) (w : List ℕ) (a : α),
    (w, a) ∈ (S.run n x).answers ↔ S.item x w = some (.inl a) ∧ w.length ≤ n
  | n, .inl b, w, a => by
      cases w with
      | nil => simp [eq_comm]
      | cons i w => simp
  | 0, .inr s, w, a => by
      cases w with
      | nil => simp
      | cons i w => simp
  | n + 1, .inr s, w, a => by
      rw [run_succ, mem_branch]
      cases w with
      | nil => simp
      | cons i w =>
          simp only [item_inr_cons, Option.bind_eq_some_iff, List.length_cons, zero_add,
            List.cons.injEq, mem_run n, Nat.add_le_add_iff_right]
          constructor
          · rintro ⟨j, w', ⟨rfl, rfl⟩, y, get, answer, short⟩
            exact ⟨⟨y, get, answer⟩, short⟩
          · rintro ⟨⟨y, get, answer⟩, short⟩
            exact ⟨i, w, ⟨rfl, rfl⟩, y, get, answer, short⟩

/-- Every reported answer is reported once. -/
theorem nodup_run : ∀ (n : ℕ) (x : α ⊕ σ), (S.run n x).answers.Nodup
  | n, .inl a => by simp
  | 0, .inr s => by simp
  | n + 1, .inr s => nodup_branch _ 0 _ fun y _ => nodup_run n y

/-- **A run is finished exactly when every state lies above the budget.** -/
theorem status_run_eq_finished_iff : ∀ (n : ℕ) (x : α ⊕ σ),
    (S.run n x).status = .finished ↔ ∀ w t, S.item x w = some (.inr t) → w.length < n
  | n, .inl a => by
      simp only [run_inl, Outcome.pure_status, true_iff]
      intro w t h
      cases w <;> simp at h
  | 0, .inr s => by
      simp only [run_zero, Outcome.unknown_status, reduceCtorEq, false_iff, not_forall]
      exact ⟨[], s, by simp, by simp⟩
  | n + 1, .inr s => by
      rw [run_succ, branch_status_eq_finished_iff]
      constructor
      · intro finished w t h
        cases w with
        | nil => simp
        | cons i w =>
            rw [item_inr_cons, Option.bind_eq_some_iff] at h
            obtain ⟨y, get, h⟩ := h
            have := (status_run_eq_finished_iff n y).mp
              (finished y (List.mem_iff_getElem?.mpr ⟨i, get⟩)) w t h
            simp only [List.length_cons]
            omega
      · intro shallow y member
        obtain ⟨i, get⟩ := List.mem_iff_getElem?.mp member
        apply (status_run_eq_finished_iff n y).mpr
        intro w t h
        have := shallow (i :: w) t (by rw [item_inr_cons, get]; exact h)
        simp only [List.length_cons] at this
        omega

/-- **Monotonicity in the budget**, in the information order. -/
theorem run_le_run_succ : ∀ (n : ℕ) (x : α ⊕ σ), S.run n x ≤ S.run (n + 1) x
  | n, .inl a => by simp
  | 0, .inr s => bot_le
  | n + 1, .inr s => branch_le_branch (fun y => run_le_run_succ n y) 0 _

theorem run_mono (x : α ⊕ σ) : Monotone fun n => S.run n x :=
  monotone_nat_of_le_succ fun n => S.run_le_run_succ n x

theorem approx_mono (x : α ⊕ σ) : Monotone fun n => S.approx n x :=
  fun _ _ h => Outcome.map_mono _ (S.run_mono x h)

/-- **Finished is stable**: a finished run is the run at every larger budget. -/
theorem run_eq_of_finished {n m : ℕ} {x : α ⊕ σ} (h : n ≤ m)
    (finished : (S.run n x).status = .finished) : S.run m x = S.run n x :=
  Outcome.eq_of_finished_le finished (S.run_mono x h)

theorem answers_subset_of_le {n m : ℕ} {x : α ⊕ σ} (h : n ≤ m) :
    (S.run n x).answers ≤ (S.run m x).answers :=
  Outcome.answers_le_of_le (S.run_mono x h)

/-- **Every reported answer is an answer of the unbounded semantics.** -/
theorem run_sound {n : ℕ} {x : α ⊕ σ} {p : List ℕ × α} (h : p ∈ (S.run n x).answers) :
    p ∈ S.Answers x :=
  ((S.mem_run n x p.1 p.2).mp h).1

/-- A finished run has reached every answer. -/
theorem length_le_of_finished : ∀ {n : ℕ} {x : α ⊕ σ} {w : List ℕ} {a : α},
    (S.run n x).status = .finished → S.item x w = some (.inl a) → w.length ≤ n
  | n, x, [], _, _, _ => Nat.zero_le n
  | n, .inl b, i :: w, a, _, h => by simp at h
  | 0, .inr s, i :: w, a, finished, _ => by simp at finished
  | n + 1, .inr s, i :: w, a, finished, h => by
      rw [item_inr_cons, Option.bind_eq_some_iff] at h
      obtain ⟨y, get, h⟩ := h
      rw [run_succ, branch_status_eq_finished_iff] at finished
      have := length_le_of_finished (finished y (List.mem_iff_getElem?.mpr ⟨i, get⟩)) h
      simp only [List.length_cons]
      omega

/-- **Finished means complete**: a finished run reports every answer of the unbounded semantics. -/
theorem mem_run_of_finished {n : ℕ} {x : α ⊕ σ} (finished : (S.run n x).status = .finished)
    {p : List ℕ × α} (h : p ∈ S.Answers x) : p ∈ (S.run n x).answers :=
  (S.mem_run n x p.1 p.2).mpr ⟨h, S.length_le_of_finished finished h⟩

/-- **Multiplicities are bounded by the unbounded semantics.** -/
theorem count_approx_le [DecidableEq α] (n : ℕ) (x : α ⊕ σ) (a : α) :
    ((S.approx n x).answers.count a : ℕ∞) ≤ S.multiplicity x a := by
  let found : Finset (List ℕ × α) :=
    ⟨(S.run n x).answers.filter (fun p => a = p.2), (S.nodup_run n x).filter _⟩
  have count : (S.approx n x).answers.count a = found.card := by
    simp [approx, Multiset.count_map, found]
  rw [count, ← Set.encard_coe_eq_coe_finsetCard]
  apply Set.encard_le_encard_of_injOn (f := Prod.fst)
  · intro p member
    have member : p ∈ (S.run n x).answers ∧ a = p.2 := Multiset.mem_filter.mp member
    show S.item x p.1 = some (.inl a)
    rw [member.2]
    exact S.run_sound member.1
  · intro p member q member' same
    have member : p ∈ (S.run n x).answers ∧ a = p.2 := Multiset.mem_filter.mp member
    have member' : q ∈ (S.run n x).answers ∧ a = q.2 := Multiset.mem_filter.mp member'
    exact Prod.ext same (member.2.symm.trans member'.2)

/-- **A finished run has the multiplicities of the unbounded semantics.** -/
theorem count_approx_eq_of_finished [DecidableEq α] {n : ℕ} {x : α ⊕ σ}
    (finished : (S.run n x).status = .finished) (a : α) :
    ((S.approx n x).answers.count a : ℕ∞) = S.multiplicity x a := by
  apply le_antisymm (S.count_approx_le n x a)
  let found : Finset (List ℕ × α) :=
    ⟨(S.run n x).answers.filter (fun p => a = p.2), (S.nodup_run n x).filter _⟩
  have count : (S.approx n x).answers.count a = found.card := by
    simp [approx, Multiset.count_map, found]
  rw [count, ← Set.encard_coe_eq_coe_finsetCard]
  have injective : Set.InjOn Prod.fst (found : Set (List ℕ × α)) := by
    intro p member q member' same
    have member : p ∈ (S.run n x).answers ∧ a = p.2 := Multiset.mem_filter.mp member
    have member' : q ∈ (S.run n x).answers ∧ a = q.2 := Multiset.mem_filter.mp member'
    exact Prod.ext same (member.2.symm.trans member'.2)
  rw [← injective.encard_image]
  apply Set.encard_le_encard
  intro w h
  refine ⟨(w, a), ?_, rfl⟩
  exact Multiset.mem_filter.mpr ⟨S.mem_run_of_finished finished h, rfl⟩

/-! ## Incomplete is never none -/

/-- **A run is cut off exactly when a state lies at the budget or below.** -/
theorem status_run_eq_cutOff_iff (n : ℕ) (x : α ⊕ σ) :
    (S.run n x).status = .cutOff ↔ ∃ w t, S.item x w = some (.inr t) ∧ n ≤ w.length := by
  have := S.status_run_eq_finished_iff n x
  constructor
  · intro cut
    by_contra none
    push Not at none
    have finished := this.mpr fun w t h => none w t h
    rw [cut] at finished
    exact Status.noConfusion finished
  · rintro ⟨w, t, h, deep⟩
    apply Status.eq_cutOff_of_ne_finished
    intro finished
    have := this.mp finished w t h
    omega

/-- **Answers beyond a cut are not reported**: every answer below a state at the budget or below
is an answer of the unbounded semantics that the run does not report. -/
theorem beyond_cut {n : ℕ} {x : α ⊕ σ} {w : List ℕ} {t : σ} (state : S.item x w = some (.inr t))
    (deep : n ≤ w.length) {w' : List ℕ} {a : α} (answer : S.item (.inr t) w' = some (.inl a)) :
    (w ++ w', a) ∈ S.Answers x ∧ (w ++ w', a) ∉ (S.run n x).answers := by
  have nonempty : w' ≠ [] := by
    rintro rfl
    simp at answer
  have reached : S.item x (w ++ w') = some (.inl a) := by
    rw [item_append, state]
    exact answer
  refine ⟨reached, fun member => ?_⟩
  have := ((S.mem_run n x _ a).mp member).2
  have : w'.length ≠ 0 := fun zero => nonempty (List.length_eq_zero_iff.mp zero)
  rw [List.length_append] at *
  omega

/-- **A refuted readout is sound for the unbounded semantics**: there are no answers at all. -/
theorem refuted_sound {n : ℕ} {x : α ⊕ σ} (h : (S.approx n x).verdict = .refuted) :
    ∀ w a, S.item x w ≠ some (.inl a) := by
  rw [Outcome.verdict_eq_refuted_iff] at h
  intro w a answer
  have finished : (S.run n x).status = .finished := by
    have := congrArg Outcome.status h
    simpa [approx, Outcome.refuted] using this
  have member := S.mem_run_of_finished finished (p := (w, a)) answer
  have : a ∈ (S.approx n x).answers := Multiset.mem_map.mpr ⟨(w, a), member, rfl⟩
  rw [h] at this
  simp [Outcome.refuted] at this

/-- **A commit is sound at every status.** -/
theorem commit_sound {n : ℕ} {x : α ⊕ σ} (h : (S.approx n x).verdict = .commit) :
    ∃ w a, S.item x w = some (.inl a) ∧ (w, a) ∈ (S.run n x).answers := by
  rw [Outcome.verdict_eq_commit_iff] at h
  obtain ⟨a, member⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨⟨w, a'⟩, found, rfl⟩ := Multiset.mem_map.mp member
  exact ⟨w, a', S.run_sound found, found⟩

/-- **A cut-off run never reads refuted.** -/
theorem verdict_ne_refuted_of_cutOff {n : ℕ} {x : α ⊕ σ} (cut : (S.run n x).status = .cutOff) :
    (S.approx n x).verdict ≠ .refuted :=
  Outcome.verdict_ne_refuted_of_cutOff (by simpa [approx] using cut)

/-- **A definite readout never changes with more budget.** -/
theorem verdict_run_eq_of_le {n m : ℕ} {x : α ⊕ σ} (h : n ≤ m)
    (definite : (S.approx n x).verdict ≠ .suspended) :
    (S.approx m x).verdict = (S.approx n x).verdict :=
  Outcome.verdict_eq_of_le (S.approx_mono x h) definite

end Space

#print axioms mem_branch
#print axioms nodup_branch
#print axioms Space.item_append
#print axioms Space.approx_succ
#print axioms Space.mem_run
#print axioms Space.nodup_run
#print axioms Space.status_run_eq_finished_iff
#print axioms Space.run_mono
#print axioms Space.approx_mono
#print axioms Space.run_eq_of_finished
#print axioms Space.run_sound
#print axioms Space.mem_run_of_finished
#print axioms Space.count_approx_le
#print axioms Space.count_approx_eq_of_finished
#print axioms Space.status_run_eq_cutOff_iff
#print axioms Space.beyond_cut
#print axioms Space.refuted_sound
#print axioms Space.commit_sound
#print axioms Space.verdict_ne_refuted_of_cutOff
#print axioms Space.verdict_run_eq_of_le

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
