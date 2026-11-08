import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchPolicy

/-!
# When every policy finishes

A search finishes under some policy exactly when its tree is finite, and then **every** policy
finishes within one common budget: the number of items of the tree (`finishes`, `size`). The
proof counts the items below the pending entries (`measure`); each step of the machine removes
exactly one.

Consequences for the verbs:

* `all` is defined exactly when some budgeted run is finished, for every policy alike
  (`all_dom_iff`, `all_dom_iff_dom`), and then it is the collection of the unbounded search
  (`collect_eq_all`).
* `within` is monotone in its budget, in the information order (`within_mono`); a cut-off `within`
  never reads refuted (`within_verdict_ne_refuted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

universe u v w

theorem map_finRange_getElem {β : Type u} {γ : Type v} (l : List β) (g : β → γ) :
    (List.finRange l.length).map (fun i => g l[i]) = l.map g := by
  conv_rhs => rw [← List.ofFn_getElem (xs := l)]
  rw [List.finRange, List.map_ofFn, List.map_ofFn]
  rfl

namespace Space

variable {σ : Type u} {α : Type v} (S : Space σ α)

/-- The number of items within depth `n` below an item. -/
def size : ℕ → α ⊕ σ → ℕ
  | _, .inl _ => 1
  | 0, .inr _ => 1
  | n + 1, .inr s => 1 + ((S.unfold s).map (size n)).sum

theorem one_le_size : ∀ (n : ℕ) (x : α ⊕ σ), 1 ≤ S.size n x
  | n, .inl _ => by cases n <;> simp [size]
  | 0, .inr _ => le_rfl
  | n + 1, .inr _ => Nat.le_add_right 1 _

/-- The items below the pending entries, within a depth bound. -/
def measure (N : ℕ) (pending : List (List ℕ × (α ⊕ σ))) : ℕ :=
  (pending.map fun e => S.size (N - e.1.length) e.2).sum

theorem measure_cons (N : ℕ) (e : List ℕ × (α ⊕ σ)) (rest : List (List ℕ × (α ⊕ σ))) :
    S.measure N (e :: rest) = S.size (N - e.1.length) e.2 + S.measure N rest := by
  simp [measure]

theorem measure_perm (N : ℕ) {l l' : List (List ℕ × (α ⊕ σ))} (h : l.Perm l') :
    S.measure N l = S.measure N l' :=
  (h.map _).sum_eq

theorem measure_append (N : ℕ) (l l' : List (List ℕ × (α ⊕ σ))) :
    S.measure N (l ++ l') = S.measure N l + S.measure N l' := by
  simp [measure]

theorem measure_children (N : ℕ) (w : List ℕ) (s : σ) :
    S.measure N (S.children w s) = ((S.unfold s).map (S.size (N - (w.length + 1)))).sum := by
  simp only [measure, children, List.map_map, Function.comp_def, List.length_append,
    List.length_singleton]
  congr 1
  exact map_finRange_getElem (S.unfold s) (S.size (N - (w.length + 1)))

theorem pos_measure (N : ℕ) {l : List (List ℕ × (α ⊕ σ))} (h : l ≠ []) : 0 < S.measure N l := by
  obtain ⟨e, rest, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [measure_cons]
  have := S.one_le_size (N - e.1.length) e.2
  omega

variable (P : Policy (List ℕ × (α ⊕ σ)))

/-- **Each step removes exactly one item**, while the states pending are above the depth bound. -/
theorem measure_step {N : ℕ} {x : α ⊕ σ} (finished : (S.run N x).status = .finished)
    {c : Config σ α} {done : List (List ℕ)} (covers : S.Covers x c done) (busy : c.pending ≠ []) :
    S.measure N (S.step P c).pending + 1 = S.measure N c.pending := by
  obtain ⟨found, pending⟩ := c
  match pending, covers, busy with
  | (w, .inl a) :: rest, _, _ =>
      show S.measure N rest + 1 = S.measure N ((w, .inl a) :: rest)
      rw [measure_cons]
      cases h : N - w.length <;> simp [size] <;> omega
  | (w, .inr s) :: rest, covers, _ =>
      show S.measure N (P.insert (S.children w s) rest) + 1 = S.measure N ((w, .inr s) :: rest)
      have state := covers.pending_valid _ (List.mem_cons_self ..)
      have shallow := (S.status_run_eq_finished_iff N x).mp finished w s state
      rw [S.measure_perm N (P.perm _ _), S.measure_append, measure_cons, measure_children]
      obtain ⟨m, hm⟩ : ∃ m, N - w.length = m + 1 := ⟨N - w.length - 1, by omega⟩
      have : N - (w.length + 1) = m := by omega
      simp only [hm, this, size]
      omega

theorem measure_search {N : ℕ} {x : α ⊕ σ} (finished : (S.run N x).status = .finished) :
    ∀ k : ℕ, (S.search P k x).pending = [] ∨
      S.measure N (S.search P k x).pending + k = S.size N x
  | 0 => .inr (by simp [search, Config.start, measure])
  | k + 1 => by
      rcases measure_search finished k with idle | count
      · left
        rw [search_succ, S.step_of_finished P idle]
        exact idle
      · by_cases idle : (S.search P (k + 1) x).pending = []
        · exact .inl idle
        · right
          obtain ⟨done, _, covers⟩ := S.covers_search P x k
          have busy : (S.search P k x).pending ≠ [] := by
            intro empty
            rw [search_succ, S.step_of_finished P empty] at idle
            exact idle empty
          have := S.measure_step P finished covers busy
          rw [← search_succ] at this
          omega

/-- **Every policy finishes a finite tree within one budget**: the number of its items. -/
theorem finishes {N : ℕ} {x : α ⊕ σ} (finished : (S.run N x).status = .finished) :
    (S.search P (S.size N x) x).pending = [] := by
  rcases S.measure_search P finished (S.size N x) with idle | count
  · exact idle
  · by_contra busy
    have := S.pos_measure N busy
    omega

/-- **A policy finishes exactly when the tree is finite.** -/
theorem finishes_iff (x : α ⊕ σ) :
    (∃ k, (S.search P k x).pending = []) ↔ ∃ N, (S.run N x).status = .finished := by
  constructor
  · rintro ⟨k, idle⟩
    exact ⟨k, (S.status_run_eq_finished_iff k x).mpr fun w t state =>
      S.length_lt_of_finished P idle state⟩
  · rintro ⟨N, finished⟩
    exact ⟨_, S.finishes P finished⟩

/-- **`all` is defined exactly when the tree is finite.** -/
theorem all_dom_iff (x : α ⊕ σ) : (S.all P x).Dom ↔ ∃ N, (S.run N x).status = .finished := by
  rw [← S.finishes_iff P x]
  simp only [all, List.isEmpty_iff]

/-- **Whether `all` is defined does not depend on the policy.** -/
theorem all_dom_iff_dom (P' : Policy (List ℕ × (α ⊕ σ))) (x : α ⊕ σ) :
    (S.all P x).Dom ↔ (S.all P' x).Dom :=
  (S.all_dom_iff P x).trans (S.all_dom_iff P' x).symm

/-- **`all` is the collection of the unbounded search.** -/
theorem collect_eq_all {x : α ⊕ σ} {N : ℕ} (finished : (S.run N x).status = .finished) :
    Outcome.collect (S.approx N x) =
      Outcome.pure (((S.all P x).get ((S.all_dom_iff P x).mpr ⟨N, finished⟩)).map Prod.snd) := by
  have answers : (S.all P x).get ((S.all_dom_iff P x).mpr ⟨N, finished⟩) = (S.run N x).answers :=
    (Multiset.Nodup.ext (S.nodup_all P _) (S.nodup_run N x)).mpr fun p =>
      (S.mem_all P _ p).trans
        ⟨fun h => S.mem_run_of_finished finished h, fun h => S.run_sound h⟩
  rw [answers]
  have status : (S.approx N x).status = .finished := finished
  unfold approx at status ⊢
  generalize S.run N x = o at status ⊢
  obtain ⟨A, st⟩ := o
  change st = _ at status
  subst status
  rfl

/-- **`within` is monotone in its budget.** -/
theorem within_mono (x : α ⊕ σ) {k k' : ℕ} (h : k ≤ k') : S.within P k x ≤ S.within P k' x := by
  by_cases idle : (S.search P k x).pending = []
  · have same : S.search P k' x = S.search P k x := by
      induction h with
      | refl => rfl
      | step _ ih => rw [search_succ, ih, S.step_of_finished P idle]
    rw [Space.within, Space.within, same]
  · refine .inr ⟨?_, ?_⟩
    · show (S.search P k x).status = .cutOff
      apply Status.eq_cutOff_of_ne_finished
      rwa [Ne, Config.status_eq_finished_iff]
    · obtain ⟨rest, same⟩ := S.found_prefix_of_le P x h
      show (((S.search P k x).found : Multiset (List ℕ × α)).map Prod.snd) ≤
        ((S.search P k' x).found : Multiset (List ℕ × α)).map Prod.snd
      rw [← same, ← Multiset.coe_add]
      exact Multiset.map_le_map (Multiset.le_add_right _ _)

/-- **A cut-off `within` never reads refuted.** -/
theorem within_verdict_ne_refuted {k : ℕ} {x : α ⊕ σ} (cut : (S.within P k x).status = .cutOff) :
    (S.within P k x).verdict ≠ .refuted :=
  Outcome.verdict_ne_refuted_of_cutOff cut

end Space

#print axioms map_finRange_getElem
#print axioms Space.measure_step
#print axioms Space.measure_search
#print axioms Space.finishes
#print axioms Space.finishes_iff
#print axioms Space.all_dom_iff
#print axioms Space.all_dom_iff_dom
#print axioms Space.collect_eq_all
#print axioms Space.within_mono
#print axioms Space.within_verdict_ne_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
