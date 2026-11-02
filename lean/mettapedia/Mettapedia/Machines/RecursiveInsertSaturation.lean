import Mettapedia.Machines.RecursiveInsertAgenda

/-!
# Recursive insertion reaches the independent Horn closure

Pending insertion obligations, delayed rule checks and seed obligations are
preserved separately. Completion therefore implies closure, not merely that
the algorithm stopped finding work. The reference semantics is the existing
Horn derivability theorem, independent of this agenda implementation.

These are local, count-qualified permission laws. They do not identify an
arbitrary MeTTa region, a deletion-based prover, or probabilistic revision
with a Horn program.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert

open Mettapedia.Logic

variable {Fact : Type} [DecidableEq Fact]

theorem handle_known_mono (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact)) :
    known ⊆ (handle rules policy task rest known log).known := by
  cases task with
  | insert fact => by_cases h : fact ∈ known <;> simp [handle, h]
  | check rule => by_cases h : rule.premises ⊆ known <;> simp [handle, h]

theorem handle_rest_mem (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (later : Task Fact) (held : later ∈ rest) :
    later ∈ (handle rules policy task rest known log).pending := by
  cases task with
  | insert fact => by_cases h : fact ∈ known <;> simp [handle, h, held]
  | check rule => by_cases h : rule.premises ⊆ known <;> simp [handle, h, held]

theorem handle_insert_obligation (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (fact : Fact) (held : fact ∈ known ∨ Task.insert fact ∈ task :: rest) :
    fact ∈ (handle rules policy task rest known log).known ∨
      Task.insert fact ∈ (handle rules policy task rest known log).pending := by
  rcases held with hk | hp
  · exact Or.inl (handle_known_mono rules policy task rest known log hk)
  · rcases List.mem_cons.mp hp with he | hr
    · subst task
      by_cases h : fact ∈ known <;> simp [handle, h]
    · exact Or.inr (handle_rest_mem rules policy task rest known log _ hr)

def RuleCovered (state : State Fact) (rule : LP.PropRule Fact) : Prop :=
  rule.head ∈ state.known ∨ Task.insert rule.head ∈ state.pending ∨ Task.check rule ∈ state.pending

theorem handle_check_obligation (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (rule : LP.PropRule Fact) (held : Task.check rule ∈ task :: rest)
    (enabled : rule.premises ⊆ (handle rules policy task rest known log).known) :
    RuleCovered (handle rules policy task rest known log) rule := by
  rcases List.mem_cons.mp held with he | hr
  · subst task
    have he : rule.premises ⊆ known := by
      by_cases h : rule.premises ⊆ known
      · exact h
      · simp [handle, h] at enabled
    simp [RuleCovered, handle, he]
  · exact Or.inr (Or.inr (handle_rest_mem rules policy task rest known log _ hr))

theorem newly_enabled_check (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (rule : LP.PropRule Fact) (member : rule ∈ rules) (wasDisabled : ¬ rule.premises ⊆ known)
    (enabled : rule.premises ⊆ (handle rules policy task rest known log).known) :
    Task.check rule ∈ (handle rules policy task rest known log).pending := by
  cases task with
  | check other =>
      by_cases h : other.premises ⊆ known <;>
        exact False.elim (wasDisabled (by simpa [handle, h] using enabled))
  | insert fact =>
      by_cases held : fact ∈ known
      · exact False.elim (wasDisabled (by simpa [handle, held] using enabled))
      · have uses : fact ∈ rule.premises := by
          by_contra absent
          apply wasDisabled
          intro premise hp
          have hm : premise ∈ insert fact known := by simpa [handle, held] using enabled hp
          rcases Finset.mem_insert.mp hm with same | old
          · exact False.elim (absent (same ▸ hp))
          · exact old
        simp only [handle, held, ↓reduceIte, enqueue_mem]
        exact Or.inl ((triggered_mem rules fact _).2 ⟨rule, member, uses, rfl⟩)

/-- The two coverage obligations needed at quiescence. -/
structure Covered (rules : List (LP.PropRule Fact)) (seeds : List Fact) (state : State Fact) : Prop where
  seeds : ∀ fact ∈ seeds, fact ∈ state.known ∨ Task.insert fact ∈ state.pending
  rules : ∀ rule ∈ rules, rule.premises ⊆ state.known → RuleCovered state rule

theorem initial_covered (rules : List (LP.PropRule Fact)) (seeds : List Fact) :
    Covered rules seeds (initial rules seeds) := by
  constructor
  · intro fact member
    exact Or.inr (by simp [initial, member])
  · intro rule member enabled
    have empty : rule.premises = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun fact hf => by simpa [initial] using enabled hf)
    simp [RuleCovered, initial, member, empty]

theorem handle_covered (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (task : Task Fact) (rest : List (Task Fact))
    (known : Finset Fact) (log : List (Event Fact))
    (covered : Covered rules seeds ⟨known, task :: rest, log⟩) :
    Covered rules seeds (handle rules policy task rest known log) := by
  constructor
  · intro fact member
    exact handle_insert_obligation rules policy task rest known log fact (covered.seeds fact member)
  · intro rule member enabled
    by_cases old : rule.premises ⊆ known
    · rcases covered.rules rule member old with hk | hi | hc
      · exact Or.inl (handle_known_mono rules policy task rest known log hk)
      · rcases handle_insert_obligation rules policy task rest known log rule.head (Or.inr hi) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact handle_check_obligation rules policy task rest known log rule hc enabled
    · exact Or.inr (Or.inr (newly_enabled_check rules policy task rest known log rule member old enabled))

def TaskSafe (rules : List (LP.PropRule Fact)) (target : Finset Fact) : Task Fact → Prop
  | .insert fact => fact ∈ target
  | .check rule => rule ∈ rules

structure Safe (rules : List (LP.PropRule Fact)) (target : Finset Fact) (state : State Fact) : Prop where
  known : state.known ⊆ target
  pending : ∀ task ∈ state.pending, TaskSafe rules target task

theorem initial_safe (rules : List (LP.PropRule Fact)) (seeds : List Fact) (target : Finset Fact)
    (includes : seeds.toFinset ⊆ target) : Safe rules target (initial rules seeds) := by
  constructor
  · simp [initial]
  · intro task member
    simp only [initial, List.mem_append, List.mem_map] at member
    rcases member with ⟨fact, hf, rfl⟩ | ⟨rule, hr, rfl⟩
    · exact includes (List.mem_toFinset.mpr hf)
    · exact (List.mem_filter.mp hr).1

theorem handle_safe (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (target : Finset Fact)
    (closed : ∀ rule ∈ rules, rule.premises ⊆ target → rule.head ∈ target)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (safe : Safe rules target ⟨known, task :: rest, log⟩) :
    Safe rules target (handle rules policy task rest known log) := by
  have selected := safe.pending task (List.mem_cons_self ..)
  have remaining : ∀ later ∈ rest, TaskSafe rules target later :=
    fun later member => safe.pending later (List.mem_cons_of_mem _ member)
  cases task with
  | insert fact =>
      by_cases held : fact ∈ known
      · constructor
        · simpa [handle, held] using safe.known
        · simpa [handle, held] using remaining
      · constructor
        · simpa [handle, held] using Finset.insert_subset selected safe.known
        · intro later member
          simp only [handle, held, ↓reduceIte, enqueue_mem] at member
          rcases member with child | old
          · rcases (triggered_mem rules fact later).1 child with ⟨rule, hr, _, rfl⟩
            exact hr
          · exact remaining later old
  | check rule =>
      by_cases enabled : rule.premises ⊆ known
      · constructor
        · simpa [handle, enabled] using safe.known
        · intro later member
          simp only [handle, enabled, ↓reduceIte, enqueue_mem, List.mem_singleton] at member
          rcases member with rfl | old
          · exact closed rule selected (Finset.Subset.trans enabled safe.known)
          · exact remaining later old
      · constructor
        · simpa [handle, enabled] using safe.known
        · simpa [handle, enabled] using remaining

theorem run_preserves (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (target : Finset Fact)
    (closed : ∀ rule ∈ rules, rule.premises ⊆ target → rule.head ∈ target)
    (fuel : Nat) (start finish : State Fact)
    (safe : Safe rules target start) (covered : Covered rules seeds start)
    (result : run rules policy fuel start = .done finish) :
    Safe rules target finish ∧ Covered rules seeds finish := by
  induction fuel generalizing start with
  | zero =>
      by_cases empty : start.pending = []
      · have eq : start = finish := by simpa [run, empty] using result
        simpa [← eq] using And.intro safe covered
      · simp [run, empty] at result
  | succ fuel ih =>
      cases hp : start.pending with
      | nil =>
          have eq : start = finish := by simpa [run, hp] using result
          simpa [← eq] using And.intro safe covered
      | cons task rest =>
          have eq : start = ⟨start.known, task :: rest, start.log⟩ := by cases start; simp_all
          exact ih _ (handle_safe rules policy target closed task rest _ _ (eq ▸ safe))
            (handle_covered rules seeds policy task rest _ _ (eq ▸ covered))
            (by simpa [run, hp] using result)

section Finite

variable [Fintype Fact]

def reference (rules : List (LP.PropRule Fact)) (seeds : List Fact) : Finset Fact :=
  LP.saturate rules.toFinset seeds.toFinset

/-- Every terminating admitted schedule computes the independently defined closure. -/
theorem completed_eq_reference (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initial rules seeds) = .done finish) :
    finish.known = reference rules seeds := by
  have includes : seeds.toFinset ⊆ reference rules seeds := LP.saturate_contains_facts _ _
  have closed : ∀ rule ∈ rules, rule.premises ⊆ reference rules seeds →
      rule.head ∈ reference rules seeds := by
    intro rule member enabled
    exact LP.rule_closed_saturate _ _ (List.mem_toFinset.mpr member) enabled
  rcases run_preserves rules seeds policy (reference rules seeds) closed fuel _ finish
    (initial_safe rules seeds _ includes) (initial_covered rules seeds) result with ⟨safe, covered⟩
  have empty := run_done_empty rules policy fuel _ finish result
  apply Finset.Subset.antisymm safe.known
  intro fact member
  apply LP.derivable_subset_of_closed rules.toFinset seeds.toFinset finish.known
  · intro seed hs
    simpa [empty] using covered.seeds seed (List.mem_toFinset.mp hs)
  · intro rule hr enabled
    simpa [RuleCovered, empty] using covered.rules rule (List.mem_toFinset.mp hr) enabled
  · exact LP.saturate_sound _ _ fact member

theorem finite_saturation (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) :
    ∃ finish, run rules policy (potential rules (initial rules seeds) + 1) (initial rules seeds) =
      .done finish ∧ finish.known = reference rules seeds := by
  rcases run_completes rules policy (potential rules (initial rules seeds) + 1)
    (initial rules seeds) (Nat.lt_succ_self _) with ⟨finish, h⟩
  exact ⟨finish, h, completed_eq_reference rules seeds policy _ finish h⟩

theorem completed_schedules_agree (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (first second : QueuePolicy Fact) (m n : Nat) (left right : State Fact)
    (hl : run rules first m (initial rules seeds) = .done left)
    (hr : run rules second n (initial rules seeds) = .done right) : left.known = right.known := by
  rw [completed_eq_reference rules seeds first m left hl,
    completed_eq_reference rules seeds second n right hr]

end Finite

end Mettapedia.Machines.RecursiveInsert
