import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-!
# Inferred finite dependency interfaces

Dependencies of context entries can be closed transitively without requiring
an author to enumerate them. The finite saturation below computes the least
dependency-closed superset of the variables actually used. An explicit interface
is checked against the same closure law; extra permitted dependencies need not
be used.

This is finite syntactic dependency inference, not inference of every semantic
effect or of the most general logical theorem justified by an arbitrary program.
The exchange controls express a necessary declaration-order condition, not a
complete dependent type checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ScopeDependencies

variable {n : ℕ}

abbrev Dependencies (n : ℕ) := Fin n → Finset (Fin n)

def Closed (deps : Dependencies n) (allowed : Finset (Fin n)) : Prop :=
  ∀ entry ∈ allowed, deps entry ⊆ allowed

instance (deps : Dependencies n) (allowed : Finset (Fin n)) : Decidable (Closed deps allowed) :=
  inferInstanceAs (Decidable (∀ entry ∈ allowed, deps entry ⊆ allowed))

def step (deps : Dependencies n) (used : Finset (Fin n)) : Finset (Fin n) :=
  used ∪ used.biUnion deps

theorem subset_step (deps : Dependencies n) (used : Finset (Fin n)) : used ⊆ step deps used :=
  Finset.subset_union_left

theorem step_empty (deps : Dependencies n) : step deps ∅ = ∅ := by simp [step]

theorem step_eq_iff (deps : Dependencies n) (allowed : Finset (Fin n)) :
    step deps allowed = allowed ↔ Closed deps allowed := by
  constructor
  · intro same entry member dependency present
    have included : dependency ∈ step deps allowed :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨entry, member, present⟩)
    simpa only [same] using included
  · intro closed
    apply Finset.Subset.antisymm
    · intro entry member
      rcases Finset.mem_union.mp member with prior | introduced
      · exact prior
      · obtain ⟨parent, present, needed⟩ := Finset.mem_biUnion.mp introduced
        exact closed parent present needed
    · exact subset_step deps allowed

def grow (deps : Dependencies n) (used : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => used
  | k + 1 => step deps (grow deps used k)

theorem used_subset_grow (deps : Dependencies n) (used : Finset (Fin n)) (k : ℕ) :
    used ⊆ grow deps used k := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact ih.trans (subset_step deps _)

theorem grow_fixed_succ (deps : Dependencies n) (used : Finset (Fin n)) (k : ℕ)
    (fixed : step deps (grow deps used k) = grow deps used k) :
    step deps (grow deps used (k + 1)) = grow deps used (k + 1) := by
  simp only [grow, fixed]

theorem card_grow_of_not_fixed (deps : Dependencies n) (used : Finset (Fin n)) (k : ℕ)
    (changing : step deps (grow deps used k) ≠ grow deps used k) :
    k + 1 ≤ (grow deps used k).card := by
  induction k with
  | zero =>
      have nonempty : used ≠ ∅ := by
        intro empty
        exact changing (by simp [grow, empty, step_empty])
      have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonempty)
      change 1 ≤ used.card
      omega
  | succ k ih =>
      have prior : step deps (grow deps used k) ≠ grow deps used k := by
        intro fixed
        exact changing (grow_fixed_succ deps used k fixed)
      have lower := ih prior
      have strict : grow deps used k ⊂ step deps (grow deps used k) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨subset_step deps _, Ne.symm prior⟩
      have increase := Finset.card_lt_card strict
      simp only [grow] at *
      omega

/-- At most one strict increase per context entry. The bound comes from the
input context size and is not a fixed implementation resource limit. -/
theorem grow_fixed (deps : Dependencies n) (used : Finset (Fin n)) :
    step deps (grow deps used n) = grow deps used n := by
  by_contra changing
  have lower := card_grow_of_not_fixed deps used n changing
  have upper : (grow deps used n).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (grow deps used n))
  omega

def infer (deps : Dependencies n) (used : Finset (Fin n)) : Finset (Fin n) :=
  grow deps used n

theorem infer_contains (deps : Dependencies n) (used : Finset (Fin n)) : used ⊆ infer deps used :=
  used_subset_grow deps used n

theorem infer_closed (deps : Dependencies n) (used : Finset (Fin n)) : Closed deps (infer deps used) :=
  (step_eq_iff deps _).mp (grow_fixed deps used)

theorem grow_least (deps : Dependencies n) {used allowed : Finset (Fin n)}
    (included : used ⊆ allowed) (closed : Closed deps allowed) (k : ℕ) :
    grow deps used k ⊆ allowed := by
  induction k with
  | zero => exact included
  | succ k ih =>
      intro entry member
      rcases Finset.mem_union.mp member with prior | introduced
      · exact ih prior
      · obtain ⟨parent, present, needed⟩ := Finset.mem_biUnion.mp introduced
        exact closed parent (ih present) needed

theorem infer_least (deps : Dependencies n) {used allowed : Finset (Fin n)}
    (included : used ⊆ allowed) (closed : Closed deps allowed) : infer deps used ⊆ allowed :=
  grow_least deps included closed n

theorem infer_idempotent (deps : Dependencies n) (used : Finset (Fin n)) :
    infer deps (infer deps used) = infer deps used :=
  Finset.Subset.antisymm (infer_least deps (Finset.Subset.refl _) (infer_closed deps used))
    (infer_contains deps _)

/-- An explicit dependency-closed interface admits exactly the inferred
minimum and all of its allowed widenings. -/
theorem explicit_iff_inferred (deps : Dependencies n) {used allowed : Finset (Fin n)}
    (closed : Closed deps allowed) : used ⊆ allowed ↔ infer deps used ⊆ allowed :=
  ⟨fun included => infer_least deps included closed,
    fun included => (infer_contains deps used).trans included⟩

/-- Relabel a dependency graph. This does not assert that the new numeric
order is a well-formed dependent telescope. -/
def relabel (names : Equiv.Perm (Fin n)) (deps : Dependencies n) : Dependencies n :=
  fun entry => (deps (names.symm entry)).image names

theorem relabel_inverse (names : Equiv.Perm (Fin n)) (deps : Dependencies n) :
    relabel names.symm (relabel names deps) = deps := by
  funext entry
  simp [relabel, Finset.image_image]

theorem closed_relabel (names : Equiv.Perm (Fin n)) (deps : Dependencies n)
    {allowed : Finset (Fin n)} (closed : Closed deps allowed) :
    Closed (relabel names deps) (allowed.image names) := by
  intro entry present dependency needed
  obtain ⟨old, oldPresent, rfl⟩ := Finset.mem_image.mp present
  simp only [relabel, names.symm_apply_apply] at needed
  obtain ⟨oldDependency, oldNeeded, rfl⟩ := Finset.mem_image.mp needed
  exact Finset.mem_image.mpr ⟨oldDependency, closed old oldPresent oldNeeded, rfl⟩

theorem infer_relabel_le (names : Equiv.Perm (Fin n)) (deps : Dependencies n)
    (used : Finset (Fin n)) :
    infer (relabel names deps) (used.image names) ⊆ (infer deps used).image names := by
  apply infer_least
  · intro entry present
    obtain ⟨old, oldPresent, rfl⟩ := Finset.mem_image.mp present
    exact Finset.mem_image.mpr ⟨old, infer_contains deps used oldPresent, rfl⟩
  · exact closed_relabel names deps (infer_closed deps used)

/-- The computed minimal interface is invariant under a consistent
renumbering of the variables and their declared dependencies. -/
theorem infer_relabel (names : Equiv.Perm (Fin n)) (deps : Dependencies n)
    (used : Finset (Fin n)) :
    infer (relabel names deps) (used.image names) = (infer deps used).image names := by
  apply Finset.Subset.antisymm (infer_relabel_le names deps used)
  have reverse : infer deps used ⊆
      (infer (relabel names deps) (used.image names)).image names.symm := by
    simpa only [relabel_inverse, Finset.image_image, Function.comp_def, names.symm_apply_apply,
      Finset.image_id'] using infer_relabel_le names.symm (relabel names deps) (used.image names)
  intro entry present
  obtain ⟨old, oldPresent, rfl⟩ := Finset.mem_image.mp present
  obtain ⟨new, newPresent, same⟩ := Finset.mem_image.mp (reverse oldPresent)
  have back : new = names old := by simpa only [names.apply_symm_apply] using congrArg names same
  rw [← back]
  exact newPresent

def RespectsOrder (deps : Dependencies n) (position : Fin n → Fin n) : Prop :=
  ∀ entry, ∀ dependency ∈ deps entry, position dependency < position entry

instance (deps : Dependencies n) (position : Fin n → Fin n) :
    Decidable (RespectsOrder deps position) :=
  inferInstanceAs (Decidable
    (∀ entry, ∀ dependency ∈ deps entry, position dependency < position entry))

namespace Controls

/-- Entry 0 is x; entry 1 is v whose declaration mentions x. -/
def dependentPair : Dependencies 2 := fun entry => if entry = 1 then {0} else ∅

theorem selecting_only_the_dependent_entry_is_not_closed :
    ¬Closed dependentPair {1} := by decide

theorem inference_adds_the_undeclared_type_dependency :
    infer dependentPair {1} = {0, 1} := by decide

theorem an_unused_allowed_parameter_is_fine : Closed dependentPair {0, 1} ∧
    ({0} : Finset (Fin 2)) ⊆ {0, 1} := by decide

theorem dependency_order_allows_identity : RespectsOrder dependentPair id := by decide

theorem dependency_order_refuses_swap :
    ¬RespectsOrder dependentPair (fun i => if i = 0 then 1 else 0) := by decide

theorem independent_entries_allow_any_exchange (position : Fin 2 → Fin 2) :
    RespectsOrder (fun _ => ∅) position := by simp [RespectsOrder]

end Controls
end Mettapedia.TypeTheory.ScopeDependencies
