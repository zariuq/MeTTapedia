import Mettapedia.GSLT.Core.AnnotatedHorn

/-!
# Decidable finite support without selecting quotient representatives

The input list itself supplies an enumeration. Duplicate erasure is performed
by its decidable equality, retaining the last occurrence. Membership and the
absence of duplicates are proved directly for that computation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.Finite

universe u
variable {A : Type u} [DecidableEq A]

/-- Direct membership does not require an extensional `SetLike` instance. -/
@[instance_reducible] def membership : Membership A (Finset A) where
  mem elements item := item ∈ elements.val

attribute [local instance] membership

def unique : List A → List A
  | [] => []
  | first :: rest => if first ∈ unique rest then unique rest else first :: unique rest

@[simp] theorem mem_unique (item : A) (items : List A) : item ∈ unique items ↔ item ∈ items := by
  induction items with
  | nil => exact Iff.rfl
  | cons first rest induction =>
    rw [unique]
    split
    · rename_i present
      constructor
      · intro member
        exact List.mem_cons_of_mem _ (induction.mp member)
      · intro member
        rcases List.mem_cons.mp member with same | member
        · subst item
          exact present
        · exact induction.mpr member
    · constructor
      · intro member
        rcases List.mem_cons.mp member with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (induction.mp member))
      · intro member
        rcases List.mem_cons.mp member with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (induction.mpr member))

theorem nodup_unique (items : List A) : (unique items).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons first rest induction =>
    rw [unique]
    split
    · exact induction
    · rename_i absent
      exact List.nodup_cons.mpr ⟨absent, induction⟩

def support (items : List A) : Finset A :=
  ⟨(unique items : Multiset A), nodup_unique items⟩

@[simp] theorem mem_support (item : A) (items : List A) : item ∈ support items ↔ item ∈ items :=
  mem_unique item items

private theorem erased_absent (item : A) {items : List A} (nodup : items.Nodup) :
    item ∉ items.erase item := by
  induction items with
  | nil => exact List.not_mem_nil
  | cons first rest induction =>
    have distinct := List.nodup_cons.mp nodup
    cases (inferInstance : Decidable (first = item)) with
    | isTrue same =>
      subst first
      rw [List.erase_cons_head]
      exact distinct.1
    | isFalse different =>
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using different)]
      intro present
      rcases List.mem_cons.mp present with same | present
      · exact different same.symm
      · exact induction distinct.2 present

private theorem erase_ne_members (item removed : A) (different : item ≠ removed)
    (items : List A) : item ∈ items.erase removed ↔ item ∈ items := by
  induction items with
  | nil => exact Iff.rfl
  | cons first rest induction =>
    cases (inferInstance : Decidable (first = removed)) with
    | isTrue same =>
      subst first
      rw [List.erase_cons_head]
      constructor
      · exact List.mem_cons_of_mem _
      · intro present
        rcases List.mem_cons.mp present with impossible | present
        · exact (different impossible).elim
        · exact present
    | isFalse absent =>
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using absent)]
      rw [List.mem_cons, List.mem_cons]
      exact or_congr Iff.rfl induction

private theorem erase_members (item removed : A) {items : List A} (nodup : items.Nodup) :
    item ∈ items.erase removed ↔ item ≠ removed ∧ item ∈ items := by
  cases (inferInstance : Decidable (item = removed)) with
  | isTrue same =>
    subst item
    exact ⟨fun present => (erased_absent removed nodup present).elim,
      fun impossible => (impossible.1 rfl).elim⟩
  | isFalse different =>
    rw [erase_ne_members item removed different items]
    exact ⟨fun present => ⟨different, present⟩, And.right⟩

private theorem front_erase (item : A) (items : List A) (present : item ∈ items) :
    items.Perm (item :: items.erase item) := by
  induction items with
  | nil => exact (List.not_mem_nil present).elim
  | cons first rest induction =>
    cases (inferInstance : Decidable (first = item)) with
    | isTrue same =>
      subst first
      rw [List.erase_cons_head]
    | isFalse different =>
      have remaining : item ∈ rest := by
        rcases List.mem_cons.mp present with same | remaining
        · exact (different same.symm).elim
        · exact remaining
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using different)]
      exact (List.Perm.cons first (induction remaining)).trans (List.Perm.swap _ _ _)

/-- Decidable, duplicate-free enumerations with the same members are permuted. -/
theorem nodup_perm {first second : List A} (left : first.Nodup) (right : second.Nodup)
    (members : ∀ item, item ∈ first ↔ item ∈ second) : first.Perm second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => exact List.Perm.nil
    | cons head tail =>
      exact (List.not_mem_nil ((members head).mpr List.mem_cons_self)).elim
  | cons head tail induction =>
    have nodup := List.nodup_cons.mp left
    have present := (members head).mp List.mem_cons_self
    have rest := induction nodup.2 (right.erase head) (by
      intro item
      rw [erase_members item head right]
      constructor
      · intro member
        refine ⟨?_, (members item).mp (List.mem_cons_of_mem _ member)⟩
        intro same
        subst item
        exact nodup.1 member
      · rintro ⟨different, member⟩
        rcases List.mem_cons.mp ((members item).mpr member) with same | member
        · exact (different same).elim
        · exact member)
    exact (List.Perm.cons head rest).trans (front_erase head second present).symm

theorem support_ext {first second : List A}
    (members : ∀ item, item ∈ support first ↔ item ∈ support second) :
    support first = support second := by
  have perm : (unique first).Perm (unique second) :=
    nodup_perm (nodup_unique first) (nodup_unique second) members
  exact Finset.val_injective (Quot.sound perm)

/-- Cardinal reflection from actual finite enumerations, without a chosen `Fintype`. -/
theorem fin_size_of_equiv {n m : Nat} (equivalence : Fin n ≃ Fin m) : n = m := by
  have perm : ((List.finRange n).map equivalence).Perm (List.finRange m) :=
    nodup_perm ((List.nodup_finRange n).map equivalence.injective) (List.nodup_finRange m) (by
      intro item
      constructor
      · intro _
        exact List.mem_finRange item
      · intro _
        exact List.mem_map.mpr ⟨equivalence.symm item, List.mem_finRange _, equivalence.apply_symm_apply _⟩)
  simpa only [List.length_map, List.length_finRange] using perm.length_eq

/-- A supported list element has a computed first index, using decidable equality. -/
def firstIndex (items : List A) (item : A) (present : item ∈ items) : Fin items.length :=
  match items with
  | [] => (List.not_mem_nil present).elim
  | first :: rest =>
    if same : first = item then ⟨0, Nat.zero_lt_succ _⟩
    else (firstIndex rest item (by
      rcases List.mem_cons.mp present with identical | remaining
      · exact (same identical.symm).elim
      · exact remaining)).succ

theorem get_firstIndex (items : List A) (item : A) (present : item ∈ items) :
    items.get (firstIndex items item present) = item := by
  induction items with
  | nil => exact (List.not_mem_nil present).elim
  | cons first rest induction =>
    dsimp only [firstIndex]
    split
    · rename_i same
      exact same
    · exact induction _

end Mettapedia.GSLT.ProgrammableSpaceEvidence.Finite
