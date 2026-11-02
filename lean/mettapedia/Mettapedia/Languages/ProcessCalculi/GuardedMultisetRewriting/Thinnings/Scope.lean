import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Operations

/-! # Scope checks on canonical shared references -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type}

mutual
theorem supportedAt_iff : ∀ (depth : Nat) (term : Term Head),
    Term.supportedAt depth term = true ↔ ∀ i, freeAt term i = true → i < depth
  | depth, .idx k => by
    simp only [Term.supportedAt, decide_eq_true_eq, freeAt_idx]
    exact ⟨fun h i e => by rw [← e]; exact h, fun h => h k (by simp)⟩
  | depth, .node _ fs => by
    simp only [Term.supportedAt, freeAt_node]
    exact fieldsSupportedAt_iff depth fs

theorem fieldsSupportedAt_iff : ∀ (depth : Nat) (fs : Fields Head),
    Term.Fields.supportedAt depth fs = true ↔ ∀ i, fieldsFreeAt fs i = true → i < depth
  | _, .nil => by simp [Term.Fields.supportedAt]
  | depth, .cons binders term rest => by
    simp only [Term.Fields.supportedAt, Bool.and_eq_true, fieldsFreeAt_cons, Bool.or_eq_true]
    rw [supportedAt_iff (depth + binders) term, fieldsSupportedAt_iff depth rest]
    constructor
    · rintro ⟨body, tail⟩ i (here | there)
      · have := body (i + binders) here; omega
      · exact tail i there
    · intro within
      refine ⟨fun i used => ?_, fun i used => within i (Or.inr used)⟩
      by_cases bound : i < binders
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + binders := ⟨i - binders, by omega⟩
        have := within j (Or.inl used); omega
end

theorem bit_last_of_trimmed : ∀ {mask : Thin}, trimmed mask = true → mask ≠ [] →
    bit mask (mask.length - 1) = true
  | [], _, nonempty => absurd rfl nonempty
  | [b], valid, _ => by simpa using valid
  | a :: b :: rest, valid, _ => by
    have := bit_last_of_trimmed (mask := b :: rest) (trimmed_tail valid) (by simp)
    simpa using this

theorem lt_length_of_bit {mask : Thin} {i : Nat} (used : bit mask i = true) : i < mask.length := by
  by_contra outside
  rw [bit_of_length_le (Nat.le_of_not_lt outside)] at used
  cases used

/-- No node traversal: only the reference's support mask is inspected. -/
def check (reference : Ref) (width : Nat) : Bool := decide (reference.thin.length ≤ width)

theorem check_spec {store : Store Head} (canonical : Canonical store) {reference : Ref}
    (valid : CanonRef store reference) (width : Nat) :
    Term.supportedAt width (unfold store reference) = check reference width := by
  have exactBound : Term.supportedAt width (unfold store reference) = true ↔
      reference.thin.length ≤ width := by
    rw [supportedAt_iff]
    simp only [freeAt_unfold canonical valid]
    constructor
    · intro within
      by_cases empty : reference.thin = []
      · rw [empty]; exact Nat.zero_le _
      · have := within _ (bit_last_of_trimmed valid.trim empty); omega
    · intro bound i used
      have := lt_length_of_bit used; omega
  apply Bool.eq_iff_iff.mpr
  simpa only [check, decide_eq_true_eq] using exactBound

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope
