import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosing

/-!
# The two orders of a native diamond reserve the same scopes

An activation reserves one scope per port after every occupied scope, and the solver's helper frame one
more (`ContextualFreshFrameScopeLedger.helperLedger`). After it, the ledger is the old one with one
interval added (`helperLedger_after`), and the next activation starts after that interval
(`start_helperLedger_after`). Two activations in sequence reserve one interval whose length is the sum
of their port counts plus two (`composite_ledger`), whichever fires first.

So the two composite published states of the closing leg have **the same scope ledger**
(`LiveFiring.closing_occupied`): with `LiveFiring.closing`, the two orders agree on their present
occurrences and their ledger, and are the one joint state carried along their inclusions in their rows
and their knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open ContextualActivationScopes ContextualFreshFrameScopeLedger

namespace NativeClosingScopes

variable {O : Type}

/-- Above every occupied scope, an interval ends one below its bound. -/
theorem sup_union_Ico (occupied : Finset ℕ) {bound : ℕ} (above : start occupied < bound) :
    (occupied ∪ Finset.Ico (start occupied) bound).sup id = bound - 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro scope member
    rcases Finset.mem_union.mp member with old | new
    · have := occupied_lt_start occupied old
      show scope ≤ bound - 1
      omega
    · have := Finset.mem_Ico.mp new
      show scope ≤ bound - 1
      omega
  · have member : bound - 1 ∈ occupied ∪ Finset.Ico (start occupied) bound :=
      Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    exact Finset.le_sup (f := id) member

theorem count_pos (selection : Selection O) : 1 ≤ count selection := by
  unfold count
  omega

theorem start_after (occupied : Finset ℕ) (selection : Selection O) :
    start (after occupied selection) = start occupied + count selection := by
  have positive := count_pos selection
  show (occupied ∪ Finset.Ico (start occupied) (start occupied + count selection)).sup id + 1 = _
  rw [sup_union_Ico occupied (by omega)]
  omega

/-- **An activation adds one interval to the ledger**: its ports and its helper scope. -/
theorem helperLedger_after (occupied : Finset ℕ) (selection : Selection O) :
    helperLedger (after occupied selection) =
      occupied ∪ Finset.Ico (start occupied) (start occupied + count selection + 1) := by
  rw [helperLedger, helperScope, start_after]
  ext scope
  rw [Finset.mem_insert]
  show scope = start occupied + count selection ∨
      scope ∈ occupied ∪ Finset.Ico (start occupied) (start occupied + count selection) ↔ _
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
  by_cases old : scope ∈ occupied
  · exact ⟨fun _ => Or.inl old, fun _ => Or.inr (Or.inl old)⟩
  · constructor
    · rintro (same | old' | ⟨low, high⟩)
      · exact Or.inr ⟨by omega, by omega⟩
      · exact absurd old' old
      · exact Or.inr ⟨low, by omega⟩
    · rintro (old' | ⟨low, high⟩)
      · exact absurd old' old
      · by_cases top : scope = start occupied + count selection
        · exact Or.inl top
        · exact Or.inr (Or.inr ⟨low, by omega⟩)

/-- The next activation starts after the interval. -/
theorem start_helperLedger_after (occupied : Finset ℕ) (selection : Selection O) :
    start (helperLedger (after occupied selection)) = start occupied + count selection + 1 := by
  rw [helperLedger_after]
  show (occupied ∪ Finset.Ico (start occupied) (start occupied + count selection + 1)).sup id + 1 = _
  rw [sup_union_Ico occupied (by omega)]
  omega

/-- **Two activations in sequence reserve one interval**, of the sum of their port counts plus two. -/
theorem composite_ledger (occupied : Finset ℕ) (first second : Selection O) :
    helperLedger (after (helperLedger (after occupied first)) second) =
      occupied ∪ Finset.Ico (start occupied) (start occupied + count first + count second + 2) := by
  rw [helperLedger_after (helperLedger (after occupied first)), start_helperLedger_after,
    helperLedger_after, Finset.union_assoc,
    Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  congr 2
  omega

/-- **The order does not change the composite ledger.** -/
theorem composite_ledger_comm (occupied : Finset ℕ) (first second : Selection O) :
    helperLedger (after (helperLedger (after occupied first)) second) =
      helperLedger (after (helperLedger (after occupied second)) first) := by
  rw [composite_ledger, composite_ledger, Nat.add_right_comm (start occupied) (count first) (count second)]

end NativeClosingScopes

namespace LiveFiring

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {s : NativeState S O Γ sort}

/-- **The two orders of the closing leg reserve the same scopes.** -/
theorem closing_occupied {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (rawTarget (residualExecution first second clearF)).state.occupied =
      (rawTarget (residualExecution second first clearG)).state.occupied := by
  show ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after
      (ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after s.state.occupied (execution second).selection))
      (residualExecution first second clearF).selection) =
    ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after
      (ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after s.state.occupied (execution first).selection))
      (residualExecution second first clearG).selection)
  rw [(residualExecution_executes first second clearF).selection,
    (residualExecution_executes second first clearG).selection,
    (execution_data second).2.1, (execution_data first).2.1]
  exact NativeClosingScopes.composite_ledger_comm _ _ _

end LiveFiring

#print axioms NativeClosingScopes.sup_union_Ico
#print axioms NativeClosingScopes.helperLedger_after
#print axioms NativeClosingScopes.start_helperLedger_after
#print axioms NativeClosingScopes.composite_ledger
#print axioms NativeClosingScopes.composite_ledger_comm
#print axioms LiveFiring.closing_occupied

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
