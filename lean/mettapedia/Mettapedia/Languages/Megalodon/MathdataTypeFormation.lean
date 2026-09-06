import Mettapedia.Languages.Megalodon.MathdataKernel
import Lean.Elab.Tactic.Omega

/-!
# Native type formation under weakening and specialization

Plain type formation is preserved when variables are weakened or a type-variable
level is removed by capture-avoiding substitution. At substitution depth `depth`
inside a context of size `bound + 1`, the replacement is formed in the outer
context of size `bound - depth`; the native operation shifts it across the
intervening binders.

These laws concern the existing native type syntax and its formation checker.
They do not infer formation of declarations from an unchecked environment or
change the separate prefix-polymorphic formation judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.MathdataKernel.Tp

/-- Zero weakening is the identity, including below prefix type binders. -/
theorem shift_zero (cutoff : Nat) (type : Tp) : shift cutoff 0 type = type := by
  induction type generalizing cutoff with
  | var index => by_cases h : index < cutoff <;> simp [shift, h]
  | prop | base => rfl
  | arr a b iha ihb => simp [shift, iha, ihb]
  | all body ih => simp [shift, ih]

/-- Substitution beyond a plain type's free variables leaves it unchanged. -/
theorem instantiateAt_eq_of_plain {bound depth : Nat} (type replacement : Tp)
    (plain : type.plainWellFormed bound = true) (beyond : bound ≤ depth) :
    instantiateAt depth replacement type = type := by
  induction type with
  | var index =>
      simp only [plainWellFormed, decide_eq_true_eq] at plain
      simp [instantiateAt, show index < depth by omega]
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      simp only [plainWellFormed, Bool.and_eq_true] at plain
      simp [instantiateAt, ihd plain.1, ihc plain.2]
  | all body ih => simp [plainWellFormed] at plain

/-- A plain type remains formed when more type variables are available. -/
theorem plainWellFormed_mono {type : Tp} {bound upper : Nat}
    (formed : type.plainWellFormed bound = true) (bound_le : bound ≤ upper) :
    type.plainWellFormed upper = true := by
  induction type with
  | var index =>
      simp only [plainWellFormed, decide_eq_true_eq] at formed ⊢
      omega
  | prop => rfl
  | base _ => rfl
  | arr domain codomain ihd ihc =>
      simp only [plainWellFormed, Bool.and_eq_true] at formed ⊢
      exact ⟨ihd formed.1, ihc formed.2⟩
  | all body _ => simp [plainWellFormed] at formed

/-- Shifting at an arbitrary cutoff preserves formation in the enlarged
type-variable context. The cutoff may also lie beyond the context. -/
theorem plainWellFormed_shift {type : Tp} {bound : Nat} (cutoff amount : Nat)
    (formed : type.plainWellFormed bound = true) :
    (type.shift cutoff amount).plainWellFormed (bound + amount) = true := by
  induction type with
  | var index =>
      simp only [plainWellFormed, decide_eq_true_eq] at formed
      by_cases below : index < cutoff
      · simp only [shift, below, ↓reduceIte, plainWellFormed, decide_eq_true_eq]
        omega
      · simp only [shift, below, ↓reduceIte, plainWellFormed, decide_eq_true_eq]
        omega
  | prop => rfl
  | base _ => rfl
  | arr domain codomain ihd ihc =>
      simp only [plainWellFormed, Bool.and_eq_true] at formed
      simp only [shift, plainWellFormed, Bool.and_eq_true]
      exact ⟨ihd formed.1, ihc formed.2⟩
  | all body _ => simp [plainWellFormed] at formed

/-- Removing one type-variable level preserves native plain formation. The
replacement is formed outside the `depth` intervening binders. -/
theorem plainWellFormed_instantiateAt {type replacement : Tp} {bound depth : Nat}
    (formed : type.plainWellFormed (bound + 1) = true)
    (replacement_formed : replacement.plainWellFormed (bound - depth) = true)
    (depth_le : depth ≤ bound) :
    (instantiateAt depth replacement type).plainWellFormed bound = true := by
  induction type with
  | var index =>
      simp only [plainWellFormed, decide_eq_true_eq] at formed
      by_cases below : index < depth
      · simp only [instantiateAt, below, ↓reduceIte, plainWellFormed,
          decide_eq_true_eq]
        omega
      · by_cases selected : index = depth
        · subst index
          simp only [instantiateAt, Nat.lt_irrefl, ↓reduceIte]
          have shifted := plainWellFormed_shift 0 depth replacement_formed
          simpa only [Nat.sub_add_cancel depth_le] using shifted
        · simp only [instantiateAt, below, selected, ↓reduceIte, plainWellFormed,
            decide_eq_true_eq]
          omega
  | prop => rfl
  | base _ => rfl
  | arr domain codomain ihd ihc =>
      simp only [plainWellFormed, Bool.and_eq_true] at formed
      simp only [instantiateAt, plainWellFormed, Bool.and_eq_true]
      exact ⟨ihd formed.1, ihc formed.2⟩
  | all body _ => simp [plainWellFormed] at formed

/-- The outermost specialization used by native type application preserves
plain formation of the result type. -/
theorem plainWellFormed_instantiate {type replacement : Tp} {bound : Nat}
    (formed : type.plainWellFormed (bound + 1) = true)
    (replacement_formed : replacement.plainWellFormed bound = true) :
    (instantiate replacement type).plainWellFormed bound = true := by
  exact plainWellFormed_instantiateAt formed
    (by simpa only [Nat.sub_zero] using replacement_formed) (Nat.zero_le bound)

end Mettapedia.Languages.Megalodon.MathdataKernel.Tp

namespace Mettapedia.Languages.Megalodon.MathdataTypeFormation

open MathdataKernel

/-- Substitution beneath a binder retains the inner variable and shifts the
outer replacement, while removing the selected level from later variables.
Both source and target are genuinely open plain types. -/
theorem nonzero_specialization_formed :
    Tp.plainWellFormed 3 (.arr (.var 0) (.arr (.var 1) (.var 2))) = true ∧
      Tp.plainWellFormed 1 (.arr (.var 0) (.var 0)) = true ∧
      Tp.instantiateAt 1 (.arr (.var 0) (.var 0)) (.arr (.var 0) (.arr (.var 1) (.var 2))) =
        .arr (.var 0) (.arr (.arr (.var 1) (.var 1)) (.var 1)) ∧
      (Tp.instantiateAt 1 (.arr (.var 0) (.var 0))
        (.arr (.var 0) (.arr (.var 1) (.var 2)))).plainWellFormed 2 = true := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact Tp.plainWellFormed_instantiateAt (bound := 2) (depth := 1)
    (by decide) (by decide) (by decide)

/-- Both expressions pass the resulting scope check, but omitting the shift
captures a different variable. Formation alone does not establish the
correctness of capture-avoiding substitution. -/
theorem unshifted_specialization_captures :
    Tp.plainWellFormed 2 (.arr (.var 0) (.var 0)) = true ∧
      Tp.instantiateAt 1 (.var 0) (.arr (.var 0) (.var 1)) ≠
        .arr (.var 0) (.var 0) := by
  decide

/-- A replacement with a free variable in an empty outer context can make
the specialized result unformed. -/
theorem unformed_replacement_rejected :
    Tp.plainWellFormed 1 (.var 0) = true ∧
      Tp.plainWellFormed 0 (.var 0) = false ∧
      (Tp.instantiateAt 0 (.var 0) (.var 0)).plainWellFormed 0 = false := by
  decide

#print axioms Tp.plainWellFormed_mono
#print axioms Tp.shift_zero
#print axioms Tp.instantiateAt_eq_of_plain
#print axioms Tp.plainWellFormed_shift
#print axioms Tp.plainWellFormed_instantiateAt
#print axioms Tp.plainWellFormed_instantiate
#print axioms nonzero_specialization_formed
#print axioms unshifted_specialization_captures
#print axioms unformed_replacement_rejected

end Mettapedia.Languages.Megalodon.MathdataTypeFormation
