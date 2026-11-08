import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore

/-!
# The scoped reading of an equation is its opening

The dynamic pattern fragment is defined from the store alone: a side is opened by applying it to fresh locals
(`ContextualDependentDynamicFragment.openCode`), and the conditions are read on the normal forms of the
opening, with the newest `count` variables rigid (`openedFlexible`). The solver reads the same side under a
discovered local telescope (`Spine.openFunction`), with the outer variables flexible (`outerFlexible`).

These are the same code, up to the cast of the context length (`openFunction_code`), and the same marking
(`outerFlexible_eq`). Renamings that respect the marking keep the rigid support (`rigidSupport_rename`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentDynamicFragment
open ContextualDependentGeneralPattern (liftFlexible outerFlexible)

section Rename

variable {Head : Type}

/-- **A renaming that respects the marking keeps the rigid support.** -/
theorem rigidSupport_rename : ∀ {n m : Nat} (t : Tm Head n) {ρ : Ren n m}
    {flexible : Fin n → Bool} {flexible' : Fin m → Bool} (_ : ∀ i, flexible' (ρ i) = flexible i)
    {index : Fin n}, index ∈ rigidSupport flexible t → ρ index ∈ rigidSupport flexible' (rename ρ t)
  | _, _, .var _, _, _, _, _, _, member => by
      simp only [rigidSupport, Finset.mem_singleton] at member
      subst member
      simp [rigidSupport, rename]
  | _, _, .const _, _, _, _, _, _, member => by simp [rigidSupport] at member
  | _, _, .head _, _, _, _, _, _, member => by simp [rigidSupport] at member
  | _, _, .pi A B, ρ, _, _, respects, index, member => by
      simp only [rigidSupport, Finset.mem_union, mem_outerSupport] at member
      simp only [rename, rigidSupport, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (rigidSupport_rename A respects member)
      · exact .inr (rigidSupport_rename B (ρ := liftRen ρ) (liftFlexible_respects respects) member)
  | _, _, .sigma A B, ρ, _, _, respects, index, member => by
      simp only [rigidSupport, Finset.mem_union, mem_outerSupport] at member
      simp only [rename, rigidSupport, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (rigidSupport_rename A respects member)
      · exact .inr (rigidSupport_rename B (ρ := liftRen ρ) (liftFlexible_respects respects) member)
  | _, _, .id A a b, _, _, _, respects, _, member => by
      simp only [rigidSupport, Finset.mem_union] at member
      simp only [rename, rigidSupport, Finset.mem_union]
      rcases member with (member | member) | member
      · exact .inl (.inl (rigidSupport_rename A respects member))
      · exact .inl (.inr (rigidSupport_rename a respects member))
      · exact .inr (rigidSupport_rename b respects member)
  | _, _, .lam body, ρ, _, _, respects, _, member => by
      simp only [rigidSupport, mem_outerSupport] at member
      simp only [rename, rigidSupport, mem_outerSupport]
      exact rigidSupport_rename body (ρ := liftRen ρ) (liftFlexible_respects respects) member
  | _, _, .app f a, ρ, flexible, flexible', respects, _, member => by
      by_cases flexibleSpine : flexHead flexible (spineHead f) = true
      · simp [rigidSupport, flexibleSpine] at member
      · have rigidSpine : flexHead flexible (spineHead f) = false := by simpa using flexibleSpine
        have renamed : flexHead flexible' (spineHead (rename ρ f)) = false := by
          rw [spineHead_rename, flexHead_rename ρ respects, rigidSpine]
        simp only [rigidSupport, rigidSpine, Bool.false_eq_true, if_false, Finset.mem_union] at member
        simp only [rename, rigidSupport, renamed, Bool.false_eq_true, if_false, Finset.mem_union]
        rcases member with member | member
        · exact .inl (rigidSupport_rename f respects member)
        · exact .inr (rigidSupport_rename a respects member)
  | _, _, .pair a b, _, _, _, respects, _, member => by
      simp only [rigidSupport, Finset.mem_union] at member
      simp only [rename, rigidSupport, Finset.mem_union]
      rcases member with member | member
      · exact .inl (rigidSupport_rename a respects member)
      · exact .inr (rigidSupport_rename b respects member)
  | _, _, .fst p, _, _, _, respects, _, member => by
      simp only [rigidSupport] at member
      simp only [rename, rigidSupport]
      exact rigidSupport_rename p respects member
  | _, _, .snd p, _, _, _, respects, _, member => by
      simp only [rigidSupport] at member
      simp only [rename, rigidSupport]
      exact rigidSupport_rename p respects member
  | _, _, .refl a, _, _, _, respects, _, member => by
      simp only [rigidSupport] at member
      simp only [rename, rigidSupport]
      exact rigidSupport_rename a respects member

/-- Opening a weakened side applied to the newest variable is opening one more time. -/
theorem openCode_fresh {n : Nat} (code : Tm Head n) :
    ∀ count : Nat, rename (Fin.cast (by omega : n + 1 + count = n + (count + 1)))
      (openCode count (.app (rename wk code) (.var 0))) = openCode (count + 1) code
  | 0 => (rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)
  | count + 1 => by
      have earlier := openCode_fresh code count
      change rename (Fin.cast _) (Tm.app (rename wk (openCode count (.app (rename wk code) (.var 0)))) (.var 0)) =
        Tm.app (rename wk (openCode (count + 1) code)) (.var 0)
      rw [← earlier]
      simp only [rename, rename_comp]
      congr 1

end Rename

section Spines

variable {Head : Type} {rules : Rules Head}

/-- **The solver's opening of a side is the fragment's opening**, up to the cast of the context length. -/
theorem openFunction_code : ∀ {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (function : Term Γ type),
    (scope.openFunction function).code =
      rename (Fin.cast scope.target_arity.symm) (openCode scope.length function.code)
  | _, _, .stop _, function => ((rename_ext (fun _ => Fin.ext rfl) _).trans (rename_id _)).symm
  | _, _, .bind shape rest, function => by
      change (rest.openFunction (shape.fresh function)).code =
        rename (Fin.cast _) (openCode (rest.length + 1) function.code)
      rw [openFunction_code rest (shape.fresh function), ← openCode_fresh function.code rest.length, rename_comp]
      apply rename_ext
      intro i
      exact Fin.ext rfl

theorem outerRen_val : ∀ {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (index : Fin Γ.arity),
    (scope.outerRen index).val = index.val + scope.length
  | _, _, .stop _, _ => rfl
  | _, _, .bind _ rest, index => by
      change (rest.outerRen index.succ).val = index.val + (rest.length + 1)
      rw [outerRen_val rest index.succ, Fin.val_succ]
      omega

theorem localIndex_val : ∀ {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (position : scope.Local),
    (scope.localIndex position).val < scope.length
  | _, _, .stop _, position => position.elim
  | _, _, .bind shape rest, position => by
      change Unit ⊕ rest.Local at position
      rcases position with ⟨⟩ | position
      · rw [Spine.localIndex_head, outerRen_val]
        change 0 + rest.length < rest.length + 1
        omega
      · rw [Spine.localIndex_tail]
        have inner := localIndex_val rest position
        change _ < rest.length + 1
        omega

end Spines

section Marking

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The outer variables of a telescope are those past its locals.** -/
theorem outerFlexible_eq {Γ : Context S.R} {type : TypeOver Γ} (scope : Spine type) (index : Fin scope.target.arity) :
    outerFlexible scope index = decide (scope.length ≤ index.val) := by
  rcases scope.variable_cases index with ⟨outer, rfl⟩ | ⟨position, rfl⟩
  · have origin : scope.originEquiv.symm (scope.outerRen outer) = .inl outer := by
      rw [← scope.outer_origin, Equiv.symm_apply_apply]
    simp only [outerFlexible, origin, Sum.isLeft_inl, outerRen_val]
    symm
    exact decide_eq_true (by omega)
  · have origin : scope.originEquiv.symm (scope.localIndex position) = .inr position := by
      unfold Spine.localIndex
      rw [Equiv.symm_apply_apply]
    have below := localIndex_val scope position
    simp only [outerFlexible, origin, Sum.isLeft_inr]
    symm
    exact decide_eq_false (by omega)

/-- The cast of the context length carries the fragment's marking to the solver's. -/
theorem outerFlexible_cast {Γ : Context S.R} {type : TypeOver Γ} (scope : Spine type) (index : Fin (Γ.arity + scope.length)) :
    outerFlexible scope (Fin.cast scope.target_arity.symm index) = openedFlexible scope.length index := by
  rw [outerFlexible_eq]
  rfl

end Marking

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
