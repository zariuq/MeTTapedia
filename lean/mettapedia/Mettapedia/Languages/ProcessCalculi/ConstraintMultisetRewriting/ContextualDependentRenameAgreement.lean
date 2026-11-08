import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalObservations

/-!
# Pointwise renaming agreement on native support

Two renamings of one raw term are literally equal exactly when the maps
agree at every variable used by that term. Fresh function observation and
both pair projections preserve the information needed to recover this
pointwise agreement. No injectivity assumption is needed for these laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenameAgreement

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open ContextualDependentNormalObservations

def Agrees {n m : Nat} (first second : Ren n m) (slots : Finset (Fin n)) : Prop :=
  ∀ index ∈ slots, first index = second index

theorem agrees_empty {n m : Nat} (first second : Ren n m) : Agrees first second ∅ := by
  simp [Agrees]

theorem agrees_singleton {n m : Nat} (first second : Ren n m) (index : Fin n) :
    Agrees first second {index} ↔ first index = second index := by simp [Agrees]

theorem agrees_union {n m : Nat} (first second : Ren n m) (one two : Finset (Fin n)) :
    Agrees first second (one ∪ two) ↔ Agrees first second one ∧ Agrees first second two := by
  simp only [Agrees, Finset.mem_union, or_imp, forall_and]

theorem agrees_lift {n m : Nat} (first second : Ren n m) (slots : Finset (Fin (n + 1))) :
    Agrees (liftRen first) (liftRen second) slots ↔ Agrees first second (outerSupport slots) := by
  constructor
  · intro same index present
    exact Fin.succ_injective _ (same index.succ (mem_outerSupport.mp present))
  · intro same index
    refine Fin.cases ?_ (fun index => ?_) index
    · intro _; rfl
    · intro present
      exact congrArg Fin.succ (same index (mem_outerSupport.mpr present))

theorem rename_eq_iff_agrees {Head : Type} {n m : Nat} (term : Tm Head n) (first second : Ren n m) :
    Presentation.rename first term = Presentation.rename second term ↔ Agrees first second term.support := by
  induction term generalizing m <;>
    simp_all [Presentation.rename, Tm.support, agrees_empty, agrees_singleton, agrees_union, agrees_lift]

theorem fresh_rename {Head : Type} {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    freshValue (Presentation.rename rho term) = Presentation.rename (liftRen rho) (freshValue term) := by
  by_cases isLambda : ∃ body, term = .lam body
  · obtain ⟨body, rfl⟩ := isLambda
    rfl
  · have originalShape : freshValue term = .app (Presentation.rename wk term) (.var 0) := by
      cases term <;> try rfl
      exact False.elim (isLambda ⟨_, rfl⟩)
    have renamedShape : freshValue (Presentation.rename rho term) =
        .app (Presentation.rename wk (Presentation.rename rho term)) (.var 0) := by
      cases term <;> try rfl
      exact False.elim (isLambda ⟨_, rfl⟩)
    rw [originalShape, renamedShape]
    change Tm.app (Presentation.rename wk (Presentation.rename rho term)) (.var 0) =
      .app (Presentation.rename (liftRen rho) (Presentation.rename wk term)) (.var 0)
    rw [rename_comp, rename_comp]
    rfl

theorem rename_eq_head {Head : Type} {n m : Nat} {rho : Ren n m} {term : Tm Head n} {head : Head}
    (same : Presentation.rename rho term = .head head) : term = .head head := by
  cases term <;> simp only [Presentation.rename, reduceCtorEq, Tm.head.injEq] at same
  rw [same]

theorem first_rename {Head : Type} {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    firstValue (Presentation.rename rho term) = Presentation.rename rho (firstValue term) := by cases term <;> rfl

theorem second_rename {Head : Type} {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    secondValue (Presentation.rename rho term) = Presentation.rename rho (secondValue term) := by cases term <;> rfl

theorem agrees_of_fresh {Head : Type} {n m : Nat} (first second : Ren n m) (term : Tm Head n)
    (same : Agrees (liftRen first) (liftRen second) (freshValue term).support) : Agrees first second term.support := by
  have outer := (agrees_lift first second _).mp same
  rwa [fresh_support] at outer

theorem agrees_of_projections {Head : Type} {n m : Nat} (first second : Ren n m) (term : Tm Head n)
    (one : Agrees first second (firstValue term).support)
    (two : Agrees first second (secondValue term).support) : Agrees first second term.support := by
  have together := (agrees_union first second _ _).mpr ⟨one, two⟩
  rwa [projections_support] at together

end ContextualDependentRenameAgreement
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
