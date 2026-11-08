import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NormalizingLift
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Renaming

/-!
# Normal observations preserve outer support in the rigid-constant profile

Applying a normal function to a fresh variable and projecting a normal pair
have immediate normal representatives. The fresh application preserves outer
support; the two projections jointly preserve support. Constants are rigid
in this profile, so eta observation cannot expose an erasing root definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalObservations

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentNormalChecking ContextualDependentSupport

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

include rigid in
theorem no_root {n : Nat} {first second : Tm Head n} : ¬ S.R.computation.step first second := by
  intro step
  obtain ⟨name, _, _, _, role, _⟩ := S.shape.spine step
  rw [rigid name] at role
  cases role

theorem normal_whnf {n : Nat} {term : Tm Head n} (normal : Normal (S := S) term) :
    Whnf S.R S.roles term := fun target step => normal target step.directed

include rigid in
theorem normal_var {n : Nat} (index : Fin n) : Normal (S := S) (.var index) := by
  intro target step
  cases step with
  | root step => exact no_root rigid step

include rigid in
theorem normal_rename {n m : Nat} (rho : Ren n m) {term : Tm Head n}
    (normal : Normal (S := S) term) : Normal (S := S) (Presentation.rename rho term) := by
  intro target step
  have reflects : TypedEquality.StrongNormalization.RootReflectsRename S.R.computation := by
    intro n m rho term result rootStep
    exact False.elim (no_root rigid rootStep)
  obtain ⟨original, reduced, _⟩ := TypedEquality.StrongNormalization.Reduces.rename_inv reflects step
  exact normal original reduced

theorem normal_lam {n : Nat} {body : Tm Head (n + 1)} (normal : Normal (S := S) (.lam body)) :
    Normal (S := S) body := fun _ step => normal _ (.congLam step)

theorem normal_pair {n : Nat} {first second : Tm Head n} (normal : Normal (S := S) (.pair first second)) :
    Normal (S := S) first ∧ Normal (S := S) second :=
  ⟨fun _ step => normal _ (.congPairFst step), fun _ step => normal _ (.congPairSnd step)⟩

include rigid in
theorem normal_app {n : Nat} {function argument : Tm Head n}
    (normalFunction : Normal (S := S) function) (normalArgument : Normal (S := S) argument)
    (notLambda : ∀ body, function ≠ .lam body) : Normal (S := S) (.app function argument) := by
  intro target step
  cases step with
  | root step => exact no_root rigid step
  | betaPi body argument => exact notLambda body rfl
  | congAppFun step => exact normalFunction _ step
  | congAppArg step => exact normalArgument _ step

include rigid in
theorem normal_fst {n : Nat} {value : Tm Head n} (normal : Normal (S := S) value)
    (notPair : ∀ first second, value ≠ .pair first second) : Normal (S := S) (.fst value) := by
  intro target step
  cases step with
  | root step => exact no_root rigid step
  | betaSigmaFst => exact notPair _ _ rfl
  | congFst step => exact normal _ step

include rigid in
theorem normal_snd {n : Nat} {value : Tm Head n} (normal : Normal (S := S) value)
    (notPair : ∀ first second, value ≠ .pair first second) : Normal (S := S) (.snd value) := by
  intro target step
  cases step with
  | root step => exact no_root rigid step
  | betaSigmaSnd => exact notPair _ _ rfl
  | congSnd step => exact normal _ step

def freshValue {n : Nat} (term : Tm Head n) : Tm Head (n + 1) :=
  match term with
  | .lam body => body
  | other => .app (Presentation.rename wk other) (.var 0)

def firstValue {n : Nat} (term : Tm Head n) : Tm Head n :=
  match term with
  | .pair first _ => first
  | other => .fst other

def secondValue {n : Nat} (term : Tm Head n) : Tm Head n :=
  match term with
  | .pair _ second => second
  | other => .snd other

theorem fresh_beta {n : Nat} (body : Tm Head (n + 1)) :
    inst0 (.var (0 : Fin (n + 1))) (Presentation.rename (liftRen wk) body) = body := by
  rw [inst0, subst_rename]
  calc
    _ = subst ids body := by
      apply subst_ext
      intro index
      refine Fin.cases rfl (fun index => rfl) index
    _ = body := subst_ids body

theorem fresh_reduces {n : Nat} (term : Tm Head n) :
    WhRed S.R S.roles (.app (Presentation.rename wk term) (.var 0)) (freshValue term) := by
  cases term <;> try exact .refl
  case lam body =>
    simpa only [Presentation.rename, freshValue, fresh_beta] using
      (Relation.ReflTransGen.single (WhStep.beta (R := S.R) (roles := S.roles)
        (Presentation.rename (liftRen wk) body) (.var 0)))

theorem first_reduces {n : Nat} (term : Tm Head n) :
    WhRed S.R S.roles (.fst term) (firstValue term) := by
  cases term <;> try exact .refl
  exact .single (.fstPair _ _)

theorem second_reduces {n : Nat} (term : Tm Head n) :
    WhRed S.R S.roles (.snd term) (secondValue term) := by
  cases term <;> try exact .refl
  exact .single (.sndPair _ _)

include rigid in
theorem fresh_normal {n : Nat} {term : Tm Head n} (normal : Normal (S := S) term) :
    Normal (S := S) (freshValue term) := by
  by_cases isLambda : ∃ body, term = .lam body
  · obtain ⟨body, rfl⟩ := isLambda
    exact normal_lam normal
  · have shape : freshValue term = .app (Presentation.rename wk term) (.var 0) := by
      cases term <;> simp_all [freshValue]
    rw [shape]
    apply normal_app rigid (normal_rename rigid wk normal) (normal_var rigid 0)
    intro body same
    obtain ⟨original, originalShape, _⟩ := TypedEquality.StrongNormalization.rename_eq_lam same
    exact isLambda ⟨original, originalShape⟩

include rigid in
theorem projections_normal {n : Nat} {term : Tm Head n} (normal : Normal (S := S) term) :
    Normal (S := S) (firstValue term) ∧ Normal (S := S) (secondValue term) := by
  by_cases isPair : ∃ first second, term = .pair first second
  · obtain ⟨first, second, rfl⟩ := isPair
    exact normal_pair normal
  · have firstShape : firstValue term = .fst term := by cases term <;> simp_all [firstValue]
    have secondShape : secondValue term = .snd term := by cases term <;> simp_all [secondValue]
    rw [firstShape, secondShape]
    exact ⟨normal_fst rigid normal (fun first second same => isPair ⟨first, second, same⟩),
      normal_snd rigid normal (fun first second same => isPair ⟨first, second, same⟩)⟩

theorem outer_weaken_add {n : Nat} (slots : Finset (Fin n)) :
    outerSupport (slots.image wk ∪ {0}) = slots := by
  ext index
  simp [mem_outerSupport, Finset.mem_image, wk, Fin.succ_inj]

theorem fresh_support {n : Nat} (term : Tm Head n) :
    outerSupport (freshValue term).support = term.support := by
  cases term <;> simp only [freshValue, Tm.support, support_rename, outer_weaken_add]

theorem projections_support {n : Nat} (term : Tm Head n) :
    (firstValue term).support ∪ (secondValue term).support = term.support := by
  cases term <;> simp only [firstValue, secondValue, Tm.support, Finset.union_self]

include rigid in
theorem function_whnf {n : Nat} {term : Tm Head n} (shape : IsFun S.roles term) :
    Whnf S.R S.roles term := by
  rcases shape with ⟨body, rfl⟩ | neutral | ⟨name, args, arity, role, _, _⟩
  · exact lam_whnf S.shape body
  · exact neutral.whnf S.shape
  · rcases role with constructor | ⟨inspect, computes⟩
    · rw [rigid name] at constructor; cases constructor
    · rw [rigid name] at computes; cases computes

theorem pair_whnf_of_shape {n : Nat} {term : Tm Head n} (shape : IsPair S.roles term) :
    Whnf S.R S.roles term := by
  rcases shape with ⟨first, second, rfl⟩ | neutral
  · exact pair_whnf S.shape first second
  · exact neutral.whnf S.shape

end ContextualDependentNormalObservations
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
