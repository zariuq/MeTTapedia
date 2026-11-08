import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3Controls

/-!
# A store of the Miller class that R86's in-place step reorders out of it

Over `A B : U0, G : U0 → U0 → U0, X : U0, Z : X, Y : G A B, Y' : G B A`, the store

  `λ x y. G x y ≐ λ x y. G y x`, then the twin `Y ≐ Y'` (at `G A B` on the left, `G B A` on the right), then `X ≐ A`

is in the stratified Miller class (`reorder_stratifiedMiller`): its sides are Miller, and the twin's annotations are
equal under every solution of the intersection before it, which makes `G` take equal values at `(A, B)` and `(B, A)`
(`twin_after_intersection`).

At budget 16 the last family's first round solves `X` in place (it cannot rotate `X`, which `Z` mentions): R86's
separation puts the equations that mention the later declarations first, so the residual store starts with the twin,
whose annotations `G A B` and `G B A` are different codes, and the intersection comes after it
(`reorder_first_round`). Under the identity the twin's annotations are two η-long neutral types with distinct
arguments, so the residual store is outside the class, whose first equation must have equal annotations under the
identity (`…MillerClosureReorderOutside.reorder_leaves_class`). The run is suspended after eight rounds
(`reorder_suspended`).

So the order of the store matters to the class, and R86's separation does not keep it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure.ReorderControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.InPlaceControls
open ContextualDependentShortClosure ContextualDependentShortClosure.Controls ContextualDependentClosure

/-! ## The store -/

/-- `A : U0, B : U0`. -/
def typeB : TypeOver typeContext := formIn typeContext (.head (.sort Tower.zero)) (by decide +kernel)
abbrev withB := extend typeContext typeB

/-- `G : U0 → U0 → U0`. -/
def typeG : TypeOver withB :=
  formIn withB (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)
abbrev withBG := extend withB typeG

/-- `X : U0`. -/
def typeX : TypeOver withBG := formIn withBG (.head (.sort Tower.zero)) (by decide +kernel)
abbrev withBGX := extend withBG typeX

/-- `Z : X`. -/
def typeZ : TypeOver withBGX := formIn withBGX (.var 0) (by decide +kernel)
abbrev withBGXZ := extend withBGX typeZ

/-- `Y : G A B`. -/
def typeY : TypeOver withBGXZ := formIn withBGXZ (.app (.app (.var 2) (.var 4)) (.var 3)) (by decide +kernel)
abbrev withY := extend withBGXZ typeY

/-- `Y' : G B A`. -/
def typeY' : TypeOver withY := formIn withY (.app (.app (.var 3) (.var 4)) (.var 5)) (by decide +kernel)

/-- `A, B, G, X, Z, Y, Y'`. -/
abbrev withTwins := extend withY typeY'

def binaryTwins : TypeOver withTwins :=
  formIn withTwins (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)
def gAB : TypeOver withTwins := formIn withTwins (.app (.app (.var 4) (.var 6)) (.var 5)) (by decide +kernel)
def gBA : TypeOver withTwins := formIn withTwins (.app (.app (.var 4) (.var 5)) (.var 6)) (by decide +kernel)
def universeTwins : TypeOver withTwins := formIn withTwins (.head (.sort Tower.zero)) (by decide +kernel)

/-- `λ x y. G x y ≐ λ x y. G y x`. -/
def symmetric : Equation (TotalTerm withTwins) :=
  (termIn withTwins binaryTwins (.lam (.lam (.app (.app (.var 6) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withTwins binaryTwins (.lam (.lam (.app (.app (.var 6) (.var 0)) (.var 1)))) (by decide +kernel))

/-- `Y ≐ Y'`, at `G A B` on the left and `G B A` on the right. -/
def twin : Equation (TotalTerm withTwins) :=
  (termIn withTwins gAB (.var 1) (by decide +kernel), termIn withTwins gBA (.var 0) (by decide +kernel))

/-- `X ≐ A`. -/
def solveX : Equation (TotalTerm withTwins) :=
  (termIn withTwins universeTwins (.var 3) (by decide +kernel), termIn withTwins universeTwins (.var 6) (by decide +kernel))

def reorderStore : EquationStore (TotalTerm withTwins) := [symmetric, twin, solveX]

/-! ## The store is in the Miller class -/

/-- Contracting `λ x y. M` against two arguments. -/
theorem beta_two {n : Nat} (g a b : Tower.Tm n) :
    inst0 b (subst (liftSub (subst0 a)) (.app (.app (Presentation.rename wk (Presentation.rename wk g)) (.var 1))
      (.var 0))) = .app (.app g a) b ∧
    inst0 b (subst (liftSub (subst0 a)) (.app (.app (Presentation.rename wk (Presentation.rename wk g)) (.var 0))
      (.var 1))) = .app (.app g b) a := by
  have head : inst0 b (subst (liftSub (subst0 a)) (Presentation.rename wk (Presentation.rename wk g))) = g := by
    rw [subst_liftSub_wk]
    change inst0 b (Presentation.rename wk (inst0 a (Presentation.rename wk g))) = g
    rw [inst0_rename_wk, inst0_rename_wk]
  have first : inst0 b (liftSub (subst0 a) 1 : Tower.Tm (n + 1)) = a := by
    change inst0 b (Presentation.rename wk a) = a
    exact inst0_rename_wk b a
  have second : inst0 b (liftSub (subst0 a) 0 : Tower.Tm (n + 1)) = b := rfl
  constructor
  · change Tm.app (.app (inst0 b (subst (liftSub (subst0 a)) (Presentation.rename wk (Presentation.rename wk g))))
      (inst0 b (liftSub (subst0 a) 1))) (inst0 b (liftSub (subst0 a) 0)) = _
    rw [head, first, second]
  · change Tm.app (.app (inst0 b (subst (liftSub (subst0 a)) (Presentation.rename wk (Presentation.rename wk g))))
      (inst0 b (liftSub (subst0 a) 0))) (inst0 b (liftSub (subst0 a) 1)) = _
    rw [head, first, second]

/-- **The twin's annotations are equal under every solution of the intersection.** -/
theorem twin_after_intersection : StratifiedAt setting.levels [symmetric] twin := by
  intro Δ σ solved
  have held := ((models_iff setting.levels σ [symmetric]).mp solved symmetric List.mem_cons_self).2
  have binaryCode : symmetric.1.1.code =
      .pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) := by decide +kernel
  have leftCode : twin.1.1.code = .app (.app (.var 4) (.var 6)) (.var 5) := by decide +kernel
  have rightCode : twin.2.1.code = .app (.app (.var 4) (.var 5)) (.var 6) := by decide +kernel
  rw [binaryCode] at held
  rw [leftCode, rightCode]
  change Equal setting.R Δ.raw
      (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 4))) (.var 1)) (.var 0))))
      (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 4))) (.var 0)) (.var 1))))
      (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))) at held
  change TypeEq setting.R Δ.raw (.app (.app (σ.substitution 4) (σ.substitution 6)) (σ.substitution 5))
    (.app (.app (σ.substitution 4) (σ.substitution 5)) (σ.substitution 6))
  have ta : Typed setting.R Δ.raw (σ.substitution 6) (.head (.sort Tower.zero)) := σ.typed 6
  have tb : Typed setting.R Δ.raw (σ.substitution 5) (.head (.sort Tower.zero)) := σ.typed 5
  have applied := Derivable.appCong (Derivable.appCong held (.refl ta)) (.refl tb)
  change Equal setting.R Δ.raw _ _ (.head (.sort Tower.zero)) at applied
  obtain ⟨leftBeta, rightBeta⟩ := beta_two (σ.substitution 4) (σ.substitution 6) (σ.substitution 5)
  have leftRed : WhRed setting.R setting.roles
      (.app (.app (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 4)))
        (.var 1)) (.var 0)))) (σ.substitution 6)) (σ.substitution 5))
      (.app (.app (σ.substitution 4) (σ.substitution 6)) (σ.substitution 5)) := by
    rw [← leftBeta]
    exact (Relation.ReflTransGen.single (WhStep.appFun (WhStep.beta _ _))).tail (WhStep.beta _ _)
  have rightRed : WhRed setting.R setting.roles
      (.app (.app (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 4)))
        (.var 0)) (.var 1)))) (σ.substitution 6)) (σ.substitution 5))
      (.app (.app (σ.substitution 4) (σ.substitution 5)) (σ.substitution 6)) := by
    rw [← rightBeta]
    exact (Relation.ReflTransGen.single (WhStep.appFun (WhStep.beta _ _))).tail (WhStep.beta _ _)
  have left := (WhRed.preserve TowerModel.facts TowerModel.roots Δ.formed leftRed
    (Equal.typed applied Δ.formed).1).2
  have right := (WhRed.preserve TowerModel.facts TowerModel.roots Δ.formed rightRed
    (Equal.typed applied Δ.formed).2).2
  exact ⟨.sort Tower.zero, .sort _, left.symm.trans (applied.trans right)⟩

/-- **The store is in the stratified Miller class.** -/
theorem reorder_stratifiedMiller : StratifiedMiller setting.levels reorderStore := by
  have millerSymmetric : sidesMiller symmetric = true := by decide +kernel
  have millerTwin : sidesMiller twin = true := by decide +kernel
  have millerX : sidesMiller solveX = true := by decide +kernel
  intro before after equation split
  match before, split with
  | [], split =>
      simp only [reorderStore, List.nil_append] at split
      obtain ⟨rfl, -⟩ := split
      exact ⟨sidesMiller_sound millerSymmetric, fun σ _ => (symmetric.1.1.reindex σ).isType.refl⟩
  | [one], split =>
      simp only [reorderStore, List.cons_append, List.nil_append] at split
      obtain ⟨rfl, rfl, -⟩ := split
      exact ⟨sidesMiller_sound millerTwin, twin_after_intersection⟩
  | [one, two], split =>
      simp only [reorderStore, List.cons_append, List.nil_append] at split
      obtain ⟨rfl, rfl, rfl, -⟩ := split
      exact ⟨sidesMiller_sound millerX, fun σ _ => (solveX.1.1.reindex σ).isType.refl⟩
  | _ :: _ :: _ :: _, split =>
      have rest := (List.cons.inj (List.cons.inj (List.cons.inj split).2).2).2
      exact absurd rest.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

/-! ## The first round reorders it -/

/-- The first equation's annotations are the same code. -/
def headHomogeneous {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [] => true
  | equation :: _ => decide (equation.1.1.code = equation.2.1.code)

/-- After one round: two equations left, Miller sides, a first equation whose annotations are different codes. -/
noncomputable def reorderedCheck : Bool :=
  match run inPlaceOnly reorderStore 1 with
  | .cutoff state => decide (state.remaining.length = 2) && state.remaining.all sidesMiller &&
      !headHomogeneous state.remaining
  | _ => false

theorem reorderedCheck_true : reorderedCheck = true := by decide +kernel

/-- **The first round leaves a heterogeneous twin at the head**: the in-place answer for `X` moved the twin before the
intersection it depends on. -/
theorem reorder_first_round :
    ∃ state : ContextualDependentUpdate.Update setting.levels reorderStore,
      run inPlaceOnly reorderStore 1 = .cutoff state ∧ state.remaining.length = 2 ∧
      (∀ equation ∈ state.remaining, FragmentSidesMiller equation) ∧
      headHomogeneous state.remaining = false := by
  have key := reorderedCheck_true
  unfold reorderedCheck at key
  generalize ran : run inPlaceOnly reorderStore 1 = outcome at key
  cases outcome with
  | cutoff state =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true] at key
      obtain ⟨⟨length, sides⟩, heterogeneous⟩ := key
      exact ⟨state, rfl, length, fun equation member => sidesMiller_sound (sides equation member), heterogeneous⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

/-- **The last family suspends on the store** after eight rounds. -/
theorem reorder_suspended : (run inPlaceOnly reorderStore 8).readout = .suspended := by decide +kernel

end ContextualDependentMillerClosure.ReorderControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
