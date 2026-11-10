import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSkeletonControls

/-!
# A gap in the spine decomposition: piece annotations with a redex on an abstraction

Over `A X : U0`, at `Π (h : Π (f : (U0 → U0) → U0) (z : Id U0 (f (λ w. w)) (f (λ w. w))). U0). U0`, the equation
**`λ h. h (λ k. k X) (refl X) ≐ λ h. h (λ k. k A) (refl A)`** (`pieceStore`) is in the dynamic pattern fragment
(`piece_in_fragment`) and solvable by `X := A` (`piece_solvable`). The skeleton family is stuck in its first round on it
at budgets 16 and 64, and so is the under-binder family at 256 (`piece_skeleton_stuck`, `piece_skeleton_stuck_64`,
`piece_under_stuck_256`).

The two sides are spines of one local with one skeleton, at a rigid base. Their decomposition needs the annotation of
the second argument, `h`'s second domain at the first argument, `Id U0 ((λ k. k X) (λ w. w)) ((λ k. k X) (λ w. w))`.
The executable formation of types runs the bidirectional synthesizer, which reads a redex only when its argument
synthesizes; an abstraction does not, so that annotation is not formed even at budget 256
(`pieceType_not_formed`, `closedPieceType_not_formed`), while its normal form `Id U0 X X` is (`pieceNormal_formed`).
A redex `(λ y. y) X` whose argument synthesizes is formed (`redex_formed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.PieceControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4

abbrev two := ContextualDependentInversion.Controls.withExtra

def u0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

/-- `Π (h : Π (f : (U0 → U0) → U0) (z : Id U0 (f (λ w. w)) (f (λ w. w))). U0). U0` over `A X : U0`. -/
def higher : TypeOver two := formIn two
  (.pi (.pi (.pi (.pi u0 u0) u0) (.pi (.id u0 (.app (.var 0) (.lam (.var 0))) (.app (.var 0) (.lam (.var 0)))) u0))
    u0) (by decide +kernel)

/-- `λ h. h (λ k. k X) (refl X) ≐ λ h. h (λ k. k A) (refl A)`. -/
def pieceEquation : Equation (TotalTerm two) :=
  (termIn two higher (.lam (.app (.app (.var 0) (.lam (.app (.var 0) (.var 2)))) (.refl (.var 1))))
      (by decide +kernel),
    termIn two higher (.lam (.app (.app (.var 0) (.lam (.app (.var 0) (.var 3)))) (.refl (.var 2))))
      (by decide +kernel))
def pieceStore : EquationStore (TotalTerm two) := [pieceEquation]

theorem piece_in_fragment : InFragmentStore pieceStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl pieceEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `X := A`. -/
def answer : ContextualDependentInversion.Controls.typeContext ⟶ two :=
  Elimination.instantiate ContextualDependentInversion.Controls.typeContext
    (termIn ContextualDependentInversion.Controls.typeContext ContextualDependentInversion.Controls.extraType (.var 0)
      (by decide +kernel)).2

theorem piece_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ContextualDependentInversion.Controls.typeContext.raw (subst answer.substitution pieceEquation.1.2.code)
      (subst answer.substitution pieceEquation.2.2.code)
      (subst answer.substitution pieceEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `X := A`. -/
theorem piece_solvable : (frames setting.levels).Solvable pieceStore := by
  refine ⟨ContextualDependentInversion.Controls.typeContext, answer,
    (models_iff setting.levels answer pieceStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(higher.reindex answer).isType.refl, ?_⟩
  have check := piece_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ContextualDependentInversion.Controls.typeContext.raw (subst answer.substitution pieceEquation.1.2.code)
      (subst answer.substitution pieceEquation.2.2.code) (subst answer.substitution pieceEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ContextualDependentInversion.Controls.typeContext.formed (pieceEquation.1.2.reindex answer).typed
        (pieceEquation.2.2.reindex answer).typed

/-- **The skeleton family is stuck in its first round** on the store, at budget 16. -/
theorem piece_skeleton_stuck : isStuck (run (skeletonTower.solver 16) pieceStore 1) = true := by decide +kernel
theorem piece_skeleton_stuck_64 : isStuck (run (skeletonTower.solver 64) pieceStore 1) = true := by decide +kernel
/-- **The under-binder family too**, at budget 256. -/
theorem piece_under_stuck_256 : isStuck (run (underTower.solver 256) pieceStore 1) = true := by decide +kernel

/-- `Id U0 ((λ k. k X) (λ w. w)) ((λ k. k X) (λ w. w))` is not formed. -/
theorem pieceType_not_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 256 two
    (.id u0 (.app (.lam (.app (.var 0) (.var 1))) (.lam (.var 0)))
      (.app (.lam (.app (.var 0) (.var 1))) (.lam (.var 0))))).isSome = false := by decide +kernel

/-- The same under the abstraction of `h`, as the decomposition closes its pieces. -/
theorem closedPieceType_not_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 256 two
    (.pi (.pi (.pi (.pi u0 u0) u0) (.pi (.id u0 (.app (.var 0) (.lam (.var 0))) (.app (.var 0) (.lam (.var 0)))) u0))
      (.id u0 (.app (.lam (.app (.var 0) (.var 2))) (.lam (.var 0)))
        (.app (.lam (.app (.var 0) (.var 2))) (.lam (.var 0)))))).isSome = false := by decide +kernel

/-- Its normal form `Id U0 X X` is formed. -/
theorem pieceNormal_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 two
    (.id u0 (.var 0) (.var 0))).isSome = true := by decide +kernel

/-- A redex whose argument synthesizes, `(λ y. y) X`, is formed. -/
theorem redex_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 64 two
    (.app (.lam (.var 0)) (.var 0))).isSome = true := by decide +kernel

end ContextualDependentEtaDepth.PieceControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
