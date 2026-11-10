import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPieces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPieceGap

/-!
# Controls for the piece family

* **The piece family commits** on `PieceControls.pieceStore`, where the skeleton family is stuck
  (`piece_piece_committed`), and on its Σ twin over `A X : U0`,
  **`(λ k. k X, refl X) ≐ (λ k. k A, refl A)`** at `Σ (f : (U0 → U0) → U0). Id U0 (f (λ w. w)) (f (λ w. w))`
  (`pairStore`): in the dynamic pattern fragment (`pair_in_fragment`), solvable by `X := A` (`pair_solvable`), and the
  skeleton family is stuck in its first round on it (`pair_skeleton_stuck`), its second piece being annotated by
  `Id U0 ((λ k. k X) (λ w. w)) ((λ k. k X) (λ w. w))`.
* It keeps the outcomes of the η-long prepared and skeleton families on their controls, and decides R119's 44 census
  stores as the in-place family does (`piece_of_final`).
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
open ContextualDependentIntersectionGeneral.InPlaceControls ContextualDependentIntersectionGeneral.DeadControls
open ContextualDependentEtaDepth.Controls

/-! ## The Σ twin of the piece store -/

/-- `Σ (f : (U0 → U0) → U0). Id U0 (f (λ w. w)) (f (λ w. w))` over `A X : U0`. -/
def pairType : TypeOver two := formIn two
  (.sigma (.pi (.pi u0 u0) u0) (.id u0 (.app (.var 0) (.lam (.var 0))) (.app (.var 0) (.lam (.var 0)))))
  (by decide +kernel)

/-- `(λ k. k X, refl X) ≐ (λ k. k A, refl A)`. -/
def pairEquation : Equation (TotalTerm two) :=
  (termIn two pairType (.pair (.lam (.app (.var 0) (.var 1))) (.refl (.var 0))) (by decide +kernel),
    termIn two pairType (.pair (.lam (.app (.var 0) (.var 2))) (.refl (.var 1))) (by decide +kernel))
def pairStore : EquationStore (TotalTerm two) := [pairEquation]

theorem pair_in_fragment : InFragmentStore pairStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl pairEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem pair_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ContextualDependentInversion.Controls.typeContext.raw (subst answer.substitution pairEquation.1.2.code)
      (subst answer.substitution pairEquation.2.2.code)
      (subst answer.substitution pairEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The Σ twin is solvable**, by `X := A`. -/
theorem pair_solvable : (frames setting.levels).Solvable pairStore := by
  refine ⟨ContextualDependentInversion.Controls.typeContext, answer,
    (models_iff setting.levels answer pairStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(pairType.reindex answer).isType.refl, ?_⟩
  have check := pair_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ContextualDependentInversion.Controls.typeContext.raw (subst answer.substitution pairEquation.1.2.code)
      (subst answer.substitution pairEquation.2.2.code) (subst answer.substitution pairEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ContextualDependentInversion.Controls.typeContext.formed (pairEquation.1.2.reindex answer).typed
        (pairEquation.2.2.reindex answer).typed

/-- **The skeleton family is stuck in its first round** on the Σ twin. -/
theorem pair_skeleton_stuck : isStuck (run (skeletonTower.solver 16) pairStore 1) = true := by decide +kernel

/-! ## The piece family -/

/-- **The piece family commits on the piece store.** -/
theorem piece_piece_committed : (run (pieceTower.solver 16) pieceStore 8).readout = .commit := by decide +kernel
/-- **The piece family commits on its Σ twin.** -/
theorem pair_piece_committed : (run (pieceTower.solver 16) pairStore 8).readout = .commit := by decide +kernel

theorem shallow_piece_refuted : (run (pieceTower.solver 16) shallowStore 8).readout = .refuted := by decide +kernel
theorem deep_piece_refuted : (run (pieceTower.solver 16) deepStore 8).readout = .refuted := by decide +kernel
theorem twice_piece_refuted : (run (pieceTower.solver 16) twiceStore 8).readout = .refuted := by decide +kernel
theorem other_piece_refuted : (run (pieceTower.solver 16) otherStore 8).readout = .refuted := by decide +kernel
theorem solvable_piece_committed : (run (pieceTower.solver 16) solvableStore 8).readout = .commit := by
  decide +kernel
theorem flexible_piece_refuted :
    (run (pieceTower.solver 16) ContextualDependentEtaDepth.Controls.flexibleStore 8).readout = .refuted := by
  decide +kernel

/-! ## R119's census -/

/-- **R119's census under the piece family.** -/
theorem piece_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (pieceTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := skeleton_of_final final
  refine ⟨decided, ?_⟩
  have skeletonDecided : (run (skeletonTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact piece_run_of_skeleton (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    skeletonDecided

end ContextualDependentEtaDepth.PieceControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
