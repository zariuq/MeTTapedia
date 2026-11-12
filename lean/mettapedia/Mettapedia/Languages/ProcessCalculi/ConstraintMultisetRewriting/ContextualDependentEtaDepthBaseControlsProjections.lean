import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseGap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily

/-!
# Equal projections of two spines at a base type that is an application

Over `A : U0, X : U0`, at `Π (G : U0 → U0) (g : U0 → Σ (_ : G A). U0). G A`, the equation
**`λ G g. fst (g X) ≐ λ G g. fst (g A)`** (`projStore`) is in the dynamic pattern fragment (`proj_in_fragment`). Its
sides are equal projections of two spines of the local `g`, at the base type `G A`. The Σ family is stuck on it
(`proj_sigma_stuck`); the decomposition at every base type reads the projected spines (`proj_spines_read`) and the
base family commits (`proj_base_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.BaseControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls

/-- `Π (G : U0 → U0) (g : U0 → Σ (_ : G A). U0). G A` over `A, X`. -/
def projFamily : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.pi u0 (.sigma (.app (.var 1) (.var 3)) u0)) (.app (.var 1) (.var 3)))) (by decide +kernel)

/-- `λ G g. fst (g X) ≐ λ G g. fst (g A)`. -/
def projEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX projFamily (.lam (.lam (.fst (.app (.var 0) (.var 2))))) (by decide +kernel),
    termIn ctxAX projFamily (.lam (.lam (.fst (.app (.var 0) (.var 3))))) (by decide +kernel))
def projStore : EquationStore (TotalTerm ctxAX) := [projEquation]

theorem proj_in_fragment : InFragmentStore projStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl projEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The decomposition at every base type reads the projected spines.** -/
theorem proj_spines_read : (spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    projEquation.1.1.code projEquation.1.2.code projEquation.2.2.code).isSome = true := by decide +kernel

/-- **The Σ family is stuck in its first round** on the store, at budget 16. -/
theorem proj_sigma_stuck : isStuck (run (sigmaTower.solver 16) projStore 1) = true := by decide +kernel

/-- **The base family commits on the store.** -/
theorem proj_base_committed : (run (baseTower.solver 16) projStore 8).readout = .commit := by decide +kernel

end ContextualDependentEtaDepth.BaseControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
