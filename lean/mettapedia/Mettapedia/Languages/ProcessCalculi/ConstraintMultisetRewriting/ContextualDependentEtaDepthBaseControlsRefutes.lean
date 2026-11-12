import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseGap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily

/-!
# A refutation at a base type that is an application

Over `A`, at `Π (G : U0 → U0) (g : U1 → G A). G A`, the equation `λ G g. g U0 ≐ λ G g. g (U0 → U0)` has two spines of
the local `g` whose arguments are types of distinct kinds, at the base type `G A`. The Σ family is stuck on it
(`kindsApplied_sigma_stuck`); the base family refutes it with a certified refutation (`kindsApplied_base_refuted`),
so it is unsolvable (`kindsApplied_unsolvable`).
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

/-- `Π (G : U0 → U0) (g : U1 → G A). G A` over `A`. -/
def familyKinds : TypeOver ctxA := formIn ctxA
  (.pi (.pi u0 u0) (.pi (.pi u1 (.app (.var 1) (.var 2))) (.app (.var 1) (.var 2)))) (by decide +kernel)

/-- `λ G g. g U0 ≐ λ G g. g (U0 → U0)`: arguments of distinct kinds. -/
def kindsApplied : EquationStore (TotalTerm ctxA) :=
  [(termIn ctxA familyKinds (.lam (.lam (.app (.var 0) u0))) (by decide +kernel),
    termIn ctxA familyKinds (.lam (.lam (.app (.var 0) (.pi u0 u0)))) (by decide +kernel))]

/-- **The Σ family is stuck in its first round** on the store, at budget 16. -/
theorem kindsApplied_sigma_stuck : isStuck (run (sigmaTower.solver 16) kindsApplied 1) = true := by
  decide +kernel

/-- **The base family refutes the store**, with a certified refutation. -/
theorem kindsApplied_base_refuted : (run (baseTower.solver 16) kindsApplied 8).readout = .refuted := by
  decide +kernel

theorem kindsApplied_unsolvable : ¬ (frames setting.levels).Solvable kindsApplied :=
  Outcome.readout_eq_refuted kindsApplied_base_refuted

end ContextualDependentEtaDepth.BaseControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
