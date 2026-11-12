import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesHigher

/-!
# The counterpart of `higherStore` with the argument at its declared type: a kernel statement

**`exactHigherStore`**: over `A : U0, H : (U0 → U0) → U0`,

  `λ f. H f ≐ λ f. f A`  at  `Π (f : U0 → U0). U0`.

It is `higherStore` with the local `f` declared at the type `H` declares for its argument. The top family
(`sortTower`) commits on it, at budget 16; the run is evaluated by the kernel (`exactHigher_committed`).

The run of the top family on `higherStore` itself, evaluated by the kernel alone in a module, exceeds the memory of
the check; no kernel statement of it is made. Its compiled run reads `stuck` (an evaluation), and
`higher_gap_of_ending` reduces the stuck run to that reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-- `(U0 → U0) → U0`, over `A`. -/
def exactHigherFamily : TypeOver ctxA :=
  formIn ctxA (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))
    (by decide +kernel)

/-- `A : U0, H : (U0 → U0) → U0`. -/
abbrev ctxAHe := extend ctxA exactHigherFamily

/-- `Π (f : U0 → U0). U0`, over `A H`. -/
def exactHigherType : TypeOver ctxAHe :=
  formIn ctxAHe (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))
    (by decide +kernel)

/-- `λ f. H f ≐ λ f. f A` at `Π (f : U0 → U0). U0`. -/
def exactHigherEquation : Equation (TotalTerm ctxAHe) :=
  (termIn ctxAHe exactHigherType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxAHe exactHigherType (.lam (.app (.var 0) (.var 2))) (by decide +kernel))

def exactHigherStore : EquationStore (TotalTerm ctxAHe) := [exactHigherEquation]

theorem exactHigher_in_fragment : InFragmentStore exactHigherStore := storeInside_sound (by decide +kernel)

/-- **The top family commits** on `exactHigherStore`, at budget 16. -/
theorem exactHigher_committed : (run (sortTower.solver 16) exactHigherStore 3).readout = .commit := by
  decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
