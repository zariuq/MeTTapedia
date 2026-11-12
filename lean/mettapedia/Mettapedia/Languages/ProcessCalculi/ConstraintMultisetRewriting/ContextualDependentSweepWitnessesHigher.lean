import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesSort

/-!
# An unknown of second order applied to a local function declared below its argument type

**`higherStore`**: over `A : U0, H : (U0 → U1) → U1`,

  `λ f. H f ≐ λ f. f A`  at  `Π (f : U0 → U0). U1`.

The local `f` is declared at `U0 → U0`, and `H` declares `U0 → U1` for its argument; `f` is usable there because
a Π type is below the Π type with a larger codomain. The store is in the dynamic pattern fragment and solvable, by
`H := λ g. g A` (`higher_solvable`), and the top family (`sortTower`) is stuck on it wherever its compiled run reads
`stuck`: the pattern rules do not read an argument whose declared type is below, and not equal to, the type the
unknown declares for it.
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

/-- `(U0 → U1) → U1`, over `A`. -/
def higherFamily : TypeOver ctxA :=
  formIn ctxA (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))))
    (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `A : U0, H : (U0 → U1) → U1`. -/
abbrev ctxAH := extend ctxA higherFamily

/-- `Π (f : U0 → U0). U1`, over `A H`. -/
def higherType : TypeOver ctxAH :=
  formIn ctxAH (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
    (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `λ f. H f ≐ λ f. f A` at `Π (f : U0 → U0). U1`. -/
def higherEquation : Equation (TotalTerm ctxAH) :=
  (termIn ctxAH higherType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxAH higherType (.lam (.app (.var 0) (.var 2))) (by decide +kernel))

def higherStore : EquationStore (TotalTerm ctxAH) := [higherEquation]

/-- The raw problem of the sweep. -/
def higherProblem : Problem :=
  { unknowns := [.u0, .pi (.pi .u0 .u1) .u1],
    equations := [(.pi (.pi .u0 .u0) .u1, .lam (.app (.var 1) (.var 0)), .lam (.app (.var 0) (.var 2)))] }

theorem higher_in_fragment : InFragmentStore higherStore := storeInside_sound (by decide +kernel)

/-- `H := λ g. g A`. -/
def higherAnswer : ctxA ⟶ ctxAH :=
  Elimination.instantiate ctxA (termIn ctxA higherFamily (.lam (.app (.var 0) (.var 1))) (by decide +kernel)).2

/-- **The store is solvable**, by `H := λ g. g A`. -/
theorem higher_solvable : (frames setting.levels).Solvable higherStore :=
  solvable_by higherAnswer higherEquation.1.2 higherEquation.2.2 (by decide +kernel)

/-- **A solvable store of the fragment on which the top family is stuck** wherever its compiled run reads
`stuck`. -/
theorem higher_gap_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxAH higherStore = .stuck) :
    InFragmentStore higherStore ∧ (frames setting.levels).Solvable higherStore ∧
      isStuck (run (sortTower.solver fuel) higherStore rounds) = true :=
  ⟨higher_in_fragment, higher_solvable, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
