import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairs

/-!
# The refutation of a universe in a component of a pair: its witness and its controls

**`pairSortStore`**, `p ≐ ⟨A, U0⟩` at `Σ (_ : U0). U1` with `p : Σ (_ : U0). U0`: the rule reads it
(`pairSort_read`), so the top family refutes it wherever its compiled run reads `refuted`
(`pairSort_refuted_of_ending`).

**Control: the reading of the codes alone refutes a solvable store.** `pairWideStore`, `q ≐ ⟨A, U0⟩` at
`Σ (_ : U0). U1` with `q : Σ (_ : U0). U1`, is solved by `q := ⟨A, U0⟩` (`pairWide_solvable`). Its annotation and
right side have the reading of the rule at `U0` (`pairWide_code_read`): a pair that holds a universe where the
lowered annotation does not. What makes the rule sound is the check that the left side is a term of the lowered
type, which fails here: the rule does not read the store (`pairWide_not_read`).
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

/-- **The rule reads `pairSortStore`**, at budget 16. -/
theorem pairSort_read : (towerPairRefuted 16 pairSortStore).isSome = true := by decide +kernel

/-- **A store of the fragment without solution that the top family refutes** wherever its compiled run reads
`refuted`. -/
theorem pairSort_refuted_of_ending {fuel rounds : Nat}
    (read : endingPair fuel rounds ctxAp pairSortStore = .refuted) :
    InFragmentStore pairSortStore ∧ ¬ (frames setting.levels).Solvable pairSortStore ∧
      endingOf (run (pairTower.solver fuel) pairSortStore rounds) = .refuted :=
  ⟨pairSort_in_fragment, pairSort_unsolvable, (endingPair_run fuel rounds pairSortStore).trans read⟩

/-- `Σ (_ : U0). U1`, over `A`. -/
def pairWideFamily : TypeOver ctxA :=
  formIn ctxA (.sigma (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `A : U0, q : Σ (_ : U0). U1`. -/
abbrev ctxAq := extend ctxA pairWideFamily

/-- `Σ (_ : U0). U1`, over `A q`. -/
def pairWideType : TypeOver ctxAq :=
  formIn ctxAq (.sigma (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `q ≐ ⟨A, U0⟩` at `Σ (_ : U0). U1`. -/
def pairWideEquation : Equation (TotalTerm ctxAq) :=
  (termIn ctxAq pairWideType (.var 0) (by decide +kernel),
    termIn ctxAq pairWideType (.pair (.var 1) (.head (.sort Tower.zero))) (by decide +kernel))

def pairWideStore : EquationStore (TotalTerm ctxAq) := [pairWideEquation]

theorem pairWide_in_fragment : InFragmentStore pairWideStore := storeInside_sound (by decide +kernel)

/-- `q := ⟨A, U0⟩`. -/
def pairWideAnswer : ctxA ⟶ ctxAq :=
  Elimination.instantiate ctxA
    (termIn ctxA pairWideFamily (.pair (.var 0) (.head (.sort Tower.zero))) (by decide +kernel)).2

/-- **The store is solvable**, by `q := ⟨A, U0⟩`. -/
theorem pairWide_solvable : (frames setting.levels).Solvable pairWideStore :=
  solvable_by pairWideAnswer pairWideEquation.1.2 pairWideEquation.2.2 (by decide +kernel)

/-- The annotation and the right side have the reading of the rule at `U0`. -/
theorem pairWide_code_read :
    (pairCodes (S := setting) ExecutableTowerChoices.choices
      ContextualDependentNormalCheckingTower.head_typing_unique (.sort Tower.zero) pairWideEquation.1.1.code
      pairWideEquation.2.2.code).isEmpty = false := by decide +kernel

/-- **The rule does not read the store**: its left side is not a term of the lowered type. -/
theorem pairWide_not_read : (towerPairRefuted 16 pairWideStore).isNone = true := by decide +kernel

/-- **The reading of the codes alone refutes a solvable store.** -/
theorem naive_pair_refutation_unsound :
    (pairCodes (S := setting) ExecutableTowerChoices.choices
      ContextualDependentNormalCheckingTower.head_typing_unique (.sort Tower.zero) pairWideEquation.1.1.code
      pairWideEquation.2.2.code).isEmpty = false ∧
      (frames setting.levels).Solvable pairWideStore :=
  ⟨pairWide_code_read, pairWide_solvable⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
