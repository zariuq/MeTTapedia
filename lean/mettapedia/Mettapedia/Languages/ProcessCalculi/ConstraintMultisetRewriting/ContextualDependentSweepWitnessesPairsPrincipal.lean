import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairsRaisedRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjectiveSigma

/-!
# `pairRaisedStore` has a principal answer

`pairRaisedStore`, `p ≐ ⟨A, A⟩` at `Σ (_ : U0). U1` with `A : U0, p : Σ (_ : U0). U0`, on which the top family is
stuck, read at `Σ (_ : U0). U0` has exactly its solutions (`pairLowered_solves`, by
`ContextualDependentUniverseInjective.LowersWithin.equal_iff`), and the top family commits on that reading
(`pairLowered_committed`, evaluated by the kernel at budget 16). So the store has a principal answer
(`pairRaised_principal`): what is missing is the search that finds the lowered annotation through a component of a
Σ type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective ContextualDependentRigidFormers
open ContextualDependentTwinsUnder

/-- `Σ (_ : U0). U0`, over `A p`. -/
def pairLoweredType : TypeOver ctxAp :=
  formIn ctxAp (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `p ≐ ⟨A, A⟩` at `Σ (_ : U0). U0`. -/
def pairLoweredEquation : Equation (TotalTerm ctxAp) :=
  (termIn ctxAp pairLoweredType (.var 0) (by decide +kernel),
    termIn ctxAp pairLoweredType (.pair (.var 1) (.var 1)) (by decide +kernel))

def pairLoweredStore : EquationStore (TotalTerm ctxAp) := [pairLoweredEquation]

/-- **The equation at the lowered annotation has exactly the solutions of the equation.** -/
theorem pairLowered_solves {Δ : Context setting.R} (σ : Δ ⟶ ctxAp) :
    (frames setting.levels).Solves σ pairLoweredEquation ↔ (frames setting.levels).Solves σ pairRaisedEquation := by
  have smallCode : pairLoweredType.code = .sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
    formIn_code _ _ _
  have largeCode : pairRaisedType.code =
      .sigma (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  have isSmall : IsType setting.R Δ.raw (subst σ.substitution pairLoweredType.code) :=
    (pairLoweredType.reindex σ).isType
  have isLarge : IsType setting.R Δ.raw (subst σ.substitution pairRaisedType.code) :=
    (pairRaisedType.reindex σ).isType
  have typedLeft : Typed setting.R Δ.raw (subst σ.substitution pairLoweredEquation.1.2.code)
      (subst σ.substitution pairLoweredType.code) := pairLoweredEquation.1.2.typed.substitute σ.typed
  have typedRight : Typed setting.R Δ.raw (subst σ.substitution pairLoweredEquation.2.2.code)
      (subst σ.substitution pairLoweredType.code) := pairLoweredEquation.2.2.typed.substitute σ.typed
  have lowers : LowersWithin setting.R (subst σ.substitution pairLoweredType.code)
      (subst σ.substitution pairRaisedType.code) := by
    rw [smallCode, largeCode]
    exact .sigmaSecond (.sort (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have same := lowers.equal_iff (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete Δ.formed isSmall isLarge
    typedLeft typedRight
  constructor
  · intro held
    have read := (solves_raw (S := setting) σ pairLoweredEquation).mp held
    exact (solves_raw (S := setting) σ pairRaisedEquation).mpr ⟨IsType.refl isLarge, same.mpr read.2⟩
  · intro held
    have read := (solves_raw (S := setting) σ pairRaisedEquation).mp held
    exact (solves_raw (S := setting) σ pairLoweredEquation).mpr ⟨IsType.refl isSmall, same.mp read.2⟩

/-- The store at the lowered annotation has exactly the solutions of the store. -/
theorem pairLowered_equivalent : (frames setting.levels).Equivalent pairRaisedStore pairLoweredStore :=
  fun _ σ =>
    ⟨fun solved equation member => by
        rw [List.mem_singleton.mp member]
        exact (pairLowered_solves σ).mpr (solved pairRaisedEquation List.mem_cons_self),
      fun solved equation member => by
        rw [List.mem_singleton.mp member]
        exact (pairLowered_solves σ).mp (solved pairLoweredEquation List.mem_cons_self)⟩

/-- **`pairRaisedStore` read at `Σ (_ : U0). U0`**, as an update of `pairRaisedStore`. -/
def pairLoweredUpdate : Update setting.levels pairRaisedStore :=
  collapseOf (S := setting) ⟨pairLoweredStore, pairLowered_equivalent⟩

/-- **The top family commits on the store at the lowered annotation**, at budget 16. -/
theorem pairLowered_committed :
    (run (sortTower.solver 16) pairLoweredUpdate.remaining 3).readout = .commit := by decide +kernel

/-- **`pairRaisedStore` has a principal answer.** -/
theorem pairRaised_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAp), (frames setting.levels).Principal pairRaisedStore answer := by
  cases outcome : run (sortTower.solver 16) pairLoweredUpdate.remaining 3 with
  | solved state finished => exact ⟨_, _, (pairLoweredUpdate.then state).completed finished⟩
  | stuck _ =>
      have committed := pairLowered_committed
      rw [outcome] at committed
      cases committed
  | refuted _ =>
      have committed := pairLowered_committed
      rw [outcome] at committed
      cases committed
  | cutoff _ =>
      have committed := pairLowered_committed
      rw [outcome] at committed
      cases committed

/-- **A store of the fragment that has a principal answer and on which the top family is stuck**: the missing
piece is the search for the lowered annotation through a component of a Σ type. -/
theorem pairRaised_missing_search :
    InFragmentStore pairRaisedStore ∧
      (∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAp),
        (frames setting.levels).Principal pairRaisedStore answer) ∧
      isStuck (run (sortTower.solver 16) pairRaisedStore 1) = true :=
  ⟨pairRaised_in_fragment, pairRaised_principal, pairRaised_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
