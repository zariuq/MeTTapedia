import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhasesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupControls

/-!
# Controls: a glb group mixed with arrow codes, in the tree's tower

The two-level-variable store (`λ x. X x ≐ λ x. Y x` over `X : U0 → U_a, Y : U0 → U_b`, where neither codomain lies
below the other) with an equation between arrow codes (`Z ≐ Π (_ : U0). U0`, `Z : U1`): the level equation is read by
the Miller reader, whose round meets the codomains at their greatest lower bound, so the store is a mixed store
(`lg_inMixed`) and the mixed solver, one rank, decides it (`lg_committed`, `lg_principal`). The solver of glb groups
alone does not (`lg_groups_alone`): the arrow equation is outside its fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

def lgZ : TypeOver ctxAB := formIn ctxAB (.head U1) (by decide +kernel)
/-- `X : U0 → U_a, Y : U0 → U_b, Z : U1`. -/
abbrev ctxLG := extend ctxAB lgZ
def lgAbType : TypeOver ctxLG := formIn ctxLG (.pi (.head U0) (.head Uab)) (by decide +kernel)
def lgUType : TypeOver ctxLG := formIn ctxLG (.head U1) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`. -/
def lgLevel : Equation (TotalTerm ctxLG) :=
  (termIn ctxLG lgAbType (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
    termIn ctxLG lgAbType (.lam (.app (.var 2) (.var 0))) (by decide +kernel))

/-- `Z ≐ Π (_ : U0). U0` at `U1`. -/
def lgArrow : Equation (TotalTerm ctxLG) :=
  (termIn ctxLG lgUType (.var 0) (by decide +kernel),
    termIn ctxLG lgUType (.pi (.head U0) (.head U0)) (by decide +kernel))

def lgStore : EquationStore (TotalTerm ctxLG) := [lgLevel, lgArrow]

/-- **A mixed store**: the level equation read by the Miller reader, the other between arrow codes. -/
theorem lg_inMixed : inMixedB ExecutableTowerChoices.choices lgStore = true := by decide +kernel

/-- **The mixed solver decides it.** -/
theorem lg_committed : decidedKind (Decided.ofRun towerMixedSolver 8 lgStore) = 1 := by decide +kernel

theorem lg_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxLG),
    (frames setting.levels).Principal lgStore answer := principal_of_decided lg_committed

/-- **The solver of glb groups alone does not.** -/
theorem lg_groups_alone : decidedKind (Decided.ofRun glbTowerSolver 8 lgStore) = 0 := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
