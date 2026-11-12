import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseGap

/-!
# Witnesses of the stuck families found by the sweep

The sweep of elimination spines by shape (`spineProblems`) finds stores of the dynamic pattern fragment on which the
base family is stuck. They fall in two families, each with one witness here over `A : U0, X : U0`,
solvable by `X := A`:

* **A projection below an application, at a base type that is an application** (`belowStore`):
  `λ G g. (fst g) X ≐ λ G g. (fst g) A` at `Π (G : U0 → U0) (g : Σ (_ : U0 → G A). U0). G A`.
* **A projection at a Σ base type** (`sigmaBaseStore`):
  `λ G g. fst (g X) ≐ λ G g. fst (g A)` at `Π (G : U0 → U0) (g : U0 → Σ (_ : Σ U0 U0). U0). Σ U0 U0`.

and a third store of the first family, the one R124 could not run in the kernel:

* **Two projections above an application, at a base type that is an application** (`nestedStore`):
  `λ G g. fst (fst (g X)) ≐ λ G g. fst (fst (g A))` at `Π (G : U0 → U0) (g : U0 → Σ (_ : Σ (_ : G A). U0). U0). G A`.

Each is in the fragment by the decided membership test (`*_in_fragment`) and solvable (`*_solvable`); the raw problem
of the sweep is recorded beside it (`*Problem`). The compiled run of the base family ends stuck on each at budgets
16, 64 and 256; the kernel statements of stuckness are in `ContextualDependentSweepWitnessesStuck`.

**Controls.** With a universe as base type the first sides are read (`belowUniverse_*`), and with the projection
above the application at the applied base they are read (R124's `proj_base_committed`).
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

/-- **A one-equation store over `A X` is solvable by `X := A`** as soon as the executable conversion accepts its
instantiated sides. -/
theorem solvable_of_accepted {type : TypeOver ctxAX} (left right : Term ctxAX type)
    (accepted : (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst BaseControls.answer.substitution left.code) (subst BaseControls.answer.substitution right.code)
      (subst BaseControls.answer.substitution type.code)).isSome = true) :
    (frames setting.levels).Solvable [((⟨type, left⟩ : TotalTerm ctxAX), (⟨type, right⟩ : TotalTerm ctxAX))] := by
  refine ⟨ctxA, BaseControls.answer, (models_iff setting.levels BaseControls.answer _).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(type.reindex BaseControls.answer).isType.refl, ?_⟩
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst BaseControls.answer.substitution left.code) (subst BaseControls.answer.substitution right.code)
      (subst BaseControls.answer.substitution type.code) with
  | none =>
      rw [computed] at accepted
      cases accepted
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (left.reindex BaseControls.answer).typed (right.reindex BaseControls.answer).typed

/-! ## A projection below an application, at an applied base type -/

/-- `Π (G : U0 → U0) (g : Σ (_ : U0 → G A). U0). G A`. -/
def belowType : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.sigma (.pi u0 (.app (.var 1) (.var 3))) u0) (.app (.var 1) (.var 3)))) (by decide +kernel)

/-- `λ G g. (fst g) X ≐ λ G g. (fst g) A`. -/
def belowEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX belowType (.lam (.lam (.app (.fst (.var 0)) (.var 2)))) (by decide +kernel),
    termIn ctxAX belowType (.lam (.lam (.app (.fst (.var 0)) (.var 3)))) (by decide +kernel))
def belowStore : EquationStore (TotalTerm ctxAX) := [belowEquation]

/-- The raw problem of the sweep. -/
def belowProblem : Problem :=
  { unknowns := [.u0, .u0],
    equations := [(.pi (.pi .u0 .u0) (.pi (.sigma (.pi .u0 (.app (.var 1) (.var 3))) .u0) (.app (.var 1) (.var 3))),
      .lam (.lam (.app (.fst (.var 0)) (.var 2))), .lam (.lam (.app (.fst (.var 0)) (.var 3))))] }

theorem below_in_fragment : InFragmentStore belowStore := storeInside_sound (by decide +kernel)

theorem below_solvable : (frames setting.levels).Solvable belowStore :=
  solvable_of_accepted belowEquation.1.2 belowEquation.2.2 (by decide +kernel)

/-! ### The same sides at a universe are read -/

/-- `Π (G : U0 → U0) (g : Σ (_ : U0 → U0). U0). U0`. -/
def belowUniverseType : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.sigma (.pi u0 u0) u0) u0)) (by decide +kernel)

/-- `λ G g. (fst g) X ≐ λ G g. (fst g) A`, at a universe. -/
def belowUniverseEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX belowUniverseType (.lam (.lam (.app (.fst (.var 0)) (.var 2)))) (by decide +kernel),
    termIn ctxAX belowUniverseType (.lam (.lam (.app (.fst (.var 0)) (.var 3)))) (by decide +kernel))
def belowUniverseStore : EquationStore (TotalTerm ctxAX) := [belowUniverseEquation]

theorem belowUniverse_in_fragment : InFragmentStore belowUniverseStore := storeInside_sound (by decide +kernel)

/-! ## A projection at a Σ base type -/

/-- `Π (G : U0 → U0) (g : U0 → Σ (_ : Σ U0 U0). U0). Σ U0 U0`. -/
def sigmaBaseType : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.pi u0 (.sigma (.sigma u0 u0) u0)) (.sigma u0 u0))) (by decide +kernel)

/-- `λ G g. fst (g X) ≐ λ G g. fst (g A)`. -/
def sigmaBaseEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX sigmaBaseType (.lam (.lam (.fst (.app (.var 0) (.var 2))))) (by decide +kernel),
    termIn ctxAX sigmaBaseType (.lam (.lam (.fst (.app (.var 0) (.var 3))))) (by decide +kernel))
def sigmaBaseStore : EquationStore (TotalTerm ctxAX) := [sigmaBaseEquation]

/-- The raw problem of the sweep. -/
def sigmaBaseProblem : Problem :=
  { unknowns := [.u0, .u0],
    equations := [(.pi (.pi .u0 .u0) (.pi (.pi .u0 (.sigma (.sigma .u0 .u0) .u0)) (.sigma .u0 .u0)),
      .lam (.lam (.fst (.app (.var 0) (.var 2)))), .lam (.lam (.fst (.app (.var 0) (.var 3)))))] }

theorem sigmaBase_in_fragment : InFragmentStore sigmaBaseStore := storeInside_sound (by decide +kernel)

theorem sigmaBase_solvable : (frames setting.levels).Solvable sigmaBaseStore :=
  solvable_of_accepted sigmaBaseEquation.1.2 sigmaBaseEquation.2.2 (by decide +kernel)

/-! ## Two projections above an application, at an applied base type -/

/-- `Π (G : U0 → U0) (g : U0 → Σ (_ : Σ (_ : G A). U0). U0). G A`. -/
def nestedType : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.pi u0 (.sigma (.sigma (.app (.var 1) (.var 3)) u0) u0)) (.app (.var 1) (.var 3))))
  (by decide +kernel)

/-- `λ G g. fst (fst (g X)) ≐ λ G g. fst (fst (g A))`. -/
def nestedEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX nestedType (.lam (.lam (.fst (.fst (.app (.var 0) (.var 2)))))) (by decide +kernel),
    termIn ctxAX nestedType (.lam (.lam (.fst (.fst (.app (.var 0) (.var 3)))))) (by decide +kernel))
def nestedStore : EquationStore (TotalTerm ctxAX) := [nestedEquation]

/-- The raw problem of the sweep. -/
def nestedProblem : Problem :=
  { unknowns := [.u0, .u0],
    equations := [(.pi (.pi .u0 .u0)
        (.pi (.pi .u0 (.sigma (.sigma (.app (.var 1) (.var 3)) .u0) .u0)) (.app (.var 1) (.var 3))),
      .lam (.lam (.fst (.fst (.app (.var 0) (.var 2))))), .lam (.lam (.fst (.fst (.app (.var 0) (.var 3))))))] }

theorem nested_in_fragment : InFragmentStore nestedStore := storeInside_sound (by decide +kernel)

theorem nested_solvable : (frames setting.levels).Solvable nestedStore :=
  solvable_of_accepted nestedEquation.1.2 nestedEquation.2.2 (by decide +kernel)

/-! ## Controls of the builder -/

/-- **An ill-scoped problem builds no store.** -/
theorem illScoped_none : ({ unknowns := [.u0], equations := [(.u0, .var 1, .var 0)] } : Problem).store? = none := by
  decide +kernel

/-- **An ill-typed problem builds no store**: `A ≐ A` at `A`. -/
theorem illTyped_none : ({ unknowns := [.u0], equations := [(.var 0, .var 0, .var 0)] } : Problem).store? = none := by
  decide +kernel

/-- **A typed problem outside the fragment**: over `A : U0, P : U0 → U0`, `P A ≐ A` at `U0` applies an unknown to an
unknown. -/
theorem outside_verdict :
    ({ unknowns := [.u0, .pi .u0 .u0], equations := [(.u0, .app (.var 0) (.var 1), .var 1)] } : Problem).verdict 16 8 =
      .outside := by
  decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
