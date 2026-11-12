import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSigmaGap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSpines

/-!
# A gap in the spine decompositions: a base type that is an application

Every decomposition between two spines of one local asks the base type, the annotation under its Π binders, to be a
universe, an identity type or a variable: `rigidBase` for the readings between spines of one local (R97's
`dependentUnder`, R107's `elimBase`, R121's `dependentUnderN`), and `baseShape` for the flexible-base reading (R110's
`elimAnyUnder`). A base type that is an **application** is accepted by none of them.

* **A bound local applied.** Over `A : U0, X : U0`, at `Π (G : U0 → U0) (g : U0 → G A). G A`, the equation
  **`λ G g. g X ≐ λ G g. g A`** (`appliedStore`) is in the dynamic pattern fragment (`applied_in_fragment`) and
  solvable by `X := A` (`applied_solvable`). Its sides are spines of the local `g`, of one skeleton, at the base type
  `G A`. No decomposition reads it, at any budget (`applied_reducts_none`, `applied_literal_none`,
  `applied_elims_none`, `applied_formers_none`: none of them takes a budget into the base test), and the Σ family,
  the top family, is stuck in its first round at budgets 16 and 64 (`applied_sigma_stuck`, `applied_sigma_stuck_64`).
* **A metavariable applied.** Over `A : U0, X : U0, P : U0 → U0`, at `Π (g : U0 → P A). P A`, the equation
  **`λ g. g X ≐ λ g. g A`** (`flexStore`) is in the fragment and solvable (`flex_in_fragment`, `flex_solvable`); the
  readings read nothing (`flex_reducts_none`, `flex_elims_none`) and the Σ family is stuck (`flex_sigma_stuck`).

The sides of the first store have the shape of two spines of one local except for the base test: with a universe as
base type the same sides are read (`universe_reads`, `universe_sigma_committed`). So the census row of spines of one
local is the row at a *rigid* base (`LocalSpines`), and reading these stores needs one more rule, a decomposition
between spines of one local at a neutral base type. That rule would not make the Σ family decide the fragment: at the
tower the fragment also holds `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), on which every run stops postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`).
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

/-! ## A bound local applied -/

/-- `U0`, over `A`. -/
def universeA : TypeOver ctxA := formIn ctxA u0 (by decide +kernel)

/-- `A : U0, X : U0`. -/
abbrev ctxAX := extend ctxA universeA

/-- `Π (G : U0 → U0) (g : U0 → G A). G A`. -/
def family : TypeOver ctxAX := formIn ctxAX
  (.pi (.pi u0 u0) (.pi (.pi u0 (.app (.var 1) (.var 3))) (.app (.var 1) (.var 3)))) (by decide +kernel)

/-- `λ G g. g X ≐ λ G g. g A`. -/
def appliedEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX family (.lam (.lam (.app (.var 0) (.var 2)))) (by decide +kernel),
    termIn ctxAX family (.lam (.lam (.app (.var 0) (.var 3)))) (by decide +kernel))
def appliedStore : EquationStore (TotalTerm ctxAX) := [appliedEquation]

theorem applied_in_fragment : InFragmentStore appliedStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl appliedEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `X := A`. -/
def answer : ctxA ⟶ ctxAX :=
  Elimination.instantiate ctxA (termIn ctxA universeA (.var 0) (by decide +kernel)).2

theorem applied_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution appliedEquation.1.2.code)
      (subst answer.substitution appliedEquation.2.2.code)
      (subst answer.substitution appliedEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `X := A`. -/
theorem applied_solvable : (frames setting.levels).Solvable appliedStore := by
  refine ⟨ctxA, answer, (models_iff setting.levels answer appliedStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(family.reindex answer).isType.refl, ?_⟩
  have check := applied_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst answer.substitution appliedEquation.1.2.code)
      (subst answer.substitution appliedEquation.2.2.code)
      (subst answer.substitution appliedEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (appliedEquation.1.2.reindex answer).typed (appliedEquation.2.2.reindex answer).typed

/-- **The sides have the shape of two spines of one local, except for the base test**: the base type `G A` is not a
rigid base. -/
theorem applied_not_localSpines :
    ¬ LocalSpines 0 appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code := by
  intro shape
  have decided := shape.decided
  have refused : localSpinesAt 0 appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code =
      false := by decide +kernel
  rw [refused] at decided
  cases decided

/-- **The reading along the reducts of the instantiated types reads no pieces**, at any budget. -/
theorem applied_reducts_none (fuel : Nat) :
    dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer fuel []
      appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code = none := by
  cases found : dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer fuel []
      appliedEquation.1.1.code appliedEquation.1.2.code appliedEquation.2.2.code with
  | none => rfl
  | some pieces =>
      exact absurd (dependentUnderN_rel _ fuel [] _ _ _ found).localSpines applied_not_localSpines

/-- **The literal reading between spines of one local reads no pieces.** -/
theorem applied_literal_none : ContextualDependentSpinesMany.dependentUnder [] appliedEquation.1.1.code
    appliedEquation.1.2.code appliedEquation.2.2.code = none := by decide +kernel

/-- **The reading between elimination spines at a base shape reads no pieces.** -/
theorem applied_elims_none : ContextualDependentSpineEta.elimAnyUnder [] appliedEquation.1.1.code
    appliedEquation.1.2.code appliedEquation.2.2.code = none := by decide +kernel

/-- **The reading between formers reads no pieces.** -/
theorem applied_formers_none : ContextualDependentSpinesMany.underParts (S := setting) appliedEquation.1.1.code
    appliedEquation.1.2.code appliedEquation.2.2.code = none := by decide +kernel

/-- **The Σ family is stuck in its first round** on the store, at budget 16. -/
theorem applied_sigma_stuck : isStuck (run (sigmaTower.solver 16) appliedStore 1) = true := by decide +kernel

/-- The same at budget 64. -/
theorem applied_sigma_stuck_64 : isStuck (run (sigmaTower.solver 64) appliedStore 1) = true := by decide +kernel

/-! ## The same sides at a universe are read -/

/-- `Π (G : U0 → U0) (g : U0 → U0). U0`. -/
def atUniverse : TypeOver ctxAX := formIn ctxAX (.pi (.pi u0 u0) (.pi (.pi u0 u0) u0)) (by decide +kernel)

/-- `λ G g. g X ≐ λ G g. g A`, at a universe. -/
def universeEquation : Equation (TotalTerm ctxAX) :=
  (termIn ctxAX atUniverse (.lam (.lam (.app (.var 0) (.var 2)))) (by decide +kernel),
    termIn ctxAX atUniverse (.lam (.lam (.app (.var 0) (.var 3)))) (by decide +kernel))
def universeStore : EquationStore (TotalTerm ctxAX) := [universeEquation]

theorem universe_reads : (dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer 16 []
    universeEquation.1.1.code universeEquation.1.2.code universeEquation.2.2.code).isSome = true := by
  decide +kernel

theorem universe_sigma_committed : (run (sigmaTower.solver 16) universeStore 8).readout = .commit := by
  decide +kernel

/-! ## A metavariable applied -/

/-- `U0 → U0`, over `A, X`. -/
def families : TypeOver ctxAX := formIn ctxAX (.pi u0 u0) (by decide +kernel)

/-- `A : U0, X : U0, P : U0 → U0`. -/
abbrev ctxAXP := extend ctxAX families

/-- `Π (g : U0 → P A). P A`. -/
def flexFamily : TypeOver ctxAXP := formIn ctxAXP
  (.pi (.pi u0 (.app (.var 1) (.var 3))) (.app (.var 1) (.var 3))) (by decide +kernel)

/-- `λ g. g X ≐ λ g. g A`. -/
def flexEquation : Equation (TotalTerm ctxAXP) :=
  (termIn ctxAXP flexFamily (.lam (.app (.var 0) (.var 2))) (by decide +kernel),
    termIn ctxAXP flexFamily (.lam (.app (.var 0) (.var 3))) (by decide +kernel))
def flexStore : EquationStore (TotalTerm ctxAXP) := [flexEquation]

theorem flex_in_fragment : InFragmentStore flexStore := by
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl flexEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `P := λ _. A`, then `X := A`. -/
def flexAnswer : ctxA ⟶ ctxAXP :=
  answer ≫ Elimination.instantiate ctxAX (termIn ctxAX families (.lam (.var 2)) (by decide +kernel)).2

theorem flex_accepted :
    (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst flexAnswer.substitution flexEquation.1.2.code)
      (subst flexAnswer.substitution flexEquation.2.2.code)
      (subst flexAnswer.substitution flexEquation.1.1.code)).isSome = true := by
  decide +kernel

/-- **The store is solvable**, by `P := λ _. A` and `X := A`. -/
theorem flex_solvable : (frames setting.levels).Solvable flexStore := by
  refine ⟨ctxA, flexAnswer, (models_iff setting.levels flexAnswer flexStore).mpr ?_⟩
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(flexFamily.reindex flexAnswer).isType.refl, ?_⟩
  have check := flex_accepted
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      ctxA.raw (subst flexAnswer.substitution flexEquation.1.2.code)
      (subst flexAnswer.substitution flexEquation.2.2.code)
      (subst flexAnswer.substitution flexEquation.1.1.code) with
  | none =>
      rw [computed] at check
      cases check
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down ctxA.formed (flexEquation.1.2.reindex flexAnswer).typed (flexEquation.2.2.reindex flexAnswer).typed

theorem flex_not_localSpines :
    ¬ LocalSpines 0 flexEquation.1.1.code flexEquation.1.2.code flexEquation.2.2.code := by
  intro shape
  have decided := shape.decided
  have refused : localSpinesAt 0 flexEquation.1.1.code flexEquation.1.2.code flexEquation.2.2.code = false := by
    decide +kernel
  rw [refused] at decided
  cases decided

theorem flex_reducts_none (fuel : Nat) :
    dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer fuel []
      flexEquation.1.1.code flexEquation.1.2.code flexEquation.2.2.code = none := by
  cases found : dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer fuel []
      flexEquation.1.1.code flexEquation.1.2.code flexEquation.2.2.code with
  | none => rfl
  | some pieces =>
      exact absurd (dependentUnderN_rel _ fuel [] _ _ _ found).localSpines flex_not_localSpines

theorem flex_elims_none : ContextualDependentSpineEta.elimAnyUnder [] flexEquation.1.1.code
    flexEquation.1.2.code flexEquation.2.2.code = none := by decide +kernel

/-- **The Σ family is stuck in its first round** on the store, at budget 16. -/
theorem flex_sigma_stuck : isStuck (run (sigmaTower.solver 16) flexStore 1) = true := by decide +kernel

end ContextualDependentEtaDepth.BaseControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
