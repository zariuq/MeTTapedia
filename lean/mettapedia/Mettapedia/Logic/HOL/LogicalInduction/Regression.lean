import Mettapedia.Logic.HOL.LogicalInduction.Calibration
import Mettapedia.Logic.HOL.LogicalInduction.Criterion
import Mettapedia.Logic.HOL.LogicalInduction.EmpiricalSpecialCase
import Mettapedia.Logic.HOL.WorldModel

/-!
# Regression Surface for HOL Logical-Induction Infrastructure

This module packages the main positive and negative toy fixtures for the
logical-induction-ready HOL belief layer into one explicit regression target.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the goal here is not yet a full
logical-inductor construction.  Instead we collect the stable regression-facing
facts that future `ProbHOL` work should continue to preserve:

- positive and negative timely-learning/calibration fixtures,
- conditioning/theory-extension laws,
- a non-exploitability sanity check for the silent trader,
- and the theorem that the current static HOL world-model semantics is the
  empirical special case of the day-level belief interface.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Model : Type w}
variable (satisfies : Model → ClosedFormulaCode Const → Prop)

theorem regression_processOne_trustsVisibleTheorems
    (D : DeductiveProcess Const) :
    TrustsVisibleTheorems (Const := Const) D (processOne (Const := Const)) :=
  processOne_trustsVisibleTheorems (Const := Const) D

theorem regression_processOne_timelyLearnsAtOne
    (D : DeductiveProcess Const) :
    TimelyLearnsAtOne (Const := Const) D (processOne (Const := Const)) :=
  processOne_timelyLearnsAtOne (Const := Const) D

theorem regression_processZero_not_trustsVisibleTheorems_constant
    (φ : ClosedFormulaCode Const) :
    ¬ TrustsVisibleTheorems
        (Const := Const)
        (DeductiveProcess.constant
          (Const := Const) ({φ} : Finset (ClosedFormulaCode Const)))
        (processZero (Const := Const)) :=
  processZero_not_trustsVisibleTheorems_constant (Const := Const) φ

theorem regression_processZero_not_timelyLearnsAtOne_constant
    (φ : ClosedFormulaCode Const) :
    ¬ TimelyLearnsAtOne
        (Const := Const)
        (DeductiveProcess.constant
          (Const := Const) ({φ} : Finset (ClosedFormulaCode Const)))
        (processZero (Const := Const)) :=
  processZero_not_timelyLearnsAtOne_constant (Const := Const) φ

theorem regression_processHalf_not_eventuallyExactOnFiniteSample_one
    {φ : ClosedFormulaCode Const} :
    ¬ EventuallyExactOnFiniteSample
        (Const := Const)
        (fun _ => Price01.one)
        ({φ} : Finset (ClosedFormulaCode Const))
        (processHalf (Const := Const)) :=
  processHalf_not_eventuallyExactOnFiniteSample_one (Const := Const)

theorem regression_forceAxiomsAtOne_respectsTheoryExtension :
    RespectsTheoryExtension (Base := Base) (Const := Const)
      (forceAxiomsAtOneOperator (Const := Const)) :=
  forceAxiomsAtOne_respectsTheoryExtension (Base := Base) (Const := Const)

theorem regression_forceAxiomsAtOne_preservesOutsideAxioms :
    PreservesOutsideAxioms (Base := Base) (Const := Const)
      (forceAxiomsAtOneOperator (Const := Const)) :=
  forceAxiomsAtOne_preservesOutsideAxioms (Base := Base) (Const := Const)

theorem regression_forceAxiomsAtOne_idem
    (Γ : TheoryExtension Const)
    (P : BeliefProcess Const) :
    forceAxiomsAtOne (Const := Const) Γ (forceAxiomsAtOne (Const := Const) Γ P) =
      forceAxiomsAtOne (Const := Const) Γ P :=
  forceAxiomsAtOne_idem (Const := Const) Γ P

theorem regression_forceAxiomsAtOne_union
    (Γ Δ : TheoryExtension Const)
    (P : BeliefProcess Const) :
    forceAxiomsAtOne (Const := Const) (Γ ∪ Δ) P =
      forceAxiomsAtOne (Const := Const) Δ (forceAxiomsAtOne (Const := Const) Γ P) :=
  forceAxiomsAtOne_union (Const := Const) Γ Δ P

theorem regression_silent_not_exploits
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) :
    ¬ Exploits (Const := Const) satisfies D P (Trader.silent (Const := Const)) :=
  silent_not_exploits (Const := Const) satisfies D P

theorem regression_empiricalDayStrength_eq_staticQueryStrength
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormulaCode Const) :
    dayQueryStrength (Const := Const)
      (empiricalBeliefDay (Base := Base) (Const := Const) W) φ =
      Mettapedia.Logic.PLNWorldModel.WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := Mettapedia.Logic.HOL.WorldModel.HOLQuery Const)
        W (decodeClosedFormula φ) :=
  empiricalDayStrength_eq_staticQueryStrength (Base := Base) (Const := Const) W φ

theorem regression_empiricalBeliefDay_singleton_of_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormulaCode Const)
    (hφ : Mettapedia.Logic.HOL.WorldModel.holSatisfies M (decodeClosedFormula φ)) :
    empiricalBeliefDay (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = Price01.one :=
  empiricalBeliefDay_singleton_of_satisfies M φ hφ

theorem regression_empiricalBeliefDay_singleton_of_not_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormulaCode Const)
    (hφ : ¬ Mettapedia.Logic.HOL.WorldModel.holSatisfies M (decodeClosedFormula φ)) :
    empiricalBeliefDay (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = Price01.zero :=
  empiricalBeliefDay_singleton_of_not_satisfies M φ hφ

end Mettapedia.Logic.HOL.LogicalInduction
