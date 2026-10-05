import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
/-!
# The maintained pi-to-rho source fragment in the authored GSLT

Restriction-free structural congruence is interpreted by the declared parallel
laws, and each existing restriction-free reduction reaches its exact encoded
endpoint in the generated pi GSLT. No communication freshness premise is needed
for this source comparison; the rho compiler retains its separate safety
hypotheses. This is a forward interpretation, not a reflection theorem for
arbitrary authored steps or arbitrary rho schedules.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

theorem rfsc_authored_equivalent {P Q : Process} (equivalent : StructuralCongruenceRF P Q) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern P) (piToPattern Q) := by
  induction equivalent with
  | refl P => exact .refl _
  | symm P Q _ ih => exact .symm _ _ ih
  | trans P Q R _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond
  | par_cong P P' Q Q' _ _ ihFirst ihSecond =>
      exact piPar_equivalent_congr (piToPattern_hasType P) (piToPattern_hasType P')
        (piToPattern_hasType Q) (piToPattern_hasType Q') ihFirst ihSecond
  | par_comm P Q => exact piPar_equivalent_comm (piToPattern_hasType P) (piToPattern_hasType Q)
  | par_assoc P Q R =>
      exact piPar_equivalent_assoc (piToPattern_hasType P) (piToPattern_hasType Q) (piToPattern_hasType R)
  | par_nil_left P => exact piPar_equivalent_unit_left (piToPattern_hasType P)
  | par_nil_right P => exact piPar_equivalent_unit_right (piToPattern_hasType P)

theorem reducesRF_authored_step {P Q : Process} (step : ReducesRF P Q) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc (piToPattern P) (piToPattern Q) := by
  induction step with
  | comm channel bound datum P => exact piComm_named_semantic_step channel bound datum P
  | par_left P P' Q _ ih => exact piPar_named_semantic_step Q ih
  | par_right P Q Q' _ ih =>
      exact stepModuloEquations_change_source
        (piPar_equivalent_comm (piToPattern_hasType Q) (piToPattern_hasType P))
        (stepModuloEquations_resp_right _ _ (piPar_named_semantic_step P ih)
          (piPar_equivalent_comm (piToPattern_hasType Q') (piToPattern_hasType P)))
  | struct P P' Q Q' before _ after ih =>
      exact stepModuloEquations_change_source (.symm _ _ (rfsc_authored_equivalent before))
        (stepModuloEquations_resp_right _ _ ih (rfsc_authored_equivalent after))

theorem multiStepRF_authored_steps {P Q : Process} (path : MultiStepRF P Q) :
    Relation.ReflTransGen (StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc)
      (piToPattern P) (piToPattern Q) := by
  induction path with
  | refl P => exact .refl
  | step first rest ih => exact (Relation.ReflTransGen.single (reducesRF_authored_step first)).trans ih
end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
