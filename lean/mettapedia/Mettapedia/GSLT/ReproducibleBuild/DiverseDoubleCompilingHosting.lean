import Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling
import Mettapedia.GSLT.ReproducibleBuild.Hosting

/-!
# Diverse double-compiling at a GSLT hosting boundary

Wheeler DDC compares compiler executables at exact equality.  A two-sided GSLT
hosting certificate can transport production of that matched executable at the
same result observation.  Exact transport of the execution witness itself
requires the strictly stronger proof-relevant hosting interface.

This bridge does not turn an observation-exact hosting example into a DDC
instance.  The complete compiler-source and two-stage Wheeler premises remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompilingHosting

open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling

/-- Exact DDC equality transports an actually witnessed source production
through behavioral hosting.  This is a result-level statement only. -/
def match_transports_hosted_production
    {Source Language Environment Effects : Type}
    {Executable : Type}
    {source target : ObservedOperationalObject Executable}
    (hosting : BehavioralHosting source target)
    (experiment : Experiment Source Executable Language Environment Effects)
    (matched : Matches experiment)
    (initial : source.operational.theory.Term)
    (sourceWitness :
      ObservationFibre source initial experiment.stageTwo) :
    ObservationFibre target (hosting.compile initial)
      experiment.compilerUnderTest := by
  rw [<- matched]
  exact mapObservationFibre hosting.forward sourceWitness

/-- Under proof-relevant hosting, the complete execution fibre producing the
DDC result is equivalent across the hosting boundary. -/
def match_executionFibreEquiv
    {Source Language Environment Effects : Type}
    {Executable : Type}
    {source target : ObservedOperationalObject Executable}
    (hosting : ProofRelevantHosting source target)
    (experiment : Experiment Source Executable Language Environment Effects)
    (matched : Matches experiment)
    (initial : source.operational.theory.Term) :
    ObservationFibre source initial experiment.stageTwo ≃
      ObservationFibre target (hosting.behavioral.compile initial)
        experiment.compilerUnderTest := by
  rw [<- matched]
  exact hosting.fibreEquiv initial experiment.stageTwo

/-- Result-exact behavioral hosting alone still need not preserve DDC-relevant
execution histories: the existing fusion witness has exact public results but
its actual forward path map is non-injective. -/
theorem result_transport_does_not_imply_proof_fibre_fidelity :
    (forall value,
      ProducesObservation
          Mettapedia.GSLT.LanguageDef.NIKObservedRefinement.FusionCanary.targetObserved
          (Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.FusionCanary.hosting.compile
            (false, true)) value <->
        ProducesObservation
          Mettapedia.GSLT.LanguageDef.NIKObservedRefinement.FusionCanary.sourceObserved
          (false, true) value) /\
      Not (Function.Injective
        (mapObservationFibre
          Mettapedia.GSLT.LanguageDef.NIKObservedRefinement.FusionCanary.observedFusion
          (initial := (false, true)) (value := true))) :=
  Mettapedia.GSLT.ReproducibleBuild.Hosting.Canary.behavioral_result_exact_but_forward_fibre_not_injective

end Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompilingHosting

#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompilingHosting.match_transports_hosted_production
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompilingHosting.match_executionFibreEquiv
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompilingHosting.result_transport_does_not_imply_proof_fibre_fidelity
