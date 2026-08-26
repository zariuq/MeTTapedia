import Mettapedia.GSLT.Core.ReproducibleBuild
import Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

/-!
# Reproducible execution builds transported through two-sided hosting

An observed operational object determines a proof-relevant build relation:
an initial term builds a public value when a complete execution path produces
that observation.  A `BehavioralHosting` proof makes the target execution
relation exact on compiled source states, so rebuildability, result-level
consistency, declaration sufficiency, and reproducibility transport in both
directions at any observation of the public value.

This is deliberately a result-level theorem.  Exact source and target execution
fibres are equivalent only under `ProofRelevantHosting`.  The existing fusion
canary remains the strict negative control: it is exact on public results while
its forward path map collapses distinct administrative histories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.Hosting

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

universe uDeclared uObserved

/-- Complete observed executions as a relational build from initial terms to
public values. -/
def executionBuild {Value : Type}
    (object : ObservedOperationalObject Value) :
    RelationalBuild object.operational.theory.Term Value :=
  fun initial value => ObservationFibre object initial value

/-- Target execution pulled back to the source term space through the compiler
selected by a two-sided hosting proof. -/
def hostedExecutionBuild {Value : Type}
    {source target : ObservedOperationalObject Value}
    (hosting : BehavioralHosting source target) :
    RelationalBuild source.operational.theory.Term Value :=
  fun initial value =>
    ObservationFibre target (hosting.compile initial) value

namespace BehavioralHosting

variable {Value : Type}
  {source target : ObservedOperationalObject Value}

/-- Two-sided hosting preserves and reflects existence of some observed result
from each compiled source state. -/
theorem rebuildableAt_iff
    (hosting : BehavioralHosting source target)
    (initial : source.operational.theory.Term) :
    RebuildableAt (hostedExecutionBuild hosting) initial <->
      RebuildableAt (executionBuild source) initial := by
  constructor
  · rintro ⟨⟨value, targetWitness⟩⟩
    obtain ⟨sourceWitness⟩ :=
      hosting.noInvention initial value ⟨targetWitness⟩
    exact ⟨⟨value, sourceWitness⟩⟩
  · rintro ⟨⟨value, sourceWitness⟩⟩
    exact ⟨⟨value, mapObservationFibre hosting.forward sourceWitness⟩⟩

/-- Rebuildability over the common source domain is invariant under two-sided
hosting. -/
theorem rebuildable_iff (hosting : BehavioralHosting source target) :
    Rebuildable (hostedExecutionBuild hosting) <->
      Rebuildable (executionBuild source) := by
  constructor
  · intro targetRebuildable initial
    exact (rebuildableAt_iff hosting initial).mp
      (targetRebuildable initial)
  · intro sourceRebuildable initial
    exact (rebuildableAt_iff hosting initial).mpr
      (sourceRebuildable initial)

/-- Two-sided hosting preserves and reflects consistency at every observation
of the public result value. -/
theorem observationConsistentAt_iff
    (hosting : BehavioralHosting source target)
    (observation : ArtifactObservation.{0, uObserved} Value)
    (initial : source.operational.theory.Term) :
    ObservationConsistentAt (hostedExecutionBuild hosting) observation initial
      <->
    ObservationConsistentAt (executionBuild source) observation initial := by
  constructor
  · intro targetConsistent left right leftWitness rightWitness
    exact targetConsistent
      (mapObservationFibre hosting.forward leftWitness)
      (mapObservationFibre hosting.forward rightWitness)
  · intro sourceConsistent left right leftWitness rightWitness
    obtain ⟨sourceLeft⟩ :=
      hosting.noInvention initial left ⟨leftWitness⟩
    obtain ⟨sourceRight⟩ :=
      hosting.noInvention initial right ⟨rightWitness⟩
    exact sourceConsistent sourceLeft sourceRight

/-- Global result-level observational consistency is invariant under two-sided
hosting on compiled source states. -/
theorem observationConsistent_iff
    (hosting : BehavioralHosting source target)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    ObservationConsistent (hostedExecutionBuild hosting) observation <->
      ObservationConsistent (executionBuild source) observation := by
  constructor
  · intro targetConsistent initial
    exact (observationConsistentAt_iff hosting observation initial).mp
      (targetConsistent initial)
  · intro sourceConsistent initial
    exact (observationConsistentAt_iff hosting observation initial).mpr
      (sourceConsistent initial)

/-- Source-identical result-level reproducibility transports exactly through
two-sided hosting. -/
theorem reproducible_iff
    (hosting : BehavioralHosting source target)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    Reproducible (hostedExecutionBuild hosting) observation <->
      Reproducible (executionBuild source) observation := by
  constructor
  · rintro ⟨targetRebuildable, targetConsistent⟩
    exact ⟨(rebuildable_iff hosting).mp targetRebuildable,
      (observationConsistent_iff hosting observation).mp targetConsistent⟩
  · rintro ⟨sourceRebuildable, sourceConsistent⟩
    exact ⟨(rebuildable_iff hosting).mpr sourceRebuildable,
      (observationConsistent_iff hosting observation).mpr sourceConsistent⟩

/-- Declaration sufficiency over source terms is invariant under two-sided
hosting.  Target occurrences are reflected with `noInvention`; source
occurrences are preserved by the forward execution map. -/
theorem declarationSufficient_iff
    (hosting : BehavioralHosting source target)
    (view : InputView.{0, uDeclared}
      source.operational.theory.Term)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    DeclarationSufficient (hostedExecutionBuild hosting) view observation <->
      DeclarationSufficient (executionBuild source) view observation := by
  constructor
  · intro targetSufficient
    rintro ⟨leftInitial, leftValue, leftWitness⟩
      ⟨rightInitial, rightValue, rightWitness⟩ sameDeclaration
    let targetLeft : Occurrence (hostedExecutionBuild hosting) :=
      ⟨leftInitial, leftValue,
        mapObservationFibre hosting.forward leftWitness⟩
    let targetRight : Occurrence (hostedExecutionBuild hosting) :=
      ⟨rightInitial, rightValue,
        mapObservationFibre hosting.forward rightWitness⟩
    exact targetSufficient
      (a := targetLeft) (b := targetRight) sameDeclaration
  · intro sourceSufficient
    rintro ⟨leftInitial, leftValue, leftWitness⟩
      ⟨rightInitial, rightValue, rightWitness⟩ sameDeclaration
    obtain ⟨sourceLeft⟩ :=
      hosting.noInvention leftInitial leftValue ⟨leftWitness⟩
    obtain ⟨sourceRight⟩ :=
      hosting.noInvention rightInitial rightValue ⟨rightWitness⟩
    let sourceLeftOccurrence : Occurrence (executionBuild source) :=
      ⟨leftInitial, leftValue, sourceLeft⟩
    let sourceRightOccurrence : Occurrence (executionBuild source) :=
      ⟨rightInitial, rightValue, sourceRight⟩
    exact sourceSufficient
      (a := sourceLeftOccurrence) (b := sourceRightOccurrence)
      sameDeclaration

/-- Declared-view reproducibility transports through two-sided hosting at the
same public result observation. -/
theorem declaredViewReproducible_iff
    (hosting : BehavioralHosting source target)
    (view : InputView.{0, uDeclared}
      source.operational.theory.Term)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    DeclaredViewReproducible (hostedExecutionBuild hosting) view observation
      <->
    DeclaredViewReproducible (executionBuild source) view observation := by
  constructor
  · rintro ⟨targetRebuildable, targetSufficient⟩
    exact ⟨(rebuildable_iff hosting).mp targetRebuildable,
      (declarationSufficient_iff hosting view observation).mp
        targetSufficient⟩
  · rintro ⟨sourceRebuildable, sourceSufficient⟩
    exact ⟨(rebuildable_iff hosting).mpr sourceRebuildable,
      (declarationSufficient_iff hosting view observation).mpr
        sourceSufficient⟩

/-- Identity hosting is neutral for result-level reproducibility. -/
theorem id_reproducible_iff
    (object : ObservedOperationalObject Value)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    Reproducible
        (hostedExecutionBuild
          (Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.BehavioralHosting.id
            object)) observation <->
      Reproducible (executionBuild object) observation :=
  reproducible_iff
    (Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.BehavioralHosting.id
      object) observation

/-- Composition of hosting certificates transports reproducibility in one
step to the same source theorem as the composite compiler. -/
theorem comp_reproducible_iff
    {middle : ObservedOperationalObject Value}
    (earlier : BehavioralHosting source middle)
    (later : BehavioralHosting middle target)
    (observation : ArtifactObservation.{0, uObserved} Value) :
    Reproducible (hostedExecutionBuild (earlier.comp later)) observation <->
      Reproducible (executionBuild source) observation :=
  reproducible_iff (earlier.comp later) observation

end BehavioralHosting

/-! ## Proof-fibre strengthening -/

namespace ProofRelevantHosting

variable {Value : Type}
  {source target : ObservedOperationalObject Value}

/-- Exact proof-relevant hosting equates the complete result/execution fibre at
each initial source term, not merely its inhabited public-result support. -/
def executionFibreEquiv
    (hosting : ProofRelevantHosting source target)
    (initial : source.operational.theory.Term) :
    (Sigma fun value => ObservationFibre source initial value) ≃
      (Sigma fun value => ObservationFibre target
        (hosting.behavioral.compile initial) value) where
  toFun witness :=
    ⟨witness.1, hosting.fibreEquiv initial witness.1 witness.2⟩
  invFun witness :=
    ⟨witness.1, (hosting.fibreEquiv initial witness.1).symm witness.2⟩
  left_inv witness := by
    rcases witness with ⟨value, sourceWitness⟩
    simp
  right_inv witness := by
    rcases witness with ⟨value, targetWitness⟩
    simp

/-- The exact execution-fibre equivalence uses the same forward route map as
the underlying behavioral hosting. -/
theorem executionFibreEquiv_agrees
    (hosting : ProofRelevantHosting source target)
    (initial : source.operational.theory.Term) (value : Value)
    (witness : ObservationFibre source initial value) :
    (executionFibreEquiv hosting initial ⟨value, witness⟩).2 =
      mapObservationFibre hosting.toBehavioralHosting.forward witness :=
  hosting.fibreEquiv_agrees initial value witness

end ProofRelevantHosting

/-! ## Result exactness does not imply proof-fibre exactness -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.FusionCanary
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement.FusionCanary

/-- The existing fusion is valid result-level hosting while its actual forward
map collapses two distinct proof-relevant execution histories. -/
theorem behavioral_result_exact_but_forward_fibre_not_injective :
    (forall value,
      ProducesObservation targetObserved
          (hosting.compile (false, true)) value <->
        ProducesObservation sourceObserved (false, true) value) /\
      Not (Function.Injective
        (mapObservationFibre observedFusion
          (initial := (false, true)) (value := true))) := by
  constructor
  · intro value
    exact hosting.produces_iff (false, true) value
  · exact forward_fibre_not_injective

namespace ExtraBehavior

private abbrev extraSourceObserved :=
  Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.ExtraBehaviorCanary.sourceObserved
private abbrev extraTargetObserved :=
  Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.ExtraBehaviorCanary.targetObserved

/-- Target executions pulled back through the one-way compiler in the
extra-behavior canary. -/
def pulledTargetBuild : RelationalBuild Unit Bool :=
  fun initial value =>
    ObservationFibre extraTargetObserved
      (Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.ExtraBehaviorCanary.forward.refinement.realization.mapTerm initial) value

theorem source_exact_reproducible :
    Reproducible (executionBuild extraSourceObserved)
      (ArtifactObservation.identity Bool) := by
  constructor
  · intro initial
    exact ⟨⟨false, ⟨initial, ⟨.refl initial, rfl⟩⟩⟩⟩
  · intro initial left right leftWitness rightWitness
    rcases leftWitness with ⟨leftFinal, leftPath, leftObserved⟩
    rcases rightWitness with ⟨rightFinal, rightPath, rightObserved⟩
    have leftEq : false = left := Option.some.inj leftObserved
    have rightEq : false = right := Option.some.inj rightObserved
    exact leftEq.symm.trans rightEq

theorem pulledTarget_not_exact_reproducible :
    Not (Reproducible pulledTargetBuild
      (ArtifactObservation.identity Bool)) := by
  intro reproducible
  have falseWitness : pulledTargetBuild () false :=
    ⟨false, ⟨.refl false, rfl⟩⟩
  have trueWitness : pulledTargetBuild () true :=
    ⟨true,
      ⟨Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.ExtraBehaviorCanary.extraPath,
        rfl⟩⟩
  have falseEqTrue := reproducible.2 () falseWitness trueWitness
  exact Bool.false_ne_true falseEqTrue

/-- A forward simulation can preserve every source execution while the target
invents an additional observed result.  It therefore cannot transport
reproducibility without the no-invention half of `BehavioralHosting`. -/
theorem forward_preservation_does_not_transport_reproducibility :
    Nonempty (ObservedRefinement extraSourceObserved extraTargetObserved) /\
      Reproducible (executionBuild extraSourceObserved)
        (ArtifactObservation.identity Bool) /\
      Not (Reproducible pulledTargetBuild
        (ArtifactObservation.identity Bool)) :=
  ⟨⟨Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting.ExtraBehaviorCanary.forward⟩,
    source_exact_reproducible,
    pulledTarget_not_exact_reproducible⟩

end ExtraBehavior

end Canary

#print axioms BehavioralHosting.reproducible_iff
#print axioms BehavioralHosting.declarationSufficient_iff
#print axioms BehavioralHosting.id_reproducible_iff
#print axioms BehavioralHosting.comp_reproducible_iff
#print axioms ProofRelevantHosting.executionFibreEquiv_agrees
#print axioms Canary.behavioral_result_exact_but_forward_fibre_not_injective
#print axioms Canary.ExtraBehavior.forward_preservation_does_not_transport_reproducibility

end Mettapedia.GSLT.ReproducibleBuild.Hosting
