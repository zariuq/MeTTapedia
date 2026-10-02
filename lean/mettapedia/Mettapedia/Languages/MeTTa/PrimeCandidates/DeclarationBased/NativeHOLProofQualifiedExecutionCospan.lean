import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLProofFamilyOperationalQualification
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.IntrinsicNativeListMapExecutionPath
import Mettapedia.GSLT.Dynamics.ObservationTransport

/-!
# Proof-qualified, proof-relevant operational cospans

Endpoint reachability is enough for a generated possibility modality, but it
forgets which primitive transitions were taken.  This module refines the
proof-qualified reachability cospan by retaining both executions in the free
path category.  Erasure recovers the earlier cospan; exact-history and other
observation disciplines remain free to distinguish the two routes.

The map-fusion instance joins the recursively compiled HOL proof to the actual
native beta/iota executions.  The two programs have one common extensional
result while retaining different operational histories and costs.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLProofQualifiedExecutionCospan

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.GSLT.Dynamics.ObservationTransport
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open NativeHOLProofQualifiedOperationalCospan

universe uTerm uEvidence uEvidence' uValue

/-! ## The path-retaining interface -/

/-- Two proof-relevant executions to one observed apex, qualified by evidence
indexed by their source endpoints. -/
structure ProofQualifiedExecutionCospan
    (system : GSLT.{uTerm}) (Evidence : Type uEvidence)
    (Qualifies : Evidence -> system.Term -> system.Term -> Prop)
    (observation : EquationPredicate system.closure)
    (left right : system.Term) where
  evidence : Evidence
  qualification : Qualifies evidence left right
  apex : system.Term
  leftPath : ExecutionPath system left apex
  rightPath : ExecutionPath system right apex
  apexObserved : observation apex

namespace ProofQualifiedExecutionCospan

variable {system : GSLT.{uTerm}} {Evidence : Type uEvidence}
  {Qualifies : Evidence -> system.Term -> system.Term -> Prop}
  {observation : EquationPredicate system.closure}
  {left right : system.Term}

@[ext]
theorem ext
    {first second : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right}
    (evidence : first.evidence = second.evidence)
    (apex : first.apex = second.apex)
    (leftPath : HEq first.leftPath second.leftPath)
    (rightPath : HEq first.rightPath second.rightPath) : first = second := by
  cases first
  cases second
  cases evidence
  cases apex
  cases leftPath
  cases rightPath
  rfl

/-- Forgetting occurrence identity and order gives the earlier
proposition-valued cospan. -/
def toReachability
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    ProofQualifiedReachabilityCospan system Evidence Qualifies observation
      left right where
  evidence := cospan.evidence
  qualification := cospan.qualification
  apex := cospan.apex
  leftReaches := executionPathToMultiStep cospan.leftPath
  rightReaches := executionPathToMultiStep cospan.rightPath
  apexObserved := cospan.apexObserved

/-- Refine an existing endpoint cospan with actual executions to its retained
apex.  Proposition-valued reachability proofs need not be compared because
they are proof-irrelevant. -/
def refineWithPaths
    (cospan : ProofQualifiedReachabilityCospan system Evidence Qualifies
      observation left right)
    (leftPath : ExecutionPath system left cospan.apex)
    (rightPath : ExecutionPath system right cospan.apex) :
    ProofQualifiedExecutionCospan system Evidence Qualifies observation
      left right where
  evidence := cospan.evidence
  qualification := cospan.qualification
  apex := cospan.apex
  leftPath := leftPath
  rightPath := rightPath
  apexObserved := cospan.apexObserved

@[simp] theorem toReachability_refineWithPaths
    (cospan : ProofQualifiedReachabilityCospan system Evidence Qualifies
      observation left right)
    (leftPath : ExecutionPath system left cospan.apex)
    (rightPath : ExecutionPath system right cospan.apex) :
    (refineWithPaths cospan leftPath rightPath).toReachability = cospan := by
  apply ProofQualifiedReachabilityCospan.ext <;> rfl

/-- Generated modal possibility is a projection of the retained paths. -/
theorem semanticDiamonds
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    semanticDiamond system.closure observation left /\
      semanticDiamond system.closure observation right :=
  cospan.toReachability.semanticDiamonds

/-- The retained proof-relevant paths observe the apex through its equation
class.  Literal equality of representatives is not required by this
projection. -/
theorem quotient_apex_observed
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    descendPredicate system.closure observation
        (Quotient.mk system.closure.equations cospan.apex) :=
  cospan.toReachability.quotient_apex_observed

/-- Exact chronological provenance keeps the complete ordered event list as
both witness container and observed value. -/
def exactHistory (system : GSLT.{uTerm}) : GSLTObservation system where
  collection :=
    { Container := List system.LabeledStep
      collect := some }
  Value := List system.LabeledStep
  readout := id

@[simp] theorem exactHistory_observe (events : List system.LabeledStep) :
    (exactHistory system).observe events = some events :=
  rfl

/-- Event extraction retains exactly one event per primitive route step. -/
theorem events_length {source target : system.Term}
    (path : ExecutionPath system source target) :
    (events path).length = path.length := by
  induction path with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [events, Mettapedia.GSLT.Ultrainfinite.Route.length,
        inductionHypothesis, Nat.add_comm]

theorem left_exact_history
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    ofDiscipline (exactHistory system) cospan.leftPath =
      some (events cospan.leftPath) :=
  rfl

theorem right_exact_history
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    ofDiscipline (exactHistory system) cospan.rightPath =
      some (events cospan.rightPath) :=
  rfl

/-- Distinct primitive-step counts force distinct exact-history observations,
even when both executions have the same observed endpoint. -/
theorem exactHistory_distinct_of_length_ne
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right)
    (different : cospan.leftPath.length ≠ cospan.rightPath.length) :
    ofDiscipline (exactHistory system) cospan.leftPath ≠
      ofDiscipline (exactHistory system) cospan.rightPath := by
  intro observedEqual
  have eventEqual : events cospan.leftPath = events cospan.rightPath :=
    Option.some.inj observedEqual
  apply different
  rw [← events_length cospan.leftPath, ← events_length cospan.rightPath,
    eventEqual]

/-! ## Naturality under operational translations -/

/-- Translate evidence, both executions, and their common apex together.
Qualification and apex observation remain explicit naturality obligations. -/
def mapAlong
    {source : GSLT.{uTerm}} {target : GSLT.{uTerm}}
    {SourceEvidence : Type uEvidence} {TargetEvidence : Type uEvidence'}
    {SourceQualifies : SourceEvidence -> source.Term -> source.Term -> Prop}
    {TargetQualifies : TargetEvidence -> target.Term -> target.Term -> Prop}
    {sourceObservation : EquationPredicate source.closure}
    {sourceLeft sourceRight : source.Term}
    (cospan : ProofQualifiedExecutionCospan source SourceEvidence
      SourceQualifies sourceObservation sourceLeft sourceRight)
    (translation : OperationalTranslation source target)
    (translateEvidence : SourceEvidence -> TargetEvidence)
    (targetObservation : EquationPredicate target.closure)
    (qualificationNaturality : forall evidence first second,
      SourceQualifies evidence first second ->
        TargetQualifies (translateEvidence evidence)
          (translation.mapTerm first) (translation.mapTerm second))
    (observationNaturality : forall term,
      sourceObservation term -> targetObservation (translation.mapTerm term)) :
    ProofQualifiedExecutionCospan target TargetEvidence TargetQualifies
      targetObservation (translation.mapTerm sourceLeft)
        (translation.mapTerm sourceRight) where
  evidence := translateEvidence cospan.evidence
  qualification := qualificationNaturality _ _ _ cospan.qualification
  apex := translation.mapTerm cospan.apex
  leftPath := translation.mapRoute cospan.leftPath
  rightPath := translation.mapRoute cospan.rightPath
  apexObserved := observationNaturality cospan.apex cospan.apexObserved

/-- Identity transport changes neither evidence nor either retained route. -/
@[simp] theorem mapAlong_id
    (cospan : ProofQualifiedExecutionCospan system Evidence Qualifies
      observation left right) :
    cospan.mapAlong (OperationalTranslation.id system)
        (fun evidence => evidence) observation
        (fun _ _ _ qualified => qualified)
        (fun _ observed => observed) = cospan := by
  apply ext
  · rfl
  · rfl
  · exact heq_of_eq (OperationalTranslation.mapRoute_id cospan.leftPath)
  · exact heq_of_eq (OperationalTranslation.mapRoute_id cospan.rightPath)

/-- Two stages of operational translation agree with the composite on the
retained proof evidence, common apex, and both complete paths. -/
theorem mapAlong_comp
    {source middle target : GSLT.{uTerm}}
    {SourceEvidence : Type uEvidence}
    {MiddleEvidence : Type uEvidence'} {TargetEvidence : Type uValue}
    {SourceQualifies : SourceEvidence -> source.Term -> source.Term -> Prop}
    {MiddleQualifies : MiddleEvidence -> middle.Term -> middle.Term -> Prop}
    {TargetQualifies : TargetEvidence -> target.Term -> target.Term -> Prop}
    {sourceObservation : EquationPredicate source.closure}
    {sourceLeft sourceRight : source.Term}
    (cospan : ProofQualifiedExecutionCospan source SourceEvidence
      SourceQualifies sourceObservation sourceLeft sourceRight)
    (earlier : OperationalTranslation source middle)
    (later : OperationalTranslation middle target)
    (toMiddle : SourceEvidence -> MiddleEvidence)
    (toTarget : MiddleEvidence -> TargetEvidence)
    (middleObservation : EquationPredicate middle.closure)
    (targetObservation : EquationPredicate target.closure)
    (firstQualification : forall evidence first second,
      SourceQualifies evidence first second ->
        MiddleQualifies (toMiddle evidence)
          (earlier.mapTerm first) (earlier.mapTerm second))
    (secondQualification : forall evidence first second,
      MiddleQualifies evidence first second ->
        TargetQualifies (toTarget evidence)
          (later.mapTerm first) (later.mapTerm second))
    (firstObservation : forall term,
      sourceObservation term -> middleObservation (earlier.mapTerm term))
    (secondObservation : forall term,
      middleObservation term -> targetObservation (later.mapTerm term)) :
    (cospan.mapAlong earlier toMiddle middleObservation
        firstQualification firstObservation).mapAlong
          later toTarget targetObservation
          secondQualification secondObservation =
      cospan.mapAlong (earlier.comp later)
        (fun evidence => toTarget (toMiddle evidence)) targetObservation
        (fun evidence first second qualified =>
          secondQualification _ _ _
            (firstQualification evidence first second qualified))
        (fun term observed =>
          secondObservation _ (firstObservation term observed)) := by
  apply ext
  · rfl
  · rfl
  · exact heq_of_eq
      (OperationalTranslation.mapRoute_comp earlier later cospan.leftPath).symm
  · exact heq_of_eq
      (OperationalTranslation.mapRoute_comp earlier later cospan.rightPath).symm

/-- Path translation commutes literally with the lossy reachability
projection. -/
theorem toReachability_mapAlong
    {source : GSLT.{uTerm}} {target : GSLT.{uTerm}}
    {SourceEvidence : Type uEvidence} {TargetEvidence : Type uEvidence'}
    {SourceQualifies : SourceEvidence -> source.Term -> source.Term -> Prop}
    {TargetQualifies : TargetEvidence -> target.Term -> target.Term -> Prop}
    {sourceObservation : EquationPredicate source.closure}
    {sourceLeft sourceRight : source.Term}
    (cospan : ProofQualifiedExecutionCospan source SourceEvidence
      SourceQualifies sourceObservation sourceLeft sourceRight)
    (translation : OperationalTranslation source target)
    (translateEvidence : SourceEvidence -> TargetEvidence)
    (targetObservation : EquationPredicate target.closure)
    (qualificationNaturality : forall evidence first second,
      SourceQualifies evidence first second ->
        TargetQualifies (translateEvidence evidence)
          (translation.mapTerm first) (translation.mapTerm second))
    (observationNaturality : forall term,
      sourceObservation term -> targetObservation (translation.mapTerm term)) :
    (cospan.mapAlong translation translateEvidence targetObservation
      qualificationNaturality observationNaturality).toReachability =
      cospan.toReachability.mapAlong translation translateEvidence
        targetObservation qualificationNaturality observationNaturality := by
  apply ProofQualifiedReachabilityCospan.ext <;> rfl

/-- Exact history obeys the standard observation-transport square. -/
theorem exactHistory_natural
    {source : GSLT.{uTerm}} {target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {first last : source.Term}
    (path : ExecutionPath source first last) :
    ofDiscipline
        (ObservationDiscipline.pullback (mapEvent translation)
          (exactHistory target)) path =
      ofDiscipline (exactHistory target) (translation.mapRoute path) :=
  observe_mapRoute translation (exactHistory target) path

end ProofQualifiedExecutionCospan

/-! ## The retained recursive HOL map-fusion proof and its actual paths -/

namespace MapFusion

open Presentation NativeIndexedFamilies IntrinsicNativeListMapComputation
open NativeHOLRecursiveProofOperationalObservation
open NativeHOLRecursiveProofNIKQualification
open NativeHOLRecursiveProofNIKQualification.Controls
open NativeHOLTraceRecursiveExtensionalCompilerSemantics
open HOLLeibnizNativeQualifiedHOTGIntegration
open NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms
open IntrinsicNativeListMapExecutionPath
open NativeHOLProofFamilyOperationalQualification
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation

universe u

/-- The path pair induced by the fields of one concrete native map-fusion
program.  This is definitionally the same program pair used by the endpoint
qualification relation. -/
def programPaths {n : Nat} (level : LevelExpr Nat)
    (programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms n) :
    PathReduces level programs.unfused programs.common ×
      PathReduces level programs.fused programs.common :=
  fusion_common_output_paths level programs.source programs.middle
    programs.target programs.first programs.second programs.inputs

/-- Exact work is inherited from the proof-relevant beta/iota construction,
not recomputed from an external cost model. -/
theorem programPath_lengths {n : Nat} (level : LevelExpr Nat)
    (programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms n) :
    (programPaths level programs).1.length = 8 * programs.inputs.length + 10 /\
      (programPaths level programs).2.length =
        5 * programs.inputs.length + 5 :=
  fusion_common_output_path_lengths level programs.source programs.middle
    programs.target programs.first programs.second programs.inputs

/-- The recursively compiled HOL proof family, its Aczel-valued endpoint
observation, and both actual native executions in one object. -/
noncomputable def recursiveExecutionCospan
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (first second : Tower.Tm n)
    (firstMeaning secondMeaning : FunctionMeaning a context)
    (firstDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      first firstMeaning)
    (secondDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      second secondMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (firstMeaning environment) (secondMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    let programs := NativeHOLProofQualifiedOperationalCospan.nativeListPrograms
      first second (heads.map Prod.fst)
    ProofQualifiedExecutionCospan (reduction level n)
      (ConnectedIntrinsicEvidence a)
      (CompiledProofQualifies
        (NativeHOLProofFamilyOperationalQualification.MapFusion.specification
          level))
      (semanticObservation level environment property)
      programs.unfused programs.fused := by
  let programs := NativeHOLProofQualifiedOperationalCospan.nativeListPrograms
    first second (heads.map Prod.fst)
  let base :=
    NativeHOLProofFamilyOperationalQualification.MapFusion.recursiveCospan
      level first second firstMeaning secondMeaning firstDenotes secondDenotes
        heads interpreted environment property accepted
  let paths := programPaths level programs
  refine
    { evidence := base.evidence
      qualification := base.qualification
      apex := programs.common
      leftPath := paths.1
      rightPath := paths.2
      apexObserved := ?_ }
  exact base.apexObserved

/-- Path refinement preserves the complete mathematical connection carried by
the proof-family evidence. -/
theorem recursiveExecutionCospan_retains_source
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (first second : Tower.Tm n)
    (firstMeaning secondMeaning : FunctionMeaning a context)
    (firstDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      first firstMeaning)
    (secondDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      second secondMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (firstMeaning environment) (secondMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    (recursiveExecutionCospan level first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property
        accepted).evidence.proof = retainedMapFusionProof := by
  rfl

/-- The actual path fields retain the exact beta/iota cost formula; the
proof-family and Aczel layers do not collapse it. -/
theorem recursiveExecutionCospan_path_lengths
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (first second : Tower.Tm n)
    (firstMeaning secondMeaning : FunctionMeaning a context)
    (firstDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      first firstMeaning)
    (secondDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      second secondMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (firstMeaning environment) (secondMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    let cospan := recursiveExecutionCospan level first second
      firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
        environment property accepted
    cospan.leftPath.length = 8 * (heads.map Prod.fst).length + 10 /\
      cospan.rightPath.length = 5 * (heads.map Prod.fst).length + 5 := by
  exact programPath_lengths level
    (NativeHOLProofQualifiedOperationalCospan.nativeListPrograms
      first second (heads.map Prod.fst))

/-- The same qualified transformation has equal extensional apex observation
and unequal exact histories.  The inequality holds for every finite input,
including the empty list. -/
theorem recursiveExecutionCospan_exact_histories_differ
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (first second : Tower.Tm n)
    (firstMeaning secondMeaning : FunctionMeaning a context)
    (firstDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      first firstMeaning)
    (secondDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      second secondMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (firstMeaning environment) (secondMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    let cospan := recursiveExecutionCospan level first second
      firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
        environment property accepted
    ofDiscipline (ProofQualifiedExecutionCospan.exactHistory (reduction level n))
        cospan.leftPath ≠
      ofDiscipline
        (ProofQualifiedExecutionCospan.exactHistory (reduction level n))
        cospan.rightPath := by
  let cospan := recursiveExecutionCospan level first second
    firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
      environment property accepted
  apply cospan.exactHistory_distinct_of_length_ne
  have lengths := recursiveExecutionCospan_path_lengths level first second
    firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
      environment property accepted
  rw [lengths.1, lengths.2]
  omega

/-- The path-retaining instance has the same generated modal endpoint
observations as its proposition-valued projection. -/
theorem recursiveExecutionCospan_semanticDiamonds
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (first second : Tower.Tm n)
    (firstMeaning secondMeaning : FunctionMeaning a context)
    (firstDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      first firstMeaning)
    (secondDenotes : NativeHOLTraceDisplayedTerms.Denotes a context
      second secondMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (firstMeaning environment) (secondMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    let programs := NativeHOLProofQualifiedOperationalCospan.nativeListPrograms
      first second (heads.map Prod.fst)
    semanticDiamond (reduction level n).closure
        (semanticObservation level environment property) programs.unfused /\
      semanticDiamond (reduction level n).closure
        (semanticObservation level environment property) programs.fused := by
  exact (recursiveExecutionCospan level first second firstMeaning secondMeaning
    firstDenotes secondDenotes heads interpreted environment property
      accepted).semanticDiamonds

end MapFusion

#print axioms ProofQualifiedExecutionCospan.semanticDiamonds
#print axioms ProofQualifiedExecutionCospan.quotient_apex_observed
#print axioms ProofQualifiedExecutionCospan.events_length
#print axioms ProofQualifiedExecutionCospan.exactHistory_distinct_of_length_ne
#print axioms ProofQualifiedExecutionCospan.mapAlong_comp
#print axioms ProofQualifiedExecutionCospan.toReachability_mapAlong
#print axioms ProofQualifiedExecutionCospan.exactHistory_natural
#print axioms MapFusion.programPath_lengths
#print axioms MapFusion.recursiveExecutionCospan_retains_source
#print axioms MapFusion.recursiveExecutionCospan_path_lengths
#print axioms MapFusion.recursiveExecutionCospan_exact_histories_differ
#print axioms MapFusion.recursiveExecutionCospan_semanticDiamonds

end NativeHOLProofQualifiedExecutionCospan
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
