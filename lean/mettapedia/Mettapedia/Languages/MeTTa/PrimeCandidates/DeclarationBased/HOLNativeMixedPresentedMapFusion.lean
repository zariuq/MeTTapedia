import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedPresentedDriver
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLProofQualifiedExecutionCospan

/-!
# Retained HOL evidence and map execution through the presented driver

The mathematical connection already retains one recursively compiled HOL
proof, its Aczel-trace denotation, and two native beta/iota routes.  This module
moves that whole object through the mixed rule-data driver.  The evidence is
not re-proved, the target observation is the direct image of the original
equation-respecting observation, and both paths retain their ordered primitive
steps.

The result is the executable commuting face needed before a runtime
realization can be qualified: proof evidence, native computation, generic
interpreter execution, and generated modal observation inhabit one connected
construction.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedPresentedMapFusion

open Presentation NativeIndexedFamilies IntrinsicMaps
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open HOLNativeMixedRuleData
open HOLNativeMixedPresentedDriver
open IntrinsicNativeListMapComputation
open NativeHOLProofFamilyOperationalQualification
open NativeHOLProofQualifiedExecutionCospan
open NativeHOLRecursiveProofOperationalObservation
open NativeHOLTraceRecursiveExtensionalCompilerSemantics
open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation

universe uEvidence u

/-! ## Direct images of qualification and observation -/

/-- Endpoint-indexed evidence transported to canonical encoded endpoints.
The existential witnesses expose exactly where the canonical-image boundary
is used. -/
def EncodedQualifies {n : Nat} {Evidence : Type uEvidence}
    (qualifies : Evidence -> Tower.Tm n -> Tower.Tm n -> Prop)
    (evidence : Evidence)
    (left right : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : Prop :=
  exists nativeLeft nativeRight,
    left = encoded nativeLeft /\
      right = encoded nativeRight /\
        qualifies evidence nativeLeft nativeRight

/-- Direct image of an equation-respecting native observation along canonical
encoding.  The driver has syntactic equality as its equation theory, so the
image predicate is automatically invariant. -/
def encodedObservation {n : Nat}
    (observation : EquationPredicate
      (IntrinsicNativeListMapComputation.reduction Tower.zero n).closure) :
    EquationPredicate driverSystem.closure :=
  invariantPredicate driverSystem.closure
    (fun encodedTerm => exists nativeTerm,
      encodedTerm = encoded nativeTerm /\ observation nativeTerm)
    (by
      intro left right same
      change left = right at same
      subst right
      exact Iff.rfl)

/-- Move any proof-qualified level-zero List execution cospan through the
actual mixed-rule driver. -/
def toDriver {n : Nat} {Evidence : Type uEvidence}
    {qualifies : Evidence -> Tower.Tm n -> Tower.Tm n -> Prop}
    {observation : EquationPredicate
      (IntrinsicNativeListMapComputation.reduction Tower.zero n).closure}
    {left right : Tower.Tm n}
    (cospan : ProofQualifiedExecutionCospan
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      Evidence qualifies observation left right) :
    ProofQualifiedExecutionCospan driverSystem Evidence
      (EncodedQualifies qualifies) (encodedObservation observation)
      (encoded left) (encoded right) :=
  cospan.mapAlong (listToDriver n) id (encodedObservation observation)
    (fun _evidence first second qualified =>
      ⟨first, second, rfl, rfl, qualified⟩)
    (fun term observed => ⟨term, rfl, observed⟩)

@[simp]
theorem toDriver_evidence {n : Nat} {Evidence : Type uEvidence}
    {qualifies : Evidence -> Tower.Tm n -> Tower.Tm n -> Prop}
    {observation : EquationPredicate
      (IntrinsicNativeListMapComputation.reduction Tower.zero n).closure}
    {left right : Tower.Tm n}
    (cospan : ProofQualifiedExecutionCospan
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      Evidence qualifies observation left right) :
    (toDriver cospan).evidence = cospan.evidence :=
  rfl

@[simp]
theorem toDriver_path_lengths {n : Nat} {Evidence : Type uEvidence}
    {qualifies : Evidence -> Tower.Tm n -> Tower.Tm n -> Prop}
    {observation : EquationPredicate
      (IntrinsicNativeListMapComputation.reduction Tower.zero n).closure}
    {left right : Tower.Tm n}
    (cospan : ProofQualifiedExecutionCospan
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      Evidence qualifies observation left right) :
    (toDriver cospan).leftPath.length = cospan.leftPath.length /\
      (toDriver cospan).rightPath.length = cospan.rightPath.length := by
  exact ⟨OperationalTranslation.mapRoute_length
      (listToDriver n) cospan.leftPath,
    OperationalTranslation.mapRoute_length
      (listToDriver n) cospan.rightPath⟩

/-- The generated modal observation is available at both encoded program
sources after transport through the actual driver. -/
theorem toDriver_semanticDiamonds {n : Nat} {Evidence : Type uEvidence}
    {qualifies : Evidence -> Tower.Tm n -> Tower.Tm n -> Prop}
    {observation : EquationPredicate
      (IntrinsicNativeListMapComputation.reduction Tower.zero n).closure}
    {left right : Tower.Tm n}
    (cospan : ProofQualifiedExecutionCospan
      (IntrinsicNativeListMapComputation.reduction Tower.zero n)
      Evidence qualifies observation left right) :
    semanticDiamond driverSystem.closure (encodedObservation observation)
        (encoded left) /\
      semanticDiamond driverSystem.closure (encodedObservation observation)
        (encoded right) :=
  (toDriver cospan).semanticDiamonds

/-! ## The recursive HOL/Aczel/map-fusion instance -/

namespace MapFusion

open NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms
open NativeHOLProofQualifiedExecutionCospan.MapFusion

/-- The recursively compiled HOL proof and its two concrete map routes,
executed through the mixed rule-data driver. -/
noncomputable def recursiveDriverCospan
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (first second : Tower.Tm n)
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
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :=
  toDriver
    (recursiveExecutionCospan Tower.zero first second
      firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
      environment property accepted)

/-- The driver cospan retains the exact submitted and recursively compiled
map-fusion proof. -/
theorem recursiveDriverCospan_retains_source
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (first second : Tower.Tm n)
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
    (recursiveDriverCospan first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property
      accepted).evidence.proof =
        NativeHOLRecursiveProofNIKQualification.Controls.retainedMapFusionProof := by
  exact recursiveExecutionCospan_retains_source Tower.zero first second
    firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
    environment property accepted

/-- The executable driver retains the distinct primitive-step costs of the
two programs for every input spine. -/
theorem recursiveDriverCospan_path_lengths
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (first second : Tower.Tm n)
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
    let cospan := recursiveDriverCospan first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property accepted
    cospan.leftPath.length = 8 * (heads.map Prod.fst).length + 10 /\
      cospan.rightPath.length = 5 * (heads.map Prod.fst).length + 5 := by
  let sourceCospan := recursiveExecutionCospan Tower.zero first second
    firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
    environment property accepted
  have sourceLengths := recursiveExecutionCospan_path_lengths Tower.zero
    first second firstMeaning secondMeaning firstDenotes secondDenotes heads
    interpreted environment property accepted
  have mappedLengths := toDriver_path_lengths sourceCospan
  exact ⟨mappedLengths.1.trans sourceLengths.1,
    mappedLengths.2.trans sourceLengths.2⟩

/-- The common Aczel-valued result does not identify the driver histories.
Their different lengths give a concrete cost-sensitive observation which
distinguishes the two proof-qualified programs. -/
theorem recursiveDriverCospan_exact_histories_differ
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (first second : Tower.Tm n)
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
    let cospan := recursiveDriverCospan first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property accepted
    ofDiscipline (ProofQualifiedExecutionCospan.exactHistory driverSystem)
        cospan.leftPath ≠
      ofDiscipline (ProofQualifiedExecutionCospan.exactHistory driverSystem)
        cospan.rightPath := by
  let cospan := recursiveDriverCospan first second firstMeaning secondMeaning
    firstDenotes secondDenotes heads interpreted environment property accepted
  apply cospan.exactHistory_distinct_of_length_ne
  have lengths := recursiveDriverCospan_path_lengths first second
    firstMeaning secondMeaning firstDenotes secondDenotes heads interpreted
    environment property accepted
  rw [lengths.1, lengths.2]
  omega

/-- The connected instance reaches the OSLF generated from the executable
driver on both sides of the proof-qualified transformation. -/
theorem recursiveDriverCospan_semanticDiamonds
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (first second : Tower.Tm n)
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
    let observation := encodedObservation
      (semanticObservation Tower.zero environment property)
    semanticDiamond driverSystem.closure observation
        (encoded programs.unfused) /\
      semanticDiamond driverSystem.closure observation
        (encoded programs.fused) := by
  exact toDriver_semanticDiamonds
    (recursiveExecutionCospan Tower.zero first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property
      accepted)

end MapFusion

#print axioms encodedObservation
#print axioms toDriver
#print axioms toDriver_path_lengths
#print axioms toDriver_semanticDiamonds
#print axioms MapFusion.recursiveDriverCospan_retains_source
#print axioms MapFusion.recursiveDriverCospan_path_lengths
#print axioms MapFusion.recursiveDriverCospan_exact_histories_differ
#print axioms MapFusion.recursiveDriverCospan_semanticDiamonds

end HOLNativeMixedPresentedMapFusion
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
