import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLProofQualifiedOperationalCospan

/-!
# Recursive HOL proof families as operational evidence

An operational observation and a source proof establish different facts.  A
source proof has first to survive the recursive HOL-to-native compiler, native
dependent typing, and the common Aczel-trace interpretation.  Only then may a
language-specific specification say which pair of programs that evidence
qualifies.

`ConnectedIntrinsicEvidence` retains that whole mathematical route for an
arbitrary closed proof in the recursive compiler's advertised fragment.
`OperationalSpecification` is the smaller operational boundary: it receives
the requested source claim, the exact emitted native witness, and two program
endpoints.  It does not receive semantic truth alone.

The map-fusion construction is an instance.  Its specification requires the
actual map-fusion claim, the compiler's exact native output, and endpoints of
the native map programs.  Consequently the same generic evidence construction
also packages nested function extensionality, while an accepted proof of the
identity theorem cannot qualify map fusion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLProofFamilyOperationalQualification

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open NativeHOLTraceRecursiveExtensionalCompilerSemantics
open NativeHOLRecursiveProofNIKQualification
open NativeHOLRecursiveProofNIKQualification.Controls
open NativeHOLProofQualifiedOperationalCospan
open NativeHOLRecursiveProofOperationalObservation
open IntrinsicNativeListMapComputation
open ZFSetUniformListTraceTypeInterpretation

universe u uTerm

/-! ## The proof-family boundary -/

/-- One submitted proof after all mathematical parts of the connected route
have agreed on it.  The requested claim is retained separately from the proof's
intrinsic conclusion; `accepted` is the exact binding between the two. -/
structure ConnectedIntrinsicEvidence (a : ZFSet.{u}) where
  request : ClosedClaim
  proof : IntrinsicProof
  accepted : intrinsicKernel.decide request proof = true
  native : Tower.Tm 0
  code : Tower.Tm 0
  compiled :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        proof.source Fin.elim0 Fin.elim0 = some native
  represented :
    HOLLeibnizNativeQualifiedIntegration.Compiler.represent request = some code
  typed :
    Presentation.FormationSensitive.Judgment
      FormationSensitiveHOLExtensionalProfile.rules .nil native
      (FormationSensitiveHOLProofFamily.proof code)
  denotes :
    ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
      (formulaMeaning request
        NativeHOLTraceDisplayedTerms.Controls.emptyContext
        (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
          (a := a)))

namespace ConnectedIntrinsicEvidence

/-- The recursive compiler is total precisely on the retained supported
fragment, so its output can be selected computationally rather than by choice
from a semantic existence theorem. -/
private theorem compiled_isSome (proof : IntrinsicProof) :
    (HOLLeibnizNativeRecursiveExtensionalCompiler.compile
      proof.source (n := 0) Fin.elim0 Fin.elim0).isSome := by
  rw [Option.isSome_iff_exists,
    HOLLeibnizNativeQualifiedIntegration.Compiler.compile_some_iff_supported]
  exact proof.supported

def compiledNative (proof : IntrinsicProof) : Tower.Tm 0 :=
  (HOLLeibnizNativeRecursiveExtensionalCompiler.compile
    proof.source (n := 0) Fin.elim0 Fin.elim0).get (compiled_isSome proof)

theorem compiledNative_spec (proof : IntrinsicProof) :
    HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        proof.source Fin.elim0 Fin.elim0 = some (compiledNative proof) := by
  exact (Option.some_get (compiled_isSome proof)).symm

/-- Acceptance also guarantees that the requested conclusion is representable.
This proof remains proposition-valued; the code itself is selected from the
deterministic representation function. -/
private theorem represented_isSome (request : ClosedClaim)
    (a : ZFSet.{u})
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    (HOLLeibnizNativeQualifiedIntegration.Compiler.represent request).isSome := by
  rw [Option.isSome_iff_exists]
  obtain ⟨_native, code, _compiled, represented, _typed, _denotes⟩ :=
    native_acceptance_compiles_connected (a := a) request proof accepted
  exact ⟨code, represented⟩

def representedCode (a : ZFSet.{u}) (request : ClosedClaim) (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) : Tower.Tm 0 :=
  (HOLLeibnizNativeQualifiedIntegration.Compiler.represent request).get
    (represented_isSome request a proof accepted)

theorem representedCode_spec (a : ZFSet.{u}) (request : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    HOLLeibnizNativeQualifiedIntegration.Compiler.represent request =
      some (representedCode a request proof accepted) := by
  exact (Option.some_get (represented_isSome request a proof accepted)).symm

/-- The connected theorem specializes to the deterministic compiler and
representation outputs used by the evidence object. -/
private theorem accepted_properties (a : ZFSet.{u}) (request : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    Presentation.FormationSensitive.Judgment
        FormationSensitiveHOLExtensionalProfile.rules .nil
        (compiledNative proof)
        (FormationSensitiveHOLProofFamily.proof
          (representedCode a request proof accepted)) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext
        (compiledNative proof)
        (formulaMeaning request
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  obtain ⟨native, code, compiled, represented, typed, denotes⟩ :=
    native_acceptance_compiles_connected (a := a) request proof accepted
  have nativeEqual : native = compiledNative proof :=
    Option.some.inj (compiled.symm.trans (compiledNative_spec proof))
  have codeEqual : code = representedCode a request proof accepted :=
    Option.some.inj
      (represented.symm.trans (representedCode_spec a request proof accepted))
  subst native
  subst code
  exact ⟨typed, denotes⟩

/-- NIK acceptance constructs the complete connected evidence object for the
submitted proof itself. -/
def ofAccepted (a : ZFSet.{u}) (request : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    ConnectedIntrinsicEvidence a where
  request := request
  proof := proof
  accepted := accepted
  native := compiledNative proof
  code := representedCode a request proof accepted
  compiled := compiledNative_spec proof
  represented := representedCode_spec a request proof accepted
  typed := (accepted_properties a request proof accepted).1
  denotes := (accepted_properties a request proof accepted).2

/-- Every intrinsic proof is accepted at its own retained conclusion. -/
@[simp] theorem intrinsic_self_accepted (proof : IntrinsicProof) :
    intrinsicKernel.decide proof.conclusion proof = true := by
  apply (intrinsicKernel.correct proof.conclusion proof).mpr
  rfl

/-- Compile and connect any intrinsic proof at its own conclusion. -/
def ofIntrinsic (a : ZFSet.{u}) (proof : IntrinsicProof) :
    ConnectedIntrinsicEvidence a :=
  ofAccepted a proof.conclusion proof (intrinsic_self_accepted proof)

@[simp] theorem ofAccepted_request (a : ZFSet.{u}) (request : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    (ofAccepted a request proof accepted).request = request := by
  rfl

@[simp] theorem ofAccepted_proof (a : ZFSet.{u}) (request : ClosedClaim)
    (proof : IntrinsicProof)
    (accepted : intrinsicKernel.decide request proof = true) :
    (ofAccepted a request proof accepted).proof = proof := by
  rfl

@[simp] theorem ofIntrinsic_request (a : ZFSet.{u}) (proof : IntrinsicProof) :
    (ofIntrinsic a proof).request = proof.conclusion := by
  rfl

@[simp] theorem ofIntrinsic_proof (a : ZFSet.{u}) (proof : IntrinsicProof) :
    (ofIntrinsic a proof).proof = proof := by
  rfl

/-- The emitted native witness is determined by the retained source proof,
independently of how the existential compiler theorem was unpacked. -/
theorem native_unique {a : ZFSet.{u}}
    (evidence : ConnectedIntrinsicEvidence a)
    (other : Tower.Tm 0)
    (compiled :
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          evidence.proof.source Fin.elim0 Fin.elim0 = some other) :
    evidence.native = other := by
  exact Option.some.inj (evidence.compiled.symm.trans compiled)

/-- Every recursively supported closed source tree produces connected evidence
that retains that very tree.  This quantifies over the whole advertised
compiler fragment rather than enumerating its constructors a second time. -/
theorem exists_of_supported (a : ZFSet.{u}) {claim : ClosedClaim}
    (source : Mettapedia.Logic.HOL.ProofSyntax Symbol [] claim)
    (supported :
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true) :
    ∃ evidence : ConnectedIntrinsicEvidence a,
      evidence.request = claim ∧ HEq evidence.proof.source source := by
  let proof : IntrinsicProof :=
    { conclusion := claim
      source := source
      supported := supported }
  exact ⟨ofIntrinsic a proof, rfl, HEq.rfl⟩

end ConnectedIntrinsicEvidence

/-- A language-specific account of which program pair is licensed by a
requested HOL claim and the exact native proof term emitted for it. -/
abbrev OperationalSpecification (system : GSLT.{uTerm}) :=
  ClosedClaim -> Tower.Tm 0 -> system.Term -> system.Term -> Prop

/-- Connected evidence qualifies endpoints only through the selected
operational specification.  Typing and denotation are already retained in the
evidence and therefore cannot be replaced by a bare truth witness. -/
def CompiledProofQualifies {system : GSLT.{uTerm}} {a : ZFSet.{u}}
    (specification : OperationalSpecification system)
    (evidence : ConnectedIntrinsicEvidence a)
    (left right : system.Term) : Prop :=
  specification evidence.request evidence.native left right

/-- The proof-family specialization of the general operational cospan. -/
abbrev ProofFamilyOperationalCospan
    (system : GSLT.{uTerm}) (a : ZFSet.{u})
    (specification : OperationalSpecification system)
    (observation : EquationPredicate system.closure)
    (left right : system.Term) :=
  ProofQualifiedReachabilityCospan system (ConnectedIntrinsicEvidence a)
    (CompiledProofQualifies specification) observation left right

/-- Every proof-family cospan exposes the complete retained mathematical
route, not only the endpoint qualification selected by the operational
specification. -/
theorem ProofFamilyOperationalCospan.retainedConnection
    {system : GSLT.{uTerm}} {a : ZFSet.{u}}
    {specification : OperationalSpecification system}
    {observation : EquationPredicate system.closure}
    {left right : system.Term}
    (cospan : ProofFamilyOperationalCospan system a specification
      observation left right) :
    let evidence := cospan.evidence
    intrinsicKernel.decide evidence.request evidence.proof = true ∧
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          evidence.proof.source Fin.elim0 Fin.elim0 = some evidence.native ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.represent
          evidence.request = some evidence.code ∧
      Presentation.FormationSensitive.Judgment
          FormationSensitiveHOLExtensionalProfile.rules .nil evidence.native
          (FormationSensitiveHOLProofFamily.proof evidence.code) ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext
        evidence.native
        (formulaMeaning evidence.request
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  exact ⟨cospan.evidence.accepted, cospan.evidence.compiled,
    cospan.evidence.represented, cospan.evidence.typed,
    cospan.evidence.denotes⟩

/-! ## The retained map-fusion instance -/

namespace MapFusion

open NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms

/-- The operational reading of the map-fusion theorem.  The theorem requested
from NIK, the compiler output, and the program endpoints must all agree. -/
def specification {n : Nat} (level : LevelExpr) :
    OperationalSpecification (reduction level n) :=
  fun claim native left right =>
    claim = HOLLeibnizMapFusionNative.closedClaim ∧
      native = HOLLeibnizMapFusionNative.nativeProof ∧
      ∃ programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms n,
        left = programs.unfused ∧ right = programs.fused

/-- The earlier map-fusion qualifier entails the general compiler-evidence
qualifier.  Its NIK check fixes the requested claim, and determinism of the
compiler fixes the native witness. -/
theorem qualification_of_retained {n : Nat} {a : ZFSet.{u}}
    (level : LevelExpr) (proof : IntrinsicProof)
    (left right : Tower.Tm n)
    (qualified : RetainedMapFusionQualifies proof left right) :
    CompiledProofQualifies (specification (n := n) level)
      (ConnectedIntrinsicEvidence.ofIntrinsic a proof) left right := by
  refine ⟨?_, ?_, qualified.2.2⟩
  · have bound : proof.conclusion = HOLLeibnizMapFusionNative.closedClaim :=
      (intrinsicKernel.correct HOLLeibnizMapFusionNative.closedClaim proof).mp
        qualified.1
    exact (ConnectedIntrinsicEvidence.ofIntrinsic_request a proof).trans bound
  · exact ConnectedIntrinsicEvidence.native_unique
      (ConnectedIntrinsicEvidence.ofIntrinsic a proof)
      HOLLeibnizMapFusionNative.nativeProof qualified.2.1

/-- The map-fusion cospan reindexed by the general connected proof family.
No execution or observation witness is rebuilt. -/
noncomputable def recursiveCospan
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr) (first second : Tower.Tm n)
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
    ProofFamilyOperationalCospan (reduction level n) a
      (specification level)
      (semanticObservation level environment property)
      programs.unfused programs.fused := by
  exact
    (NativeHOLProofQualifiedOperationalCospan.recursiveMapFusionCospan
      level first second firstMeaning secondMeaning firstDenotes secondDenotes
        heads interpreted environment property accepted).mapEvidence
      (fun proof => ConnectedIntrinsicEvidence.ofIntrinsic a proof)
      (fun proof left right qualified =>
        qualification_of_retained level proof left right qualified)

/-- The generalized cospan still carries the actual retained induction proof,
not merely its conclusion or a separately reconstructed inhabitant. -/
theorem recursiveCospan_retains_source
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr) (first second : Tower.Tm n)
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
    (recursiveCospan level first second firstMeaning secondMeaning
      firstDenotes secondDenotes heads interpreted environment property
        accepted).evidence.proof = retainedMapFusionProof := by
  rfl

/-- The generalized cospan exposes the same pair of generated modal
observations as the underlying map-fusion execution. -/
theorem recursiveCospan_semanticDiamonds
    {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr) (first second : Tower.Tm n)
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
        (semanticObservation level environment property) programs.unfused ∧
      semanticDiamond (reduction level n).closure
        (semanticObservation level environment property) programs.fused := by
  exact (recursiveCospan level first second firstMeaning secondMeaning
    firstDenotes secondDenotes heads interpreted environment property
      accepted).semanticDiamonds

end MapFusion

/-! ## Family-level controls -/

namespace Controls

open HOLLeibnizNativeRecursiveExtensionalCompiler.Controls
open HOLLeibnizNativeExtensionalProofTranslation.Controls

/-- A nested symmetry-over-function-extensionality proof uses the same general
evidence constructor; it is not a map-fusion-specific path. -/
def nestedExtensionalProof : IntrinsicProof where
  conclusion := .eq propositionIdentityFunction propositionIdentityFunction
  source := symmetricFunctionExtensionality
  supported :=
    HOLLeibnizNativeQualifiedIntegration.Controls.nested_extensional_source_supported

noncomputable def nestedExtensionalEvidence (a : ZFSet.{u}) :
    ConnectedIntrinsicEvidence a :=
  ConnectedIntrinsicEvidence.ofIntrinsic a nestedExtensionalProof

theorem nested_extensional_evidence_retains_and_compiles (a : ZFSet.{u}) :
    (nestedExtensionalEvidence a).proof = nestedExtensionalProof ∧
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          nestedExtensionalProof.source Fin.elim0 Fin.elim0 =
        some (nestedExtensionalEvidence a).native := by
  exact ⟨rfl, (nestedExtensionalEvidence a).compiled⟩

/-- The whole advertised recursive fragment has connected evidence, while the
existing unsupported conjunction lies outside it. -/
theorem supported_family_and_conjunction_boundary (a : ZFSet.{u})
    (p : HOLLeibnizNativeQualifiedIntegration.Compiler.Formula []) :
    (∀ {claim : ClosedClaim}
      (source : Mettapedia.Logic.HOL.ProofSyntax Symbol [] claim),
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true ->
        ∃ evidence : ConnectedIntrinsicEvidence a,
          evidence.request = claim ∧ HEq evidence.proof.source source) ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported
        (HOLLeibnizNativeQualifiedIntegration.Controls.unsupportedConjunction p) =
          false := by
  exact ⟨fun source supported =>
      ConnectedIntrinsicEvidence.exists_of_supported a source supported,
    HOLLeibnizNativeQualifiedIntegration.Controls.conjunction_is_not_supported p⟩

/-- A connected proof of a different theorem cannot satisfy the map-fusion
operational specification. -/
theorem identity_evidence_does_not_qualify_mapFusion
    (level : LevelExpr) (a : ZFSet.{u}) {n : Nat}
    (programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms n) :
    ¬ CompiledProofQualifies (MapFusion.specification level)
      (ConnectedIntrinsicEvidence.ofIntrinsic a identityProof)
      programs.unfused programs.fused := by
  intro qualified
  have requestEqual := qualified.1
  have accepted :
      intrinsicKernel.decide HOLLeibnizMapFusionNative.closedClaim
        identityProof = true := by
    apply (intrinsicKernel.correct
      HOLLeibnizMapFusionNative.closedClaim identityProof).mpr
    exact (ConnectedIntrinsicEvidence.ofIntrinsic_request a identityProof).symm.trans
      requestEqual
  rw [NativeHOLProofQualifiedOperationalCospan.identityProof_rejected_for_mapFusion]
    at accepted
  exact Bool.false_ne_true accepted

end Controls

#print axioms ConnectedIntrinsicEvidence.exists_of_supported
#print axioms ConnectedIntrinsicEvidence.native_unique
#print axioms ProofFamilyOperationalCospan.retainedConnection
#print axioms MapFusion.qualification_of_retained
#print axioms MapFusion.recursiveCospan_retains_source
#print axioms MapFusion.recursiveCospan_semanticDiamonds
#print axioms Controls.nested_extensional_evidence_retains_and_compiles
#print axioms Controls.supported_family_and_conjunction_boundary
#print axioms Controls.identity_evidence_does_not_qualify_mapFusion

end NativeHOLProofFamilyOperationalQualification
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
