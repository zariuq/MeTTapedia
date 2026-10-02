import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedHOTGOperationalIntegration
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListCognitiveWorkload

/-!
# The qualified STT/HOL fragment inside the native dependent tower

This module packages the exact theorem boundary established by the recursive
HOL compiler and its models.  It is intentionally not an unrestricted
embedding claim.

For every set carrier, a supported closed source proof compiles to one retained
native term that is both formation-sensitively typed and a section of the
Aczel-trace interpretation of its source conclusion.  Compiler success is
equivalent to the structural support classifier.  Conversion is reflected on
the intrinsically typed simple image, and adding the opaque extensional proof
constants changes no native conversion.

Three stronger reflection claims remain false and are fields of the package,
not prose qualifications: new extensional inhabitants need not type in the
constructive base, unrestricted raw tower inhabitants need not reflect to the
legacy calculus, and erasing intrinsic domain annotations is not injective.

The concrete trace model has full and inhabited domains and consequently a
semantic Hilbert-choice operation.  That model property is separate from the
source compiler, whose exact structural classifier does not gain an extra
choice rule from the model.
-/

open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeQualifiedFragmentTheorem

open Presentation Presentation.FormationSensitive Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open NativeTraceLambdaSemantics (Context)
open ZFSetUniverseLift

universe u

abbrev SourceContext :=
  HOLLeibnizNativeQualifiedIntegration.Compiler.SourceContext

abbrev Formula := HOLLeibnizNativeQualifiedIntegration.Compiler.Formula

/-! ## One reusable theorem package -/

/-- Formation-sensitive laws that make the opaque extensional proof family an
attachment rather than an isolated collection of constants.  Open
constructive derivations may be included and instantiated by proof terms that
exist only in the extension. -/
structure ProofFamilyAttachmentLaws : Prop where
  includeConversion :
    ∀ {n : Nat} {left right : Tower.Tm n},
      Conv FormationSensitiveHOLProofFamily.rules.headEq left right
          FormationSensitiveHOLProofFamily.rules.computation →
        Conv FormationSensitiveHOLExtensionalProfile.rules.headEq left right
          FormationSensitiveHOLExtensionalProfile.rules.computation

  attachBaseDerivation :
    ∀ {k n : Nat} {source : Tower.Ctx k} {target : Tower.Ctx n}
      {body type : Tower.Tm k} {substitution : Sub Tower.Head k n},
      Typing FormationSensitiveHOLProofFamily.rules source body type →
      Presentation.FormationSensitive.CtxMor
          FormationSensitiveHOLExtensionalProfile.rules
          source target substitution →
      Typing FormationSensitiveHOLExtensionalProfile.rules target
        (subst substitution body) (subst substitution type)

  instantiateBaseOperation :
    ∀ {n : Nat} {context : Tower.Ctx n}
      {domain result : Tower.Tm n} {body : Tower.Tm (n + 1)}
      {argument : Tower.Tm n},
      Typing FormationSensitiveHOLProofFamily.rules
          (.snoc context domain) body (rename wk result) →
      Typing FormationSensitiveHOLExtensionalProfile.rules
          context argument domain →
      Typing FormationSensitiveHOLExtensionalProfile.rules context
        (subst (consSub argument ids) body) result

  instantiateBaseOperation2 :
    ∀ {n : Nat} {context : Tower.Ctx n}
      {firstDomain secondDomain result : Tower.Tm n}
      {body : Tower.Tm (n + 2)} {firstArgument secondArgument : Tower.Tm n},
      Typing FormationSensitiveHOLProofFamily.rules
          (.snoc (.snoc context firstDomain) (rename wk secondDomain)) body
          (rename wk (rename wk result)) →
      Typing FormationSensitiveHOLExtensionalProfile.rules
          context firstArgument firstDomain →
      Typing FormationSensitiveHOLExtensionalProfile.rules
          context secondArgument secondDomain →
      Typing FormationSensitiveHOLExtensionalProfile.rules context
        (subst (consSub secondArgument (consSub firstArgument ids)) body)
        result

/-- The existing context-comprehension construction supplies all general
attachment laws. -/
theorem proofFamilyAttachmentLaws : ProofFamilyAttachmentLaws where
  includeConversion :=
    FormationSensitiveHOLExtensionalDerived.include_conversion
  attachBaseDerivation :=
    FormationSensitiveHOLExtensionalDerived.attach_base_derivation
  instantiateBaseOperation :=
    FormationSensitiveHOLExtensionalDerived.instantiate_base_operation
  instantiateBaseOperation2 :=
    FormationSensitiveHOLExtensionalDerived.instantiate_base_operation2

/-- Exact guarantees and exact failures for the current recursive HOL fragment
at one chosen trace carrier.  This is a theorem bundle, not a candidate
language selection. -/
structure QualifiedFragment (a : ZFSet.{u}) where
  attachment : ProofFamilyAttachmentLaws

  compilerExact :
    ∀ {gamma : SourceContext} {delta : List (Formula gamma)}
      {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
      {n : Nat} (objects : Sub Tower.Head gamma.length n)
      (hypotheses : Fin delta.length → Tower.Tm n),
      (∃ native,
          HOLLeibnizNativeRecursiveExtensionalCompiler.compile
            source objects hypotheses = some native) ↔
        HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true

  closedConnection :
    ∀ {phi : Formula []} (source : HOL.ProofSyntax Symbol [] phi),
      HOLLeibnizNativeQualifiedIntegration.Compiler.supported source = true →
      ∃ native code,
        HOLLeibnizNativeRecursiveExtensionalCompiler.compile
            source Fin.elim0 Fin.elim0 = some native ∧
        HOLLeibnizNativeQualifiedIntegration.Compiler.represent phi =
          some code ∧
        Judgment FormationSensitiveHOLExtensionalProfile.rules .nil native
          (FormationSensitiveHOLProofFamily.proof code) ∧
        NativeHOLTraceRecursiveExtensionalCompilerSemantics.ProofDenotes a
          NativeHOLTraceDisplayedTerms.Controls.emptyContext native
          (NativeHOLTraceRecursiveExtensionalCompilerSemantics.formulaMeaning
            phi NativeHOLTraceDisplayedTerms.Controls.emptyContext
            (fun _ =>
              ZFSetUniformListTraceTermInterpretation.emptyValuation
                (a := a)))

  opaqueConversionConservative :
    ∀ {n : Nat} (left right : Tower.Tm n),
      Conv FormationSensitiveHOLProofFamily.rules.headEq left right
          FormationSensitiveHOLProofFamily.rules.computation ↔
        Conv FormationSensitiveHOLExtensionalProfile.rules.headEq left right
          FormationSensitiveHOLExtensionalProfile.rules.computation

  simpleConversionReflected :
    ∀ {gamma : List Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Ty}
      {type : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Ty}
      (left right : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.Term gamma type),
      Conv Tower.HeadEq
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm left)
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm right) ↔
        Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT.BetaConv left right

  extensionalTypingNotReflected :
    ¬ (∀ (term type : Tower.Tm 0),
      Typing FormationSensitiveHOLExtensionalProfile.rules .nil term type →
        Typing FormationSensitiveHOLProofFamily.rules .nil term type)

  unrestrictedRawTypingNotReflected :
    ¬ (∀ (Γ : Presentation.Legacy.Ctx 0)
      (term type : Presentation.Legacy.Tm 0),
      Presentation.Tower.HasType (Presentation.Legacy.embedCtx Γ)
          (Presentation.Legacy.embed term) (Presentation.Legacy.embed type) →
        Presentation.Legacy.HasType Γ term type)

  sourceErasureNotReflected :
    Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity ≠
        Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity ∧
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
          Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity =
        Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
          Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity ∧
      Judgment Tower.rules .nil
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
            Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardAtomicIdentity)
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTypeAt 0
            FormationSensitiveSimpleFragment.Examples.endomorphism) ∧
      Judgment Tower.rules .nil
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTerm
            Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ErasureBoundary.discardFunctionIdentity)
          (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT.eraseTypeAt 0
            FormationSensitiveSimpleFragment.Examples.endomorphism)

  unsupportedConjunctionStaysOutside :
    ∀ (p : Formula []),
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
        (HOLLeibnizNativeQualifiedIntegration.Controls.unsupportedConjunction p)
        (n := 0) Fin.elim0 (fun _ => .const `unsupportedHypothesis) = none

/-- The currently proved recursive compiler and formation-sensitive tower
satisfy the package for every chosen set carrier. -/
theorem current (a : ZFSet.{u}) : QualifiedFragment a where
  attachment := proofFamilyAttachmentLaws
  compilerExact :=
    HOLLeibnizNativeQualifiedIntegration.Compiler.compile_some_iff_supported
  closedConnection := fun source supported =>
    HOLLeibnizNativeQualifiedIntegration.Connected.compile_closed_preserves_typing_and_trace
      source supported
  opaqueConversionConservative :=
    HOLLeibnizNativeQualifiedIntegration.Boundary.extensional_conversion_iff
  simpleConversionReflected :=
    HOLLeibnizNativeQualifiedIntegration.Boundary.simple_conversion_on_image
  extensionalTypingNotReflected :=
    HOLLeibnizNativeQualifiedIntegration.Boundary.extensional_typing_reflection_is_false
  unrestrictedRawTypingNotReflected :=
    HOLLeibnizNativeQualifiedIntegration.Boundary.unrestricted_raw_typing_reflection_is_false
  sourceErasureNotReflected :=
    HOLLeibnizNativeQualifiedIntegration.Boundary.source_syntax_reflection_is_false
  unsupportedConjunctionStaysOutside :=
    HOLLeibnizNativeQualifiedIntegration.Controls.conjunction_is_not_compiled

/-! ## The source and model assumptions are separate -/

/-- The source simple types have only propositions, named base types, and
arrows.  There is no source-level type-variable or type-quantifier constructor
in this fragment. -/
theorem source_type_shape (type : HOL.Ty BaseSort) :
    type = .prop ∨
      (∃ base : BaseSort, type = .base base) ∨
      ∃ domain codomain : HOL.Ty BaseSort, type = .arr domain codomain := by
  cases type with
  | prop => exact Or.inl rfl
  | base base => exact Or.inr (Or.inl ⟨base, rfl⟩)
  | arr domain codomain => exact Or.inr (Or.inr ⟨domain, codomain, rfl⟩)

/-- One admissible value at each base sort of the concrete trace model. -/
noncomputable def baseWitness (base : BaseSort) :
    ZFSetUniformListModel.carrier carrierCode.{u} base :=
  match base with
  | .element => ZFSetUniverseLift.encode ∅
  | .sequence => ZFSetList.nil carrierCode.{u}
  | .count => ZFSetUniformListModel.encodeCount 0

/-- The actual trace model used by the HOTG instance has an admissible
inhabitant at every simple type. -/
noncomputable def inhabitedDomains :
    (ZFSetUniformListModel.model carrierCode.{u}).InhabitedDomains :=
  (ZFSetUniformListModel.model carrierCode.{u}).inhabitedDomains_of_fullDomains
    (ZFSetUniformListModel.fullDomains carrierCode.{u}) baseWitness

/-- Hilbert choice is available semantically because this particular model is
both full and inhabited.  It is not a new source proof constructor. -/
noncomputable def hilbertChoice :
    (ZFSetUniformListModel.model carrierCode.{u}).HilbertChoice :=
  HOL.HenkinModel.HilbertChoice.ofFullInhabitedDomains
    (ZFSetUniformListModel.fullDomains carrierCode.{u}) inhabitedDomains

/-- The model-side assumptions are explicit proof objects. -/
theorem concrete_model_properties :
    (ZFSetUniformListModel.model carrierCode.{u}).FullDomains ∧
      Nonempty (ZFSetUniformListModel.model
        carrierCode.{u}).InhabitedDomains ∧
      Nonempty (ZFSetUniformListModel.model
        carrierCode.{u}).HilbertChoice :=
  ⟨ZFSetUniformListModel.fullDomains carrierCode.{u},
    ⟨inhabitedDomains⟩, ⟨hilbertChoice⟩⟩

/-! ## Nontrivial instantiations and controls -/

/-- Nested function extensionality lies inside the exact recursive fragment
and reaches the connected theorem package. -/
theorem nested_extensionality_connected :
    ∃ native code,
      HOLLeibnizNativeRecursiveExtensionalCompiler.compile
          HOLLeibnizNativeRecursiveExtensionalCompiler.Controls.symmetricFunctionExtensionality
          Fin.elim0 Fin.elim0 = some native ∧
      HOLLeibnizNativeQualifiedIntegration.Compiler.represent
          (.eq
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction) =
        some code ∧
      Judgment FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) ∧
      NativeHOLTraceRecursiveExtensionalCompilerSemantics.ProofDenotes
        carrierCode.{u} NativeHOLTraceDisplayedTerms.Controls.emptyContext
        native
        (NativeHOLTraceRecursiveExtensionalCompilerSemantics.formulaMeaning
          (.eq
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction
            HOLLeibnizNativeExtensionalProofTranslation.Controls.propositionIdentityFunction)
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ =>
            ZFSetUniformListTraceTermInterpretation.emptyValuation
              (a := carrierCode.{u}))) :=
  HOLLeibnizNativeQualifiedIntegration.Controls.nested_extensional_connected
    carrierCode.{u}

/-- The exact connected claim instantiated by the actual HOTG/operational
singleton. -/
abbrev HOTGOperationalClaim (level : LevelExpr Nat)
    (lower : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (x : ZFSetUniformListTraceTypeInterpretation.Value
      carrierCode.{u} element) : Prop :=
    (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
        level lower x).evidence.proof =
          NativeHOLRecursiveProofNIKQualification.Controls.retainedMapFusionProof ∧
      (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
        level lower x).evidence.native = HOLLeibnizMapFusionNative.nativeProof ∧
      (HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgConsumedEndpoint
        lower (ZFSetList.encodeValue [x])).1 =
        (HOLLeibnizNativeQualifiedHOTGIntegration.DependentConsumption.recursiveFusionIdentityPoint
          (NativeHOLCompiledMapFusionHOTG.universeMap lower)
          NativeHOLCompiledMapFusionHOTG.powerMap
          (ZFSetList.encodeValue [x])).1.1.2.1 ∧
      (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
        level lower x).leftPath.length = 18 ∧
      (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
        level lower x).rightPath.length = 10 ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (IntrinsicNativeListMapComputation.reduction level 3).closure
        (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.observation
          level lower x)
        HOLLeibnizNativeQualifiedHOTGOperationalIntegration.programs.unfused ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
        (IntrinsicNativeListMapComputation.reduction level 3).closure
        (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.observation
          level lower x)
        HOLLeibnizNativeQualifiedHOTGOperationalIntegration.programs.fused ∧
      Mettapedia.GSLT.Dynamics.ExecutionPathObservation.ofDiscipline
          (NativeHOLProofQualifiedExecutionCospan.ProofQualifiedExecutionCospan.exactHistory
            (IntrinsicNativeListMapComputation.reduction level 3))
          (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
            level lower x).leftPath ≠
        Mettapedia.GSLT.Dynamics.ExecutionPathObservation.ofDiscipline
          (NativeHOLProofQualifiedExecutionCospan.ProofQualifiedExecutionCospan.exactHistory
            (IntrinsicNativeListMapComputation.reduction level 3))
          (HOLLeibnizNativeQualifiedHOTGOperationalIntegration.executionCospan
            level lower x).rightPath

/-- The actual HOTG/operational singleton is the nontrivial instance of this
qualified mathematical boundary. -/
theorem hotg_operational_instance (level : LevelExpr Nat)
    (lower : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (x : ZFSetUniformListTraceTypeInterpretation.Value
      carrierCode.{u} element) : HOTGOperationalClaim level lower x :=
  HOLLeibnizNativeQualifiedHOTGOperationalIntegration.connected_hotg_map_fusion
    level lower x

/-! ## The connected candidate boundary -/

/-- The assumption-change control used by the connected package.  The actual
chart proof of map length is accepted under the full induction theory, but the
same request is rejected when the induction principle is removed and only the
four computation equations remain. -/
abbrev ChangedAssumptionsRejected : Prop :=
  UniformListCognitiveWorkload.consume 1 2
      [UniformListCognitiveWorkload.emptySample,
        UniformListCognitiveWorkload.nonemptySample]
      .inputLength HOL.UniformListInduction.equations
      { UniformListChartNIKService.actualRequest [] with
        claim := (HOL.UniformListInduction.equations,
          HOL.UniformListInduction.mapLength) }
      HOL.UniformListInductionRevisionViews.Induction.initialEnvironment =
    .proofRejected

/-- One theorem package collecting the current mathematical and operational
connection, including the controls that delimit it.  In particular, rejection
at a wrong conclusion is not refutation, evidence for another theorem cannot
qualify map fusion, and internalizing the HOTG proof value requires a genuinely
higher universe assumption. -/
structure QualifiedConnectedPackage : Prop where
  fragment : QualifiedFragment carrierCode.{u}

  wrongTargetBoundary :
    NativeHOLRecursiveProofNIKQualification.intrinsicKernel.decide
        NativeHOLRecursiveProofNIKQualification.Controls.identityClaim
        NativeHOLRecursiveProofNIKQualification.Controls.retainedMapFusionProof =
          false ∧
      NativeHOLRecursiveProofNIKQualification.intrinsicKernel.decide
        NativeHOLRecursiveProofNIKQualification.Controls.identityClaim
        NativeHOLRecursiveProofNIKQualification.Controls.identityProof = true ∧
      NativeHOLRecursiveProofNIKQualification.sourceTarget.Meaning
        NativeHOLRecursiveProofNIKQualification.Controls.identityClaim

  distinctProofDoesNotQualify :
    ∀ (level : LevelExpr Nat) {n : Nat}
      (programs : NativeHOLProofQualifiedOperationalCospan.MapFusionPrograms n),
      ¬ NativeHOLProofFamilyOperationalQualification.CompiledProofQualifies
          (NativeHOLProofFamilyOperationalQualification.MapFusion.specification
            level)
          (NativeHOLProofFamilyOperationalQualification.ConnectedIntrinsicEvidence.ofIntrinsic
            carrierCode.{u}
            NativeHOLRecursiveProofNIKQualification.Controls.identityProof)
          programs.unfused programs.fused

  changedAssumptionsRejected : ChangedAssumptionsRejected

  hotgOperational :
    ∀ (level : LevelExpr Nat)
      (lower : ZFSetUniverseClosure.CofinalInaccessibles.{u})
      (x : ZFSetUniformListTraceTypeInterpretation.Value
        carrierCode.{u} element),
      HOTGOperationalClaim level lower x

  proofValueInHigherUniverse :
    ∀ (lower : ZFSetUniverseClosure.CofinalInaccessibles.{u})
      (upper : ZFSetUniverseClosure.CofinalInaccessibles.{u + 1})
      (xs : ZFSetUniformListTraceTypeInterpretation.Value
        carrierCode.{u} sequence),
      (HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgFusionProofValue
        lower xs).1 ∈
        ZFSetInterpretation.universeSet upper
          (ZFSetIndexedClosure.seed carrierCode.{u}) 0

  finiteClosureInsufficient :
    ∃ U a : ZFSet.{u}, ZFSetUniverseClosure.Closed U ∧ a ∈ U ∧
      ZFSetList.listCode a ⊆ U ∧ ZFSetList.listCode a ∉ U

  sameLevelLiteralCodeImpossible :
    ¬ ∃ code : ZFSet.{u},
      Nonempty (ZFSetDependentProducts.Elements code ≃ ZFSet.{u})

/-- The current retained proof, recursive compiler, dependent consumer, HOTG
interpretation, and native operational observation satisfy the connected
package.  No new candidate language is selected by this theorem. -/
theorem connectedPackage : QualifiedConnectedPackage.{u} where
  fragment := current carrierCode.{u}
  wrongTargetBoundary :=
    NativeHOLRecursiveProofNIKQualification.Controls.wrong_target_rejection_does_not_refute
  distinctProofDoesNotQualify := fun level {_n} programs =>
    NativeHOLProofFamilyOperationalQualification.Controls.identity_evidence_does_not_qualify_mapFusion
      level carrierCode.{u} programs
  changedAssumptionsRejected :=
    UniformListCognitiveWorkload.changed_assumptions_rejected
  hotgOperational := hotg_operational_instance
  proofValueInHigherUniverse :=
    HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.hotgFusionProofValue_small
  finiteClosureInsufficient :=
    HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.finite_closure_is_insufficient
  sameLevelLiteralCodeImpossible :=
    HOLLeibnizNativeQualifiedHOTGIntegration.HOTG.same_level_literal_code_is_impossible

#print axioms current
#print axioms proofFamilyAttachmentLaws
#print axioms source_type_shape
#print axioms concrete_model_properties
#print axioms nested_extensionality_connected
#print axioms hotg_operational_instance
#print axioms connectedPackage

end HOLLeibnizNativeQualifiedFragmentTheorem
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
