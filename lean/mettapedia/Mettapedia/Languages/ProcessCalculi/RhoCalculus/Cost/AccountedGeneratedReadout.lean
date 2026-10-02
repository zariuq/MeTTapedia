import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSourceReification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedCommitments
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImageReadback
import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction
import Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation

/-!
# Source-indexed accounted readout of actual generated code

The existing decoder and runtime reifier construct a full scoped rho value.
The relative free binding model receives this value through genuine clone
morphisms. Its observation is the full source equation class. The original
decoder value and authored Pattern index retain literal keys and authority.

This is a source readout of the supported decoder image, not an interpretation
of arbitrary generated Cost contexts or a simulation of resource firing.
Ordinary clone substitution is retained before the separately selected
reflective computation; process drop/quote computation is not added as an
equation of the name-only reflective quotient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AccountedGeneratedReadout

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open RuntimeSourceReification

noncomputable abbrev source := AccountBindingAlgebra.RhoSourceComparison.source

noncomputable def sourceBase : Over source := Over.mk (𝟙 source)

noncomputable def accounted := FreeAccountBindingModel.model source Srt.pr sourceBase

/-- The complete source quotient enters the actual free model by its unit. -/
noncomputable def sourceFold :
    FreeBindingClone.Hom (BindingCloneAlgebra.terms sig) accounted.observed.left :=
  FreeBindingClone.Hom.comp (BindingEquationQuotientModel.projection rhoSourceE)
    (FreeAccountBindingModel.generatorHom source Srt.pr sourceBase)

noncomputable def program {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    accounted.observed.left.substitution.Carrier Γ sort := sourceFold.raw.map term

/-- This comparison keeps the whole source class, including the input binder. -/
theorem program_observation {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    accounted.observed.hom.raw.map (program term) =
      (Quotient.mk (eqSetoid rhoSourceE Γ sort) term : TermQ rhoSourceE Γ sort) := rfl

theorem program_substitute {Γ Δ : Ctx sig} {sort : Srt}
    (env : Sub sig Γ Δ) (term : Term sig Γ sort) :
    program (bind env term) = accounted.observed.left.substitution.substitute
      (fun s position => program (env s position)) (program term) :=
  sourceFold.map_substitute env term

/-- No account extrusion is used: the continuation remains in its extended context. -/
theorem program_input {Γ : Ctx sig} (channel : Term sig Γ Srt.nm)
    (continuation : Term sig (Srt.nm :: Γ) Srt.pr) :
    program (.op Op.inp (.cons channel (.cons continuation .nil))) =
      accounted.observed.left.operation Op.inp
        (.cons (program channel) (.cons (program continuation) .nil)) :=
  sourceFold.raw.map_operation Op.inp (.cons channel (.cons continuation .nil))

/-- The two coordinates are data returned by independent executable functions. -/
structure Readout (depth : Nat) (origin : Pattern) where
  runtime : DecodedCode depth origin
  intrinsic : Term sig (nameContext depth) Srt.pr

def readout? (fuel depth : Nat) (origin : Pattern) : Option (Readout depth origin) :=
  match ActivationGenerated.code? fuel depth origin with
  | none => none
  | some runtime => (RuntimeSourceReification.code? depth runtime.val).map
      (fun intrinsic => ⟨runtime, intrinsic⟩)

theorem readout_found {fuel depth : Nat} {origin : Pattern}
    {result : Readout depth origin} (found : readout? fuel depth origin = some result) :
    ActivationGenerated.code? fuel depth origin = some result.runtime ∧
      RuntimeSourceReification.code? depth result.runtime.val = some result.intrinsic := by
  unfold readout? at found
  cases runtimeFound : ActivationGenerated.code? fuel depth origin with
  | none => simp [runtimeFound] at found
  | some runtime =>
      simp only [runtimeFound] at found
      obtain ⟨intrinsic, intrinsicFound, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      exact ⟨rfl, intrinsicFound⟩

theorem readout_exists {fuel depth : Nat} {origin : Pattern}
    {runtime : DecodedCode depth origin}
    (parsed : ActivationGenerated.code? fuel depth origin = some runtime) :
    ∃ result, readout? fuel depth origin = some result ∧ result.runtime = runtime := by
  have image := code_parser_image (by simp only [parsed, Option.map_some] :
    (ActivationGenerated.code? fuel depth origin).map Subtype.val = some runtime.val)
  obtain ⟨intrinsic, intrinsicFound, _⟩ := code_image_readout image
  exact ⟨⟨runtime, intrinsic⟩, by simp [readout?, parsed, intrinsicFound], rfl⟩

theorem readout_of_image {depth : Nat} {origin : Pattern}
    {runtime : CostTerm LiteralAuthority} (image : CodeImage depth origin runtime) :
    ∃ fuel result, readout? fuel depth origin = some result ∧ result.runtime.val = runtime := by
  obtain ⟨fuel, parsed⟩ := code_parser_iff_image.mpr image
  obtain ⟨decoded, decodedFound, same⟩ := Option.map_eq_some_iff.mp parsed
  obtain ⟨result, resultFound, exactRuntime⟩ := readout_exists decodedFound
  exact ⟨fuel, result, resultFound, by rw [exactRuntime, same]⟩

theorem readout_image {fuel depth : Nat} {origin : Pattern}
    {result : Readout depth origin} (found : readout? fuel depth origin = some result) :
    CodeImage depth origin result.runtime.val := by
  have parsed := (readout_found found).1
  exact code_parser_image (fuel := fuel) (by simp only [parsed, Option.map_some])

theorem readout_quoteSafe {fuel depth : Nat} {origin : Pattern}
    {result : Readout depth origin} (found : readout? fuel depth origin = some result) :
    intrinsicQuoteSafe depth result.intrinsic = true :=
  code_readout_quoteSafe (readout_image found) (readout_found found).2

/-- Source observation agrees with the erased authored origin after actual canonicalization. -/
theorem readout_canonical_observation {fuel depth : Nat} {origin : Pattern}
    {result : Readout depth origin} (found : readout? fuel depth origin = some result) :
    encodeEquationClass (accounted.observed.hom.raw.map (program result.intrinsic)) =
      canonicalize (eraseGenerated origin) := by
  rw [program_observation, encodeEquationClass_mk]
  exact code_readout_canonical (readout_image found) (readout_found found).2

/-- Closed reified values enter the original admitted source fibre. -/
def closedSource (term : Term sig [] Srt.pr) (safe : intrinsicQuoteSafe 0 term = true) :
    rhoCIGSLT.CanonicalCarrier := by
  let closed := ClosedCarrierAgreement.closedProcessEquiv.symm (encodeClosedProcess term safe)
  refine ⟨closed.val, ?_⟩
  rcases closed.property with ⟨⟨typed, _, canonical, object, scope⟩, reflective⟩
  exact ⟨⟨typed, canonical, object, scope⟩, reflective⟩

theorem closedSource_pattern (term : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 term = true) :
    (closedSource term safe).val = encodeTerm term := rfl

theorem closedSource_key (term : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 term = true) :
    (rhoCIGSLT.canonicalKey (closedSource term safe)).val.val =
      canonicalize (encodeTerm term) := by
  change canonicalize (closedSource term safe).val = _
  rfl

/-- The admitted source key is constructively associated to the retained origin's erasure. -/
theorem readout_source_key {fuel : Nat} {origin : Pattern} {result : Readout 0 origin}
    (found : readout? fuel 0 origin = some result) :
    (rhoCIGSLT.canonicalKey (closedSource result.intrinsic (readout_quoteSafe found))).val.val =
      canonicalize (eraseGenerated origin) := by
  rw [closedSource_key]
  exact code_readout_canonical (readout_image found) (readout_found found).2

/-- The authority is constructed from the admitted retained source readout. -/
def readoutAuthority {fuel : Nat} {origin : Pattern} {result : Readout 0 origin}
    (found : readout? fuel 0 origin = some result) :=
  Commitments.authority (closedSource result.intrinsic (readout_quoteSafe found))

theorem readoutAuthority_positive {fuel : Nat} {origin : Pattern}
    {result : Readout 0 origin} (found : readout? fuel 0 origin = some result) :
    (readoutAuthority found).val.RuntimeValid := Commitments.positive_authority _

theorem readoutAuthority_decoded {fuel : Nat} {origin : Pattern}
    {result : Readout 0 origin} (found : readout? fuel 0 origin = some result) :
    signature? (AtomicSignatureInterpretation.canonical rhoCIGSLT
      (closedSource result.intrinsic (readout_quoteSafe found))) =
      some (readoutAuthority found) := Commitments.canonical_decoded _

/-- Exact authority syntax commits to the source key, before an optional numerical valuation. -/
theorem readoutAuthority_literal {fuel : Nat} {origin : Pattern}
    {result : Readout 0 origin} (found : readout? fuel 0 origin = some result) :
    (readoutAuthority found).val =
      ({AtomicSignatureInterpretation.commitLiteral (canonicalize (eraseGenerated origin))} :
        CostSig LiteralAuthority) := by
  change ({AtomicSignatureInterpretation.commitLiteral
    (rhoCIGSLT.canonicalKey (closedSource result.intrinsic
      (readout_quoteSafe found))).val.val} : CostSig LiteralAuthority) = _
  rw [readout_source_key found]

/-- The constructed commitment denotes one nontrivial account atom of the retained key. -/
theorem readoutAuthority_annotation {fuel : Nat} {origin : Pattern}
    {result : Readout 0 origin} (found : readout? fuel 0 origin = some result) :
    AtomicSignatureInterpretation.readSignature?
      (AtomicSignatureInterpretation.canonical rhoCIGSLT
        (closedSource result.intrinsic (readout_quoteSafe found))) =
      some (FreeMonoid.of (AtomicSignatureInterpretation.keyOfNat
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (canonicalize (eraseGenerated origin))))) := by
  rw [AtomicSignatureInterpretation.canonical,
    AtomicSignatureInterpretation.readSignature_commitLiteral, readout_source_key found]

theorem readoutAuthority_annotation_nonunit {fuel : Nat} {origin : Pattern}
    {result : Readout 0 origin} (found : readout? fuel 0 origin = some result) :
    ∃ account, AtomicSignatureInterpretation.readSignature?
      (AtomicSignatureInterpretation.canonical rhoCIGSLT
        (closedSource result.intrinsic (readout_quoteSafe found))) = some account ∧ account ≠ 1 :=
  ⟨_, readoutAuthority_annotation found, AtomicSignatureInterpretation.committed_account_nonunit _⟩

/-- Evaluate the original unit/product sublanguage, independently of literal authority. -/
def signatureAnnotation? {M : Type} [Monoid M] : Pattern → Option M
  | .apply constructor [] =>
      if constructor = costSignatureUnitConstructorName then some 1 else none
  | .apply constructor [left, right] =>
      if constructor = costSignatureProductConstructorName then do
        let first ← signatureAnnotation? left
        let second ← signatureAnnotation? right
        pure (first * second)
      else none
  | _ => none
termination_by signature => sizeOf signature
decreasing_by
  all_goals
    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega

theorem literal_signature_annotation {M : Type} [Monoid M] {literal : Pattern}
    (shape : LegacyLiteralSignatureSyntax literal) : signatureAnnotation? (M := M) literal = some 1 := by
  induction shape with
  | unit => simp [signatureAnnotation?]
  | product left right leftIH rightIH => simp [signatureAnnotation?, leftIH, rightIH]

/-- Accepted literals in the original unit/product sublanguage have unit grade. -/
theorem accepted_signature_annotation {M : Type} [Monoid M] {literal : Pattern}
    {signature : TypedSignature literal} (_accepted : signature? literal = some signature)
    (legacy : LegacyLiteralSignatureSyntax literal) :
    signatureAnnotation? (M := M) literal = some 1 :=
  literal_signature_annotation legacy

theorem legacy_canonical_annotation {M : Type} [Monoid M]
    (sourceOrigin : rhoCIGSLT.CanonicalCarrier) :
    signatureAnnotation? (M := M) (LiteralSignatureCommitment.canonical rhoCIGSLT sourceOrigin) =
      some 1 :=
  literal_signature_annotation (AtomicSignatureInterpretation.number_legacy
    (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
      (rhoCIGSLT.canonicalKey sourceOrigin).val.val))

/-- The original unit/product readout does not distinguish its literal authority atoms. -/
theorem distinct_authorities_equal_annotation {M : Type} [Monoid M] :
    ({LiteralSignatureCommitment.canonical rhoCIGSLT Commitments.zeroOrigin} :
      CostSig LiteralAuthority) ≠
      {LiteralSignatureCommitment.canonical rhoCIGSLT Commitments.sendOrigin} ∧
    signatureAnnotation? (M := M) (LiteralSignatureCommitment.canonical rhoCIGSLT
      Commitments.zeroOrigin) = some 1 ∧
    signatureAnnotation? (M := M) (LiteralSignatureCommitment.canonical rhoCIGSLT
      Commitments.sendOrigin) = some 1 := by
  refine ⟨?_, legacy_canonical_annotation Commitments.zeroOrigin,
    legacy_canonical_annotation Commitments.sendOrigin⟩
  intro same
  have sourceEquivalent := (LiteralSignatureCommitment.canonical_eq_iff _ _ _).mp
    (Multiset.singleton_inj.mp same)
  exact Commitments.distinct_origins_distinct_authority.1
    ((Commitments.authority_eq_iff _ _).mpr sourceEquivalent)

def sendUnderInputOrigin : Pattern :=
  .apply costSignedConstructorName
    [.apply (costBaseConstructorName "PInput")
      [.apply (costBaseConstructorName "NQuote") [.apply (costBaseConstructorName "PZero") []],
       .lambda none (.apply costSignedConstructorName
         [.apply (costBaseConstructorName "POutput")
           [.bvar 0, .apply (costWrappedConstructorName "PDrop") [.bvar 0]],
          AtomicSignatureInterpretation.canonical rhoCIGSLT Commitments.zeroOrigin])],
     AtomicSignatureInterpretation.canonical rhoCIGSLT Commitments.zeroOrigin]

def sendUnderInputRuntime : CostTerm LiteralAuthority :=
  .signed (.recv (.quote .nil)
    (.signed (.send (.bvar 0) (.drop (.bvar 0))) (Commitments.authority Commitments.zeroOrigin).val))
    (Commitments.authority Commitments.zeroOrigin).val

/-- A real admitted structural image uses the bound name in both output positions. -/
theorem sendUnderInput_image : CodeImage 0 sendUnderInputOrigin sendUnderInputRuntime :=
  .signed (Commitments.authority Commitments.zeroOrigin) (Commitments.canonical_decoded _)
    (.recv .baseZeroQuote
      (.signed (Commitments.authority Commitments.zeroOrigin) (Commitments.canonical_decoded _)
        (.send (.bvar (by decide +kernel)) (.drop (.bvar (by decide +kernel))))))

theorem sendUnderInput_intrinsic :
    RuntimeSourceReification.code? 0 sendUnderInputRuntime =
      some AccountBindingAlgebra.RhoSourceComparison.input := rfl

/-- The actual parser returns both the exact signed tree and its full scoped source readout. -/
theorem sendUnderInput_readout :
    ∃ fuel result, readout? fuel 0 sendUnderInputOrigin = some result ∧
      result.runtime.val = sendUnderInputRuntime ∧
      result.intrinsic = AccountBindingAlgebra.RhoSourceComparison.input := by
  obtain ⟨fuel, result, found, exactRuntime⟩ := readout_of_image sendUnderInput_image
  refine ⟨fuel, result, found, exactRuntime, ?_⟩
  have read := (readout_found found).2
  rw [exactRuntime, sendUnderInput_intrinsic] at read
  exact (Option.some.inj read).symm

/-- The complete binder-bearing source value is nonzero in the accounted model. -/
theorem sendUnderInput_program_nonzero :
    program AccountBindingAlgebra.RhoSourceComparison.input ≠ program nilP := by
  intro same
  have observed := congrArg (fun value => encodeEquationClass
    (accounted.observed.hom.raw.map value)) same
  simp only [program_observation, encodeEquationClass_mk] at observed
  have separate : canonicalize (encodeTerm AccountBindingAlgebra.RhoSourceComparison.input) ≠
      canonicalize (encodeTerm nilP) := by decide +kernel
  exact separate observed

#print axioms sourceFold
#print axioms program_substitute
#print axioms readout_canonical_observation
#print axioms closedSource
#print axioms readoutAuthority_literal
#print axioms distinct_authorities_equal_annotation
#print axioms sendUnderInput_readout
#print axioms sendUnderInput_program_nonzero

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AccountedGeneratedReadout
