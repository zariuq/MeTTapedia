import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ClosedOriginAccountInterpretation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRHS

/-!
# Full process readout before outer signing

The existing process decoder reads the complete receiver-plus-sender pair
before an outer signature is supplied. Its full intrinsic binding value
constructs an admitted closed source origin. The canonical commitment is
therefore computed from the authored erased pair, with no auxiliary signature
inserted to make the code decoder accept it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PreSigningProcessReadout

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open RuntimeSourceReification

structure Readout (depth : Nat) (source : Pattern) where
  runtime : DecodedProc depth source
  intrinsic : Term sig (nameContext depth) Srt.pr

def readout? (fuel depth : Nat) (source : Pattern) : Option (Readout depth source) :=
  match ActivationGenerated.proc? fuel depth source with
  | none => none
  | some runtime => (RuntimeSourceReification.process? depth runtime.val).map
      (fun intrinsic => ⟨runtime, intrinsic⟩)

theorem readout_found {fuel depth : Nat} {source : Pattern}
    {result : Readout depth source} (found : readout? fuel depth source = some result) :
    ActivationGenerated.proc? fuel depth source = some result.runtime ∧
      RuntimeSourceReification.process? depth result.runtime.val = some result.intrinsic := by
  unfold readout? at found
  cases parsed : ActivationGenerated.proc? fuel depth source with
  | none => simp [parsed] at found
  | some runtime =>
    simp only [parsed] at found
    obtain ⟨intrinsic, intrinsicFound, equal⟩ := Option.map_eq_some_iff.mp found
    cases equal
    exact ⟨rfl, intrinsicFound⟩

/-- Structural images construct a successful readout through both real functions. -/
theorem readout_of_image {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
    (image : ProcImage depth source process) :
    ∃ fuel result, readout? fuel depth source = some result ∧ result.runtime.val = process := by
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  obtain ⟨decoded, parsed, exactRuntime⟩ :=
    Option.map_eq_some_iff.mp (readback fuel (le_refl fuel))
  obtain ⟨intrinsic, reified, _⟩ := process_image_readout image
  refine ⟨fuel, ⟨decoded, intrinsic⟩, ?_, exactRuntime⟩
  simp [readout?, parsed, exactRuntime, reified]

theorem readout_quoteSafe {fuel depth : Nat} {source : Pattern} {result : Readout depth source}
    (image : ProcImage depth source result.runtime.val)
    (found : readout? fuel depth source = some result) :
    intrinsicQuoteSafe depth result.intrinsic = true := by
  obtain ⟨term, reified, safe, _⟩ := process_image_readout image
  have equal := Option.some.inj (reified.symm.trans (readout_found found).2)
  exact equal ▸ safe

/-- Whole source observation, including both components and the input binder. -/
theorem readout_canonical {fuel depth : Nat} {source : Pattern} {result : Readout depth source}
    (image : ProcImage depth source result.runtime.val)
    (found : readout? fuel depth source = some result) :
    canonicalize (encodeTerm result.intrinsic) = canonicalize (eraseGenerated source) := by
  obtain ⟨term, reified, _, agreement⟩ := process_image_readout image
  have equal := Option.some.inj (reified.symm.trans (readout_found found).2)
  subst term
  have congruence := StructuralCongruence.trans _ _ _
    (agreement (fun _ => .apply "PZero" []))
    (image.erase_structural (fun _ => .apply "PZero" []))
  exact canonicalize_eq_of_structuralCongruence congruence (encodedTerm_hashSetFree _)
    ((hashSetFree_iff_of_structuralCongruence congruence).mp (encodedTerm_hashSetFree _))

def origin {fuel : Nat} {source : Pattern} {result : Readout 0 source}
    (image : ProcImage 0 source result.runtime.val)
    (found : readout? fuel 0 source = some result) : ClosedOriginAccountInterpretation.Origin :=
  ⟨result.intrinsic, readout_quoteSafe image found⟩

theorem origin_source_key {fuel : Nat} {source : Pattern} {result : Readout 0 source}
    (image : ProcImage 0 source result.runtime.val)
    (found : readout? fuel 0 source = some result) :
    (rhoCIGSLT.canonicalKey (ClosedOriginAccountInterpretation.admitted (origin image found))).val.val =
      canonicalize (eraseGenerated source) := by
  rw [ClosedOriginAccountInterpretation.admitted, origin, AccountedGeneratedReadout.closedSource_key]
  exact readout_canonical image found

theorem origin_signature {fuel : Nat} {source : Pattern} {result : Readout 0 source}
    (image : ProcImage 0 source result.runtime.val)
    (found : readout? fuel 0 source = some result) :
    AtomicSignatureInterpretation.canonical rhoCIGSLT
      (ClosedOriginAccountInterpretation.admitted (origin image found)) =
        AtomicSignatureInterpretation.commitLiteral (canonicalize (eraseGenerated source)) := by
  rw [AtomicSignatureInterpretation.canonical, origin_source_key image found]

def receiverPair (body payload : Pattern) : Pattern :=
  .collection .hashBag
    [.apply (costBaseConstructorName "PInput") [nilChannelSource, .lambda none body],
     .apply (costBaseConstructorName "POutput") [nilChannelSource, payload]] none

def receiverPairRuntime (body payload : CostTerm LiteralAuthority) : CostProc LiteralAuthority :=
  .par (.recv nilChannelLocation body) (.send nilChannelLocation payload)

theorem receiverPair_image {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ProcImage 0 (receiverPair bodySource payloadSource) (receiverPairRuntime body payload) :=
  .pair (.recv .baseZeroQuote bodyImage) (.send .baseZeroQuote payloadImage)

theorem receiverPair_readout {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ fuel result, readout? fuel 0 (receiverPair bodySource payloadSource) = some result ∧
      result.runtime.val = receiverPairRuntime body payload :=
  readout_of_image (receiverPair_image bodyImage payloadImage)

theorem purse_not_process (fuel : Nat) (stack : Pattern) :
    readout? fuel 0 (.apply costFundingConstructorName [stack]) = none := by
  cases fuel <;> rfl

#print axioms receiverPair_readout
#print axioms readout_canonical
#print axioms origin_signature

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PreSigningProcessReadout
