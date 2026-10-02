import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLiteralEncoding

/-!
# Exact raw normal readouts of admitted generated code

Both readouts are normalized by the existing raw runtime normalizer. The
comparison preserves literal authority keys and does not infer a CostStep
from an unnormalized source to a normalized target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem raw_quote_normalize_congr {left right : RawCostTerm}
    (same : left.normalize = right.normalize) :
    (RawCostName.quote left).normalize = (RawCostName.quote right).normalize := by
  simp only [RawCostName.normalize]
  rw [same]

theorem raw_term_par_normalize_congr {left right first second : RawCostTerm}
    (leftSame : left.normalize = first.normalize) (rightSame : right.normalize = second.normalize) :
    (RawCostTerm.par left right).normalize = (RawCostTerm.par first second).normalize := by
  simp only [RawCostTerm.normalize]
  rw [leftSame, rightSame]

theorem raw_proc_par_normalize_congr {left right first second : RawCostProc}
    (leftSame : left.normalize = first.normalize) (rightSame : right.normalize = second.normalize) :
    (RawCostProc.par left right).normalize = (RawCostProc.par first second).normalize := by
  simp only [RawCostProc.normalize]
  rw [leftSame, rightSame]

theorem CodeImage.finish_quote_raw_readout {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : CodeImage 0 source term) (depth : Nat) :
    ∃ name, NameImage depth
      (finishNormalizeReflectiveApply wrappedRhoDeclaration "$cost:wrapped-constructor:NQuote" [source]) name ∧
      (RawCostName.quote (literalEncodeTerm term)).normalize = (literalEncodeName name).normalize := by
  cases image with
  | zero => exact ⟨_, .quote .zero, rfl⟩
  | drop name => exact ⟨_, name.weaken (Nat.zero_le depth), rfl⟩
  | signed signature accepted process => exact ⟨_, .quote (.signed signature accepted process), rfl⟩
  | collection codes => exact ⟨_, .quote (.collection codes), rfl⟩

mutual
  theorem NameImage.normalize_raw_readout {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ normalized, NameImage depth (normalizeReflective wrappedRhoDeclaration source) normalized ∧
        (literalEncodeName name).normalize = (literalEncodeName normalized).normalize := by
    cases image with
    | bvar bound => exact ⟨_, .bvar bound, rfl⟩
    | baseZeroQuote => exact ⟨_, .baseZeroQuote, rfl⟩
    | quote code =>
      obtain ⟨normalized, codeImage, codeSame⟩ := code.normalize_raw_readout
      obtain ⟨name, nameImage, nameSame⟩ := codeImage.finish_quote_raw_readout depth
      refine ⟨name, nameImage, ?_⟩
      exact (raw_quote_normalize_congr codeSame).trans nameSame

  theorem CodeImage.normalize_raw_readout {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      ∃ normalized, CodeImage depth (normalizeReflective wrappedRhoDeclaration source) normalized ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | drop name =>
      obtain ⟨normalized, nameImage, nameSame⟩ := name.normalize_raw_readout
      refine ⟨.drop normalized, .drop nameImage, ?_⟩
      change RawCostTerm.drop (literalEncodeName _).normalize =
        RawCostTerm.drop (literalEncodeName normalized).normalize
      rw [nameSame]
    | signed signature accepted process =>
      obtain ⟨normalized, processImage, processSame⟩ := process.normalize_raw_readout
      change ∃ normalized, CodeImage depth (.apply "$cost:apparatus-constructor:signed"
        [normalizeReflective wrappedRhoDeclaration _, normalizeReflective wrappedRhoDeclaration _]) normalized ∧ _
      rw [signature?_accepted_normalization_identity accepted]
      refine ⟨_, .signed signature accepted processImage, ?_⟩
      change RawCostTerm.signed (literalEncodeProc _).normalize _ =
        RawCostTerm.signed (literalEncodeProc normalized).normalize _
      rw [processSame]
    | collection codes =>
      obtain ⟨normalized, codeImage, codeSame⟩ := codes.normalize_raw_readout
      exact ⟨_, .collection codeImage, codeSame⟩

  theorem ProcImage.normalize_raw_readout {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ normalized, ProcImage depth (normalizeReflective wrappedRhoDeclaration source) normalized ∧
        (literalEncodeProc process).normalize = (literalEncodeProc normalized).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | send name code =>
      obtain ⟨normalizedName, nameImage, nameSame⟩ := name.normalize_raw_readout
      obtain ⟨normalizedCode, codeImage, codeSame⟩ := code.normalize_raw_readout
      refine ⟨_, .send nameImage codeImage, ?_⟩
      change RawCostProc.send (literalEncodeName _).normalize (literalEncodeTerm _).normalize =
        RawCostProc.send (literalEncodeName normalizedName).normalize (literalEncodeTerm normalizedCode).normalize
      rw [nameSame, codeSame]
    | recv name code =>
      obtain ⟨normalizedName, nameImage, nameSame⟩ := name.normalize_raw_readout
      obtain ⟨normalizedCode, codeImage, codeSame⟩ := code.normalize_raw_readout
      refine ⟨_, .recv nameImage codeImage, ?_⟩
      change RawCostProc.recv (literalEncodeName _).normalize (literalEncodeTerm _).normalize =
        RawCostProc.recv (literalEncodeName normalizedName).normalize (literalEncodeTerm normalizedCode).normalize
      rw [nameSame, codeSame]
    | pair left right =>
      obtain ⟨normalizedLeft, leftImage, leftSame⟩ := left.normalize_raw_readout
      obtain ⟨normalizedRight, rightImage, rightSame⟩ := right.normalize_raw_readout
      exact ⟨_, .pair leftImage rightImage, raw_proc_par_normalize_congr leftSame rightSame⟩

  theorem CodeListImage.normalize_raw_readout {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ∃ normalized, CodeListImage depth (normalizeReflectiveList wrappedRhoDeclaration sources) normalized ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
    cases image with
    | nil => exact ⟨_, .nil, rfl⟩
    | cons head tail =>
      obtain ⟨normalizedHead, headImage, headSame⟩ := head.normalize_raw_readout
      obtain ⟨normalizedTail, tailImage, tailSame⟩ := tail.normalize_raw_readout
      exact ⟨_, .cons headImage tailImage, raw_term_par_normalize_congr headSame tailSame⟩
end

theorem code_parser_normalization_raw_readout {fuel depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (parsed : (code? fuel depth source).map Subtype.val = some term) :
    ∃ normalized fuel,
      (code? fuel depth (normalizeReflective wrappedRhoDeclaration source)).map Subtype.val = some normalized ∧
      (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
  obtain ⟨normalized, image, same⟩ := (code_parser_image parsed).normalize_raw_readout
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  exact ⟨normalized, fuel, readback fuel (le_refl fuel), same⟩

mutual
  theorem ConfigImage.normalize_raw_readout {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority} (image : ConfigImage location source term) :
      ∃ normalized, ConfigImage location (normalizeReflective wrappedRhoDeclaration source) normalized ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | drop name =>
      obtain ⟨normalized, codeImage, same⟩ := (CodeImage.drop name).normalize_raw_readout
      exact ⟨normalized, codeImage.toConfigImage location, same⟩
    | signed signature accepted process =>
      obtain ⟨normalized, codeImage, same⟩ :=
        (CodeImage.signed signature accepted process).normalize_raw_readout
      exact ⟨normalized, codeImage.toConfigImage location, same⟩
    | @contact leftSource stackSource code stackValue left stack =>
      obtain ⟨normalized, normalizedImage, same⟩ := left.normalize_raw_readout
      refine ⟨locatedContact location normalized stackValue, ?_, ?_⟩
      · change ConfigImage location (.apply "$cost:apparatus-constructor:contact"
          [normalizeReflective wrappedRhoDeclaration leftSource,
            .apply "$cost:apparatus-constructor:funding"
              [normalizeReflective wrappedRhoDeclaration stackSource]]) _
        rw [stack.normalize_identity]
        exact .contact normalizedImage stack
      · exact raw_term_par_normalize_congr same rfl
    | collection codes =>
      obtain ⟨normalized, codeImage, same⟩ := codes.normalize_raw_readout
      exact ⟨normalized, .collection codeImage, same⟩

  theorem ConfigListImage.normalize_raw_readout {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) :
      ∃ normalized, ConfigListImage location (normalizeReflectiveList wrappedRhoDeclaration sources) normalized ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
    cases image with
    | nil => exact ⟨_, .nil, rfl⟩
    | cons head tail =>
      obtain ⟨normalizedHead, headImage, headSame⟩ := head.normalize_raw_readout
      obtain ⟨normalizedTail, tailImage, tailSame⟩ := tail.normalize_raw_readout
      exact ⟨_, .cons headImage tailImage, raw_term_par_normalize_congr headSame tailSame⟩
end

theorem config_parser_normalization_raw_readout {location : CostName LiteralAuthority}
    {free : location.purseInventory = 0} {supported : location.RuntimeSupported}
    {fuel : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
    (parsed : (config? location free supported fuel source).map Subtype.val = some term) :
    ∃ normalized fuel,
      (config? location free supported fuel (normalizeReflective wrappedRhoDeclaration source)).map
        Subtype.val = some normalized ∧
      (literalEncodeTerm term).normalize = (literalEncodeTerm normalized).normalize := by
  obtain ⟨normalized, image, same⟩ := (config_parser_image parsed).normalize_raw_readout
  obtain ⟨fuel, readback⟩ := image.parser_eventually free supported
  exact ⟨normalized, fuel, readback fuel (le_refl fuel), same⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
