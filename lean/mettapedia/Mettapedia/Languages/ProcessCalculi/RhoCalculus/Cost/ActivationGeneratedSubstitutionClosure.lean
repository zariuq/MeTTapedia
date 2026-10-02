import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSubstitution

/-!
# Substitution closure of the actual generated parser image

Closed received code is substituted through arbitrary admitted receiver code.
The actual provenance-sensitive operation is used, with its selected wrapped
declaration. The result has an actual parser readback at the eliminated scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem NameImage.quote_closed_image {scope : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage scope source (.quote term)) :
    NameImage 0 source (.quote term) := by
  cases image with
  | baseZeroQuote => exact .baseZeroQuote
  | quote code => exact .quote code

theorem NameImage.literal_substitute_image {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote term))
    (replacement : Pattern) :
    ∃ normalized, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth replacement source) normalized := by
  obtain ⟨normalized, normalizedImage⟩ := image.quote_closed_image.normalize_image
  rw [image.substituteReflective_eq_mark,
    substituteNameMark_closed depth replacement image.quote_source_closed]
  exact ⟨_, normalizedImage.weaken (Nat.zero_le depth)⟩

theorem substituteReflective_drop_closed (depth : Nat) (replacement : Pattern) {source : Pattern}
    (closed : source.isWellScopedAt 0 = true) :
    substituteReflective wrappedRhoDeclaration depth replacement
      (.apply "$cost:wrapped-constructor:PDrop" [source]) =
      .apply "$cost:wrapped-constructor:PDrop" [normalizeReflective wrappedRhoDeclaration source] := by
  change (let (name, matched) := substituteNameMark wrappedRhoDeclaration depth replacement source;
    match name, matched with
    | .apply quote [process], true =>
      if quote == wrappedRhoDeclaration.quoteConstructor then process
      else .apply "$cost:wrapped-constructor:PDrop" [name]
    | _, _ => .apply "$cost:wrapped-constructor:PDrop" [name]) = _
  rw [substituteNameMark_closed depth replacement closed]
  generalize normalizeReflective wrappedRhoDeclaration source = normalized
  cases normalized <;> try rfl
  case apply constructor arguments =>
    cases arguments with
    | nil => rfl
    | cons argument arguments => cases arguments <;> rfl

theorem NameImage.substitute_image {depth : Nat} {source payloadSource : Pattern}
    {name : CostName LiteralAuthority} {payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source name) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ result, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth
    · subst index
      obtain ⟨normalized, normalizedImage⟩ := payloadImage.normalize_image
      simp only [substituteReflective, beq_self_eq_true, ite_true, generatedReplacement]
      exact ⟨_, .quote normalizedImage⟩
    · simp only [substituteReflective, beq_iff_eq, matched, ite_false]
      exact ⟨_, .bvar (by omega)⟩
  | baseZeroQuote => exact NameImage.literal_substitute_image .baseZeroQuote _
  | quote code => exact NameImage.literal_substitute_image (.quote code) _

private theorem drop_literal_substitute_image {depth : Nat} {source payloadSource : Pattern}
    {quoted : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote quoted)) :
    ∃ result, CodeImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource)
        (.apply "$cost:wrapped-constructor:PDrop" [source])) result := by
  rw [substituteReflective_drop_closed depth _ image.quote_source_closed]
  obtain ⟨normalized, normalizedImage⟩ := image.quote_closed_image.normalize_image
  exact ⟨_, .drop (normalizedImage.weaken (Nat.zero_le depth))⟩

mutual
  theorem CodeImage.substitute_image {depth : Nat} {source payloadSource : Pattern}
      {term payload : CostTerm LiteralAuthority} (image : CodeImage (depth + 1) source term)
      (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | drop name =>
      cases name with
      | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          obtain ⟨normalized, normalizedImage⟩ := payloadImage.normalize_image
          simp only [substituteReflective, substituteNameMark, normalizeReflective,
            generatedReplacement, beq_self_eq_true, ite_true]
          exact ⟨_, normalizedImage.weaken (Nat.zero_le depth)⟩
        · simp only [substituteReflective, substituteNameMark, normalizeReflective,
            beq_iff_eq, matched, ite_false]
          exact ⟨_, .drop (.bvar (by omega))⟩
      | baseZeroQuote => exact drop_literal_substitute_image .baseZeroQuote
      | quote code => exact drop_literal_substitute_image (.quote code)
    | signed signature accepted process =>
      obtain ⟨result, resultImage⟩ := process.substitute_image payloadImage
      change ∃ result, CodeImage depth
        (.apply "$cost:apparatus-constructor:signed"
          [substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _,
           substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _]) result
      rw [signature?_accepted_substitution_identity accepted]
      exact ⟨_, .signed signature accepted resultImage⟩
    | collection codes =>
      obtain ⟨result, resultImage⟩ := codes.substitute_image payloadImage
      exact ⟨_, .collection resultImage⟩

  theorem ProcImage.substitute_image {depth : Nat} {source payloadSource : Pattern}
      {process : CostProc LiteralAuthority} {payload : CostTerm LiteralAuthority}
      (image : ProcImage (depth + 1) source process) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, ProcImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | send name code =>
      obtain ⟨resultName, nameImage⟩ := name.substitute_image payloadImage
      obtain ⟨resultCode, codeImage⟩ := code.substitute_image payloadImage
      exact ⟨_, .send nameImage codeImage⟩
    | recv name code =>
      obtain ⟨resultName, nameImage⟩ := name.substitute_image payloadImage
      obtain ⟨resultCode, codeImage⟩ := code.substitute_image payloadImage
      exact ⟨_, .recv nameImage codeImage⟩
    | pair left right =>
      obtain ⟨resultLeft, leftImage⟩ := left.substitute_image payloadImage
      obtain ⟨resultRight, rightImage⟩ := right.substitute_image payloadImage
      exact ⟨_, .pair leftImage rightImage⟩

  theorem CodeListImage.substitute_image {depth : Nat} {sources : List Pattern}
      {payloadSource : Pattern} {term payload : CostTerm LiteralAuthority}
      (image : CodeListImage (depth + 1) sources term) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeListImage depth
        (substituteReflectiveList wrappedRhoDeclaration depth (generatedReplacement payloadSource) sources) result := by
    cases image with
    | nil => exact ⟨_, .nil⟩
    | cons head tail =>
      obtain ⟨resultHead, headImage⟩ := head.substitute_image payloadImage
      obtain ⟨resultTail, tailImage⟩ := tail.substitute_image payloadImage
      exact ⟨_, .cons headImage tailImage⟩
end

theorem code_parser_substitution_closed {bodyFuel payloadFuel depth : Nat}
    {bodySource payloadSource : Pattern} {body payload : CostTerm LiteralAuthority}
    (bodyParsed : (code? bodyFuel (depth + 1) bodySource).map Subtype.val = some body)
    (payloadParsed : (code? payloadFuel 0 payloadSource).map Subtype.val = some payload) :
    ∃ result fuel, (code? fuel depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) bodySource)).map
      Subtype.val = some result := by
  obtain ⟨result, image⟩ := (code_parser_image bodyParsed).substitute_image (code_parser_image payloadParsed)
  obtain ⟨fuel, parsed⟩ := code_parser_iff_image.mpr image
  exact ⟨result, fuel, parsed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
