import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImageReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureStability

/-!
# Normalization closure of the actual generated parser image

The wrapped quote/drop operation stays inside the existing parser domain.
Normalized code is read back by the actual parser. The result need not be the
literal original cost term; no operational step is inferred from normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  theorem NameImage.weaken {scope depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage scope source name) (larger : scope ≤ depth) :
      NameImage depth source name := by
    cases image with
    | bvar bound => exact .bvar (Nat.lt_of_lt_of_le bound larger)
    | baseZeroQuote => exact .baseZeroQuote
    | quote code => exact .quote code

  theorem CodeImage.weaken {scope depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage scope source term) (larger : scope ≤ depth) :
      CodeImage depth source term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop (name.weaken larger)
    | signed signature accepted process => exact .signed signature accepted (process.weaken larger)
    | collection codes => exact .collection (codes.weaken larger)

  theorem ProcImage.weaken {scope depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage scope source process) (larger : scope ≤ depth) :
      ProcImage depth source process := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send (name.weaken larger) (code.weaken larger)
    | recv name code => exact .recv (name.weaken larger) (code.weaken (Nat.add_le_add_right larger 1))
    | pair left right => exact .pair (left.weaken larger) (right.weaken larger)

  theorem CodeListImage.weaken {scope depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage scope sources term) (larger : scope ≤ depth) :
      CodeListImage depth sources term := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .cons (head.weaken larger) (tail.weaken larger)
end

theorem CodeImage.finish_quote_image {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : CodeImage 0 source term) (depth : Nat) :
    ∃ name, NameImage depth
      (finishNormalizeReflectiveApply wrappedRhoDeclaration "$cost:wrapped-constructor:NQuote" [source]) name := by
  cases image with
  | zero => exact ⟨.quote .nil, .quote .zero⟩
  | drop name => exact ⟨_, name.weaken (Nat.zero_le depth)⟩
  | signed signature accepted process => exact ⟨_, .quote (.signed signature accepted process)⟩
  | collection codes => exact ⟨_, .quote (.collection codes)⟩

mutual
  theorem NameImage.normalize_image {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ normalized, NameImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | bvar bound => exact ⟨_, .bvar bound⟩
    | baseZeroQuote => exact ⟨_, .baseZeroQuote⟩
    | quote code =>
      obtain ⟨normalized, normalizedImage⟩ := code.normalize_image
      exact normalizedImage.finish_quote_image depth

  theorem CodeImage.normalize_image {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      ∃ normalized, CodeImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | drop name =>
      obtain ⟨normalized, normalizedImage⟩ := name.normalize_image
      exact ⟨.drop normalized, .drop normalizedImage⟩
    | signed signature accepted process =>
      obtain ⟨normalized, normalizedImage⟩ := process.normalize_image
      change ∃ normalized, CodeImage depth
        (.apply "$cost:apparatus-constructor:signed"
          [normalizeReflective wrappedRhoDeclaration _, normalizeReflective wrappedRhoDeclaration _]) normalized
      rw [signature?_accepted_normalization_identity accepted]
      exact ⟨_, .signed signature accepted normalizedImage⟩
    | collection codes =>
      obtain ⟨normalized, normalizedImage⟩ := codes.normalize_image
      exact ⟨_, .collection normalizedImage⟩

  theorem ProcImage.normalize_image {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ normalized, ProcImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | send name code =>
      obtain ⟨normalizedName, nameImage⟩ := name.normalize_image
      obtain ⟨normalizedCode, codeImage⟩ := code.normalize_image
      exact ⟨_, .send nameImage codeImage⟩
    | recv name code =>
      obtain ⟨normalizedName, nameImage⟩ := name.normalize_image
      obtain ⟨normalizedCode, codeImage⟩ := code.normalize_image
      exact ⟨_, .recv nameImage codeImage⟩
    | pair left right =>
      obtain ⟨normalizedLeft, leftImage⟩ := left.normalize_image
      obtain ⟨normalizedRight, rightImage⟩ := right.normalize_image
      exact ⟨_, .pair leftImage rightImage⟩

  theorem CodeListImage.normalize_image {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ∃ normalized, CodeListImage depth (normalizeReflectiveList wrappedRhoDeclaration sources) normalized := by
    cases image with
    | nil => exact ⟨_, .nil⟩
    | cons head tail =>
      obtain ⟨normalizedHead, headImage⟩ := head.normalize_image
      obtain ⟨normalizedTail, tailImage⟩ := tail.normalize_image
      exact ⟨_, .cons headImage tailImage⟩
end

theorem name_parser_normalization_closed {fuel depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (parsed : (name? fuel depth source).map Subtype.val = some name) :
    ∃ normalized fuel, (name? fuel depth (normalizeReflective wrappedRhoDeclaration source)).map
      Subtype.val = some normalized := by
  obtain ⟨normalized, image⟩ := (name_parser_image parsed).normalize_image
  obtain ⟨fuel, parsed⟩ := name_parser_iff_image.mpr image
  exact ⟨normalized, fuel, parsed⟩

theorem code_parser_normalization_closed {fuel depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (parsed : (code? fuel depth source).map Subtype.val = some term) :
    ∃ normalized fuel, (code? fuel depth (normalizeReflective wrappedRhoDeclaration source)).map
      Subtype.val = some normalized := by
  obtain ⟨normalized, image⟩ := (code_parser_image parsed).normalize_image
  obtain ⟨fuel, parsed⟩ := code_parser_iff_image.mpr image
  exact ⟨normalized, fuel, parsed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
