import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReadout
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-!
# Success of the readout is the image; images are well scoped

The image is defined in `ActivationGenerated`. Here are the statements of the first half of
"success of the readout is the image" in terms of the readout with guarantees attached, and the
scope of the generated syntax of an image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

theorem name_parser_image {fuel depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority}
    (parsed : (name? fuel depth source).map Subtype.val = some name) :
    NameImage depth source name :=
  readName_image ((name?_val fuel depth source).symm.trans parsed)

theorem code_parser_image {fuel depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority}
    (parsed : (code? fuel depth source).map Subtype.val = some term) :
    CodeImage depth source term :=
  readCode_image ((code?_val fuel depth source).symm.trans parsed)

theorem GeneratedCodeImage.structural_image {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    CodeImage depth source term :=
  generatedCodeImage_iff_image.mp image

mutual
  theorem NameImage.scoped {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (image : NameImage depth source name) : source.isWellScopedAt depth = true := by
    cases image with
    | bvar bound => simpa [Pattern.isWellScopedAt] using bound
    | baseZeroQuote => rfl
    | quote code =>
      simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using
        isWellScopedAt_mono code.scoped (Nat.zero_le depth)

  theorem CodeImage.scoped {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage depth source term) : source.isWellScopedAt depth = true := by
    cases image with
    | zero => rfl
    | drop name => simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using name.scoped
    | @signed depth core source processTerm signature _ process =>
      have signatureSafe : source.isWellScopedAt depth = true :=
        isWellScopedAt_mono signature.property.2.isWellScopedAt (Nat.zero_le depth)
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, process.scoped, signatureSafe]
    | collection codes => exact codes.scoped

  theorem ProcImage.scoped {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
      (image : ProcImage depth source process) : source.isWellScopedAt depth = true := by
    cases image with
    | zero => rfl
    | send name code =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, name.scoped, code.scoped]
    | recv name code =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, name.scoped, code.scoped]
    | pair left right =>
      simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, left.scoped, right.scoped]

  theorem CodeListImage.scoped {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      Pattern.isWellScopedListAt depth sources = true := by
    cases image with
    | nil => rfl
    | cons head tail => simp [Pattern.isWellScopedListAt, head.scoped, tail.scoped]
end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
