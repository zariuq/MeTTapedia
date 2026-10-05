import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationClosure

/-!
# Token stacks are fixed by the generated normalizer

A stack image keeps every literal authority key and its position under the generated
normalizer. A product signature is one key; it is not several stored authority atoms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem stack_parser_image {fuel : Nat} {source : Pattern} {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) : StackImage source stack :=
  readStack_image ((stack?_val fuel source).symm.trans parsed)

theorem StackImage.parser_eventually {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (stack? fuel source).map Subtype.val = some stack := by
  simpa only [stack?_val] using image.read_eventually

theorem StackImage.normalize_identity {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    normalizeReflective wrappedRhoDeclaration source = source := by
  induction image with
  | empty => rfl
  | cons signature accepted rest ih =>
    simp only [normalizeReflective, normalizeReflectiveList]
    rw [signature?_accepted_normalization_identity accepted, ih]
    rfl

theorem stack?_accepted_normalization_identity {fuel : Nat} {source : Pattern}
    {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) :
    normalizeReflective wrappedRhoDeclaration source = source :=
  (stack_parser_image parsed).normalize_identity

theorem stack_parser_normalization_same {fuel : Nat} {source : Pattern}
    {stack : CostStack LiteralAuthority}
    (parsed : (stack? fuel source).map Subtype.val = some stack) :
    (stack? fuel (normalizeReflective wrappedRhoDeclaration source)).map Subtype.val =
      some stack := by
  rw [stack?_accepted_normalization_identity parsed]
  exact parsed

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
