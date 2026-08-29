import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

/-!
# The native presentation reflects the *regular* Pure judgment on its image

`IntrinsicPureRefinement.typingAt_embed_iff` states exactness of the native
presentation against the raw `IntrinsicPure.HasType`.  The judgment actually
implemented by the CeTTa Prime regular kernel is the strengthened
`RegularHasType` of `PresentationBoundary`, whose rules carry the
well-formedness derivations that the raw judgment omits.

This module records the direction that is already provable: every regular
derivation embeds into a native typing derivation on the Pure image.  The
converse — that a native derivation over embedded terms yields a *regular*
Pure derivation — is exactly the open question of whether `HasType` implies
`RegularHasType` for regular contexts.  It is not stated here as a theorem
because it is not proved; it is the obligation `Q-TT-004` of the research
spec, and this file is where its proof belongs when it exists.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.RegularPureImage

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.StagedReflective.IntrinsicPureRefinement

/-- A regular Pure derivation yields a native typing derivation of the
embedded term at the embedded type, at every stage. -/
theorem typingAt_embed_of_regular {binders : Nat} (stage : Nat)
    {context : Ctx binders} {term type : PureTm binders}
    (regular : RegularHasType context term type) :
    Nonempty (TypingAt stage context (embedPure stage term)
      (embedPure stage type)) :=
  (typingAt_embed_iff stage context term type).mpr regular.toHasType

/-- Restated as an inclusion of judgments on the Pure image: the regular
fragment the C kernel decides is contained in what the native presentation
accepts. -/
theorem regular_le_native {binders : Nat} (stage : Nat)
    (context : Ctx binders) (term type : PureTm binders) :
    RegularHasType context term type →
      Nonempty (TypingAt stage context (embedPure stage term)
        (embedPure stage type)) :=
  typingAt_embed_of_regular stage

/-- The one missing premise for exactness of the production Regular judgment
on the native Pure image.  Naming it separately prevents exactness from being
silently inferred from the weaker raw judgment. -/
def RawRegularization : Prop :=
  ∀ {binders : Nat} {context : Ctx binders}
    {term type : PureTm binders},
    HasType context term type → RegularHasType context term type

/-- Exact reflection of the strengthened Regular judgment by the native
presentation, uniformly in quotation stage. -/
def NativeRegularExactness : Prop :=
  ∀ {binders : Nat} (stage : Nat) (context : Ctx binders)
    (term type : PureTm binders),
    Nonempty (TypingAt stage context (embedPure stage term)
      (embedPure stage type)) ↔ RegularHasType context term type

/-- Native/Regular exactness is neither assumed nor vaguely deferred: it is
equivalent to the precise raw-to-Regular strengthening that remains to be
proved for the intrinsic Pure presentation. -/
theorem nativeRegularExactness_iff_rawRegularization :
    NativeRegularExactness ↔ RawRegularization := by
  constructor
  · intro exactness binders context term type raw
    exact (exactness 0 context term type).mp
      ((typingAt_embed_iff 0 context term type).mpr raw)
  · intro regularize binders stage context term type
    constructor
    · intro native
      exact regularize ((typingAt_embed_iff stage context term type).mp native)
    · intro regular
      exact (typingAt_embed_iff stage context term type).mpr regular.toHasType

/-- Intrinsic Pure is a strict syntactic fragment of the current Native
presentation: runtime Patterns provide a machine-checked failure of
surjectivity, rather than a naming-based claim. -/
theorem embedPure_not_surjective :
    ¬ Function.Surjective
      (embedPure 0 : PureTm 0 → StagedReflectiveTm 0 0) := by
  intro surjective
  obtain ⟨pure, equality⟩ := surjective nativeRuntimePattern
  exact nativeRuntimePattern_not_in_pure_image ⟨pure, equality⟩

/-! ## The exactness question closes negatively

Raw typing has no domain-formation premise in `lam_intro`, so it accepts the
identity function at a Π whose domain is the untyped top sort.  The regular
judgment cannot type that term at that type by any rule, conversion
included.  Hence the raw-to-regular strengthening fails, and with it the
exactness of the native image typing against the judgment the CeTTa Prime
regular kernel implements.  The repair belongs on the native side: the image
typing must be stated against `RegularHasType` (or carry context and domain
formation), not by weakening the kernel. -/

/-- The raw judgment accepts `λx. x : Π(u1). u1`. -/
theorem raw_types_identity_at_top_domain :
    HasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) := by
  have body : HasType (.snoc (.nil : Ctx 0) .u1) (.var 0) .u1 := by
    simpa [rawTopSortContext] using raw_types_variable_in_top_sort_context
  exact HasType.lam_intro body

/-- The regular judgment rejects it: structural introduction needs `u1 : u1`,
and conversion into `Π(u1). u1` needs that Π to be a formed type. -/
theorem no_regular_identity_at_top_domain :
    ¬ RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) := by
  intro regular
  cases regular with
  | lam_intro hDomain _ _ => exact no_regular_u1_term hDomain
  | conv_type _ hTarget _ => exact hTarget.subject_ne_pi_u1_domain rfl

/-- Raw typing does not regularize. -/
theorem rawRegularization_false : ¬ RawRegularization := by
  intro regularize
  exact no_regular_identity_at_top_domain (regularize raw_types_identity_at_top_domain)

/-- Therefore the native image typing is **not** exact against the regular
judgment: it accepts an embedded term the production kernel rejects. -/
theorem nativeRegularExactness_false : ¬ NativeRegularExactness := by
  intro exactness
  exact rawRegularization_false (nativeRegularExactness_iff_rawRegularization.mp exactness)

/-- The concrete gap, stated on the native side: the embedded identity is
`TypingAt`-typable at the embedded top-domain Π although no regular
derivation exists. -/
theorem native_image_accepts_what_regular_rejects :
    Nonempty (TypingAt 0 (.nil : Ctx 0)
        (embedPure 0 (.lam (.var 0))) (embedPure 0 (.pi .u1 .u1))) ∧
      ¬ RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) :=
  ⟨(typingAt_embed_iff 0 _ _ _).mpr raw_types_identity_at_top_domain,
    no_regular_identity_at_top_domain⟩

#print axioms rawRegularization_false
#print axioms nativeRegularExactness_false
#print axioms native_image_accepts_what_regular_rejects

#print axioms typingAt_embed_of_regular
#print axioms regular_le_native
#print axioms nativeRegularExactness_iff_rawRegularization
#print axioms embedPure_not_surjective

end Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.RegularPureImage
