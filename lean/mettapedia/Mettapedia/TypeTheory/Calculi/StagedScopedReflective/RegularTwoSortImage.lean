import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PermissiveComparison

/-!
# Regular two-sort inclusion and the strictness of raw native image typing

`TwoSortPiSigmaIdRefinement.typingAt_embed_iff` states exactness of the native
presentation against the raw `TwoSortPiSigmaId.HasType`.  The judgment actually
used by the verified regular checker is the strengthened `RegularHasType`
of the regular calculus, whose rules carry the
well-formedness derivations that the raw judgment omits.

Every regular derivation embeds into a native typing derivation on the two-sort
image. The converse is false: the concrete top-domain identity below is
accepted by raw native image typing and rejected by the regular judgment,
even in the empty context. `nativeRegularExactness_false` establishes this
boundary. The separate regular syntactic CwF and its presheaf representation
use regular judgments directly; they do not repair or identify this older
native image judgment. CeTTa implementation correspondence is separate.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.TypeTheory.Calculi.StagedScopedReflective.RegularTwoSortImage

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular
open Mettapedia.TypeTheory.Calculi.StagedScopedReflective.TwoSortPiSigmaIdRefinement

/-- A regular two-sort derivation yields a native typing derivation of the
embedded term at the embedded type, at every stage. -/
theorem typingAt_embed_of_regular {binders : Nat} (stage : Nat)
    {context : Ctx binders} {term type : ScopedTerm binders}
    (regular : RegularHasType context term type) :
    Nonempty (TypingAt stage context (embedTwoSort stage term)
      (embedTwoSort stage type)) :=
  (typingAt_embed_iff stage context term type).mpr regular.toHasType

/-- Restated as an inclusion of judgments on the two-sort image: the regular
judgment is contained in what the native presentation
accepts. -/
theorem regular_le_native {binders : Nat} (stage : Nat)
    (context : Ctx binders) (term type : ScopedTerm binders) :
    RegularHasType context term type →
      Nonempty (TypingAt stage context (embedTwoSort stage term)
        (embedTwoSort stage type)) :=
  typingAt_embed_of_regular stage

/-- The raw-to-regular strengthening that native image exactness would
require. It is refuted below, not assumed as a pending proof obligation. -/
def RawRegularization : Prop :=
  ∀ {binders : Nat} {context : Ctx binders}
    {term type : ScopedTerm binders},
    HasType context term type → RegularHasType context term type

/-- Exact reflection of the strengthened Regular judgment by the native
presentation, uniformly in quotation stage. -/
def NativeRegularExactness : Prop :=
  ∀ {binders : Nat} (stage : Nat) (context : Ctx binders)
    (term type : ScopedTerm binders),
    Nonempty (TypingAt stage context (embedTwoSort stage term)
      (embedTwoSort stage type)) ↔ RegularHasType context term type

/-- Native/regular exactness is equivalent to raw regularization. The
counterexample below refutes both sides. -/
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

/-- The intrinsic two-sort calculus is a strict syntactic fragment of the current Native
presentation: runtime Patterns provide a machine-checked failure of
surjectivity, rather than a naming-based claim. -/
theorem embedTwoSort_not_surjective :
    ¬ Function.Surjective
      (embedTwoSort 0 : ScopedTerm 0 → StagedReflectiveTm 0 0) := by
  intro surjective
  obtain ⟨pure, equality⟩ := surjective nativeRuntimePattern
  exact nativeRuntimePattern_not_in_twoSort_image ⟨pure, equality⟩

/-! ## The exactness question closes negatively

Raw typing has no domain-formation premise in `lam_intro`, so it accepts the
identity function at a Π whose domain is the untyped top sort.  The regular
judgment cannot type that term at that type by any rule, conversion
included.  Hence the raw-to-regular strengthening fails, and with it the
exactness of native image typing against the verified regular judgment.
The repair belongs on the native side: the image
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

/-- Therefore native image typing is not exact against the regular
judgment: it accepts an embedded term the regular calculus rejects. -/
theorem nativeRegularExactness_false : ¬ NativeRegularExactness := by
  intro exactness
  exact rawRegularization_false (nativeRegularExactness_iff_rawRegularization.mp exactness)

/-- The concrete gap, stated on the native side: the embedded identity is
`TypingAt`-typable at the embedded top-domain Π although no regular
derivation exists. -/
theorem native_image_accepts_what_regular_rejects :
    Nonempty (TypingAt 0 (.nil : Ctx 0)
        (embedTwoSort 0 (.lam (.var 0))) (embedTwoSort 0 (.pi .u1 .u1))) ∧
      ¬ RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) :=
  ⟨(typingAt_embed_iff 0 _ _ _).mpr raw_types_identity_at_top_domain,
    no_regular_identity_at_top_domain⟩

#print axioms rawRegularization_false
#print axioms nativeRegularExactness_false
#print axioms native_image_accepts_what_regular_rejects

#print axioms typingAt_embed_of_regular
#print axioms regular_le_native
#print axioms nativeRegularExactness_iff_rawRegularization
#print axioms embedTwoSort_not_surjective

end Mettapedia.TypeTheory.Calculi.StagedScopedReflective.RegularTwoSortImage
