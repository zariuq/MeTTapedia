import Mettapedia.GSLT.LanguageDef.QuoteBoundaryDivergence
import Mettapedia.GSLT.LanguageDef.ContinuationRetyping
import Mettapedia.GSLT.LanguageDef.TwoDepthRestorationApex

/-!
# The two Cost colours name genuinely different constructors

`QuoteBoundaryDivergence` proves that a profile carrying two presentations
with **distinct** quote constructors has two irreconcilable depth
disciplines.  That result is conditional on the distinctness, so this
module discharges the condition for the Cost construction itself: the base
and wrapped colours tag their constructors differently, hence a quote
carries a different name in each colour.

Consequence: the divergence is not a hypothetical about some exotic
profile.  Any Cost-generated language with both colours in scope has a
foreign quote available.

That does **not** make the one-index apex unsatisfiable there — it is
inhabited at every depth, and its foreign-quote application case is proved
(`CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`).  What it
does establish is that `QuoteStatusAgrees` fails over Cost, so any result
premised on that global agreement is vacuous here; and that a second index is
genuinely required at the one constructor where the apex's index also serves
as a canonicalization depth, namely bare `parallel`.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

/-- The two colour tags are different strings. -/
theorem costConstructorTag_distinct :
    costBaseConstructorTag ≠ costWrappedConstructorTag := by
  decide

/-- The tags have different lengths, which is what separates the two
colour-mapped spellings of one authored constructor. -/
theorem costConstructorTag_length_distinct :
    costBaseConstructorTag.length ≠ costWrappedConstructorTag.length := by
  decide

/-- Hence the same authored constructor takes different names in the two
colours.  Applied to a quote constructor, this supplies the `foreign`
hypothesis of `restorationDepth_ne_keyDepth_at_foreignQuote` and of
`not_quoteStatusAgrees_of_foreignQuote`. -/
theorem costConstructorName_distinct (name : String) :
    costBaseConstructorName name ≠ costWrappedConstructorName name := by
  intro equal
  have lengths := congrArg String.length equal
  simp only [costBaseConstructorName, costWrappedConstructorName,
    String.length_append] at lengths
  exact costConstructorTag_length_distinct (by omega)

/-! ## The agreement hypothesis is unsatisfiable in every Cost language

`QuoteStatusAgrees` is the hypothesis under which the one-index apex embeds
into the separated carrier.  The theorem below shows it is **false for every
Cost-generated language carrying an authored reflective presentation, at both
colours** — because the *other* colour's image of that same presentation is
always present in the profile and always spells its quote differently.

The consequence is operational, not decorative: any result stated with
`QuoteStatusAgrees` as a hypothesis is vacuous over Cost languages, so it
cannot be used to migrate evidence.  Terminals must be established directly
over `TwoDepthApex`. -/

/-- Membership of a colour image in the generated profile, in the form the
refutation below consumes.  The underlying fact is
`costStaticReflectivePresentationDecl_mem` (`CostCanonicalSection`); this only
rephrases its conclusion through `costWholeReflectionProfile_presentations`. -/
theorem costStaticReflectivePresentationDecl_mem_profile {source : CIGSLT}
    (color : CostStaticColor) {declaration : ReflectivePresentationDecl}
    (mem : declaration ∈ source.reflection.1.presentations) :
    costStaticReflectivePresentationDecl source color declaration ∈
      source.costWholeReflectionProfile.presentations := by
  simpa only [CIGSLT.costWholeReflectionProfile_presentations] using
    costStaticReflectivePresentationDecl_mem source color declaration mem

/-- **The agreement hypothesis is refuted over Cost, at both colours.**
Whichever colour is being canonicalized under, the opposite colour's image of
the same authored presentation supplies a quote that the profile recognizes
and the declaration does not. -/
theorem not_quoteStatusAgrees_costStatic {source : CIGSLT}
    (color : CostStaticColor) {declaration : ReflectivePresentationDecl}
    (mem : declaration ∈ source.reflection.1.presentations) :
    ¬ CostStaticAtomKeyCospan.QuoteStatusAgrees source
        (costStaticReflectivePresentationDecl source color declaration) := by
  cases color with
  | base =>
      refine CostStaticAtomKeyCospan.not_quoteStatusAgrees_of_foreignQuote
        (costStaticReflectivePresentationDecl_mem_profile .wrapped mem) ?_
      simpa [costWrappedReflectivePresentationDecl,
        costBaseReflectivePresentationDecl, mapReflectivePresentation,
        costStaticReflectivePresentationDecl, costWrappedStaticReflectiveSymbols,
        costBaseStaticReflectiveSymbols, costBaseStaticSymbols,
        costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
        (costConstructorName_distinct declaration.quoteConstructor).symm
  | wrapped =>
      refine CostStaticAtomKeyCospan.not_quoteStatusAgrees_of_foreignQuote
        (costStaticReflectivePresentationDecl_mem_profile .base mem) ?_
      simpa [costWrappedReflectivePresentationDecl,
        costBaseReflectivePresentationDecl, mapReflectivePresentation,
        costStaticReflectivePresentationDecl, costWrappedStaticReflectiveSymbols,
        costBaseStaticReflectiveSymbols, costBaseStaticSymbols,
        costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
        (costConstructorName_distinct declaration.quoteConstructor)

/-- The profile recognizes **either** colour's quote as a restoration
boundary, whichever colour is being canonicalized under.  Membership itself is
`costStaticReflectivePresentationDecl_mem` (`CostCanonicalSection`). -/
theorem isQuoteConstructor_costStaticReflectivePresentationDecl {source : CIGSLT}
    (color : CostStaticColor) (declaration : ReflectivePresentationDecl)
    (mem : declaration ∈ source.reflection.1.presentations) :
    ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile
        (costStaticReflectivePresentationDecl source color
          declaration).quoteConstructor = true := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  refine List.any_eq_true.mpr ⟨_, ?_, beq_self_eq_true _⟩
  simpa only [CIGSLT.costWholeReflectionProfile_presentations] using
    costStaticReflectivePresentationDecl_mem source color declaration mem

/-- **Distinct colours spell the same authored quote differently.**  Together
with the previous theorem this is the foreign-quote configuration: recognized
by the profile, unrecognized by the other colour's declaration. -/
theorem costStaticReflectivePresentationDecl_quoteConstructor_ne {source : CIGSLT}
    {leftColor rightColor : CostStaticColor} (distinct : leftColor ≠ rightColor)
    (declaration : ReflectivePresentationDecl) :
    (costStaticReflectivePresentationDecl source leftColor
        declaration).quoteConstructor ≠
      (costStaticReflectivePresentationDecl source rightColor
        declaration).quoteConstructor := by
  cases leftColor <;> cases rightColor
  · exact absurd rfl distinct
  · simpa [costStaticReflectivePresentationDecl,
      costBaseReflectivePresentationDecl, costWrappedReflectivePresentationDecl,
      mapReflectivePresentation, costBaseStaticReflectiveSymbols,
      costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
      costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
      costConstructorName_distinct declaration.quoteConstructor
  · simpa [costStaticReflectivePresentationDecl,
      costBaseReflectivePresentationDecl, costWrappedReflectivePresentationDecl,
      mapReflectivePresentation, costBaseStaticReflectiveSymbols,
      costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
      costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
      (costConstructorName_distinct declaration.quoteConstructor).symm
  · exact absurd rfl distinct

/-! ## The two colours' hereditary constructor images are disjoint

The apex-bearing theorems constrain the patterns they relate to
`CostStaticColor.hereditaryConstructorImage source color` — every admitted
constructor is *that colour's* spelling of an authored constructor.  The
theorem below shows the two colours' images never overlap, so a frame typed
within one colour's image contains no constructor of the other.

This is the fact that keeps a same-colour apex satisfiable: such a frame
holds no *foreign* quote, and it is only at a foreign quote that the
restoration and keying disciplines diverge.  The divergence results are
therefore about configurations that genuinely mix the colours, not about
these monochrome frames. -/

/-- **Disjointness of the hereditary constructor images.**  Note this holds
even for *different* authored constructors on the two sides: the colour tags
differ inside both, so no base spelling is ever a wrapped spelling. -/
theorem hereditaryConstructorImage_disjoint {source : CIGSLT}
    {leftColor rightColor : CostStaticColor} (distinct : leftColor ≠ rightColor)
    {targetConstructor : String}
    (inLeft : CostStaticColor.hereditaryConstructorImage source leftColor
      targetConstructor)
    (inRight : CostStaticColor.hereditaryConstructorImage source rightColor
      targetConstructor) : False := by
  obtain ⟨leftSource, _, leftSpelling⟩ := inLeft
  obtain ⟨rightSource, _, rightSpelling⟩ := inRight
  cases leftColor <;> cases rightColor
  · exact distinct rfl
  · exact costBaseConstructorName_ne_wrapped leftSource rightSource
      (by simpa [CostStaticColor.symbols, costBaseStaticSymbols,
        costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
        leftSpelling.symm.trans rightSpelling)
  · exact costBaseConstructorName_ne_wrapped rightSource leftSource
      (by simpa [CostStaticColor.symbols, costBaseStaticSymbols,
        costWrappedStaticSymbols, costBaseLanguageDefSymbolMap] using
        rightSpelling.symm.trans leftSpelling)
  · exact distinct rfl

/-- **Monochrome frames.**  A constructor admitted at one colour is *not*
admitted at the other.  Stated in the contrapositive form a consumer wants:
membership in one image refutes membership in the other. -/
theorem not_hereditaryConstructorImage_of_other_colour {source : CIGSLT}
    {leftColor rightColor : CostStaticColor} (distinct : leftColor ≠ rightColor)
    {targetConstructor : String}
    (inLeft : CostStaticColor.hereditaryConstructorImage source leftColor
      targetConstructor) :
    ¬ CostStaticColor.hereditaryConstructorImage source rightColor
      targetConstructor :=
  fun inRight => hereditaryConstructorImage_disjoint distinct inLeft inRight

/-! ## Colour confinement of frames — already established elsewhere

The disjointness above is about constructor *images*.  The corresponding fact
about *frames* — that every application head of a node's reified target frame
belongs to that node's colour — is
`CostStaticRegionNode.reifiedTargetFrame_constructorsWithinColor`
(`CostHereditaryFrameNormalization`), which composes
`constructorsWithin_mapPattern` with `constructorsWithin_thickenAmbientBVars`.

Together they give the structural reading of the atomization design: foreign
material reaches a frame only through *atom* positions, where traversal stops,
never as a rigid head.  That is what keeps the two quotation disciplines in
agreement inside a frame, since a head belonging to one colour cannot also
belong to the other. -/

/-! ## Using these with the divergence theorems

`costConstructorName_distinct` is exactly the `foreign` hypothesis of
`restorationDepth_ne_keyDepth_at_foreignQuote` and
`not_quoteStatusAgrees_of_foreignQuote`, instantiated at a quote
constructor: apply it with the authored quote's name to obtain that the
base and wrapped spellings differ, then feed that in together with the
profile-membership fact for whichever colour is in scope.

The consequence is that the divergence is **live for every Cost-generated
language carrying both colours**, not a hypothetical about some exotic
profile.  A foreign quote always exists there, so `QuoteStatusAgrees` never
holds and any result premised on it is vacuous.  The one-index apex remains
inhabited; the separated carrier is required only at bare `parallel`. -/

end Mettapedia.GSLT.LanguageDef
