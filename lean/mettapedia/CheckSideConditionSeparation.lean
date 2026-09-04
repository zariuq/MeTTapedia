import Mettapedia.GSLT.LanguageDef.Cost

/-! PROBE: is the existing side condition really "the agreement assumption"?

`TwoDepthRestorationApex.lean:311` heads a section
  "## The existing side condition *is* the agreement assumption"
and `not_ordinaryHeadCondition_of_foreignQuote` is docstringed as
  "every consumer of the one-index apex had an undischargeable obligation".

The side condition actually carried by `CommonRestorationApex.of_canonicalRootAligned`
(`CostRestorationRelation.lean:1411`) is ENDPOINT-INDEXED: it constrains only the
constructor that heads *this* pair.  `OrdinaryHeadCondition`
(`TwoDepthRestorationApex.lean:328`) is quantified over ALL strings.

If the two really were the same assumption, then wherever `OrdinaryHeadCondition`
is refuted the endpoint-indexed one would be unsatisfiable too.  The examples
below show it stays satisfiable.  So the identification fails and the
"undischargeable obligation" claim does not follow. -/

namespace Mettapedia.GSLT.LanguageDef
namespace CostStaticAtomKeyCospan

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- PROBE A. The endpoint-indexed side condition holds VACUOUSLY at any pair of
non-application endpoints — no hypothesis about the profile at all.  So it is
dischargeable at such pairs even when a foreign quote exists in the profile. -/
example {source : CIGSLT} (declaration : ReflectivePresentationDecl)
    (index : Nat) :
    ∀ {constructor : String} {leftArguments rightArguments : List Pattern},
      (Pattern.bvar index) = .apply constructor leftArguments →
      (Pattern.bvar index) = .apply constructor rightArguments →
      constructor ≠ declaration.quoteConstructor →
      ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile constructor = false := by
  intro _ _ _ absurdLeft
  exact absurd absurdLeft (by simp)

/-- PROBE B. It also holds at APPLICATION endpoints, provided only that the head
of *this* pair is not a quote of the profile — a purely local fact, with no
bearing on whether some other constructor in the profile is a foreign quote. -/
example {source : CIGSLT} (declaration : ReflectivePresentationDecl)
    (head : String) (arguments : List Pattern)
    (localFact : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile head = false) :
    ∀ {constructor : String} {leftArguments rightArguments : List Pattern},
      (Pattern.apply head arguments) = .apply constructor leftArguments →
      (Pattern.apply head arguments) = .apply constructor rightArguments →
      constructor ≠ declaration.quoteConstructor →
      ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile constructor = false := by
  rintro _ _ _ ⟨rfl, rfl⟩ _ _
  exact localFact

/-- PROBE C. The decisive separation, stated abstractly: the endpoint-indexed
condition at a non-application pair is satisfiable SIMULTANEOUSLY with the global
`OrdinaryHeadCondition` being false.  Hence the two are not the same assumption,
and refuting the global one does not refute the local one. -/
example {source : CIGSLT} {declaration owner : ReflectivePresentationDecl}
    (ownerMem : owner ∈ source.costWholeReflectionProfile.presentations)
    (foreign : owner.quoteConstructor ≠ declaration.quoteConstructor)
    (index : Nat) :
    (¬ OrdinaryHeadCondition source declaration) ∧
      (∀ {constructor : String} {leftArguments rightArguments : List Pattern},
        (Pattern.bvar index) = .apply constructor leftArguments →
        (Pattern.bvar index) = .apply constructor rightArguments →
        constructor ≠ declaration.quoteConstructor →
        ReflectiveContextSupport.isQuoteConstructor
          source.costWholeReflectionProfile constructor = false) := by
  refine ⟨not_ordinaryHeadCondition_of_foreignQuote ownerMem foreign, ?_⟩
  intro _ _ _ absurdLeft
  exact absurd absurdLeft (by simp)

end CostStaticAtomKeyCospan
end Mettapedia.GSLT.LanguageDef
