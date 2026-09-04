import Mettapedia.GSLT.LanguageDef.Cost

/-! PROBE: the "one-index apex has no inhabitant" claim.

Three places assert that where a foreign quote exists the one-index apex is
UNINHABITED / UNSATISFIABLE:

  QuoteBoundaryDivergence.lean:28-31  "Any statement that demands a single
      depth-indexed relation across both readings is therefore unsatisfiable
      wherever a foreign quote occurs"
  ColourTagSeparation.lean:220-222    "A foreign quote always exists there, so
      the one-index apex has no inhabitant and the separated carrier is required."
  COST_MAP.md:122-123                 "stating it over the one-index apex will
      consume unbounded effort for a statement that has no inhabitant."

The probes below refute the literal claim: `CommonRestorationApex` is inhabited
at EVERY depth, over EVERY source, with a foreign quote present or not. -/

namespace Mettapedia.GSLT.LanguageDef
namespace CostStaticAtomKeyCospan

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- PROBE A. Inhabited at every depth, unconditionally. -/
example {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (pattern : Pattern) :
    CommonRestorationApex source cospan declaration depth pattern pattern :=
  CommonRestorationApex.refl cospan declaration depth pattern

/-- PROBE B. Inhabited at every depth even in the PRESENCE of a foreign quote,
i.e. exactly where `QuoteStatusAgrees` is refuted.  So the refutation of
agreement does not empty the one-index carrier. -/
example {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    {declaration owner : ReflectivePresentationDecl}
    (ownerMem : owner ∈ source.costWholeReflectionProfile.presentations)
    (foreign : owner.quoteConstructor ≠ declaration.quoteConstructor)
    (depth : Nat) (pattern : Pattern) :
    (¬ QuoteStatusAgrees source declaration) ∧
      CommonRestorationApex source cospan declaration depth pattern pattern :=
  ⟨not_quoteStatusAgrees_of_foreignQuote ownerMem foreign,
    CommonRestorationApex.refl cospan declaration depth pattern⟩

/-- PROBE C. Inhabited at an APPLICATION headed by the foreign quote itself,
at any root depth: the `apply` constructor's index reset is a statement about
the CHILDREN's index, and children may be closed by `refl`.  So even the
foreign-quote node admits one-index evidence. -/
example {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (foreignQuote : String) (arguments : List Pattern) (depth : Nat) :
    CommonRestorationApex source cospan declaration depth
      (.apply foreignQuote arguments) (.apply foreignQuote arguments) :=
  CommonRestorationApex.apply foreignQuote
    (CommonRestorationApex.reflList cospan declaration _ arguments)

end CostStaticAtomKeyCospan
end Mettapedia.GSLT.LanguageDef
