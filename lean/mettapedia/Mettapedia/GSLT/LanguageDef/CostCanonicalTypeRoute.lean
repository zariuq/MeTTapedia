import Mettapedia.GSLT.LanguageDef.CostCanonicalReachablePairAlignment

/-!
# Proof-relevant type routes for Cost descent

Canonical descent through a static plan changes the active typing fibre at
constructor parameters, binder bodies, and collection elements.  This file
records those changes as data.  It deliberately separates route construction
from interpretation by a recursive type domain.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- A proof-relevant route from one generated Cost type to a descendant type.

Non-bare constructor parameters are admitted by the generic recursive-domain
law.  A structural collection endpoint is retained explicitly so an
admissible domain can reject it.  Bare-collection parameters are also
retained explicitly because their admissibility is language-specific. -/
inductive CostCanonicalTypeRoute (source : CIGSLT) (color : CostStaticColor)
    (root : TypeExpr) :
    TypeExpr → Type where
  | refl : CostCanonicalTypeRoute source color root root
  | parameter
      {rule : GrammarRule} {parameter : TermParam} {expected : TypeExpr}
      (prior : CostCanonicalTypeRoute source color root (.base rule.category))
      (membership : rule ∈ source.costWholeLanguage.terms)
      (notBare : ¬ UsesBareCollection rule)
      (parameterMembership : parameter ∈ rule.params)
      (parameterType : parameterType? parameter = some expected) :
      CostCanonicalTypeRoute source color root expected
  | codomain {domain codomain : TypeExpr}
      (prior : CostCanonicalTypeRoute source color root
        (.arrow domain codomain)) :
      CostCanonicalTypeRoute source color root codomain
  | structuralCollectionElement
      {collectionType : CollType} {elementType : TypeExpr}
      (prior : CostCanonicalTypeRoute source color root
        (.collection collectionType elementType)) :
      CostCanonicalTypeRoute source color root elementType
  | bareCollectionElement
      {rule : GrammarRule} {parameterName : String}
      {collectionType : CollType} {elementType : TypeExpr}
      (prior : CostCanonicalTypeRoute source color root
        (mapTypeExpr (color.symbols source) (.base rule.category)))
      (membership :
        rule ∈ source.theory.presentation.presentation.language.terms)
      (wrapped : rule.label ∈ source.continuationRetyping.wrappedLabels)
      (parameterShape : rule.params =
        [.simple parameterName (.collection collectionType elementType)]) :
      CostCanonicalTypeRoute source color root
        (mapTypeExpr (color.symbols source) elementType)

namespace CostCanonicalTypeRoute

/-- Language-specific closure required only for bare-collection parameters.
Every other route step is interpreted by `CostCanonicalRecursiveTypeDomain`
itself. -/
def BareCollectionAdmissible
    {source : CIGSLT} {color : CostStaticColor}
    (recursive : CostCanonicalRecursiveTypeDomain source) :
    Prop :=
  ∀ {rule : GrammarRule},
    rule ∈ source.theory.presentation.presentation.language.terms →
    rule.label ∈ source.continuationRetyping.wrappedLabels →
    ∀ {parameterName : String} {collectionType : CollType}
      {elementType : TypeExpr},
      rule.params =
        [.simple parameterName (.collection collectionType elementType)] →
      recursive.Admissible (mapTypeExpr (color.symbols source) elementType)

/-- Change only the named root of a route along an equality. -/
def castRoot
    {source : CIGSLT} {color : CostStaticColor}
    {first second endpoint : TypeExpr}
    (equal : first = second)
    (route : CostCanonicalTypeRoute source color first endpoint) :
    CostCanonicalTypeRoute source color second endpoint := by
  cases equal
  exact route

/-- Change only the endpoint of a route along an equality. -/
def castEndpoint
    {source : CIGSLT} {color : CostStaticColor}
    {root first second : TypeExpr}
    (equal : first = second)
    (route : CostCanonicalTypeRoute source color root first) :
    CostCanonicalTypeRoute source color root second := by
  cases equal
  exact route

/-- Every recorded route preserves an admissible recursive type domain once
that language's bare-collection parameters are known to be admissible. -/
theorem admissible
    {source : CIGSLT} {color : CostStaticColor}
    {root endpoint : TypeExpr}
    {recursive : CostCanonicalRecursiveTypeDomain source}
    (bare : BareCollectionAdmissible (color := color) recursive)
    (route : CostCanonicalTypeRoute source color root endpoint)
    (rootAdmissible : recursive.Admissible root) :
    recursive.Admissible endpoint := by
  induction route with
  | refl => exact rootAdmissible
  | parameter prior membership notBare parameterMembership parameterType
      _inductionHypothesis =>
      exact recursive.parameter membership notBare parameterMembership
        parameterType
  | codomain prior inductionHypothesis =>
      exact recursive.codomain inductionHypothesis
  | structuralCollectionElement prior inductionHypothesis =>
      exact (recursive.noCollection inductionHypothesis).elim
  | bareCollectionElement prior membership wrapped parameterShape
      _inductionHypothesis =>
      exact bare membership wrapped parameterShape

/-- Positive canary: doing no descent retains the root fibre exactly. -/
example {source : CIGSLT} {color : CostStaticColor} (root : TypeExpr) :
    Nonempty (CostCanonicalTypeRoute source color root root) :=
  ⟨.refl⟩

/-- Negative canary: no interpreted route from an admissible root can finish
at a structural collection fibre. -/
theorem not_endpoint_collection_of_admissible
    {source : CIGSLT} {color : CostStaticColor} {root : TypeExpr}
    {recursive : CostCanonicalRecursiveTypeDomain source}
    (bare : BareCollectionAdmissible (color := color) recursive)
    (rootAdmissible : recursive.Admissible root)
    {collectionType : CollType} {elementType : TypeExpr}
    (route : CostCanonicalTypeRoute source color root
      (.collection collectionType elementType)) : False :=
  recursive.noCollection (route.admissible bare rootAdmissible)

end CostCanonicalTypeRoute

end Mettapedia.GSLT.LanguageDef
