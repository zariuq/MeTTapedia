import Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalEvidence

/-!
# First-class GSLT presentations and typed routes in Prime

A validated language presentation is an ordinary typed native value and uses
the single staged quotation former.  An authored GSLT-IL route is separately a
proof-relevant Prime relation on its selected endpoint fibres.  A route may be
executed relationally without a compilation license; representability is the
additional evidence that exposes a direct map.

`LanguageWorkspace` associates a presentation value with an inventory of
authored routes.  The association is data, not an unstated adequacy theorem:
semantic agreement between a presentation's dynamics and a route program must
be supplied by a separate checked bridge.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe

namespace FirstClassGSLT

open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.OSLF.MeTTaIL.Syntax
open RelationalInternalLanguage.Semantic

/-! ## Presentation values -/

abbrev PresentationValue :=
  Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef

/-- A presentation is quoted by the same operation as every other native
term. -/
def quotePresentation (level : Nat) (presentation : PresentationValue) :
    NativeRawTm level 0 :=
  nativeQuotedLanguage level presentation

/-- Every first-class presentation value has the ordinary native quotation
type. -/
theorem quotePresentation_hasType (level : Nat)
    (presentation : PresentationValue) :
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (quotePresentation level presentation)
      (nativeQuoteNext level
        (NativeRawTm.u0 : NativeRawTm (level + 1) 0)) :=
  nativeQuotedLanguage_has_type level presentation

/-- Quotation retains the complete validated presentation value. -/
@[simp] theorem quotePresentation_roundtrip (level : Nat)
    (presentation : PresentationValue) :
    (quotePresentation level presentation).quotedLanguage? =
      some presentation :=
  quotedLanguage?_nativeQuotedLanguage level presentation

/-! ## Typed authored routes as relational values -/

/-- A first-class authored route, including declaration membership and its
selected native endpoint fibres. -/
structure TypedRouteValue where
  program : Program
  route : RouteDecl
  declared : route ∈ program.routes
  profile : TypedRouteProfile program route

namespace TypedRouteValue

/-- The primary meaning of a typed route is its proof-relevant relation. -/
def relation (value : TypedRouteValue) :
    RelationalInternalLanguage.Semantic.Rel
      value.profile.Source value.profile.Target :=
  AuthoredRoute.internalizeTyped value.profile

/-- A compilation license is exactly representability of the primary
relation; it is not part of route authoring. -/
abbrev License (value : TypedRouteValue) := value.profile.License

/-- Any authored route witness executes in the relational semantics, whether
or not a direct map has been licensed. -/
def execute (value : TypedRouteValue)
    {source : value.profile.Source} {target : value.profile.Target}
    (witness : value.profile.related source target) :
    (value.relation).evidence source target :=
  AuthoredRoute.executeWithoutLicense value.profile witness

/-- A license exposes one direct map on the selected typed fibre. -/
def compile (value : TypedRouteValue) (license : value.License) :
    value.profile.Source → value.profile.Target :=
  value.profile.compile license

/-- Licensed execution agrees fibrewise with the graph of the compiled map. -/
def representedAsGraph (value : TypedRouteValue) (license : value.License)
    (source : value.profile.Source) (target : value.profile.Target) :
    value.relation.evidence source target ≃
      (RelationalInternalLanguage.Semantic.Rel.graph
        (value.compile license)).evidence source target :=
  AuthoredRoute.representedAsGraph license source target

/-- The map exposed through Prime is the map selected by the GSLT-IL route
license; no second compilation decision is made. -/
@[simp] theorem represented_map_agrees (value : TypedRouteValue)
    (license : value.License) :
    ((AuthoredRoute.licenseEquiv value.profile) license).map =
      value.compile license :=
  AuthoredRoute.represented_map_agrees license

end TypedRouteValue

/-- A first-class language workspace.  Route-to-presentation adequacy is not
assumed by this container. -/
structure LanguageWorkspace where
  presentation : PresentationValue
  routes : List TypedRouteValue

namespace LanguageWorkspace

def quoted (workspace : LanguageWorkspace) (level : Nat) :
    NativeRawTm level 0 :=
  quotePresentation level workspace.presentation

theorem quoted_hasType (workspace : LanguageWorkspace) (level : Nat) :
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (workspace.quoted level)
      (nativeQuoteNext level
        (NativeRawTm.u0 : NativeRawTm (level + 1) 0)) :=
  quotePresentation_hasType level workspace.presentation

@[simp] theorem quoted_roundtrip (workspace : LanguageWorkspace)
    (level : Nat) :
    (workspace.quoted level).quotedLanguage? =
      some workspace.presentation :=
  quotePresentation_roundtrip level workspace.presentation

end LanguageWorkspace

/-! ## Positive admitted route -/

def atom (name : String) : Pattern := .apply name []

def unitRoute : RouteDecl where
  occurrence := atom "unit-route-occurrence"
  name := "unit-route"
  sourceSpace := atom "unit-source-space"
  targetSpace := atom "unit-target-space"

def unitRouteRule : RouteRule where
  occurrence := atom "unit-rule-occurrence"
  name := "unit-route"
  source := atom "unit-input"
  target := atom "unit-output"

def unitRouteProgram : Program where
  spaceRules := []
  routes := [unitRoute]
  routeRules := [unitRouteRule]

def unitRouteProfile : TypedRouteProfile unitRouteProgram unitRoute where
  Source := Unit
  Target := Unit
  sourcePattern _ := atom "unit-input"
  targetPattern _ := atom "unit-output"

def unitRouteValue : TypedRouteValue where
  program := unitRouteProgram
  route := unitRoute
  declared := by simp [unitRouteProgram]
  profile := unitRouteProfile

def unitRouteWitness : unitRouteProfile.related () () where
  routeMember := by simp [unitRouteProgram]
  rule := unitRouteRule
  ruleMember := by simp [unitRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

instance unitRouteWitness_subsingleton :
    Subsingleton (unitRouteProfile.related () ()) where
  allEq first second := by
    rcases first with
      ⟨_firstRouteMember, firstRule, firstRuleMember,
        _firstName, _firstSource, _firstTarget⟩
    rcases second with
      ⟨_secondRouteMember, secondRule, secondRuleMember,
        _secondName, _secondSource, _secondTarget⟩
    have firstRuleEq : firstRule = unitRouteRule := by
      simpa [unitRouteProgram] using firstRuleMember
    have secondRuleEq : secondRule = unitRouteRule := by
      simpa [unitRouteProgram] using secondRuleMember
    subst firstRule
    subst secondRule
    rfl

/-- The singleton typed route earns a direct identity map. -/
def unitRouteLicense : unitRouteValue.License where
  map := _root_.id
  exact source target := by
    cases source
    cases target
    exact
      { toFun := fun _ => ⟨⟨rfl⟩⟩
        invFun := fun _ => unitRouteWitness
        left_inv := by
          intro witness
          change unitRouteWitness = witness
          exact unitRouteWitness_subsingleton.allEq _ _
        right_inv := by
          rintro ⟨⟨proof⟩⟩
          rfl }

theorem unitRoute_executes :
    Nonempty (unitRouteValue.relation.evidence () ()) :=
  ⟨unitRouteValue.execute unitRouteWitness⟩

@[simp] theorem unitRoute_compiles_to_identity :
    unitRouteValue.compile unitRouteLicense = _root_.id :=
  rfl

/-! ## Negative unlicensed route with duplicate occurrences -/

def duplicateFirstRule : RouteRule :=
  { unitRouteRule with occurrence := atom "duplicate-first-occurrence" }

def duplicateSecondRule : RouteRule :=
  { unitRouteRule with occurrence := atom "duplicate-second-occurrence" }

def duplicateRouteProgram : Program where
  spaceRules := []
  routes := [unitRoute]
  routeRules := [duplicateFirstRule, duplicateSecondRule]

def duplicateRouteProfile :
    TypedRouteProfile duplicateRouteProgram unitRoute where
  Source := Unit
  Target := Unit
  sourcePattern _ := atom "unit-input"
  targetPattern _ := atom "unit-output"

def duplicateRouteValue : TypedRouteValue where
  program := duplicateRouteProgram
  route := unitRoute
  declared := by simp [duplicateRouteProgram]
  profile := duplicateRouteProfile

def duplicateFirstWitness : duplicateRouteProfile.related () () where
  routeMember := by simp [duplicateRouteProgram]
  rule := duplicateFirstRule
  ruleMember := by simp [duplicateRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

def duplicateSecondWitness : duplicateRouteProfile.related () () where
  routeMember := by simp [duplicateRouteProgram]
  rule := duplicateSecondRule
  ruleMember := by simp [duplicateRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

theorem duplicateWitnesses_distinct :
    duplicateFirstWitness ≠ duplicateSecondWitness := by
  intro equal
  have rulesEqual := congrArg RouteWitness.rule equal
  have occurrencesEqual := congrArg RouteRule.occurrence rulesEqual
  change atom "duplicate-first-occurrence" =
    atom "duplicate-second-occurrence" at occurrencesEqual
  simp [atom] at occurrencesEqual

theorem duplicateRoute_executes_twice :
    Nonempty (duplicateRouteValue.relation.evidence () ()) ∧
      Nonempty (duplicateRouteValue.relation.evidence () ()) :=
  ⟨⟨duplicateRouteValue.execute duplicateFirstWitness⟩,
    ⟨duplicateRouteValue.execute duplicateSecondWitness⟩⟩

/-- Visible single-valuedness does not license compilation when two authored
occurrences inhabit the same proof-relevant fibre. -/
theorem duplicateRoute_not_licensed :
    ¬ Nonempty duplicateRouteValue.License := by
  rintro ⟨license⟩
  have pairEqual := (license.deterministic ()).allEq
    (⟨(), duplicateFirstWitness⟩ :
      Sigma fun target => duplicateRouteProfile.related () target)
    ⟨(), duplicateSecondWitness⟩
  exact duplicateWitnesses_distinct
    (eq_of_heq (Sigma.mk.inj pairEqual).2)

/-! ## Concrete first-class workspace -/

/-- A real validated presentation value accompanied by one admitted authored
route.  The structure remains generic; this is only a positive inhabitant. -/
def positiveWorkspace : LanguageWorkspace where
  presentation :=
    Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
  routes := [unitRouteValue]

theorem positiveWorkspace_roundtrip :
    (positiveWorkspace.quoted 0).quotedLanguage? =
      some Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation :=
  rfl

theorem positiveWorkspace_has_admitted_route :
    ∃ route ∈ positiveWorkspace.routes, Nonempty route.License :=
  ⟨unitRouteValue, by simp [positiveWorkspace], ⟨unitRouteLicense⟩⟩

#print axioms quotePresentation_hasType
#print axioms quotePresentation_roundtrip
#print axioms TypedRouteValue.representedAsGraph
#print axioms unitRoute_executes
#print axioms unitRoute_compiles_to_identity
#print axioms duplicateRoute_not_licensed
#print axioms positiveWorkspace_has_admitted_route

end FirstClassGSLT

end Mettapedia.Languages.MeTTa.PureKernel.Universe
