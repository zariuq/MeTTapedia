import Mettapedia.Computability.ReflectiveCode
import Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare

/-!
# Reflective quotation at an extensional function boundary

Function application and reflective quotation observe different aspects of a
function carrier.  Application records pointwise behavior.  Executable
quotation may also retain syntax, routes, occurrences, provenance, or other
intensional data.

This module gives the exact compatibility criterion.  If quotation has static
beta, so that dropping a quotation recovers its function, then quotation
factors through the application readout exactly when the function carrier is
application-extensional.  Thus reflective code and extensional functions are
compatible, but only when quotation does not distinguish two functions that
application identifies.

The result is local to a selected function carrier and observer.  It does not
select a global equality discipline, staging calculus, code representation,
or product language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ReflectiveFunctionObserverBoundary

open Mettapedia.Computability.ReflectiveCode
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
open Mettapedia.TypeTheory.DependencyExtensionalityReadoutSquare
open Mettapedia.TypeTheory.ExtensionalReadout

universe uDomain uCodomain uFunction uCode

variable {Domain : Type uDomain} {Codomain : Domain → Type uCodomain}
variable (space : DependentFunctionSpace.{uDomain, uCodomain, uFunction}
  Domain Codomain)

/-- A quotation is behavior-invariant when pointwise indistinguishable
functions receive the same code. -/
def QuotationApplicationInvariant {Code : Type uCode}
    (quotation : space.Function → Code) : Prop :=
  ∀ left right : space.Function,
    (∀ argument, space.application left argument =
      space.application right argument) →
    quotation left = quotation right

/-- Quotation invariance is exactly fibre invariance for the canonical
application readout. -/
theorem quotationApplicationInvariant_iff_fibreInvariant
    {Code : Type uCode} (quotation : space.Function → Code) :
    QuotationApplicationInvariant space quotation ↔
      (functionReadout space).FibreInvariant quotation := by
  constructor
  · intro invariant left right sameBehavior
    apply invariant left right
    intro argument
    exact congrFun sameBehavior argument
  · intro invariant left right pointwise
    apply invariant
    funext argument
    exact pointwise argument

/-- For an executable quotation, descent through extensional behavior is
equivalent to application extensionality of the retained function carrier.

Static beta is used only for its genuine content: it makes quotation
injective, so a factorization cannot hide a source distinction. -/
theorem quotation_factors_iff_applicationExtensional
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta) :
    (functionReadout space).FactorsObserver interface.quote ↔
      space.ApplicationExtensional := by
  rw [(functionReadout space).factorsObserver_iff_fibreInvariant]
  rw [← quotationApplicationInvariant_iff_fibreInvariant space]
  constructor
  · intro invariant left right pointwise
    apply interface.quote_injective_of_staticBeta beta
    exact invariant left right pointwise
  · intro extensional left right pointwise
    exact congrArg interface.quote (extensional left right pointwise)

/-- An application-indistinguishable pair is necessarily separated by every
static-beta quotation. -/
theorem staticBeta_quotation_separates_indistinguishablePair
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta)
    (pair : space.HasApplicationIndistinguishablePair) :
    ∃ left right : space.Function,
      (∀ argument, space.application left argument =
        space.application right argument) ∧
      interface.quote left ≠ interface.quote right := by
  rcases pair with ⟨left, right, distinct, pointwise⟩
  refine ⟨left, right, pointwise, ?_⟩
  intro sameCode
  exact distinct (interface.quote_injective_of_staticBeta beta sameCode)

/-- Consequently a static-beta quotation cannot descend through application
when the carrier retains an application-invisible distinction. -/
theorem indistinguishablePair_blocks_quotation_descent
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta)
    (pair : space.HasApplicationIndistinguishablePair) :
    ¬ (functionReadout space).FactorsObserver interface.quote := by
  rw [quotation_factors_iff_applicationExtensional space interface beta]
  intro extensional
  exact
    (space.applicationExtensional_excludes_indistinguishablePair extensional)
      pair

/-! ## The code-to-behavior readout -/

/-- Execute code to a retained function and observe its pointwise behavior.
The representative first abstracts an extensional section and then quotes the
resulting function.  Static beta for code and beta for functions make this a
split readout. -/
def codeBehaviorReadout
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta) :
    SplitReadout Code ((argument : Domain) → Codomain argument) where
  observe := fun code => space.application (interface.drop code)
  representative := fun body => interface.quote (space.abstraction body)
  observe_representative := by
    intro body
    funext argument
    dsimp
    rw [beta]
    exact space.beta body argument

/-- Exactness of code-to-behavior observation has two independent
requirements.  Application extensionality removes hidden distinctions in the
function carrier; code eta removes noncanonical code outside the image of
quotation. -/
theorem codeBehaviorReadout_faithful_iff
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta) :
    (codeBehaviorReadout space interface beta).Faithful ↔
      space.ApplicationExtensional ∧ interface.StaticEta := by
  constructor
  · intro faithful
    constructor
    · intro left right pointwise
      apply interface.quote_injective_of_staticBeta beta
      apply faithful
      funext argument
      simp only [codeBehaviorReadout]
      rw [beta left, beta right]
      exact pointwise argument
    · intro code
      apply faithful
      funext argument
      simp only [codeBehaviorReadout]
      rw [beta (interface.drop code)]
  · rintro ⟨extensional, eta⟩ left right sameBehavior
    apply interface.drop_injective_of_staticEta eta
    apply extensional
    intro argument
    simpa only [codeBehaviorReadout] using congrFun sameBehavior argument

/-- Since the code-to-behavior map already has a selected representative,
its exactness has the same two-part criterion. -/
theorem codeBehaviorReadout_exact_iff
    {Code : Type uCode}
    (interface : Interface space.Function Code)
    (beta : interface.StaticBeta) :
    (codeBehaviorReadout space interface beta).Exact ↔
      space.ApplicationExtensional ∧ interface.StaticEta := by
  rw [(codeBehaviorReadout space interface beta).exact_iff_faithful]
  exact codeBehaviorReadout_faithful_iff space interface beta

/-! ## Positive and negative controls -/

namespace Canary

/-- A separate code layer retaining an entire route-sensitive function.
The constructor is representation, not behavioral erasure. -/
structure RouteCode where
  body : Bool × Bool

/-- Exact quotation and dropping for the route-retaining carrier. -/
def routeInterface : Interface (Bool × Bool) RouteCode where
  quote := RouteCode.mk
  drop := RouteCode.body

theorem routeInterface_beta : routeInterface.StaticBeta := by
  intro function
  rfl

theorem routeInterface_eta : routeInterface.StaticEta := by
  intro code
  cases code
  rfl

/-- Executable quotation retains the route tag and therefore does not descend
to pointwise behavior. -/
theorem routeQuotation_does_not_factor :
    ¬ (functionReadout simpleRouteSensitive.{0}).FactorsObserver
      routeInterface.quote :=
  indistinguishablePair_blocks_quotation_descent simpleRouteSensitive.{0}
    routeInterface routeInterface_beta
    simpleRouteSensitive_hasIndistinguishablePair

/-- Even though route code is exactly equivalent to its retained function,
the composite readout to pointwise behavior is not exact. -/
theorem routeCodeBehavior_not_exact :
    ¬ (codeBehaviorReadout simpleRouteSensitive.{0}
      routeInterface routeInterface_beta).Exact := by
  rw [codeBehaviorReadout_exact_iff simpleRouteSensitive.{0}
    routeInterface routeInterface_beta]
  intro capabilities
  exact simpleRouteSensitive_not_applicationExtensional capabilities.1

/-- The obstruction is visible directly: the two functions apply identically
but their quotations remain distinct. -/
theorem routeQuotation_separates_same_behavior :
    (∀ argument,
      simpleRouteSensitive.{0}.application (false, false) argument =
        simpleRouteSensitive.{0}.application (false, true) argument) ∧
      routeInterface.quote (false, false) ≠
        routeInterface.quote (false, true) := by
  constructor
  · intro argument
    cases argument
    rfl
  · intro sameCode
    have sameBody := congrArg RouteCode.body sameCode
    exact Bool.false_ne_true (congrArg Prod.snd sameBody)

/-- Reflective code is compatible with an extensional carrier.  The existing
exact Boolean interface descends through the application readout. -/
theorem extensionalQuotation_factors :
    (functionReadout simpleExtensional.{0}).FactorsObserver
      Mettapedia.Computability.ReflectiveCode.Canary.exactBool.quote := by
  rw [quotation_factors_iff_applicationExtensional simpleExtensional.{0}
    Mettapedia.Computability.ReflectiveCode.Canary.exactBool
    Mettapedia.Computability.ReflectiveCode.Canary.exactBool_beta]
  exact simpleExtensional_applicationExtensional

/-- Exact code and an extensional function carrier yield an exact composite
readout to behavior. -/
theorem extensionalCodeBehavior_exact :
    (codeBehaviorReadout simpleExtensional.{0}
      Mettapedia.Computability.ReflectiveCode.Canary.exactBool
      Mettapedia.Computability.ReflectiveCode.Canary.exactBool_beta).Exact := by
  rw [codeBehaviorReadout_exact_iff simpleExtensional.{0}
    Mettapedia.Computability.ReflectiveCode.Canary.exactBool
    Mettapedia.Computability.ReflectiveCode.Canary.exactBool_beta]
  exact ⟨simpleExtensional_applicationExtensional,
    Mettapedia.Computability.ReflectiveCode.Canary.exactBool_eta⟩

/-- An extensional function carrier with one additional noncanonical code.
Beta holds, while eta fails at `none`. -/
def extraCodeInterface : Interface Bool (Option Bool) where
  quote := some
  drop
    | none => false
    | some value => value

theorem extraCodeInterface_beta : extraCodeInterface.StaticBeta := by
  intro function
  rfl

theorem extraCodeInterface_not_eta : ¬ extraCodeInterface.StaticEta := by
  intro eta
  have impossible := eta none
  cases impossible

/-- Eta is independently necessary: pointwise-extensional functions do not
make a code readout exact when code contains a noncanonical element. -/
theorem extraCodeBehavior_not_exact :
    ¬ (codeBehaviorReadout simpleExtensional.{0}
      extraCodeInterface extraCodeInterface_beta).Exact := by
  rw [codeBehaviorReadout_exact_iff simpleExtensional.{0}
    extraCodeInterface extraCodeInterface_beta]
  intro capabilities
  exact extraCodeInterface_not_eta capabilities.2

/-- Static beta is essential to the equivalence: an erasing, non-executable
quotation can factor through behavior even when the source carrier is not
application-extensional. -/
def erasingInterface : Interface (Bool × Bool) PUnit where
  quote := fun _ => PUnit.unit
  drop := fun _ => (false, false)

theorem erasingInterface_not_beta : ¬ erasingInterface.StaticBeta := by
  intro beta
  have equal := beta (false, true)
  exact Bool.false_ne_true (congrArg Prod.snd equal)

theorem erasingQuotation_factors :
    (functionReadout simpleRouteSensitive.{0}).FactorsObserver
      erasingInterface.quote := by
  refine ⟨fun _ => PUnit.unit, ?_⟩
  intro function
  rfl

/-- Complete boundary canary: exact quotation descends on the extensional
carrier, fails on the route-sensitive carrier, and erasing quotation shows
why static beta cannot be omitted. -/
theorem reflective_function_extensionality_boundary :
    (functionReadout simpleExtensional.{0}).FactorsObserver
        Mettapedia.Computability.ReflectiveCode.Canary.exactBool.quote ∧
      ¬ (functionReadout simpleRouteSensitive.{0}).FactorsObserver
        routeInterface.quote ∧
      ¬ erasingInterface.StaticBeta ∧
      (functionReadout simpleRouteSensitive.{0}).FactorsObserver
        erasingInterface.quote ∧
      (codeBehaviorReadout simpleExtensional.{0}
        Mettapedia.Computability.ReflectiveCode.Canary.exactBool
        Mettapedia.Computability.ReflectiveCode.Canary.exactBool_beta).Exact ∧
      ¬ (codeBehaviorReadout simpleRouteSensitive.{0}
        routeInterface routeInterface_beta).Exact ∧
      ¬ (codeBehaviorReadout simpleExtensional.{0}
        extraCodeInterface extraCodeInterface_beta).Exact :=
  ⟨extensionalQuotation_factors,
    routeQuotation_does_not_factor,
    erasingInterface_not_beta,
    erasingQuotation_factors,
    extensionalCodeBehavior_exact,
    routeCodeBehavior_not_exact,
    extraCodeBehavior_not_exact⟩

end Canary

#print axioms quotation_factors_iff_applicationExtensional
#print axioms staticBeta_quotation_separates_indistinguishablePair
#print axioms indistinguishablePair_blocks_quotation_descent
#print axioms codeBehaviorReadout_faithful_iff
#print axioms codeBehaviorReadout_exact_iff
#print axioms Canary.routeQuotation_does_not_factor
#print axioms Canary.routeCodeBehavior_not_exact
#print axioms Canary.extensionalQuotation_factors
#print axioms Canary.extensionalCodeBehavior_exact
#print axioms Canary.extraCodeBehavior_not_exact
#print axioms Canary.reflective_function_extensionality_boundary

end Mettapedia.TypeTheory.ReflectiveFunctionObserverBoundary
