import Mettapedia.GSLT.Dynamics.EventValuationFunctor
import Mettapedia.GSLT.LanguageDef.GSLTILDisplayedRouteValuation

/-!
# Functorial valuations of retained GSLT-IL routes

The occurrence and revision grades of a path-retaining finite route are the
actions of the generic event-valuation functor on its two retained histories.
This places those observations in the free-history/partial-monoid
factorization without changing the route or assigning semantic authority to a
grade.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RouteValuationFunctor

open Mettapedia.GSLT.Dynamics.EventValuationFunctor
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation

universe u uGrade

/-- Occurrence grading is exactly the generic valuation functor applied to
the retained occurrence history. -/
theorem occurrenceGrade_eq_functorGrade
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (valuation : Valuation.{u, uGrade} Occurrence)
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    occurrenceGrade valuation route =
      functorGrade valuation route.occurrences :=
  rfl

/-- Revision grading is the same generic functorial construction on the
retained revision history. -/
theorem revisionGrade_eq_functorGrade
    {theory : Theory.{u, u, u, u}}
    (valuation : Valuation.{u, uGrade} theory.Revision)
    {Occurrence : Type u} {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    revisionGrade valuation route =
      functorGrade valuation route.revisions :=
  rfl

/-- Exact chronological valuation is the identity history action: it returns
the complete occurrence list with order and repetition intact. -/
theorem occurrenceChronology_is_exact
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    functorGrade (occurrenceChronology Occurrence) route.occurrences =
      some route.occurrences :=
  chronology_historyGrade route.occurrences

/-! ## The functorial decoration remains a projection -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation.Canary

/-- Even a total, functorial additive valuation need not faithfully encode a
retained route. -/
theorem functorial_count_is_not_route_faithful :
    ¬ Function.Injective
      (fun witness : retainedFiniteRoute collisionTheory Nat () () =>
        functorGrade countValuation witness.1.occurrences) := by
  simpa only [occurrenceGrade_eq_functorGrade] using
    count_grade_projection_not_injective

end Canary

/-! ## Axiom audit -/

#print axioms occurrenceGrade_eq_functorGrade
#print axioms revisionGrade_eq_functorGrade
#print axioms occurrenceChronology_is_exact
#print axioms Canary.functorial_count_is_not_route_faithful

end Mettapedia.GSLT.LanguageDef.GSLTIL.RouteValuationFunctor
