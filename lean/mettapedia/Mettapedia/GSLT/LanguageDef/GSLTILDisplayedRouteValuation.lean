import Mettapedia.GSLT.Core.TraceResourceCorrespondence
import Mettapedia.GSLT.Dynamics.ChoiceEffectDistributiveLaws
import Mettapedia.GSLT.LanguageDef.GSLTILFiniteRevisionRouteBridge

/-!
# Displayed valuations over path-retaining GSLT-IL routes

A path-retaining finite route carries the chronological occurrence and
revision lists that value, attention, provenance, and measured-cost observers
may inspect.  Such observers compose through their declared partial monoids;
they do not become execution authorities merely because they share one route.

This module establishes the precise boundary:

* occurrence and revision valuations preserve route composition;
* independent valuation axes combine componentwise;
* chronological valuation recovers the exact occurrence list;
* candidate-local value attachment preserves route append and multiplicity;
* whole-family maximum resolution does not preserve route append;
* an additive cost grade equals positional route demand; and
* observing that demand does not supply the source purse that funds it.

Thus values are displayed observations of execution, choice is an explicit
family-relative boundary, and funding is a separate capability.  Physical
effect authorization and receipts remain in `SemanticPhysicalRouteBinding`;
none is reconstructed here from a grade.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.TraceResourceCorrespondence
open Mettapedia.GSLT.Dynamics.ChoiceEffectDistributiveLaws
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

universe u uGrade uOtherGrade uAccount uValue

/-! ## Route identity and chronological valuation -/

namespace PathRetainingFiniteRoute

/-- The empty retained route is the identity chronology at one world. -/
def nil (theory : Theory.{u, u, u, u}) (Occurrence : Type u)
    (source : theory.World) :
    PathRetainingFiniteRoute theory Occurrence source where
  occurrences := []
  revisions := []
  target := source
  aligned := rfl
  execution := .nil source

end PathRetainingFiniteRoute

/-- Evaluate an occurrence valuation on the exact physical occurrence
chronology retained by a route. -/
def occurrenceGrade
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (valuation : Valuation.{u, uGrade} Occurrence)
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Option valuation.Grade :=
  valuation.historyGrade route.occurrences

/-- Evaluate a revision valuation on the exact named semantic chronology. -/
def revisionGrade
    {theory : Theory.{u, u, u, u}}
    (valuation : Valuation.{u, uGrade} theory.Revision)
    {Occurrence : Type u} {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Option valuation.Grade :=
  valuation.historyGrade route.revisions

@[simp] theorem occurrenceGrade_nil
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (valuation : Valuation.{u, uGrade} Occurrence)
    (source : theory.World) :
    occurrenceGrade valuation
        (PathRetainingFiniteRoute.nil theory Occurrence source) =
      some valuation.algebra.unit :=
  Valuation.historyGrade_nil valuation

@[simp] theorem revisionGrade_nil
    {theory : Theory.{u, u, u, u}}
    (valuation : Valuation.{u, uGrade} theory.Revision)
    {Occurrence : Type u} (source : theory.World) :
    revisionGrade valuation
        (PathRetainingFiniteRoute.nil theory Occurrence source) =
      some valuation.algebra.unit :=
  Valuation.historyGrade_nil valuation

/-- Occurrence observations compose over retained route composition. -/
theorem occurrenceGrade_append
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (valuation : Valuation.{u, uGrade} Occurrence)
    {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    occurrenceGrade valuation (earlier.append later) =
      (occurrenceGrade valuation earlier).bind fun left =>
        (occurrenceGrade valuation later).bind fun right =>
          valuation.algebra.op left right :=
  Valuation.historyGrade_append valuation earlier.occurrences later.occurrences

/-- Named-revision observations compose over the same route boundary. -/
theorem revisionGrade_append
    {theory : Theory.{u, u, u, u}}
    (valuation : Valuation.{u, uGrade} theory.Revision)
    {Occurrence : Type u} {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    revisionGrade valuation (earlier.append later) =
      (revisionGrade valuation earlier).bind fun left =>
        (revisionGrade valuation later).bind fun right =>
          valuation.algebra.op left right :=
  Valuation.historyGrade_append valuation earlier.revisions later.revisions

/-- Product valuation retains two independent coordinates and fails if either
coordinate refuses the route. -/
theorem occurrenceGrade_prod
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (left : Valuation.{u, uGrade} Occurrence)
    (right : Valuation.{u, uOtherGrade} Occurrence)
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    occurrenceGrade (left.prod right) route =
      (occurrenceGrade left route).bind fun leftGrade =>
        (occurrenceGrade right route).bind fun rightGrade =>
          some (leftGrade, rightGrade) :=
  Valuation.prod_historyGrade left right route.occurrences

/-- Erasing a total auxiliary coordinate recovers the original route
observation exactly.  Adding telemetry does not change the underlying value
axis. -/
theorem map_fst_occurrenceGrade_prod_of_right_total
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (left : Valuation.{u, uGrade} Occurrence)
    (right : Valuation.{u, uOtherGrade} Occurrence)
    (total : right.IsTotal) {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Option.map Prod.fst (occurrenceGrade (left.prod right) route) =
      occurrenceGrade left route :=
  Valuation.map_fst_prod_historyGrade_of_right_total left right total
    route.occurrences

/-- Proof-relevant path erasure does not alter the retained occurrence list
seen by an occurrence valuation. -/
@[simp] theorem occurrenceGrade_erase
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    (valuation : Valuation.{u, uGrade} Occurrence)
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    valuation.historyGrade route.erase.occurrences =
      occurrenceGrade valuation route :=
  rfl

/-! ## Exact chronology and local value attachment -/

/-- Exact chronology is itself a route valuation. -/
abbrev occurrenceChronology (Occurrence : Type u) :
    Valuation.{u, u} Occurrence :=
  chronological id

/-- Folding the exact chronology valuation returns its input list. -/
theorem chronology_historyGrade {Occurrence : Type u}
    (occurrences : List Occurrence) :
    (occurrenceChronology Occurrence).historyGrade occurrences =
      some occurrences := by
  induction occurrences with
  | nil => rfl
  | cons occurrence rest inductionHypothesis =>
      simp only [Valuation.historyGrade_cons]
      change
        (some [occurrence]).bind (fun head : List Occurrence =>
          ((occurrenceChronology Occurrence).historyGrade rest).bind
            fun tail => some (head ++ tail)) =
          some (occurrence :: rest)
      rw [inductionHypothesis]
      rfl

/-- Chronological valuation returns the exact retained occurrence list. -/
@[simp] theorem occurrenceGrade_chronology
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    occurrenceGrade (occurrenceChronology Occurrence) route =
      some route.occurrences :=
  chronology_historyGrade route.occurrences

/-- The occurrence bag is a deliberately coarser view than chronology: it
retains multiplicity but forgets order. -/
def occurrenceBag
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Multiset Occurrence :=
  route.occurrences

@[simp] theorem occurrenceBag_append
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    occurrenceBag (earlier.append later) =
      occurrenceBag earlier + occurrenceBag later := by
  simp [occurrenceBag, PathRetainingFiniteRoute.append]

/-- Attach a local value to every retained occurrence without changing route
identity or occurrence multiplicity. -/
def valuedOccurrenceBag
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World} {Value : Type uValue}
    (value : Occurrence -> Value)
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    Multiset (Occurrence × Value) :=
  attachValueFamily value (occurrenceBag route)

/-- Candidate-local value attachment is compositional over route append. -/
theorem valuedOccurrenceBag_append
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World} {Value : Type uValue}
    (value : Occurrence -> Value)
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    valuedOccurrenceBag value (earlier.append later) =
      valuedOccurrenceBag value earlier + valuedOccurrenceBag value later := by
  rw [valuedOccurrenceBag, occurrenceBag_append]
  exact attachValueFamily_distributesOverChoice value _ _

/-- Local value attachment preserves the route's occurrence count exactly. -/
@[simp] theorem valuedOccurrenceBag_card
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World} {Value : Type uValue}
    (value : Occurrence -> Value)
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    (valuedOccurrenceBag value route).card = route.occurrences.length := by
  rw [valuedOccurrenceBag, attachValueFamily_card]
  simp [occurrenceBag]

/-! ## Additive cost observes demand but does not supply a purse -/

/-- An additive route grade is exactly the positional demand of the retained
occurrence history. -/
theorem additive_occurrenceGrade_eq_batchDemand
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {Account : Type uAccount} [AddMonoid Account]
    (demand : Occurrence -> Account) {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    occurrenceGrade (additive demand) route =
      some (batchDemand demand route.occurrences) :=
  additive_historyGrade_eq_batchDemand demand route.occurrences

/-- Supplying the exact demand as a source account constructs an independent
funding witness for the route. -/
def exactRouteFunding
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {Account : Type uAccount} [AddMonoid Account]
    (demand : Occurrence -> Account) {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    BatchSeparation Account demand (batchDemand demand route.occurrences)
      route.occurrences :=
  exactFunding demand route.occurrences

/-! ## Separating canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary

/-- Short names for the two colliding retained routes used throughout the
separation results. -/
abbrev collisionTheory :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary.collisionTheory
abbrev falseRoute :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary.falseRoute
abbrev trueRoute :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary.trueRoute
abbrev falseWitness :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary.falseWitness
abbrev trueWitness :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge.Canary.trueWitness

@[simp] theorem falseRoute_occurrences : falseRoute.occurrences = [0] :=
  rfl

@[simp] theorem trueRoute_occurrences : trueRoute.occurrences = [1] :=
  rfl

/-- Count every retained occurrence once. -/
abbrev countValuation : Valuation Nat := additive fun _ => 1

/-- Distinct retained routes may have the same complete additive grade. -/
theorem distinct_routes_same_count_grade :
    falseWitness ≠ trueWitness /\
      occurrenceGrade countValuation falseRoute = some 1 /\
      occurrenceGrade countValuation trueRoute = some 1 := by
  constructor
  · exact retained_witnesses_distinct
  · decide

/-- Consequently an additive grade is not a faithful encoding of the
occurrence-retaining route. -/
theorem count_grade_projection_not_injective :
    Not (Function.Injective
      (fun witness : retainedFiniteRoute collisionTheory Nat () () =>
        occurrenceGrade countValuation witness.1)) := by
  intro injective
  apply retained_witnesses_distinct
  apply injective
  decide

/-- A positive exact cost observation does not mint the source account needed
to fund the route. -/
theorem positive_grade_does_not_fund_route :
    occurrenceGrade countValuation falseRoute = some 1 /\
      Not (Nonempty
        (BatchSeparation Nat (fun _ : Nat => 1) 0 falseRoute.occurrences)) := by
  constructor
  · decide
  · rintro ⟨funding⟩
    have source := funding.source_eq
    have demandValue :
        batchDemand (fun _ : Nat => 1) falseRoute.occurrences = 1 := by
      simp [batchDemand]
    rw [demandValue] at source
    omega

/-- A simple rank used to distinguish whole-family choice from local value
attachment. -/
def rank : Nat -> Nat := id

/-- Resolving each route separately retains the low occurrence, while
resolving their concatenation removes it.  Whole-race choice therefore does
not compose like a displayed route valuation. -/
theorem max_choice_does_not_preserve_route_append :
    maxSelector rank (occurrenceBag (falseRoute.append trueRoute)) ≠
      maxSelector rank (occurrenceBag falseRoute) +
        maxSelector rank (occurrenceBag trueRoute) := by
  classical
  intro equality
  have lowAlone : 0 ∈ maxSelector rank (occurrenceBag falseRoute) := by
    rw [maxSelector_isMaxSelection]
    simp [occurrenceBag, rank]
  have lowSeparate :
      0 ∈ maxSelector rank (occurrenceBag falseRoute) +
        maxSelector rank (occurrenceBag trueRoute) :=
    Multiset.mem_add.mpr (Or.inl lowAlone)
  have lowCombined :
      0 ∈ maxSelector rank
        (occurrenceBag (falseRoute.append trueRoute)) := by
    rw [equality]
    exact lowSeparate
  have maximal :=
    (maxSelector_isMaxSelection rank
      (occurrenceBag (falseRoute.append trueRoute)) 0).mp lowCombined
  have highInCombined :
      1 ∈ occurrenceBag (falseRoute.append trueRoute) := by
    rw [occurrenceBag_append]
    simp [occurrenceBag]
  have impossible := maximal.2 1 highInCombined
  simp [rank] at impossible

end Canary

/-! ## Axiom audit -/

#print axioms occurrenceGrade_append
#print axioms revisionGrade_append
#print axioms occurrenceGrade_prod
#print axioms map_fst_occurrenceGrade_prod_of_right_total
#print axioms occurrenceGrade_chronology
#print axioms valuedOccurrenceBag_append
#print axioms additive_occurrenceGrade_eq_batchDemand
#print axioms Canary.count_grade_projection_not_injective
#print axioms Canary.positive_grade_does_not_fund_route
#print axioms Canary.max_choice_does_not_preserve_route_append

end Mettapedia.GSLT.LanguageDef.GSLTIL.DisplayedRouteValuation
