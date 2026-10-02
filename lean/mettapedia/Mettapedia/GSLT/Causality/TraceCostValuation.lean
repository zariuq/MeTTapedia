import Mettapedia.GSLT.Causality.Mazurkiewicz
import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Scope.ConsumerDescent

/-!
# Which costs are properties of the trace, and which of the schedule

A parallel runtime may execute independent occurrences in either order. A
cost is a property of *what was done* only if it takes the same value on
both routes of every independence tile — that is, only if it descends to the
Mazurkiewicz trace (`Mazurkiewicz.Descends`). Otherwise it is a property of
the particular interleaving, and a scheduler is free to change it.

* `siteCostValuation` — charge each occurrence by its **site** alone. With a
  commutative cost carrier this factors through the site bag
  (`siteCostValuation_onPath`), so it descends
  (`siteCostValuation_descends`). Total work is the instance with unit or
  per-site cost.
* `grid_stateCost_not_descends` — charge the *same* occurrences by the state
  they fire in, and descent fails: the two routes of a single tile cost
  different amounts. A state-dependent cost is a schedule observation, not a
  trace invariant. It can still measure work actually spent in that schedule;
  transferring an exact total or a bound to another schedule needs a separate
  preservation or bounding law.
* `grid_siteWord_order_not_trace` recalls that an ordered record of sites is
  also a schedule observation; together the two controls bracket exactly what
  a commutative, occurrence-identity-keyed cost buys.

The work/span side: work is trace-invariant, but *span* is not a path
valuation at all — every serialisation of the tile has two steps, while the
parallel composition of the two independent occurrences has span one
(`tile_work_invariant_span_not`). Span belongs to the dependency structure,
and a chosen schedule's wave count is a third quantity again, bounded below
by span.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.TraceCostValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.Mazurkiewicz
open Mettapedia.GSLT.Core.NonFactorization

universe uSite uEvent

variable {theory : GSLT}

/-- Trace-invariance is the existing recovery-function criterion for the
actual diamond quotient. No representative or extra descent law is chosen. -/
theorem valuation_factors_trace_iff
    {P : InteractionPresentation.{uSite, uEvent} theory}
    (indep : SiteIndependence P) {A : Type*} [AddMonoid A]
    (valuation : OccurrenceValuation P A) :
    (∀ source target : theory.Term,
      Factors (mkTrace (P := P) (indep := indep) (s := source) (t := target))
        valuation.onPath) ↔ Descends indep valuation := by
  constructor
  · intro factors source target first second related
    exact (factors source target).constantOnFibers first second (mkTrace_sound related)
  · intro descends source target
    exact (Mettapedia.GSLT.Scope.function_descends_iff
      (diamondSetoid indep source target) valuation.onPath).mpr
        (fun _ _ related => descends _ _ related)

/-- Charge every occurrence by its site alone. -/
def siteCostValuation (P : InteractionPresentation.{uSite, uEvent} theory)
    {A : Type*} [AddCommMonoid A] (cost : P.Site → A) : OccurrenceValuation P A where
  grade := fun o => cost o.site

/-- **A site cost factors through the site bag.** -/
theorem siteCostValuation_onPath
    {P : InteractionPresentation.{uSite, uEvent} theory}
    {A : Type*} [AddCommMonoid A] (cost : P.Site → A)
    {s t : theory.Term} (p : OccurrencePath P s t) :
    (siteCostValuation P cost).onPath p =
      (((bagValuation P).onPath p).map cost).sum := by
  induction p with
  | refl => simp [OccurrenceValuation.onPath]
  | cons o rest ih =>
      simp only [OccurrenceValuation.onPath, ih]
      simp [bagValuation, siteCostValuation]

/-- **Every commutative site cost is a trace invariant.** -/
theorem siteCostValuation_descends
    {P : InteractionPresentation.{uSite, uEvent} theory}
    (indep : SiteIndependence P) {A : Type*} [AddCommMonoid A] (cost : P.Site → A) :
    Descends indep (siteCostValuation P cost) := by
  refine (descends_iff_tile_invariant indep _).2 ?_
  intro src tl
  rw [siteCostValuation_onPath, siteCostValuation_onPath,
    bagValuation_tile_invariant indep tl]

/-- The trace view determines every commutative site-cost observation. -/
theorem siteCostValuation_factors_trace
    {P : InteractionPresentation.{uSite, uEvent} theory}
    (indep : SiteIndependence P) {A : Type*} [AddCommMonoid A] (cost : P.Site → A)
    (source target : theory.Term) :
    Factors (mkTrace (P := P) (indep := indep) (s := source) (t := target))
      (siteCostValuation P cost).onPath :=
  (valuation_factors_trace_iff indep (siteCostValuation P cost)).mpr
    (siteCostValuation_descends indep cost) source target

/-- Work: one unit per occurrence. -/
def workValuation (P : InteractionPresentation.{uSite, uEvent} theory) :
    OccurrenceValuation P ℕ :=
  siteCostValuation P (fun _ => 1)

theorem work_descends {P : InteractionPresentation.{uSite, uEvent} theory}
    (indep : SiteIndependence P) : Descends indep (workValuation P) :=
  siteCostValuation_descends indep _

/-! ## Controls -/

/-- A cost that reads the state an occurrence fires in: a horizontal flip is
cheap from an unflipped column and expensive otherwise. -/
def gridStateCost : OccurrenceValuation gridPresentation ℕ where
  grade := fun {s _} o =>
    match o.site with
    | .horiz => if s.2 then 5 else 1
    | .vert => 1

/-- **Negative control: a state-dependent cost is not a trace invariant.**
The two routes of the grid tile perform the same two occurrences, yet cost
`2` and `6`. -/
theorem grid_stateCost_not_descends : ¬ Descends gridIndep gridStateCost := by
  intro h
  have := ((descends_iff_tile_invariant gridIndep gridStateCost).1 h) gridTile
  revert this
  decide

/-- The same trace can cost two or six units, so the trace view cannot
reconstruct this measured schedule cost. -/
theorem grid_stateCost_not_factors_trace :
    ¬ Factors
      (mkTrace (P := gridPresentation) (indep := gridIndep)
        (s := gridOrigin) (t := (true, true)))
      gridStateCost.onPath :=
  NonTrivialFiber.not_factors
    ⟨gridTile.path, gridTile.pathSwap', mkTrace_sound (.swap gridTile), by decide⟩

/-- **Positive control**: on the same tile, work is `2` along both routes. -/
theorem grid_work_both_routes :
    (workValuation gridPresentation).onPath gridTile.path = 2 ∧
      (workValuation gridPresentation).onPath gridTile.pathSwap' = 2 := by
  constructor <;> decide

/-- Recalled: an ordered site record is a schedule observation. -/
theorem grid_siteWord_order_not_trace :
    ¬ Descends gridIndep (siteListValuation (P := gridPresentation)) :=
  grid_siteList_not_descends

open Mettapedia.Algebra in
/-- **Work is the same on every serialisation; span is not a serialisation
property.**  Two independent unit occurrences cost work `2` on either route,
and a serial route has span `2`; composing them in parallel keeps work `2` but
has span `1`. -/
theorem tile_work_invariant_span_not :
    WorkSpan.sequential ⟨1, 1⟩ ⟨1, 1⟩ = ⟨2, 2⟩ ∧
      WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩ = ⟨2, 1⟩ := by
  constructor <;> rfl

end Mettapedia.GSLT.Causality.TraceCostValuation

#print axioms Mettapedia.GSLT.Causality.TraceCostValuation.siteCostValuation_descends
#print axioms Mettapedia.GSLT.Causality.TraceCostValuation.grid_stateCost_not_descends
