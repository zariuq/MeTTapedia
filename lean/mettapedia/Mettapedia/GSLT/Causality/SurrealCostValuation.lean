import Mettapedia.GSLT.Causality.TraceCostValuation
import Mettapedia.SetTheory.Surreal.DyadicEmbedding

/-!
# Surreal readings of dyadic occurrence costs

The additive order embedding of dyadics into surreals reads actual occurrence
paths. It preserves concatenation, reflects equality of totals and budget
comparisons, and preserves and reflects descent through independence diamonds.
Budgeted path fibres are equivalent with the complete occurrence path retained.

These theorems concern the dyadic image and finite paths in an arbitrary GSLT
presentation. Full surreal-library import, material encodings of its numbers,
infinite-run totals and well-founded termination ranks are separate constructions.
Equality of cost readings supplies no equality of occurrence receipts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.SurrealCostValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.Mazurkiewicz

abbrev Dyadic := Mettapedia.Algebra.Order.Dyadic
abbrev Surreal := Mettapedia.SetTheory.SignExpansion.Surreal

open Mettapedia.SetTheory.SignExpansion.Surreal

universe uSite uEvent
variable {theory : GSLT} {P : InteractionPresentation.{uSite, uEvent} theory}

/-- Read every retained occurrence charge through the additive embedding. -/
noncomputable def read (valuation : OccurrenceValuation P Dyadic) :
    OccurrenceValuation P Surreal where
  grade occurrence := toSurreal (valuation.grade occurrence)

theorem read_onPath (valuation : OccurrenceValuation P Dyadic)
    {source target : theory.Term} (path : OccurrencePath P source target) :
    (read valuation).onPath path = toSurreal (valuation.onPath path) := by
  induction path with
  | refl => exact toSurreal_zero.symm
  | cons occurrence rest ih =>
      change toSurreal (valuation.grade occurrence) + (read valuation).onPath rest =
        toSurreal (valuation.grade occurrence + valuation.onPath rest)
      rw [ih, toSurreal_add]

theorem read_append (valuation : OccurrenceValuation P Dyadic)
    {source middle target : theory.Term}
    (first : OccurrencePath P source middle) (second : OccurrencePath P middle target) :
    (read valuation).onPath (OccurrencePath.append first second) =
      toSurreal (valuation.onPath first) + toSurreal (valuation.onPath second) := by
  rw [OccurrenceValuation.onPath_append, read_onPath, read_onPath]

theorem cost_equal_iff (valuation : OccurrenceValuation P Dyadic)
    {source target otherSource otherTarget : theory.Term}
    (first : OccurrencePath P source target) (second : OccurrencePath P otherSource otherTarget) :
    (read valuation).onPath first = (read valuation).onPath second ↔
      valuation.onPath first = valuation.onPath second := by
  rw [read_onPath, read_onPath]
  exact toSurreal_inj

theorem budget_iff (valuation : OccurrenceValuation P Dyadic)
    {source target : theory.Term} (path : OccurrencePath P source target) (budget : Dyadic) :
    (read valuation).onPath path ≤ toSurreal budget ↔ valuation.onPath path ≤ budget := by
  rw [read_onPath]
  exact toSurreal_le_iff

/-- Numeric transport preserves the whole path carried by a budget witness. -/
noncomputable def budgetedRunsEquiv (valuation : OccurrenceValuation P Dyadic)
    (source target : theory.Term) (budget : Dyadic) :
    {path : OccurrencePath P source target // (read valuation).onPath path ≤ toSurreal budget} ≃
      {path : OccurrencePath P source target // valuation.onPath path ≤ budget} where
  toFun path := ⟨path.1, (budget_iff valuation path.1 budget).mp path.2⟩
  invFun path := ⟨path.1, (budget_iff valuation path.1 budget).mpr path.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem budgetedRunsEquiv_path (valuation : OccurrenceValuation P Dyadic)
    {source target : theory.Term} {budget : Dyadic}
    (path : {path : OccurrencePath P source target //
      (read valuation).onPath path ≤ toSurreal budget}) :
    (budgetedRunsEquiv valuation source target budget path).1 = path.1 := rfl

/-- The numerical embedding neither repairs nor introduces scheduling dependence. -/
theorem descends_iff (independence : SiteIndependence P)
    (valuation : OccurrenceValuation P Dyadic) :
    Descends independence (read valuation) ↔ Descends independence valuation := by
  constructor
  · intro descends source target first second related
    exact (cost_equal_iff valuation first second).mp (descends first second related)
  · intro descends source target first second related
    exact (cost_equal_iff valuation first second).mpr (descends first second related)

end Mettapedia.GSLT.Causality.SurrealCostValuation
