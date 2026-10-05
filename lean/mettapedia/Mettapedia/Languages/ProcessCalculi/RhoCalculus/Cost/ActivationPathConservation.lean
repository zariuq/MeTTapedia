import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedRefinement

/-!
# Physical resource conservation along the existing declarative Cost paths

Resource separation is preserved by the actual funded relation. Consequently
the cells physically present in a configuration bound the number of firings.
The exact signature inventory additionally records the authority atoms stored
in those cells; its depletion is compared with the path's existing ordered
demand list before applying any numerical account.

Both are readouts of the law of runs of the funded resource system. In general
the signatures stored in the purses a contractum releases join the balance; on
separated configurations no contractum releases a purse, and the stored
signatures drop by the demands alone. A declarative path is a run of the funded
resource system with the same demands.

These results concern `CostStepPath`. Transport to an executable `CostPath`
requires preservation through its explicit structural-normalization seams.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

/-- The multiset of signing atoms physically stored in all cells of a purse.
Order is deliberately forgotten by this observation, not by the stack itself. -/
def CostStack.storedSignatures {Ground : Type u} : CostStack Ground → CostSig Ground
  | .empty => 0
  | .cons head tail => head + tail.storedSignatures

/-- Stored signing atoms in the actual top-level purses of a configuration. -/
abbrev CostConfig.storedSignatures {Ground : Type u}
    (config : CostConfig Ground) : CostSig Ground :=
  config.physicalPurseMeasure CostStack.storedSignatures

section PaidFiring

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-- The signatures stored in a stack are the sum of its cells. -/
theorem CostStack.storedSignatures_eq_sum {Ground : Type u} :
    ∀ stack : CostStack Ground, stack.storedSignatures = stack.toList.sum
  | .empty => rfl
  | .cons head tail => by
      rw [CostStack.storedSignatures, CostStack.toList, List.sum_cons,
        CostStack.storedSignatures_eq_sum tail]

/-- The signatures stored in purses are the sum of their cells. -/
theorem sum_cellBag {Ground : Type u}
    (purses : Multiset (CostName Ground × List (CostSig Ground))) :
    (cellBag purses).sum =
      (purses.map fun purse => (CostStack.ofList purse.2).storedSignatures).sum := by
  induction purses using Multiset.induction_on with
  | empty => rfl
  | cons purse purses ih =>
      rw [cellBag_cons, Multiset.sum_add, ih, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_coe, CostStack.storedSignatures_eq_sum, CostStack.toList_ofList]

/-- The signatures stored in a configuration are the sum of the cells of its
purses. -/
theorem CostConfig.storedSignatures_eq {Ground : Type u} (config : CostConfig Ground) :
    config.storedSignatures = (cellBag config.purses).sum := by
  rw [CostConfig.storedSignatures, CostConfig.physicalPurseMeasure_eq_purses, sum_cellBag]

/-- **Along a run of funded firings, the stored signatures drop by what the run
spends**, apart from the signatures stored in the purses the contracta release.
The signatures stored before a run, with those stored in the released purses,
are the signatures stored after it with the spends of its events. -/
theorem costResource_run_storedSignatures {Ground : Type u} [DecidableEq Ground]
    {M N : CostConfig Ground} (p : OccurrencePath (costResourceSystem Ground).presentation M N) :
    M.storedSignatures + ((costResourceSystem Ground).instanceValuation
        fun event => event.val.contractum.storedSignatures).onPath p =
      N.storedSignatures + ((costResourceSystem Ground).instanceValuation
        fun event => event.val.spend).onPath p := by
  have summed := congrArg Multiset.sum (costResource_run_cells_taken p)
  rw [Multiset.sum_add, Multiset.sum_add,
    (costResourceSystem Ground).instanceValuation_map Multiset.sum Multiset.sum_zero
      Multiset.sum_add,
    (costResourceSystem Ground).instanceValuation_map Multiset.sum Multiset.sum_zero
      Multiset.sum_add] at summed
  rw [CostConfig.storedSignatures_eq, CostConfig.storedSignatures_eq,
    (costResourceSystem Ground).instanceValuation_congr
      (fun event => CostConfig.storedSignatures_eq event.val.contractum) p,
    (costResourceSystem Ground).instanceValuation_congr
      (g := fun event => (event.val.funding.chosen.map SelectedPurseHead.head).sum)
      (fun event => (CostedEvent.sum_selected_heads event.val).symm) p]
  exact summed

/-- **The stored signatures drop by the spend of a funded firing**, apart from
the signatures stored in the purses its contractum releases. -/
theorem costResource_storedSignatures {Ground : Type u} [DecidableEq Ground]
    (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    config.storedSignatures + event.val.contractum.storedSignatures =
      CostConfig.storedSignatures ((costResourceSystem Ground).fire config event) +
        event.val.spend := by
  have taken := congrArg Multiset.sum (costResource_cells_taken config event enabled)
  rw [Multiset.sum_add, Multiset.sum_add, CostedEvent.sum_selected_heads] at taken
  rw [CostConfig.storedSignatures_eq, CostConfig.storedSignatures_eq,
    CostConfig.storedSignatures_eq]
  exact taken

/-- The exact cover's demand is precisely the signature content removed from
the selected heads; every tail and unselected purse is retained. -/
theorem LocatedTokenCover.stored_signatures_balance {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    (available.map fun purse => purse.stack.storedSignatures).sum =
      (residual.map fun purse => purse.stack.storedSignatures).sum + demand := by
  classical
  have taken := congrArg Multiset.sum cover.cells_taken
  rw [Multiset.sum_add, ← cover.demand_eq, sum_cellBag, sum_cellBag, Multiset.map_map,
    Multiset.map_map] at taken
  simpa only [Function.comp_def, LocatedPurse.toPurse, CostStack.ofList_toList] using taken

/-- Actual stored signatures, rather than an independently initialized budget,
decrease by the labelled spend of the existing funded step. -/
theorem CostStep.stored_signatures_balance {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    source.storedSignatures = target.storedSignatures + spend := by
  classical
  obtain ⟨entry, rfl, rfl, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  have balance := costResource_storedSignatures source entry.2 enabled
  have released : entry.2.val.contractum.storedSignatures = 0 :=
    contractum_physicalPurseMeasure_eq_zero _ separated entry.2 enabled
  rwa [released, add_zero] at balance

/-- **A declarative path is a run of the funded resource system**, with the
same demands. -/
theorem CostStepPath.exists_run {Ground : Type u} [DecidableEq Ground]
    {source target : CostConfig Ground} :
    (path : CostStepPath source target) →
      ∃ run : OccurrencePath (costResourceSystem Ground).presentation source target,
        ((costResourceSystem Ground).instanceValuation fun event => event.val.spend).onPath run =
          path.demands.sum
  | .done _ => ⟨.refl _, rfl⟩
  | .fire step rest => by
      obtain ⟨entry, -, spent, enabled, fired⟩ := costStep_iff_exists_enabled_resource.mp step
      obtain ⟨run, restSpent⟩ := CostStepPath.exists_run rest
      refine ⟨.cons ⟨entry.1, ⟨entry.2, enabled, fired⟩⟩ run, ?_⟩
      change entry.2.val.spend + _ = _
      rw [restSpent, CostStepPath.demands, List.sum_cons]
      exact congrArg (· + _) spent

/-- Along a run from a separated configuration, the contracta release no
purse readout. -/
theorem costResource_run_released_eq_zero {Ground : Type u} [DecidableEq Ground]
    {Measure : Type v} [AddCommMonoid Measure] (weight : CostStack Ground → Measure)
    {M N : CostConfig Ground} (p : OccurrencePath (costResourceSystem Ground).presentation M N)
    (separated : M.ResourceSeparated) :
    ((costResourceSystem Ground).instanceValuation
      fun event => event.val.contractum.physicalPurseMeasure weight).onPath p = 0 :=
  (costResourceSystem Ground).instanceValuation_eq_zero _
    (fun _ {_} event kept enabled => costResource_preserves_resourceSeparated event kept enabled)
    (fun _ {_} event kept enabled =>
      contractum_physicalPurseMeasure_eq_zero weight kept event enabled)
    p separated

end PaidFiring

namespace CostStepPath

/-- Every intermediate funded step preserves the code/resource boundary. -/
theorem preserves_resourceSeparated {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) : target.ResourceSeparated := by
  induction path with
  | done => exact separated
  | fire step rest induction =>
      exact induction (step.preserves_resourceSeparated separated)

/-- A finite initial collection of purse cells bounds the number of actual
funded firings. Split funding can consume more than one cell per firing. -/
theorem length_add_remaining_cells_le {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) :
    path.length + target.physicalPurseCells ≤ source.physicalPurseCells := by
  induction path with
  | done => simp [length]
  | fire step rest induction =>
      have remaining := induction (step.preserves_resourceSeparated separated)
      obtain ⟨consumed, positive, balance⟩ := step.physical_cells_decrease separated
      simp only [length]
      omega

/-- Empty purses remain observable, so firing preserves purse occurrences
while decreasing their stored contents. -/
theorem physical_purse_occurrences_preserved {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) :
    source.physicalPurseOccurrences = target.physicalPurseOccurrences := by
  classical
  obtain ⟨run, -⟩ := path.exists_run
  have kept := costResource_run_physicalPurseOccurrences run
  rwa [costResource_run_released_eq_zero _ run separated, add_zero] at kept

/-- With no initial cells, no funded firing occurs. This says nothing about
unmetered structural normalization or external replenishment. -/
theorem length_zero_of_no_cells {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) (empty : source.physicalPurseCells = 0) :
    path.length = 0 := by
  have bounded := path.length_add_remaining_cells_le separated
  omega

/-- Physical configuration accounting agrees with the exact demand list of
the existing path. No prices, refunds, or order on accounts are required. -/
theorem stored_signatures_balance {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) :
    source.storedSignatures = target.storedSignatures + path.demands.sum := by
  classical
  obtain ⟨run, spent⟩ := path.exists_run
  have balance := costResource_run_storedSignatures run
  rwa [costResource_run_released_eq_zero _ run separated, add_zero, spent] at balance

/-- Every additive interpretation of signatures inherits physical
conservation. The interpreter records value; it does not authorize firing. -/
theorem account_balance {Ground : Type u} {Account : Type v} [AddCommMonoid Account]
    (price : CostSig Ground →+ Account) {source target : CostConfig Ground}
    (path : CostStepPath source target) (separated : source.ResourceSeparated) :
    price source.storedSignatures =
      price target.storedSignatures + (path.demands.map price).sum := by
  rw [path.stored_signatures_balance separated, map_add, map_list_sum]

end CostStepPath

namespace PaidControls

open Mettapedia.GSLT.Causality.ResourceInteraction

/-- **Stored signatures balance only with the released purse.** The releasing
meeting spends `{7}`, and its contractum releases a purse storing `{7}`: the
stored signatures are the same before and after. Its code holds a purse, so the
configuration is not separated. -/
theorem released_signatures_balance :
    beforeRelease.storedSignatures + releasingPaid.val.contractum.storedSignatures =
        CostConfig.storedSignatures ((costResourceSystem ℕ).fire beforeRelease releasingPaid) +
          releasingPaid.val.spend ∧
      beforeRelease.storedSignatures ≠
        CostConfig.storedSignatures ((costResourceSystem ℕ).fire beforeRelease releasingPaid) +
          releasingPaid.val.spend :=
  ⟨costResource_storedSignatures beforeRelease releasingPaid (by unfold System.Enables; decide),
    by unfold System.fire; decide⟩

end PaidControls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
