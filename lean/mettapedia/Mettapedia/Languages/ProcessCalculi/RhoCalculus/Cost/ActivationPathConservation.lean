import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedRefinement

/-!
# Physical resource conservation along the existing declarative Cost paths

Resource separation is preserved by the actual funded relation. Consequently
the cells physically present in a configuration bound the number of firings.
The exact signature inventory additionally records the authority atoms stored
in those cells; its depletion is compared with the path's existing ordered
demand list before applying any numerical account.

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

/-- The exact cover's demand is precisely the signature content removed from
the selected heads; every tail and unselected purse is retained. -/
theorem LocatedTokenCover.stored_signatures_balance {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    (available.map fun purse => purse.stack.storedSignatures).sum =
      (residual.map fun purse => purse.stack.storedSignatures).sum + demand := by
  simp only [cover.available_eq, cover.residual_eq, cover.demand_eq,
    Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
    CostStack.storedSignatures, Multiset.sum_map_add]
  ac_rfl

/-- Actual stored signatures, rather than an independently initialized budget,
decrease by the labelled spend of the existing funded step. -/
theorem CostStep.stored_signatures_balance {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    source.storedSignatures = target.storedSignatures + spend := by
  cases step with
  | wholeRecvSend valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := separated.1.2.wholeRecvSend_payloads
      simp only [CostConfig.storedSignatures, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.stored_signatures_balance]
      ac_rfl
  | wholeSendRecv valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := separated.1.2.wholeSendRecv_payloads
      simp only [CostConfig.storedSignatures, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.stored_signatures_balance]
      ac_rfl
  | split recvValid sendValid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have bodyFree := separated.1.1.2.recv_body
      have payloadFree := separated.1.2.send_payload
      simp only [CostConfig.storedSignatures, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (bodyFree.substitute payloadFree 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.stored_signatures_balance]
      ac_rfl

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
  induction path with
  | done => rfl
  | fire step rest induction =>
      exact (step.physical_purse_occurrences_preserved separated).trans
        (induction (step.preserves_resourceSeparated separated))

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
  induction path with
  | done => simp [demands]
  | fire step rest induction =>
      rw [step.stored_signatures_balance separated,
        induction (step.preserves_resourceSeparated separated)]
      simp only [demands, List.sum_cons]
      ac_rfl

/-- Every additive interpretation of signatures inherits physical
conservation. The interpreter records value; it does not authorize firing. -/
theorem account_balance {Ground : Type u} {Account : Type v} [AddCommMonoid Account]
    (price : CostSig Ground →+ Account) {source target : CostConfig Ground}
    (path : CostStepPath source target) (separated : source.ResourceSeparated) :
    price source.storedSignatures =
      price target.storedSignatures + (path.demands.map price).sum := by
  rw [path.stored_signatures_balance separated, map_add, map_list_sum]

end CostStepPath

#print axioms CostStep.stored_signatures_balance
#print axioms CostStepPath.length_add_remaining_cells_le
#print axioms CostStepPath.stored_signatures_balance
#print axioms CostStepPath.account_balance

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
