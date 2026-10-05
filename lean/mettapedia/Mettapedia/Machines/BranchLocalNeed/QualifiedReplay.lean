import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.GSLT.Distinction.LevelAccounts

/-!
# Qualified replay of Need histories

The Need machine's production account is a run account of its event
histories (`NeedWeightedResumption.coefficientAccount` with production-only
factors).  Replaying an alternative history between the same two machine
states is therefore qualified, for that account, exactly when the two
histories' production ledgers denote the same coefficient
(`replay_iff_production_ledger`); and then the replay is qualified inside any
parent history (`replay_in_parent`).  Equal endpoints are not the condition:
the coefficients are monoid elements without inverses, so no potential exists
whose differences they are (for an ordered account two routes with the same
endpoints and trace are not interchangeable,
`LevelAccounts.Controls.grid_ordered_replay_not_qualified`).

The transition work of the same histories is a second, independent reading
(`historyEventPath_length`); a replay may preserve the production account and
change it, or keep it and change the production account.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Machines.BranchLocalNeed.NeedQualifiedReplay

open Mettapedia.GSLT.Distinction.LevelAccounts
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws (CompletedReceipt)
open Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Reference (pathMachine)
open Mettapedia.Algebra.SharedCoefficientLedger (denote)

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect V : Type} [Monoid V]
variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- **Replaying an alternative Need history is qualified for the production
account exactly when the two production ledgers denote the same
coefficient.** -/
theorem replay_iff_production_ledger
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (first second : Quiver.Path before after) :
    QualifiedReplay (coefficientAccount spec (productionCoefficient coefficient) initial)
        (source := before) (target := after) first second ↔
      denote (productionLedger spec coefficient (historyEventPath spec initial first)) =
        denote (productionLedger spec coefficient (historyEventPath spec initial second)) := by
  unfold QualifiedReplay
  rw [production_history_account, production_history_account]

/-- **A qualified replay stays qualified inside any parent history.** -/
theorem replay_in_parent
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {start before after finish : RewriteEventHistory.State (system (pathMachine spec initial))}
    (first second : Quiver.Path before after)
    (sameLedger : denote (productionLedger spec coefficient (historyEventPath spec initial first)) =
      denote (productionLedger spec coefficient (historyEventPath spec initial second)))
    (prefixHistory : Quiver.Path start before) (suffixHistory : Quiver.Path after finish) :
    denote (productionLedger spec coefficient
        (historyEventPath spec initial ((prefixHistory.comp first).comp suffixHistory))) =
      denote (productionLedger spec coefficient
        (historyEventPath spec initial ((prefixHistory.comp second).comp suffixHistory))) := by
  have qualified := ((replay_iff_production_ledger spec coefficient initial first second).mpr
    sameLedger).inContext (C := RewriteEventHistory.HistoryCategory (system (pathMachine spec initial)))
    prefixHistory suffixHistory
  unfold QualifiedReplay at qualified
  rw [← production_history_account, ← production_history_account]
  have assocFirst : (prefixHistory.comp first).comp suffixHistory =
      prefixHistory.comp (first.comp suffixHistory) := Quiver.Path.comp_assoc _ _ _
  have assocSecond : (prefixHistory.comp second).comp suffixHistory =
      prefixHistory.comp (second.comp suffixHistory) := Quiver.Path.comp_assoc _ _ _
  rw [assocFirst, assocSecond]
  exact qualified

end Mettapedia.Machines.BranchLocalNeed.NeedQualifiedReplay
