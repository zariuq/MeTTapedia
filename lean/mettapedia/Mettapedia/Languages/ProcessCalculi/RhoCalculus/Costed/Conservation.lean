import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Path
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Valuation
import Mathlib.Tactic

/-!
# Receipt, account, and budget conservation

All downstream accounts in this module are folds of the one occurrence-level
causal receipt.  Ordered budget acceptance inspects every emitted prefix; it
does not infer safety from a final balance alone.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open scoped BigOperators

universe x

namespace CostPath

/-- The canonical measured causal set presented by a complete path emission. -/
def receipt {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents) :
    CausalReceipt (Fin path.emission.length) String RawCostName :=
  path.emission.toReceipt path.emitted_receipt_valid

/-- The causal receipt's raw measure is the sum of the exact demanded spends
of the executable firings. -/
theorem receipt_rawMeasure_eq_emitted_spend
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents) :
    path.receipt.totalRawMeasure = path.spends.sum := by
  unfold receipt
  rw [ReceiptEmission.toReceipt_totalRawMeasure]
  rw [path.emission_rawSpends_eq_steps]

private theorem additiveFold_list_sum
    {Delta : Type x} [AddCommMonoid Delta]
    (weight : String → Delta) : ∀ spends : List (CostSig String),
    CostSig.additiveFold weight spends.sum =
      (spends.map (CostSig.additiveFold weight)).sum
  | [] => by simp
  | spend :: rest => by
      simp [CostSig.additiveFold_add, additiveFold_list_sum weight rest]

private theorem multiplicativeFold_list_sum
    {Delta : Type x} [CommMonoid Delta]
    (weight : String → Delta) : ∀ spends : List (CostSig String),
    CostSig.multiplicativeFold weight spends.sum =
      (spends.map (CostSig.multiplicativeFold weight)).prod
  | [] => by simp
  | spend :: rest => by
      simp [CostSig.multiplicativeFold_add,
        multiplicativeFold_list_sum weight rest]

/-- Additive effort accounting is exactly the fold of path spends. -/
theorem trace_account_eq_totalCost
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] (weight : String → Delta) :
    path.receipt.totalAdditiveValue weight =
      (path.spends.map (CostSig.additiveFold weight)).sum := by
  unfold CausalReceipt.totalAdditiveValue
  rw [path.receipt_rawMeasure_eq_emitted_spend]
  exact additiveFold_list_sum weight path.spends

/-- Multiplicative and quantale readings use the same operational receipt. -/
theorem trace_multiplicativeAccount_eq_totalCost
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {Delta : Type x} [CommMonoid Delta] (weight : String → Delta) :
    path.receipt.totalMultiplicativeValue weight =
      (path.spends.map (CostSig.multiplicativeFold weight)).prod := by
  unfold CausalReceipt.totalMultiplicativeValue
  rw [path.receipt_rawMeasure_eq_emitted_spend]
  exact multiplicativeFold_list_sum weight path.spends

/-- Ordered per-event additive account. -/
def additiveAccount
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] (weight : String → Delta) : List Delta :=
  path.spends.map (CostSig.additiveFold weight)

namespace OrderedAccount

/-- Cost charged by an arbitrary ordered account prefix. -/
def prefixCost {Delta : Type x} [AddCommMonoid Delta]
    (account : List Delta) (count : Nat) : Delta :=
  (account.take count).sum

/-- Acceptance checks every prefix, not only the final group sum. -/
def PrefixAccepted {Delta : Type x} [AddCommMonoid Delta] [LE Delta]
    (account : List Delta) (initial : Delta) : Prop :=
  ∀ count, count ≤ account.length → prefixCost account count ≤ initial

end OrderedAccount

/-- Cost charged by the first `count` emitted events. -/
def prefixCost
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] (weight : String → Delta)
    (count : Nat) : Delta :=
  (path.additiveAccount weight).take count |>.sum

/-- Every ordered prefix remains within the initial effort-object budget. -/
def PrefixAccepted
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] [LE Delta]
    (weight : String → Delta) (initial : Delta) : Prop :=
  ∀ count, count ≤ (path.additiveAccount weight).length →
    path.prefixCost weight count ≤ initial

theorem prefixAccepted_iff_orderedAccount
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] [LE Delta]
    (weight : String → Delta) (initial : Delta) :
    path.PrefixAccepted weight initial ↔
      OrderedAccount.PrefixAccepted (path.additiveAccount weight) initial := by
  rfl

/-- Final path spend is one of the prefixes checked by acceptance. -/
theorem PrefixAccepted.final_cost_le
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] [LE Delta]
    (weight : String → Delta) (initial : Delta)
    (accepted : path.PrefixAccepted weight initial) :
    (path.additiveAccount weight).sum ≤ initial := by
  simpa [prefixCost] using
    accepted (path.additiveAccount weight).length (le_refl _)

/-- Remaining budget after the complete ordered account. -/
def pathRemainingBudget
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommGroup Delta]
    (weight : String → Delta) (initial : Delta) : Delta :=
  initial - (path.additiveAccount weight).sum

/-- Receipt and path definitions of remaining budget coincide. -/
theorem receipt_remainingBudget_eq_pathRemainingBudget
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {Delta : Type x} [AddCommGroup Delta]
    (weight : String → Delta) (initial : Delta) :
    path.receipt.remainingBudget weight initial =
      path.pathRemainingBudget weight initial := by
  simp [CausalReceipt.remainingBudget, pathRemainingBudget,
    trace_account_eq_totalCost, additiveAccount]

/-- What remains plus what was spent is exactly the initial budget. -/
theorem final_budget_conservation
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommGroup Delta]
    (weight : String → Delta) (initial : Delta) :
    path.pathRemainingBudget weight initial +
        (path.additiveAccount weight).sum = initial := by
  simp [pathRemainingBudget]

/-- Prefix acceptance gives a nonnegative remaining balance at every checked
prefix, including intermediate states that a final-total-only check can miss. -/
theorem PrefixAccepted.prefix_remaining_nonnegative
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type x} [AddCommGroup Delta] [LinearOrder Delta] [AddRightMono Delta]
    (weight : String → Delta) (initial : Delta)
    (accepted : path.PrefixAccepted weight initial)
    (count : Nat) (within : count ≤ (path.additiveAccount weight).length) :
    0 ≤ initial - path.prefixCost weight count :=
  sub_nonneg.mpr (accepted count within)

private theorem sum_get_eq_sum_map {Alpha : Type*} {M : Type*}
    [AddCommMonoid M] (items : List Alpha) (value : Alpha → M) :
    (∑ index : Fin items.length, value (items.get index)) =
      (items.map value).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ]
      change value head + (∑ index : Fin tail.length, value (tail.get index)) =
        value head + (tail.map value).sum
      rw [ih]

/-- Ordered local account at one nominal funding surface. -/
def rawAccountAt
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (surface : RawCostName) : CostSig String :=
  (path.emission.map fun event => event.label.rawSpendAt surface).sum

/-- Per-location restriction of the causal measure is exactly the local fold
of the ordered emission. -/
theorem per_location_restriction_account_conservation
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    (surface : RawCostName) :
    path.receipt.rawMeasureAt surface Finset.univ = path.rawAccountAt surface := by
  simpa [receipt, CausalReceipt.rawMeasureAt, ReceiptEmission.toReceipt,
    rawAccountAt] using
    sum_get_eq_sum_map path.emission
      (fun event => event.label.rawSpendAt surface)

/-- The finitely supported family of ordered local accounts glues exactly to
the path's global raw account. -/
theorem local_accounts_glue_to_global
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents) :
    (∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
      path.rawAccountAt surface) = path.receipt.totalRawMeasure := by
  calc
    (∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
        path.rawAccountAt surface) =
        ∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
          path.receipt.rawMeasureAt surface Finset.univ := by
      apply Finset.sum_congr rfl
      intro surface _member
      exact (path.per_location_restriction_account_conservation surface).symm
    _ = path.receipt.rawMeasure Finset.univ :=
      path.receipt.sum_rawMeasureAt_fundingSurfaces_eq_rawMeasure Finset.univ
    _ = path.receipt.totalRawMeasure := rfl

/-- Additive effort-object readings glue over the same finite location support. -/
theorem additive_local_accounts_glue_to_global
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {Delta : Type x} [AddCommMonoid Delta] (weight : String → Delta) :
    (∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
      CostSig.additiveFold weight (path.rawAccountAt surface)) =
      path.receipt.totalAdditiveValue weight := by
  calc
    (∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
        CostSig.additiveFold weight (path.rawAccountAt surface)) =
        ∑ surface ∈ path.receipt.fundingSurfaces Finset.univ,
          CostSig.additiveFold weight
            (path.receipt.rawMeasureAt surface Finset.univ) := by
      apply Finset.sum_congr rfl
      intro surface _member
      rw [path.per_location_restriction_account_conservation]
    _ = CostSig.additiveFold weight
        (path.receipt.rawMeasure Finset.univ) :=
      path.receipt.additive_fundingSupport_gluing weight Finset.univ
    _ = path.receipt.totalAdditiveValue weight := rfl

/-- Multiplicative/quantale readings glue without changing the operational
receipt or its location support. -/
theorem multiplicative_local_accounts_glue_to_global
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {Delta : Type x} [CommMonoid Delta] (weight : String → Delta) :
    (∏ surface ∈ path.receipt.fundingSurfaces Finset.univ,
      CostSig.multiplicativeFold weight (path.rawAccountAt surface)) =
      path.receipt.totalMultiplicativeValue weight := by
  calc
    (∏ surface ∈ path.receipt.fundingSurfaces Finset.univ,
        CostSig.multiplicativeFold weight (path.rawAccountAt surface)) =
        ∏ surface ∈ path.receipt.fundingSurfaces Finset.univ,
          CostSig.multiplicativeFold weight
            (path.receipt.rawMeasureAt surface Finset.univ) := by
      apply Finset.prod_congr rfl
      intro surface _member
      rw [path.per_location_restriction_account_conservation]
    _ = CostSig.multiplicativeFold weight
        (path.receipt.rawMeasure Finset.univ) :=
      path.receipt.multiplicative_fundingSupport_gluing weight Finset.univ
    _ = path.receipt.totalMultiplicativeValue weight := rfl

end CostPath

namespace BudgetExamples

/-- A refund can hide an earlier overspend from a final-total-only check. -/
def overshootThenRefund : List Int := [6, -2]

theorem overshootThenRefund_final_total_within_budget :
    overshootThenRefund.sum ≤ 5 := by
  norm_num [overshootThenRefund]

theorem overshootThenRefund_prefix_rejected :
    ¬CostPath.OrderedAccount.PrefixAccepted overshootThenRefund 5 := by
  intro accepted
  have first := accepted 1 (by norm_num [overshootThenRefund])
  norm_num [CostPath.OrderedAccount.prefixCost, overshootThenRefund] at first

/-- A genuinely affordable ordered account passes all of its prefixes. -/
def affordableAccount : List Int := [2, 3]

theorem affordableAccount_prefix_accepted :
    CostPath.OrderedAccount.PrefixAccepted affordableAccount 5 := by
  intro count within
  norm_num [affordableAccount] at within
  interval_cases count <;>
    norm_num [CostPath.OrderedAccount.prefixCost, affordableAccount]

end BudgetExamples

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
