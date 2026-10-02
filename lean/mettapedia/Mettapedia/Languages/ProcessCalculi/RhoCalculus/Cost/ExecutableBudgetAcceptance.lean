import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPaths
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Physical authority implies ordered budget acceptance

Exact authority is matched before pricing. On a resource-separated execution,
the initial stored signing atoms equal the remaining atoms plus the actual
spend. A nonnegative additive valuation therefore bounds every ordered spend
prefix by the value of the initial inventory. Refund-valued accounts need a
separate prefix condition; final balance alone does not establish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

namespace CostSig

/-- The existing additive valuation is a homomorphism of exact accounts. -/
def additiveFoldHom {Ground : Type u} {Measure : Type v} [AddCommMonoid Measure]
    (weight : Ground → Measure) : CostSig Ground →+ Measure where
  toFun := additiveFold weight
  map_zero' := additiveFold_zero weight
  map_add' := additiveFold_add weight

theorem additiveFold_list_sum {Ground : Type u} {Measure : Type v} [AddCommMonoid Measure]
    (weight : Ground → Measure) (spends : List (CostSig Ground)) :
    additiveFold weight spends.sum = (spends.map (additiveFold weight)).sum :=
  map_list_sum (additiveFoldHom weight) spends

theorem additiveFold_nonneg {Ground : Type u} {Measure : Type v}
    [AddCommMonoid Measure] [Preorder Measure] [AddLeftMono Measure]
    (weight : Ground → Measure) (nonnegative : ∀ atom, 0 ≤ weight atom)
    (account : CostSig Ground) : 0 ≤ additiveFold weight account := by
  apply Multiset.sum_nonneg
  intro value member
  obtain ⟨atom, _present, rfl⟩ := Multiset.mem_map.mp member
  exact nonnegative atom

end CostSig

namespace CostPath

/-- The receipt's subtractive remaining-budget observation agrees with
the value of the authority physically retained at the actual path endpoint. -/
theorem executable_receipt_remainingBudget_eq_inventory
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    {Measure : Type v} [AddCommGroup Measure] (weight : String → Measure) :
    path.receipt.remainingBudget weight
        (CostSig.additiveFold weight
          (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures) =
      CostSig.additiveFold weight
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).storedSignatures := by
  unfold CausalReceipt.remainingBudget CausalReceipt.totalAdditiveValue
  rw [path.executable_stored_signatures_receipt_balance canonical separated,
    CostSig.additiveFold_add]
  exact add_sub_cancel_right _ _

/-- Every prefix is bounded by the actual initial inventory under any
nonnegative monotone additive price, including zero prices. -/
theorem executable_prefixAccepted_initial_inventory
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    {Measure : Type v} [AddCommMonoid Measure] [Preorder Measure]
    [AddLeftMono Measure] [AddRightMono Measure]
    (weight : String → Measure) (nonnegative : ∀ atom, 0 ≤ weight atom) :
    path.PrefixAccepted weight
      (CostSig.additiveFold weight
        (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures) := by
  have balance := path.executable_additive_inventory_balance weight canonical separated
  have remaining := CostSig.additiveFold_nonneg weight nonnegative
    (decodeRawConfig (finalComponents.map RawTraceComponent.term)).storedSignatures
  have totalBound : CostSig.additiveFold weight path.spends.sum ≤
      CostSig.additiveFold weight
        (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures := by
    rw [balance]
    exact le_add_of_nonneg_left remaining
  rw [CostSig.additiveFold_list_sum] at totalBound
  intro count _within
  exact le_trans ((List.take_sublist count (path.additiveAccount weight)).sum_le_sum
    (by
      intro price member
      obtain ⟨spend, _present, rfl⟩ := List.mem_map.mp member
      exact CostSig.additiveFold_nonneg weight nonnegative spend)) totalBound

end CostPath

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The real generated parser image supplies resource separation for every
actual finite execution. Pricing is applied after exact authorization. -/
theorem ConfigImage.finite_path_prefixAccepted
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents)
    {Measure : Type v} [AddCommMonoid Measure] [Preorder Measure]
    [AddLeftMono Measure] [AddRightMono Measure]
    (weight : String → Measure) (nonnegative : ∀ atom, 0 ≤ weight atom) :
    path.PrefixAccepted weight (CostSig.additiveFold weight
      (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map
        RawTraceComponent.term)).storedSignatures) :=
  path.executable_prefixAccepted_initial_inventory
    (initialTraceComponents_canonical (literalEncodeTerm term))
    (initialTraceComponents_resourceSeparated (literalEncodeTerm term)
      (image.literal_components_resourceSeparated channelImage)) weight nonnegative

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
