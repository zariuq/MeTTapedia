import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Receipt

/-!
# Unit-closure boundary of the concrete cost-rho relation

The executable cost-rho fragment is strictly positive: public seals, selected
purse heads, and emitted funding contributions are nonempty multisets.  This
module records the resulting boundary explicitly.  In particular, the
concrete step relation has no transition labelled by the commutative-monoid
unit.  Any categorical unit that embeds an unmetered transition as a
zero-signature transition therefore requires an additional internal fragment;
it is not already present in `CostStep`.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

namespace CostSig

@[simp]
theorem zero_not_runtimeValid {Ground : Type u} :
    ¬ RuntimeValid (0 : CostSig Ground) := by
  simp [RuntimeValid]

end CostSig

namespace CostStep

/-- Every concrete cost-rho step has a strictly positive spend label. -/
theorem spend_runtimeValid {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground}
    {spend : CostSig Ground}
    (step : CostStep source location spend target) : spend.RuntimeValid := by
  cases step with
  | wholeRecvSend signature_valid _ =>
      exact signature_valid
  | wholeSendRecv signature_valid _ =>
      exact signature_valid
  | split recv_seal_valid _send_seal_valid _cover =>
      intro sum_zero
      have card_zero := congrArg Multiset.card sum_zero
      simp only [Multiset.card_add, Multiset.card_zero] at card_zero
      exact recv_seal_valid
        (Multiset.card_eq_zero.mp (Nat.eq_zero_of_add_eq_zero_right card_zero))

/-- The concrete positive fragment is not closed under a zero-spend step. -/
theorem no_unit_spend {Ground : Type u}
    (source target : CostConfig Ground) (location : CostName Ground) :
    ¬ CostStep source location 0 target := by
  intro step
  exact CostSig.zero_not_runtimeValid (step.spend_runtimeValid)

end CostStep

namespace SpendEvent

/-- Every concrete receipt event has nonempty aggregate raw spend. -/
theorem rawSpend_runtimeValid
    {Ground : Type u} {Location : Type v}
    (event : SpendEvent Ground Location) : event.rawSpend.RuntimeValid := by
  obtain ⟨contribution, contribution_mem⟩ :=
    Multiset.exists_mem_of_ne_zero event.funding_nonempty
  obtain ⟨rest, funding_eq⟩ := Multiset.exists_cons_of_mem contribution_mem
  unfold SpendEvent.rawSpend CostSig.RuntimeValid
  rw [funding_eq]
  simp only [Multiset.map_cons, Multiset.sum_cons]
  intro sum_zero
  have card_zero := congrArg Multiset.card sum_zero
  simp only [Multiset.card_add, Multiset.card_zero] at card_zero
  exact contribution.spend_valid
    (Multiset.card_eq_zero.mp (Nat.eq_zero_of_add_eq_zero_right card_zero))

@[simp]
theorem rawSpend_ne_zero
    {Ground : Type u} {Location : Type v}
    (event : SpendEvent Ground Location) : event.rawSpend ≠ 0 :=
  event.rawSpend_runtimeValid

end SpendEvent

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
