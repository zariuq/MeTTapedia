import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Located
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Valuation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalEquivalence

/-!
# Units and funding in the positive rho meter

A signature's additive unit, a zero-valued price, and a spendable temporal
cell have different operational meanings.  Every existing `CostStep` needs
a positive purse head at its interaction location: a funded step is an enabled
firing of the funded resource system, and every such firing selects a purse
there.  Wrapping a process adds
no such authority.  A signature may have price zero while its positive
authority still has to be supplied and consumed.

These results preserve the public positive relation.  They do not add a
free execution rule for unit-key wrappers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

namespace LocatedTokenCover

/-- A positive demand has a selected positive head at the declared location. -/
theorem exists_positive_head {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual)
    (valid : demand.RuntimeValid) :
    ∃ head tail, head.RuntimeValid ∧
      (⟨location, CostStack.cons head tail⟩ : LocatedPurse Ground) ∈ available := by
  have chosen_nonempty : cover.chosen ≠ 0 := by
    intro empty
    apply valid
    rw [cover.demand_eq, empty]
    simp
  obtain ⟨choice, selected⟩ := Multiset.exists_mem_of_ne_zero chosen_nonempty
  refine ⟨choice.head, choice.tail, choice.head_valid, ?_⟩
  rw [cover.available_eq]
  exact Multiset.mem_add.mpr
    (Or.inl (Multiset.mem_map.mpr ⟨choice, selected, rfl⟩))

/-- One positive cell, with its exact residual tail, funds a matching demand. -/
def singleHead {Ground : Type u} (location : CostName Ground)
    (signature : CostSig Ground) (valid : signature.RuntimeValid)
    (tail : CostStack Ground) :
    LocatedTokenCover location signature
      {⟨location, .cons signature tail⟩} {⟨location, tail⟩} where
  chosen := {⟨signature, tail, valid⟩}
  untouched := 0
  available_eq := by simp
  residual_eq := by simp
  demand_eq := by simp

end LocatedTokenCover

namespace CostStep

/-- Every charged firing consumes an actual positive head at its location. -/
theorem exists_positive_funding_purse {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground}
    {spend : CostSig Ground} (step : CostStep source location spend target) :
    ∃ head tail, head.RuntimeValid ∧
      CostTerm.purse location (.cons head tail) ∈ source := by
  classical
  obtain ⟨entry, rfl, -, enabled, -⟩ := costStep_iff_exists_enabled_resource.mp step
  obtain ⟨choice, chosen⟩ := Multiset.exists_mem_of_ne_zero
    (entry.2.val.funding.chosen_ne_zero entry.2.val.spend_valid)
  have present := (Mettapedia.GSLT.Causality.ResourceInteraction.pursesMany_enables_iff _ _ _).mp
    ((costResource_enables_iff source entry.2).mp enabled).2
  exact ⟨choice.head, choice.tail, choice.head_valid,
    purseTerm_toList entry.1 (.cons choice.head choice.tail) ▸
      (CostConfig.mem_purses_iff source _).mp (Multiset.mem_of_le present
        (Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ chosen)))⟩

/-- Absence of a purse head at this location blocks every charged firing. -/
theorem blocked_of_no_funding_at {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground}
    {spend : CostSig Ground}
    (absent : ∀ head tail,
      CostTerm.purse location (.cons head tail) ∉ source) :
    ¬ CostStep source location spend target := by
  intro step
  obtain ⟨head, tail, _valid, member⟩ := step.exists_positive_funding_purse
  exact absent head tail member

/-- A wrapper alone supplies no funding, even when its body is a redex. -/
theorem signed_singleton_blocked {Ground : Type u}
    (process : CostProc Ground) (signature : CostSig Ground)
    (location : CostName Ground) (spend : CostSig Ground)
    (target : CostConfig Ground) :
    ¬ CostStep {CostTerm.signed process signature} location spend target := by
  apply blocked_of_no_funding_at
  intro head tail member
  simp only [Multiset.mem_singleton] at member
  cases member

/-- An empty located purse adds no funding to a wrapped process. -/
theorem signed_with_empty_purse_blocked {Ground : Type u}
    (process : CostProc Ground) (signature : CostSig Ground)
    (purseLocation location : CostName Ground) (spend : CostSig Ground)
    (target : CostConfig Ground) :
    ¬ CostStep
      ({CostTerm.signed process signature} +
        {CostTerm.purse purseLocation .empty}) location spend target := by
  apply blocked_of_no_funding_at
  intro head tail member
  simp at member

/-- Returning the inert term does not perform a charged interaction. -/
theorem nil_singleton_blocked {Ground : Type u}
    (location : CostName Ground) (spend : CostSig Ground)
    (target : CostConfig Ground) :
    ¬ CostStep {CostTerm.nil} location spend target := by
  apply blocked_of_no_funding_at
  intro head tail member
  simp only [Multiset.mem_singleton] at member
  cases member

/-- One matching positive head enables the actual whole COMM rule. -/
theorem wholeRecvSend_single_head {Ground : Type u}
    (context : CostConfig Ground) (channel : CostName Ground)
    (body payload : CostTerm Ground) (signature : CostSig Ground)
    (valid : signature.RuntimeValid) (tail : CostStack Ground) :
    CostStep
      (context +
        (.signed (.par (.recv channel body) (.send channel payload))
          signature ::ₘ 0) +
        (.purse channel (.cons signature tail) ::ₘ 0))
      channel signature
      (context + (body.commSubst payload).components +
        (.purse channel tail ::ₘ 0)) := by
  simpa [LocatedPurse.configComponents, LocatedPurse.toTerm] using
    (CostStep.wholeRecvSend (context := context) (body := body)
      (payload := payload) valid
      (LocatedTokenCover.singleHead channel signature valid tail))

end CostStep

namespace UnitPolicy

/-- A literal unit-key wrapper is outside the public positive fragment. -/
theorem unit_key_wrapper_not_supported {Ground : Type u}
    (process : CostProc Ground) :
    ¬ (CostTerm.signed process 0).RuntimeSupported := by
  rintro ⟨_process_supported, signature_valid⟩
  exact CostSig.zero_not_runtimeValid signature_valid

/-- A unit-key cell is a syntactic cell, but not a supported spendable head. -/
theorem unit_key_cell_not_supported {Ground : Type u}
    (tail : CostStack Ground) :
    ¬ (CostStack.cons (0 : CostSig Ground) tail).RuntimeSupported := by
  rintro ⟨signature_valid, _tail_supported⟩
  exact CostSig.zero_not_runtimeValid signature_valid

/-- Zero price does not identify a positive authority signature with the unit. -/
theorem zero_price_positive_signature {Ground : Type u} (authority : Ground) :
    ({authority} : CostSig Ground).RuntimeValid ∧
      CostSig.additiveFold (fun _ : Ground => (0 : Nat)) {authority} = 0 := by
  constructor
  · simp [CostSig.RuntimeValid]
  · simp

/-- A zero-valued signature still cannot run an unfunded wrapped process. -/
theorem zero_price_does_not_supply_funding {Ground : Type u}
    (authority : Ground) (process : CostProc Ground)
    (location : CostName Ground) (target : CostConfig Ground) :
    CostSig.additiveFold (fun _ : Ground => (0 : Nat)) {authority} = 0 ∧
      ¬ CostStep {CostTerm.signed process {authority}}
        location {authority} target := by
  exact ⟨by simp, CostStep.signed_singleton_blocked process _ location _ target⟩

end UnitPolicy

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
