import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientInventory

/-!
# Atomic purse cells in the actual generated parser image

Every accepted generated signature is one entire literal authority atom.
The parser therefore supplies singleton purse heads throughout its admitted
configuration, including ambient contacts. Raw normalization preserves this
inventory. Actual selected-cell counts then equal demanded atom counts; the
broader raw runtime's multi-atom single cell remains outside this image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

inductive CostStack.SingletonHeads {Ground : Type u} : CostStack Ground → Prop where
  | empty : SingletonHeads .empty
  | cons {head : CostSig Ground} {tail : CostStack Ground}
      (atomic : head.card = 1) (rest : SingletonHeads tail) : SingletonHeads (.cons head tail)

theorem CostStack.SingletonHeads.relabel {Ground : Type u} {Target : Type v}
    (label : Ground → Target) {stack : CostStack Ground} (atomic : stack.SingletonHeads) :
    (stack.relabel label).SingletonHeads := by
  cases atomic with
  | empty => exact .empty
  | cons head rest =>
      exact .cons (by simpa using head) (CostStack.SingletonHeads.relabel label rest)

theorem CostTerm.component_inventory_le {Ground : Type u}
    {term component : CostTerm Ground} (member : component ∈ term.components) :
    component.purseInventory ≤ term.purseInventory := by
  cases term with
  | nil => simp [CostTerm.components] at member
  | par left right =>
      rcases Multiset.mem_add.mp member with leftMember | rightMember
      · exact le_trans (CostTerm.component_inventory_le leftMember) (Multiset.le_add_right _ _)
      · exact le_trans (CostTerm.component_inventory_le rightMember) (Multiset.le_add_left _ _)
  | signed process signature =>
      have same : component = .signed process signature := Multiset.mem_singleton.mp member
      exact same ▸ le_refl _
  | drop name =>
      have same : component = .drop name := Multiset.mem_singleton.mp member
      exact same ▸ le_refl _
  | purse location stack =>
      have same : component = .purse location stack := Multiset.mem_singleton.mp member
      exact same ▸ le_refl _

theorem rawSelectedSpend_card_eq_length {selected : List RawSelectedPurse}
    (atomic : selected.Forall fun purse => purse.head.length = 1) :
    (rawSelectedSpend selected).card = selected.length := by
  induction selected with
  | nil => rfl
  | cons purse rest ih =>
      obtain ⟨head, tail⟩ :=
        (List.forall_cons (fun purse : RawSelectedPurse => purse.head.length = 1) purse rest).mp atomic
      change (purse.head.toMultiset + rawSelectedSpend rest).card = rest.length + 1
      rw [Multiset.card_add, ih tail]
      change purse.head.length + rest.length = rest.length + 1
      omega

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem StackImage.singletonHeads {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) : stack.SingletonHeads := by
  induction image with
  | empty => exact .empty
  | cons signature accepted rest ih =>
      exact .cons (by rw [signature.property.1, Multiset.card_singleton]) ih

mutual
  theorem ConfigImage.purseInventory_singleton {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigImage location source term) (locationFree : location.purseInventory = 0)
      {stack : CostStack LiteralAuthority} (member : stack ∈ term.purseInventory) : stack.SingletonHeads := by
    cases image with
    | zero => simp [CostTerm.purseInventory] at member
    | drop name =>
      change stack ∈ CostName.purseInventory _ at member
      rw [name.purseInventory_zero] at member
      contradiction
    | signed signature accepted process =>
      have free := (CodeImage.signed signature accepted process).purseFree
      change stack ∈ (.signed _ _ : CostTerm LiteralAuthority).purseInventory at member
      rw [free] at member
      contradiction
    | contact code purse =>
      change stack ∈ CostTerm.purseInventory _ + ({_} + location.purseInventory) at member
      rw [locationFree, add_zero] at member
      rcases Multiset.mem_add.mp member with inCode | inPurse
      · exact code.purseInventory_singleton locationFree inCode
      · exact (Multiset.mem_singleton.mp inPurse) ▸ purse.singletonHeads
    | collection codes => exact codes.purseInventory_singleton locationFree member

  theorem ConfigListImage.purseInventory_singleton {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) (locationFree : location.purseInventory = 0)
      {stack : CostStack LiteralAuthority} (member : stack ∈ term.purseInventory) : stack.SingletonHeads := by
    cases image with
    | nil => simp [CostTerm.purseInventory] at member
    | cons head tail =>
      rcases Multiset.mem_add.mp member with inHead | inTail
      · exact head.purseInventory_singleton locationFree inHead
      · exact tail.purseInventory_singleton locationFree inTail
end

theorem ConfigImage.literal_inventory_singleton {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {stack : CostStack String} (member : stack ∈ (decodeCostTerm (literalEncodeTerm term)).purseInventory) :
    stack.SingletonHeads := by
  rw [literalEncodeTerm, decodeCostTerm_encodeCostTerm, CostTerm.relabel_purseInventory] at member
  obtain ⟨original, originalMember, rfl⟩ := Multiset.mem_map.mp member
  exact (image.purseInventory_singleton channelImage.purseInventory_zero originalMember).relabel literalAuthorityKey

/-- Actual canonical purse occurrences inherit singleton heads from the accepted generated syntax. -/
theorem ConfigImage.canonical_purse_head_atomic {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {purse : RawIndexedPurse} (member : purse ∈ (literalEncodeTerm term).normalizeConfig.purses) :
    purse.head.length = 1 := by
  have rawMember : purse.toTerm ∈ (literalEncodeTerm term).normalizeConfig := by
    have filtered : purse.toTerm ∈ (literalEncodeTerm term).normalizeConfig.filter RawCostTerm.isActivePurse := by
      rw [← RawCostConfig.purses_map_toTerm]
      exact List.mem_map.mpr ⟨purse, member, rfl⟩
    exact (List.mem_filter.mp filtered).1
  have typedMember : decodeCostTerm purse.toTerm ∈
      (decodeCostTerm (literalEncodeTerm term).normalize).components := by
    rw [← raw_normalConfig_components]
    change decodeCostTerm purse.toTerm ∈
      ((literalEncodeTerm term).normalizeConfig : Multiset RawCostTerm).map decodeCostTerm
    exact Multiset.mem_map.mpr ⟨purse.toTerm, rawMember, rfl⟩
  have inPurse : decodeCostStack (purse.head :: purse.tail) ∈
      (decodeCostTerm purse.toTerm).purseInventory := by
    change _ ∈ {_} + (decodeCostName purse.location).purseInventory
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))
  have inWhole := Multiset.mem_of_le (CostTerm.component_inventory_le typedMember) inPurse
  rw [RawCostTerm.decoded_inventory_normalize] at inWhole
  have atomic := image.literal_inventory_singleton channelImage inWhole
  cases atomic with
  | cons head rest => exact head

/-- In this actual parser image, selected physical cells equal the exact demand's atom count. -/
theorem ConfigImage.canonical_candidate_cells_eq_atoms {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig) :
    step.selectedPurses.length = (decodeCostSig step.spend).card := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have atomic : step.selectedPurses.Forall fun purse => purse.head.length = 1 := by
    rw [List.forall_iff_forall_mem]
    intro purse member
    exact image.canonical_purse_head_atomic channelImage (funding.selected_from_config.mem member)
  have exactCard := congrArg Multiset.card funding.exact_spend
  rw [rawSelectedSpend_card_eq_length atomic] at exactCard
  exact exactCard

/-- A two-atom raw purse cell has no readback in the current generated funding interpretation. -/
theorem no_two_atom_generated_purse {channelSource source : Pattern}
    {location : CostName LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (fuel : Nat) (left right : Pattern) (tail : CostStack LiteralAuthority) :
    (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel source).map Subtype.val ≠
      some (locatedContact location .nil (.cons ({left} + {right}) tail)) := by
  intro parsed
  have image := config_parser_image parsed
  have member : (.cons ({left} + {right}) tail) ∈
      (locatedContact location .nil (.cons ({left} + {right}) tail)).purseInventory := by
    change _ ∈ 0 + ({_} + location.purseInventory)
    simp
  have atomic := image.purseInventory_singleton channelImage.purseInventory_zero member
  cases atomic with
  | cons head rest => simp at head

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
