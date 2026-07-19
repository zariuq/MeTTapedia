import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Receipt

/-!
# Located purse covers

This module derives locality and funding facts from the proof-relevant purse
decomposition used by a concrete cost-rho firing.  Surfaces are rho names;
signatures remain a distinct multiset type.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- Funding surfaces in the concrete pure-rho profile are rho names. -/
abbrev CostSurface (Ground : Type u) := CostName Ground

/-- Nominal nearness on normalized names. -/
def near {Ground : Type u} [DecidableEq Ground]
    (left right : CostSurface Ground) : Option (CostSurface Ground) :=
  if left = right then some left else none

@[simp]
theorem near_eq_some_iff {Ground : Type u} [DecidableEq Ground]
    {left right surface : CostSurface Ground} :
    near left right = some surface ↔ left = right ∧ surface = left := by
  unfold near
  split_ifs with same
  · constructor
    · intro equality
      exact ⟨same, (Option.some.inj equality).symm⟩
    · rintro ⟨_same, rfl⟩
      rfl
  · simp [same]

@[simp]
theorem near_self {Ground : Type u} [DecidableEq Ground]
    (surface : CostSurface Ground) : near surface surface = some surface := by
  simp [near]

theorem near_eq_none_of_ne {Ground : Type u} [DecidableEq Ground]
    {left right : CostSurface Ground} (different : left ≠ right) :
    near left right = none := by
  simp [near, different]

namespace LocatedTokenCover

variable {Ground : Type u} {surface : CostName Ground} {demand : CostSig Ground}
  {available residual : Multiset (LocatedPurse Ground)}

/-- Selected purse occurrences before head consumption. -/
def selectedBefore
    (cover : LocatedTokenCover surface demand available residual) :
    Multiset (LocatedPurse Ground) :=
  cover.chosen.map fun choice =>
    ⟨surface, .cons choice.head choice.tail⟩

/-- Selected purse occurrences after exposing their tails. -/
def selectedAfter
    (cover : LocatedTokenCover surface demand available residual) :
    Multiset (LocatedPurse Ground) :=
  cover.chosen.map fun choice => ⟨surface, choice.tail⟩

/-- One receipt contribution for every selected purse head. -/
def fundingContributions
    (cover : LocatedTokenCover surface demand available residual) :
    Multiset (FundingContribution Ground (CostSurface Ground)) :=
  cover.chosen.map fun choice =>
    ⟨surface, choice.head, choice.head_valid⟩

theorem available_decomposition
    (cover : LocatedTokenCover surface demand available residual) :
    available = cover.selectedBefore + cover.untouched := by
  exact cover.available_eq

theorem residual_decomposition
    (cover : LocatedTokenCover surface demand available residual) :
    residual = cover.selectedAfter + cover.untouched := by
  exact cover.residual_eq

/-- Every selected purse before firing lies at the interaction surface. -/
theorem selected_before_surface
    (cover : LocatedTokenCover surface demand available residual)
    {purse : LocatedPurse Ground} (selected : purse ∈ cover.selectedBefore) :
    purse.surface = surface := by
  simp only [selectedBefore, Multiset.mem_map] at selected
  obtain ⟨choice, _membership, rfl⟩ := selected
  rfl

/-- Every exposed selected tail remains at the interaction surface. -/
theorem selected_tail_surface
    (cover : LocatedTokenCover surface demand available residual)
    {purse : LocatedPurse Ground} (selected : purse ∈ cover.selectedAfter) :
    purse.surface = surface := by
  simp only [selectedAfter, Multiset.mem_map] at selected
  obtain ⟨choice, _membership, rfl⟩ := selected
  rfl

/-- A purse at a different surface cannot be among the selected occurrences. -/
theorem wrong_location_not_selected
    (cover : LocatedTokenCover surface demand available residual)
    {purse : LocatedPurse Ground} (wrong : purse.surface ≠ surface) :
    purse ∉ cover.selectedBefore := by
  intro selected
  exact wrong (cover.selected_before_surface selected)

/-- Every untouched occurrence is present in the source configuration. -/
theorem untouched_le_available
    (cover : LocatedTokenCover surface demand available residual) :
    cover.untouched ≤ available := by
  apply Multiset.le_iff_exists_add.mpr
  refine ⟨cover.selectedBefore, ?_⟩
  calc
    available = cover.selectedBefore + cover.untouched :=
      cover.available_decomposition
    _ = cover.untouched + cover.selectedBefore := by ac_rfl

/-- Every untouched occurrence is present in the residual configuration. -/
theorem untouched_le_residual
    (cover : LocatedTokenCover surface demand available residual) :
    cover.untouched ≤ residual := by
  apply Multiset.le_iff_exists_add.mpr
  refine ⟨cover.selectedAfter, ?_⟩
  calc
    residual = cover.selectedAfter + cover.untouched :=
      cover.residual_decomposition
    _ = cover.untouched + cover.selectedAfter := by ac_rfl

/-- Funding records are occurrence preserving: their cardinality is exactly
the number of selected purse heads. -/
theorem funding_contributions_card
    (cover : LocatedTokenCover surface demand available residual) :
    cover.fundingContributions.card = cover.chosen.card := by
  simp [fundingContributions]

/-- Every funding contribution reports the actual COMM surface. -/
theorem funding_contribution_surface
    (cover : LocatedTokenCover surface demand available residual)
    {contribution : FundingContribution Ground (CostSurface Ground)}
    (member : contribution ∈ cover.fundingContributions) :
    contribution.surface = surface := by
  simp only [fundingContributions, Multiset.mem_map] at member
  obtain ⟨choice, _membership, rfl⟩ := member
  rfl

/-- The raw sum of emitted contributions is the demanded signature exactly. -/
theorem funding_contributions_eq_selected_heads
    (cover : LocatedTokenCover surface demand available residual) :
    (cover.fundingContributions.map FundingContribution.spend).sum = demand := by
  calc
    (cover.fundingContributions.map FundingContribution.spend).sum =
        (cover.chosen.map SelectedPurseHead.head).sum := by
      simp [fundingContributions]
    _ = demand := cover.demand_eq.symm

/-- Nonzero demand cannot be funded without an available purse occurrence. -/
theorem no_ambient_funding
    (cover : LocatedTokenCover surface demand available residual)
    (demand_valid : demand.RuntimeValid) : available ≠ 0 := by
  intro available_empty
  have selected_empty : cover.selectedBefore = 0 := by
    have sum_empty : cover.selectedBefore + cover.untouched = 0 :=
      cover.available_decomposition.symm.trans available_empty
    have card_empty := congrArg Multiset.card sum_empty
    have card_empty' : cover.selectedBefore.card + cover.untouched.card = 0 := by
      simpa using card_empty
    have selected_card_empty : cover.selectedBefore.card = 0 := by
      omega
    exact Multiset.card_eq_zero.mp selected_card_empty
  have chosen_empty : cover.chosen = 0 := by
    apply Multiset.card_eq_zero.mp
    have mapped_card : cover.selectedBefore.card = cover.chosen.card := by
      simp [selectedBefore]
    simpa [selected_empty] using mapped_card.symm
  apply demand_valid
  rw [cover.demand_eq, chosen_empty]
  simp

end LocatedTokenCover

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
