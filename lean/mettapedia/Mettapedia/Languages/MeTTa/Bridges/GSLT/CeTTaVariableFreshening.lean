import Mettapedia.Machines.VariableIndex
import Mathlib.Data.BitVec
import Mathlib.Tactic

/-!
# Full-identity inventories before native epoch replacement

The current native variable identity has two 64-bit fields: base and epoch.
Replacing only the epoch is injective on a support exactly when its base
projection already distinguishes that support. Mixed old epochs need not
have this property.

The syntax import and term-universe storage boundaries use a map keyed by
the full old identity. First occurrences receive distinct one-based slots.
Storage leaves an epochless support unchanged and otherwise renumbers the
entire support before dropping its old epochs. These finite-inventory laws
derive the qualification condition from that normalization, rather than
postulating injectivity of arbitrary epoch replacement.

This models successful inventory allocation and the nonzero-base branch.
It does not verify the allocator, the graph walk, or the separate 64-bit
frame-handle/generation codec. The older packed-word layout is not imported.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaVariableFreshening

structure VariableId where
  base : BitVec 64
  epoch : BitVec 64
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def qualify (epoch : BitVec 64) (source : VariableId) : VariableId := ⟨source.base, epoch⟩

/-- The zero-base native helper calls a fresh-base allocator, not this pure
replacement branch. Refusal here exposes that separate service obligation. -/
def qualify? (epoch : BitVec 64) (source : VariableId) : Option VariableId :=
  if source.base = 0 then none else some (qualify epoch source)

def StableBases (support : List VariableId) : Prop :=
  ∀ left ∈ support, ∀ right ∈ support, left.base = right.base → left = right

theorem qualification_equal_iff (epoch : BitVec 64) (left right : VariableId) :
    qualify epoch left = qualify epoch right ↔ left.base = right.base := by
  simp [qualify]

theorem qualification_injective_iff (epoch : BitVec 64) (support : List VariableId) :
    Set.InjOn (qualify epoch) {value | value ∈ support} ↔ StableBases support := by
  constructor
  · intro injective left leftIn right rightIn same
    exact injective leftIn rightIn ((qualification_equal_iff epoch left right).mpr same)
  · intro stable left leftIn right rightIn same
    exact stable left leftIn right rightIn ((qualification_equal_iff epoch left right).mp same)

theorem epochless_stable (support : List VariableId)
    (epochless : ∀ value ∈ support, value.epoch = 0) : StableBases support := by
  intro left leftIn right rightIn sameBase
  have sameEpoch := (epochless left leftIn).trans (epochless right rightIn).symm
  cases left; cases right; simp_all

def inventory (support : List VariableId) : List VariableId := support.eraseDups

def ordinal (support : List VariableId) (source : VariableId) : Nat :=
  (inventory support).idxOf source + 1

def canonicalVariable (support : List VariableId) (source : VariableId) : VariableId :=
  ⟨BitVec.ofNat 64 (ordinal support source), 0⟩

theorem inventory_member (support : List VariableId) (source : VariableId) :
    source ∈ inventory support ↔ source ∈ support := by simp [inventory]

theorem inventory_unique : ∀ support : List VariableId, (inventory support).Nodup
  | [] => by simp [inventory]
  | first :: rest => by
      rw [inventory, List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact inventory_unique (rest.filter fun value => !value == first)
termination_by support => support.length
decreasing_by
  have bound := List.length_filter_le (fun value : VariableId => !value == first) rest
  simp_wf
  omega

theorem ordinal_bounds (support : List VariableId) (source : VariableId) (member : source ∈ support) :
    0 < ordinal support source ∧ ordinal support source ≤ (inventory support).length := by
  have bound := List.idxOf_lt_length_iff.mpr ((inventory_member support source).mpr member)
  simp only [ordinal]
  omega

theorem ordinal_injective (support : List VariableId) {left right : VariableId}
    (leftIn : left ∈ support) (same : ordinal support left = ordinal support right) : left = right := by
  have indexes : (inventory support).idxOf left = (inventory support).idxOf right := by
    simpa only [ordinal, Nat.add_right_cancel_iff] using same
  exact (List.idxOf_inj ((inventory_member support left).mpr leftIn)).mp indexes

theorem canonical_base_exact (support : List VariableId) (bounded : (inventory support).length < 2 ^ 32)
    (source : VariableId) (member : source ∈ support) :
    (canonicalVariable support source).base.toNat = ordinal support source := by
  have bound := (ordinal_bounds support source member).2
  change (BitVec.ofNat 64 (ordinal support source)).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem canonical_base_nonzero (support : List VariableId) (bounded : (inventory support).length < 2 ^ 32)
    (source : VariableId) (member : source ∈ support) : (canonicalVariable support source).base ≠ 0 := by
  intro zero
  have read := canonical_base_exact support bounded source member
  rw [zero] at read
  change 0 = ordinal support source at read
  have positive := (ordinal_bounds support source member).1
  omega

theorem canonical_base_injective (support : List VariableId) (bounded : (inventory support).length < 2 ^ 32)
    {left right : VariableId} (leftIn : left ∈ support) (rightIn : right ∈ support)
    (same : (canonicalVariable support left).base = (canonicalVariable support right).base) : left = right := by
  apply ordinal_injective support leftIn
  have values := congrArg BitVec.toNat same
  simpa only [canonical_base_exact support bounded left leftIn,
    canonical_base_exact support bounded right rightIn] using values

/-- Existing hash-table proposals are checked against the full-identity
inventory. Equal confirmed positions cannot name different old identities. -/
theorem confirmed_position_injective (support : List VariableId) (proposal : VariableId → Option Nat)
    (left right : VariableId) (position : Nat)
    (leftFound : Mettapedia.Machines.VariableIndex.lookup support proposal left = some position)
    (rightFound : Mettapedia.Machines.VariableIndex.lookup support proposal right = some position) : left = right := by
  have first := Mettapedia.Machines.VariableIndex.lookup_sound leftFound
  have second := Mettapedia.Machines.VariableIndex.lookup_sound rightFound
  exact Option.some.inj (first.symm.trans second)

def hasEpoch (support : List VariableId) : Bool := support.any (fun value => value.epoch != 0)

def storedVariable (support : List VariableId) (source : VariableId) : VariableId :=
  if hasEpoch support then canonicalVariable support source else source

theorem stored_epochless (support : List VariableId) (source : VariableId) (member : source ∈ support) :
    (storedVariable support source).epoch = 0 := by
  unfold storedVariable
  split
  · rfl
  · rename_i absent
    have notPresent : ¬hasEpoch support = true := by simpa using absent
    by_contra nonzero
    apply notPresent
    exact List.any_eq_true.mpr ⟨source, member, by simpa using nonzero⟩

theorem stored_support_stable (support : List VariableId) : StableBases (support.map (storedVariable support)) := by
  apply epochless_stable
  intro value member
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  exact stored_epochless support source present

theorem stored_injective (support : List VariableId) (bounded : (inventory support).length < 2 ^ 32) :
    Set.InjOn (storedVariable support) {value | value ∈ support} := by
  intro left leftIn right rightIn same
  unfold storedVariable at same
  split at same
  · exact canonical_base_injective support bounded leftIn rightIn (congrArg VariableId.base same)
  · exact same

/-- Normalization followed by epoch qualification preserves exactly the
old equality partition, even when old epochs and base names are mixed. -/
theorem stored_then_qualified_injective (support : List VariableId)
    (bounded : (inventory support).length < 2 ^ 32) (epoch : BitVec 64) :
    Set.InjOn (fun value => qualify epoch (storedVariable support value)) {value | value ∈ support} := by
  intro left leftIn right rightIn same
  apply stored_injective support bounded leftIn rightIn
  exact (qualification_injective_iff epoch _).mpr (stored_support_stable support)
    (List.mem_map.mpr ⟨left, leftIn, rfl⟩) (List.mem_map.mpr ⟨right, rightIn, rfl⟩) same

theorem stored_base_nonzero (support : List VariableId)
    (bounded : (inventory support).length < 2 ^ 32)
    (nonzero : ∀ source ∈ support, source.base ≠ 0)
    (source : VariableId) (member : source ∈ support) : (storedVariable support source).base ≠ 0 := by
  unfold storedVariable
  split
  · exact canonical_base_nonzero support bounded source member
  · exact nonzero source member

/-- Successful pure native qualification after the actual storage
normalization, with the zero-base allocation case explicitly excluded. -/
theorem stored_qualification_succeeds (support : List VariableId)
    (bounded : (inventory support).length < 2 ^ 32)
    (nonzero : ∀ source ∈ support, source.base ≠ 0)
    (epoch : BitVec 64) (source : VariableId) (member : source ∈ support) :
    qualify? epoch (storedVariable support source) = some (qualify epoch (storedVariable support source)) := by
  simp only [qualify?, stored_base_nonzero support bounded nonzero source member, if_false]

theorem checked_stored_qualification_injective (support : List VariableId)
    (bounded : (inventory support).length < 2 ^ 32)
    (nonzero : ∀ source ∈ support, source.base ≠ 0) (epoch : BitVec 64) :
    Set.InjOn (fun value => qualify? epoch (storedVariable support value)) {value | value ∈ support} := by
  intro left leftIn right rightIn same
  dsimp only at same
  rw [stored_qualification_succeeds support bounded nonzero epoch left leftIn,
    stored_qualification_succeeds support bounded nonzero epoch right rightIn] at same
  exact stored_then_qualified_injective support bounded epoch leftIn rightIn (Option.some.inj same)

namespace Controls

def oldLeft : VariableId := ⟨7, 11⟩
def oldRight : VariableId := ⟨7, 12⟩
def mixed : List VariableId := [oldLeft, oldRight, oldLeft]

theorem raw_replacement_collapses_distinct_old_epochs :
    oldLeft ≠ oldRight ∧ qualify 19 oldLeft = qualify 19 oldRight := by decide

theorem full_identity_inventory_preserves_repetitions :
    mixed.map (storedVariable mixed) = [⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩] := by decide

theorem normalized_freshening_keeps_distinct_old_epochs :
    qualify 19 (storedVariable mixed oldLeft) ≠ qualify 19 (storedVariable mixed oldRight) := by decide

theorem already_epochless_support_keeps_bases :
    storedVariable [⟨101, 0⟩, ⟨205, 0⟩] ⟨205, 0⟩ = ⟨205, 0⟩ := by decide

theorem zero_base_is_not_the_pure_branch : qualify? 19 ⟨0, 11⟩ = none := by decide

end Controls

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaVariableFreshening
