import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Sets
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ClosedChains
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators
import Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure

/-!
# The set model of the tower inside the sets

The tower inside the sets (`MegalodonHOTG`) is the tower over the levels of `L` followed by the
natural numbers. This file reads it in sets by a chain of closed universes (`ClosedChains`)
that is not the chain of least universes.

**The chain** (`stages`), in the sets of the universe `u + 1` of Lean:

* at a level of `L`, the universe of the tower over the natural numbers: the least closed
  universe around the earlier ones;
* at the first level above `L`, **all the sets of the universe `u`**, carried into the
  universe `u + 1`, as one set (`carrierCode`);
* at the levels above, the least closed universes around that set.

It is a chain of closed universes (`stages_closedChain`), relative to cofinally many
inaccessible cardinals in the universes `u` and `u + 1`. So the tower inside the sets has a set
model (`lowerSets_setModel`), also with bounds on its level parameters
(`lowerSets_setModel_bounded`; with parameters that stand for levels of `L`,
`lowerSets_setModel_written`), in which:

* the type of all sets is read as all the sets of the lower universe (`lowerSets_allSets`);
* every universe at a level of `L` is one of those sets; the universe at the least level is
  the least closed universe around the natural numbers, and the universe at a successor level
  is the least closed universe around the universe at the level (`lowerSets_universe_bot`,
  `lowerSets_universe_succ`): the tower is the iteration of the universe operation;
* the least closed universe around a set is a set (`lowerSets_univOf_mem`): the type of all
  sets is closed under the universe operation, which no universe of a tower of least
  universes is (`univOf_not_closed_under_univOf`);
* the sort of the type of all sets is the least closed universe around the set of all sets
  (`lowerSets_allClasses`).

The hypothesis on the universe `u` gives the universe operation on the sets. The hypothesis on
the universe `u + 1` gives the universes above the set of all sets.

**The stages of the tower lie in every set that is closed under the universe operation**
(`universeSet_mem_of_closed`): a closed universe that contains the seed, the least closed
universe around each of its members, and the range of every family of its members indexed by
the levels below a level, contains every stage of the tower.

Negative examples. The set of all sets is a member of no universe at a level of `L`
(`lowerSets_notMem_universe`). No reading in sets has two heads each typed by the other
(`UniverseModel.headTyping_asymm`): the sets cannot be both a member of a universe and have
that universe as a member.

Lemmas that belong with the universe lift (`lift_insert`, `lift_numeral`, `lift_omega`,
`range_mem_carrierCode`), with the closed universes (`Closed.insert_mem`) and with the
universe models (`UniverseModel.headTyping_asymm`) are stated here under their names.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding

open ZFSetUniverseClosure ZFSetUniverseLift
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
  (numeral numeral_succ numeral_mem_omega natOf numeral_natOf)

universe u

/-- A closed universe contains the set of a member added to a member. -/
theorem ZFSetUniverseClosure.Closed.insert_mem {U a b : ZFSet.{u}} (closed : Closed U)
    (ha : a ∈ U) (hb : b ∈ U) : insert a b ∈ U := by
  have union : ZFSet.sUnion ({{a}, b} : ZFSet.{u}) = insert a b := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion, ZFSet.mem_insert_iff]
    constructor
    · rintro ⟨w, hw, hz⟩
      rcases ZFSet.mem_pair.mp hw with rfl | rfl
      · exact Or.inl (ZFSet.mem_singleton.mp hz)
      · exact Or.inr hz
    · rintro (rfl | hz)
      · exact ⟨{z}, ZFSet.mem_pair.mpr (Or.inl rfl), ZFSet.mem_singleton.mpr rfl⟩
      · exact ⟨b, ZFSet.mem_pair.mpr (Or.inr rfl), hz⟩
  rw [← union]
  exact closed.union_mem (closed.unorderedPair_mem (closed.singleton_mem ha) hb)

namespace ZFSetUniverseLift

/-- The lift of a set with one more member. -/
theorem lift_insert (a b : ZFSet.{u}) : lift (insert a b) = insert (lift a) (lift b) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases ZFSet.mem_insert_iff.mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (lift_mem_lift.mpr hx)
  · rintro (rfl | hz)
    · exact ⟨a, ZFSet.mem_insert _ _, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := mem_lift.mp hz
      exact ⟨x, ZFSet.mem_insert_of_mem _ hx, rfl⟩

/-- The lift of a numeral is the numeral. -/
theorem lift_numeral : ∀ k : ℕ, lift (numeral.{u} k) = numeral.{u + 1} k
  | 0 => lift_empty
  | k + 1 => by
      rw [numeral_succ, lift_insert, lift_numeral k]
      rfl

/-- **The lift of the natural numbers is the natural numbers.** -/
theorem lift_omega : lift ZFSet.omega.{u} = ZFSet.omega.{u + 1} := by
  apply ZFSet.ext
  intro z
  rw [mem_lift]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← numeral_natOf hx, lift_numeral]
    exact numeral_mem_omega _
  · intro hz
    exact ⟨numeral (natOf z), numeral_mem_omega _, by rw [lift_numeral, numeral_natOf hz]⟩

/-- The natural numbers are one of the lifted sets. -/
theorem omega_mem_carrierCode : ZFSet.omega.{u + 1} ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨ZFSet.omega, lift_omega⟩

/-- **The range of a family of lifted sets over a small index type is a lifted set.** -/
theorem range_mem_carrierCode {ι : Type} (f : ι → ZFSet.{u + 1})
    (hf : ∀ i, f i ∈ carrierCode.{u}) : ZFSet.range f ∈ carrierCode.{u} := by
  refine mem_carrierCode.mpr ⟨ZFSet.range fun i => lowerValue (f i), ?_⟩
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hx
    exact ⟨i, (lift_lowerValue (hf i)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨lowerValue (f i), ZFSet.mem_range.mpr ⟨i, rfl⟩, lift_lowerValue (hf i)⟩

/-- The least closed universe around a lifted set is a lifted set, relative to cofinally many
inaccessible cardinals in both universes. -/
theorem univOf_mem_carrierCode (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) {x : ZFSet.{u + 1}} (hx : x ∈ carrierCode.{u}) :
    univOf large x ∈ carrierCode.{u} := by
  obtain ⟨y, rfl⟩ := mem_carrierCode.mp hx
  exact mem_carrierCode.mpr ⟨univOf small y, ZFSetLiftedUniverseClosure.lift_univOf small large y⟩

end ZFSetUniverseLift

end Mettapedia.Logic.HOL.Embedding

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

universe u

/-- **No reading in sets has two heads each typed by the other**: a rule package with both
typings has no universe model. -/
theorem UniverseModel.headTyping_asymm {Head : Type} {R : Rules Head} {heads : Head → ZFSet.{u}}
    (model : UniverseModel R heads) {h k : Head} (typed : R.headTyping h k) :
    ¬ R.headTyping k h := fun back =>
  ZFSet.mem_asymm (model.headTyping_mem typed) (model.headTyping_mem back)

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed univOf mem_univOf univOf_closed)
open ZFSetUniverseLift (carrierCode carrierCode_closed omega_mem_carrierCode
  range_mem_carrierCode univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet universeSet_eq universeSet_closed universeSet_mem_of_lt
  seed_mem_universeSet universeSet_bot universeSet_succ)
open ZFSetReplayInterpretation (UniverseModel)

universe u

variable {L : Type} [LevelOrder L]

/-! ## The stages of the tower in a set closed under the universe operation -/

section Stages

variable (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})

/-- **A closed universe that contains the seed and is closed under the universe operation
contains every stage of the tower**, when it also contains the range of every family of its
members indexed by the levels below a level. -/
theorem universeSet_mem_of_closed {S : ZFSet.{u}} (closed : Closed S) (seedMem : seed ∈ S)
    (around : ∀ x ∈ S, univOf h x ∈ S)
    (ranges : ∀ (α : L) (f : {β : L // β < α} → ZFSet.{u}), (∀ β, f β ∈ S) → ZFSet.range f ∈ S)
    (α : L) : universeSet h seed α ∈ S := by
  refine LevelOrder.wf.induction (C := fun α => universeSet h seed α ∈ S) α ?_
  intro α earlier
  rw [universeSet_eq]
  exact around _ (closed.insert_mem seedMem
    (ranges α (fun β => universeSet h seed β.1) fun β => earlier β.1 β.2))

end Stages

/-! ## The chain -/

section LowerSets

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small in
/-- **Every universe of the tower over the natural numbers is a set of the lower universe**,
carried up. -/
theorem universeSet_mem_carrierCode (α : L) :
    universeSet large ZFSet.omega.{u + 1} α ∈ carrierCode.{u} :=
  universeSet_mem_of_closed large ZFSet.omega carrierCode_closed omega_mem_carrierCode
    (fun _ hx => univOf_mem_carrierCode small large hx)
    (fun _ f hf => range_mem_carrierCode f hf) α

/-- **The chain that reads the tower inside the sets**: at a level of `L` the universe of the
tower over the natural numbers; at the first level above, all the sets of the lower universe
as one set; at the levels above, the least closed universes around that set. -/
noncomputable def stages : Above L → ZFSet.{u + 1}
  | .below d => universeSet large ZFSet.omega d
  | .above 0 => carrierCode.{u}
  | .above (n + 1) => universeSet large carrierCode.{u} n

include small in
/-- **The stages are a chain of closed universes**, relative to cofinally many inaccessible
cardinals in both universes. -/
theorem stages_closedChain : ClosedChain (stages (L := L) large) where
  closed := fun a => by
    cases a with
    | below d => exact universeSet_closed large ZFSet.omega d
    | above n =>
      cases n with
      | zero => exact carrierCode_closed
      | succ n => exact universeSet_closed large carrierCode n
  mem_of_lt := fun {a b} lt => by
    cases a with
    | below c =>
      cases b with
      | below d => exact universeSet_mem_of_lt large ZFSet.omega (Above.below_lt_below.mp lt)
      | above n =>
        cases n with
        | zero => exact universeSet_mem_carrierCode small large c
        | succ n =>
          exact (universeSet_closed large carrierCode n).transitive _
            (seed_mem_universeSet large carrierCode n) (universeSet_mem_carrierCode small large c)
    | above m =>
      cases b with
      | below d => exact absurd lt (Above.not_above_lt_below m d)
      | above n =>
        have order : m < n := Above.above_lt_above.mp lt
        cases n with
        | zero => exact absurd order (Nat.not_lt_zero m)
        | succ n =>
          cases m with
          | zero => exact seed_mem_universeSet large carrierCode n
          | succ m =>
            exact universeSet_mem_of_lt large carrierCode (Nat.lt_of_succ_lt_succ order)

variable (ground : ZFSet.{u + 1}) (ν : Nat → Above L)

/-- The reading of the heads over the stages. -/
noncomputable abbrev lowerSetsHeads : Head L → ZFSet.{u + 1} :=
  chainHead (stages large) ground ν

variable {ground}

include small in
/-- **The tower inside the sets has a set model in which the type of all sets is read as all
the sets of the lower universe**, relative to cofinally many inaccessible cardinals in both
universes. -/
theorem lowerSets_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (consts : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν) consts (bare L) :=
  chain_setModel (stages_closedChain small large) groundTyped ν consts

variable {ν}

include small in
/-- **With bounds on the level parameters, the tower inside the sets has the same set model**
at every valuation that respects the bounds. -/
theorem lowerSets_setModel_bounded
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    {Δ : LevelBounds (Above L)} (valid : Δ.Valid ν) (consts : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν) consts
      (LevelTower.boundedChurch (bare L) Δ) :=
  chain_setModel_bounded (stages_closedChain small large) groundTyped valid consts

include small in
/-- **With level parameters that stand for levels of `L`, the tower inside the sets has the
same set model** at every valuation into the levels of `L`: there the universe at every level
expression over `L` is a set (`universeExpr_isSet`). -/
theorem lowerSets_setModel_written
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (written : Nat → L) (consts : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground fun i => Above.below (written i)) consts
      (LevelTower.boundedChurch (bare L) (writtenBounds L)) :=
  lowerSets_setModel_bounded small large groundTyped (writtenBounds_valid written) consts

variable (ground ν)

/-! ## What the heads are read as -/

/-- **The type of all sets is read as the set of all sets of the lower universe.** -/
theorem lowerSets_allSets :
    lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0))) = carrierCode.{u} :=
  rfl

/-- **The sort of the type of all sets is read as the least closed universe around the set
of all sets.** -/
theorem lowerSets_allClasses :
    lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 1))) =
      univOf large carrierCode.{u} :=
  universeSet_bot large carrierCode

/-- **The universe at the least level is the least closed universe around the natural
numbers.** -/
theorem lowerSets_universe_bot :
    lowerSetsHeads (L := L) large ground ν (.sort (.const (.below LevelOrder.bot))) =
      univOf large ZFSet.omega :=
  universeSet_bot large ZFSet.omega

/-- **The universe at a successor level is the least closed universe around the universe at
the level**: the tower is the iteration of the universe operation. -/
theorem lowerSets_universe_succ (d : L) :
    lowerSetsHeads (L := L) large ground ν (.sort (.const (.below (LevelOrder.succ d)))) =
      univOf large (lowerSetsHeads (L := L) large ground ν (.sort (.const (.below d)))) :=
  universeSet_succ large ZFSet.omega d

include small in
/-- **The least closed universe around a set is a set**: the set that reads the type of all
sets is closed under the universe operation. -/
theorem lowerSets_univOf_mem {x : ZFSet.{u + 1}}
    (hx : x ∈ lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0)))) :
    univOf large x ∈ lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0))) :=
  univOf_mem_carrierCode small large hx

include small in
/-- **Every universe at a level of `L` is a set.** -/
theorem lowerSets_universe_mem (d : L) :
    lowerSetsHeads (L := L) large ground ν (.sort (.const (.below d))) ∈
      lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0))) :=
  universeSet_mem_carrierCode small large d

include small in
/-- Negative example: **the set of all sets of the lower universe is a member of no universe
at a level of `L`.** -/
theorem lowerSets_notMem_universe (d : L) :
    carrierCode.{u} ∉ lowerSetsHeads (L := L) large ground ν (.sort (.const (.below d))) :=
  fun inside => ZFSet.mem_asymm inside (universeSet_mem_carrierCode small large d)

end LowerSets

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
