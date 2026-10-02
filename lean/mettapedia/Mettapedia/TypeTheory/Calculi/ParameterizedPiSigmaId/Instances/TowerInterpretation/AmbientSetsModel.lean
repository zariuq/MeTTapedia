import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.AmbientSets
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators
import Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure

/-!
# The set model of the tower inside the sets

The tower inside the sets (`AmbientSets`) has the universes of the tower, the type of all sets
with every universe as a member, and the sort `classes` of that type. This file reads it in
sets.

**A stage** (`Stage`): a set `all` for the type of all sets and a set `classes` for its sort,
over a reading of the tower's heads, such that every universe of the tower is a member of
`all`, both are closed universes, and `all` is a member of `classes`. Over a stage the rules
of the heads hold (`universeModel`), so the package without declarations has a set model
(`bare_setModel`): the universes of the tower are sets among the sets.

**The stages of the tower lie in every set that is closed under the universe operation**
(`universeSet_mem_of_closed`): a closed universe that contains the seed, the least closed
universe around each of its members, and the range of every family of its members indexed by
the levels below a level, contains every stage of the tower.

**All sets of one size as one set of the next** (`lowerSets_stage`): the sets of a universe of
Lean, carried into the next universe, form one set there. It is a closed universe, with no
assumption. Relative to cofinally many inaccessible cardinals in both universes, the tower
over the natural numbers lies in it, and it is a stage with the least closed universe around
it as `classes`. So the tower inside the sets has a set model in which the type of all sets is
read as all the sets of the lower universe (`lowerSets_setModel`), every universe of the tower
is one of those sets, the universe at the least level is the least closed universe around the
natural numbers, and the universe at a successor level is the least closed universe around
the universe at the level (`lowerSets_universe_bot`, `lowerSets_universe_succ`): the tower is
the iteration of the universe operation.

Negative examples. The type of all sets is a member of no universe of the tower in this
model (`lowerSets_notMem_universe`). No reading in sets has both the type of all sets in a
universe and that universe among the sets (`no_model_both_ways`): the two placements of the
sets exclude each other.

Lemmas that belong with the universe lift (`lift_insert`, `lift_numeral`, `lift_omega`,
`range_mem_carrierCode`) and with the closed universes (`Closed.insert_mem`) are stated here
under their names.
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

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace AmbientSets

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed univOf mem_univOf univOf_closed)
open ZFSetUniverseLift (carrierCode carrierCode_closed omega_mem_carrierCode
  range_mem_carrierCode univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet universeSet_eq earlierStages universeSet_closed
  universeSet_bot universeSet_succ)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayInterpretation (UniverseModel)
open ZFSetTraceProducts (tracePiSet)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode)

universe u

variable {L : Type} [LevelOrder L]

/-! ## A stage -/

section Stage

variable (towerValue : LevelTower.Head L → ZFSet.{u}) (all classes : ZFSet.{u})

/-- **The values of the heads** over a reading of the tower's heads: the type of all sets is
read as `all` and its sort as `classes`. -/
def headValue : Head L → ZFSet.{u}
  | .tower t => towerValue t
  | .sets => all
  | .classes => classes

/-- **A stage**: every universe of the tower is a member of the set that reads the type of
all sets; that set and the set that reads `classes` are closed universes; the first is a
member of the second. -/
structure Stage : Prop where
  universe_mem : ∀ e : LevelExpr L, towerValue (.sort e) ∈ all
  all_closed : Closed all
  all_mem : all ∈ classes
  classes_closed : Closed classes

variable {towerValue all classes}

omit [LevelOrder L] in
/-- Every member of a universe of the tower is a set of the stage. -/
theorem Stage.universe_subset (stage : Stage towerValue all classes) (e : LevelExpr L) :
    towerValue (.sort e) ⊆ all :=
  stage.all_closed.transitive _ (stage.universe_mem e)

omit [LevelOrder L] in
/-- Every set of the stage is a member of `classes`. -/
theorem Stage.all_subset (stage : Stage towerValue all classes) : all ⊆ classes :=
  stage.classes_closed.transitive _ stage.all_mem

/-- **Over a stage the rules of the heads hold in sets.** -/
theorem universeModel (tower : UniverseModel (LevelTower.rules L) towerValue)
    (stage : Stage towerValue all classes) :
    UniverseModel (rules L) (headValue towerValue all classes) where
  headTyping_mem := by
    intro head level typed
    have known : HeadTyping head level := typed
    cases known with
    | tower towerTyped => exact tower.headTyping_mem towerTyped
    | member e => exact stage.universe_mem e
    | sets => exact stage.all_mem
  cumulative_subset := by
    intro lower upper below
    have known : Cumulative lower upper := below
    cases lower with
    | tower s =>
      cases upper with
      | tower t => exact tower.cumulative_subset known
      | sets =>
        cases s with
        | legacyGround => exact known.elim
        | sort e => exact stage.universe_subset e
      | classes =>
        cases s with
        | legacyGround => exact known.elim
        | sort e => exact fun _ hx => stage.all_subset (stage.universe_subset e hx)
    | sets =>
      cases upper with
      | tower _ => exact known.elim
      | sets => exact fun _ hx => hx
      | classes => exact stage.all_subset
    | classes =>
      cases upper with
      | tower _ => exact known.elim
      | sets => exact known.elim
      | classes => exact fun _ hx => hx
  pi_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    have known : Join domainLevel bodyLevel level := joined
    cases known with
    | tower towerJoined => exact tower.pi_mem towerJoined domainTyped B bodyTyped
    | sets => exact stage.all_closed.tracePiSet_mem domainTyped B bodyTyped
    | setsClasses =>
      exact stage.classes_closed.tracePiSet_mem (stage.all_subset domainTyped) B bodyTyped
    | classesSets =>
      exact stage.classes_closed.tracePiSet_mem domainTyped B
        fun x inside => stage.all_subset (bodyTyped x inside)
    | classes => exact stage.classes_closed.tracePiSet_mem domainTyped B bodyTyped
  sigma_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    have known : Join domainLevel bodyLevel level := joined
    cases known with
    | tower towerJoined => exact tower.sigma_mem towerJoined domainTyped B bodyTyped
    | sets => exact stage.all_closed.sigmaSet_mem domainTyped B bodyTyped
    | setsClasses =>
      exact stage.classes_closed.sigmaSet_mem (stage.all_subset domainTyped) B bodyTyped
    | classesSets =>
      exact stage.classes_closed.sigmaSet_mem domainTyped B
        fun x inside => stage.all_subset (bodyTyped x inside)
    | classes => exact stage.classes_closed.sigmaSet_mem domainTyped B bodyTyped
  identity_mem := by
    intro level isUniverse P
    have known : IsUniverse level := isUniverse
    have small : truthCode P ∈ towerValue (.sort LevelTower.zero) :=
      tower.identity_mem (LevelTower.IsUniverse.sort _) P
    cases known with
    | tower towerUniverse => exact tower.identity_mem towerUniverse P
    | sets => exact stage.universe_subset _ small
    | classes => exact stage.all_subset (stage.universe_subset _ small)

/-- Equal heads have equal values, when equal heads of the tower do. -/
theorem headEq_values
    (towerEq : ∀ {h h' : LevelTower.Head L}, LevelTower.HeadEq h h' → towerValue h = towerValue h')
    {k k' : Head L} (same : HeadEq k k') :
    headValue towerValue all classes k = headValue towerValue all classes k' := by
  cases k with
  | tower s =>
    cases k' with
    | tower t => exact towerEq same
    | sets => exact same.elim
    | classes => exact same.elim
  | sets =>
    cases k' with
    | tower _ => exact same.elim
    | sets => rfl
    | classes => exact same.elim
  | classes =>
    cases k' with
    | tower _ => exact same.elim
    | sets => exact same.elim
    | classes => rfl

/-- **The tower inside the sets has a set model over every stage.** -/
theorem bare_setModel (tower : UniverseModel (LevelTower.rules L) towerValue)
    (towerEq : ∀ {h h' : LevelTower.Head L}, LevelTower.HeadEq h h' → towerValue h = towerValue h')
    (stage : Stage towerValue all classes) (consts : DeclName → ZFSet.{u}) :
    SetModel (headValue towerValue all classes) consts (bare L) where
  universes := universeModel tower stage
  headEq same := headEq_values towerEq same
  constants known := by cases known
  steps step := step.elim

end Stage

/-! ## The two placements of the sets exclude each other -/

omit [LevelOrder L] in
/-- Negative example: **no reading in sets has the type of all sets as a member of a head and
that head as a member of the type of all sets.** A rule package with both typings has no
universe model. -/
theorem no_model_both_ways {R : Rules (Head L)} {k : Head L} (setsInside : R.headTyping .sets k)
    (insideSets : R.headTyping k .sets) (heads : Head L → ZFSet.{u}) :
    ¬ UniverseModel R heads := fun model =>
  ZFSet.mem_asymm (model.headTyping_mem setsInside) (model.headTyping_mem insideSets)

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

/-! ## All sets of one size as one set of the next -/

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

variable (ground : ZFSet.{u + 1}) (ν : Nat → L)

/-- The reading of the heads: the tower over the natural numbers; the type of all sets as the
set of all sets of the lower universe; `classes` as the least closed universe around it. -/
noncomputable abbrev lowerSetsHeads : Head L → ZFSet.{u + 1} :=
  headValue (interpretHead large ZFSet.omega ground ν) carrierCode.{u}
    (univOf large carrierCode.{u})

include small in
/-- **The sets of the lower universe are a stage** for the tower over the natural numbers. -/
theorem lowerSets_stage :
    Stage (interpretHead large ZFSet.omega ground ν) carrierCode.{u}
      (univOf large carrierCode.{u}) where
  universe_mem := fun _ => universeSet_mem_carrierCode small large _
  all_closed := carrierCode_closed
  all_mem := mem_univOf large _
  classes_closed := univOf_closed large _

variable {ground}

include small in
/-- **The tower inside the sets has a set model in which the type of all sets is read as all
the sets of the lower universe**, relative to cofinally many inaccessible cardinals in both
universes. -/
theorem lowerSets_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (consts : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν) consts (bare L) :=
  bare_setModel
    (ZFSetReplayUniverseModel.universeModel large ZFSet.omega ground ν groundTyped)
    (fun same => ZFSetReplayUniverseFormation.headEq_values large ZFSet.omega ground ν same)
    (lowerSets_stage small large ground ν) consts

variable (ground)

/-- **The universe at the least level is the least closed universe around the natural
numbers.** -/
theorem lowerSets_universe_bot :
    lowerSetsHeads (L := L) large ground ν
        (.tower (.sort (.const (LevelOrder.bot : L)))) =
      univOf large ZFSet.omega :=
  universeSet_bot large ZFSet.omega

/-- **The universe at a successor level is the least closed universe around the universe at
the level**: the tower is the iteration of the universe operation. -/
theorem lowerSets_universe_succ (e : LevelExpr L) :
    lowerSetsHeads (L := L) large ground ν (.tower (.sort (.succ e))) =
      univOf large (lowerSetsHeads (L := L) large ground ν (.tower (.sort e))) :=
  universeSet_succ large ZFSet.omega (e.eval ν)

include small in
/-- Negative example: **the set of all sets of the lower universe is a member of no universe
of the tower.** -/
theorem lowerSets_notMem_universe (e : LevelExpr L) :
    carrierCode.{u} ∉ lowerSetsHeads (L := L) large ground ν (.tower (.sort e)) := fun inside =>
  ZFSet.mem_asymm inside (universeSet_mem_carrierCode small large (e.eval ν))

end LowerSets

end AmbientSets
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
