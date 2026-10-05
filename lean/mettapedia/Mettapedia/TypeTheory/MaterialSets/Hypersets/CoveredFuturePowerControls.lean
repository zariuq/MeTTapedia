import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFunctorControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet

/-!
# Larger-object controls for small-covered contextual powers

Every singleton of the ambient hyperset carrier has an actual small cover;
the full ambient carrier cannot have such a cover. The latter argument
constructs a small membership graph from a hypothetical surjection and
contradicts separation, without selecting graph representatives.

An infinite growing family raised to a larger host universe retains its
distinct future predicates at the original small cover bound. An arbitrary
inverse image can nevertheless turn a covered singleton into the forbidden
full ambient carrier. Thus image closure does not assert inverse-image
closure under every larger argument map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open PowerClassPresheafDescent.Controls
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u

/-- A surjective small cover of all hypersets would produce a universal
hyperset, even when its receipts are not unique. -/
theorem hset_has_no_small_cover {I : Type u} (reading : I → HSet.{u}) :
    ¬ Function.Surjective reading := by
  intro covers
  let edge (first second : I) : Prop := reading second ∈ reading first
  have decoration : HSet.IsDecoration edge reading := by
    intro first value
    constructor
    · intro member
      obtain ⟨second, same⟩ := covers value
      refine ⟨second, ?_, same⟩
      change reading second ∈ reading first
      rw [same]
      exact member
    · rintro ⟨second, member, rfl⟩
      exact member
  let whole : HSet.{u} := HSet.range fun root : I => AccessiblePointedGraph.generated edge root
  apply HSet.not_exists_universal
  refine ⟨whole, fun value => ?_⟩
  obtain ⟨root, same⟩ := covers value
  apply HSet.mem_range.mpr
  refine ⟨root, ?_⟩
  change HSet.decorate edge root = value
  rw [← decoration.eq_decorate]
  exact same

def ambient : Stagesᵒᵖ ⥤ Type 1 where
  obj _ := HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def ambientTop (point : Stagesᵒᵖ) : Predicate ambient point where
  holds _ := True
  closed _ _ := trivial

theorem ambientTop_not_covered (point : Stagesᵒᵖ) :
    ¬ Nonempty (Enumeration (ambientTop point)) := by
  rintro ⟨enumeration⟩
  let present : PowerClassPresheafBaseChange.Future.Objects point := ⟨point, 𝟙 point⟩
  apply hset_has_no_small_cover (enumeration.value present)
  intro value
  exact (enumeration.covered present value).mp trivial

theorem singleton_has_original_cover (point : Stagesᵒᵖ) (value : HSet.{0}) :
    Nonempty (Enumeration (singletonPower ambient point value).val) :=
  ⟨singletonEnumeration ambient point value⟩

/-- This is an actual varying family in a larger host universe, not a
constant replacement of the original growing argument family. -/
def raised : Stagesᵒᵖ ⥤ Type 1 where
  obj point := ULift.{1} (growingSource.obj point)
  map step := TypeCat.ofHom (fun value => ⟨growingSource.map step value.down⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (growingSource.map_id_apply point value.down)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (growingSource.map_comp_apply earlier later value.down)

def raiseArguments : NaturalHom growingSource raised where
  app _ value := ⟨value⟩
  naturality _ _ := rfl

def raisedThreshold (bound : Nat) : Power raised (world 0) :=
  imagePower raiseArguments (world 0) (ofFull (FuturePowerFunctorControls.threshold bound))

def raisedFuture (level : Nat) : Arguments raised (world 0) :=
  ⟨(FuturePowerFunctorControls.futureArgument level).1,
    ⟨(FuturePowerFunctorControls.futureArgument level).2⟩⟩

theorem raised_future_truth (bound level : Nat) :
    (raisedThreshold bound).val.holds (raisedFuture level) ↔ bound ≤ level := by
  constructor
  · rintro ⟨value, same, holds⟩
    have decoded := congrArg ULift.down same
    change value = (FuturePowerFunctorControls.futureArgument level).2 at decoded
    change (FuturePowerFunctorControls.threshold bound).holds
      ⟨(FuturePowerFunctorControls.futureArgument level).1, value⟩ at holds
    rw [decoded] at holds
    exact holds
  · intro available
    exact ⟨(FuturePowerFunctorControls.futureArgument level).2, rfl, available⟩

theorem raisedThreshold_injective : Function.Injective raisedThreshold := by
  intro first second same
  have firstAtSecond := congrArg (fun predicate : Power raised (world 0) =>
    predicate.val.holds (raisedFuture second)) same
  have firstBelow : first ≤ second := (raised_future_truth first second).mp
    (Eq.mpr firstAtSecond ((raised_future_truth second second).mpr (Nat.le_refl second)))
  have secondAtFirst := congrArg (fun predicate : Power raised (world 0) =>
    predicate.val.holds (raisedFuture first)) same
  have secondBelow : second ≤ first := (raised_future_truth second first).mp
    (Eq.mp secondAtFirst ((raised_future_truth first first).mpr (Nat.le_refl first)))
  exact Nat.le_antisymm firstBelow secondBelow

theorem raisedThreshold_has_original_cover (bound : Nat) :
    Nonempty (Enumeration (raisedThreshold bound).val) :=
  (raisedThreshold bound).property

theorem raised_later_thresholds_empty_present (value : raised.obj (world 0)) :
    ¬ (raisedThreshold 1).val.holds (current raised (world 0) value) ∧
      ¬ (raisedThreshold 2).val.holds (current raised (world 0) value) := by
  constructor
  · rintro ⟨argument, _, impossible⟩
    exact Nat.not_succ_le_zero 0 impossible
  · rintro ⟨argument, _, impossible⟩
    exact Nat.not_succ_le_zero 1 impossible

def forgetAmbient : NaturalHom ambient (terminal (E := Stagesᵒᵖ)) where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def singletonInverse (point : Stagesᵒᵖ) : Predicate ambient point :=
  inverseImage forgetAmbient point
    (singletonPower (terminal (E := Stagesᵒᵖ)) point PUnit.unit).val

theorem singletonInverse_is_full_ambient (point : Stagesᵒᵖ) :
    singletonInverse point = ambientTop point := by
  apply Predicate.ext
  intro argument
  exact ⟨fun _ => trivial, fun _ => rfl⟩

theorem inverseImage_does_not_preserve_small_covers (point : Stagesᵒᵖ) :
    ¬ Nonempty (Enumeration (singletonInverse point)) := by
  rw [singletonInverse_is_full_ambient]
  exact ambientTop_not_covered point

end Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls
