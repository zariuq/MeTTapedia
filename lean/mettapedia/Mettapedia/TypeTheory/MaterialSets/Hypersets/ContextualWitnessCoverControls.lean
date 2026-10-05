import Mettapedia.TypeTheory.DisplayedContextualWitnessCover
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls

/-!
# Small contextual covers with wide, advancing and cyclic witnesses

An actual infinite-loop element context acts on material natural members,
whose host carrier is `Type (u+1)`. Its free contextual cover has fibres
literally in `Type u`. Transport of the authored zero witness reaches every
material ordinal and preserves the entire arrow history. The wide functor
and this small cover both lack a compatible global section; their covering
projection therefore has no natural splitting.

A separate observed-family instance retains varying empty/cyclic material
values through the constructed displayed covering projection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWitnessCoverControls

open _root_.CategoryTheory Mettapedia.TypeTheory.ContextualWitnessCover

universe u

namespace Advancing

open ContextualSeparationCollectionControls.Advancing

/-- The target is genuinely wider than the free source: bare members of an
original-bound material natural set live in host `Type (u+1)`. -/
def wide : context.{u}.base.Elements ⥤ Type (u + 1) where
  obj _ := NaturalMember.{u}
  map arrow := TypeCat.ofHom (advance arrow.val.unop.down)
  map_id _ := rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    change advance (second.val.unop.down + first.val.unop.down) value =
      advance second.val.unop.down (advance first.val.unop.down value)
    rw [Nat.add_comm, advance_add]

def zeroWitness (_ : context.{u}.base.Elements) : NaturalMember.{u} :=
  ⟨∅, NaturalOrdinalModel.zero_member_naturals⟩

def witnessMap : NaturalHom (free (E := context.{u}.base.Elements)) wide :=
  fromWitness wide zeroWitness

def receipt (atPoint : context.{u}.base.Elements) (number : Nat) :
    (free (E := context.base.Elements)).obj atPoint := ⟨atPoint, loop atPoint number⟩

theorem advance_zero_ordinal (number : Nat) :
    (advance number (zeroWitness (point : context.{u}.base.Elements))).val =
      NaturalOrdinalModel.ordinal number := by
  induction number with
  | zero => exact NaturalOrdinalModel.ordinal_zero.symm
  | succ number previous =>
    change NaturalOrdinalModel.successor (advance number (zeroWitness point)).val =
      NaturalOrdinalModel.ordinal (number + 1)
    rw [previous, NaturalOrdinalModel.ordinal_successor]

theorem receipt_value (atPoint : context.{u}.base.Elements) (number : Nat) :
    ((witnessMap.app atPoint) (receipt atPoint number)).val = NaturalOrdinalModel.ordinal number :=
  advance_zero_ordinal number

/-- All infinitely many loop receipts remain distinguished in the actual
small cover; their transported material values distinguish them too. -/
theorem receipt_injective (atPoint : context.{u}.base.Elements) :
    Function.Injective (receipt atPoint) := by
  intro first second same
  have values := congrArg (fun receipt => (witnessMap.app atPoint receipt).val) same
  rw [receipt_value, receipt_value] at values
  exact NaturalOrdinalModel.ordinal_injective values

theorem wide_map_surjective (atPoint : context.{u}.base.Elements) :
    Function.Surjective (witnessMap.app atPoint) := by
  intro value
  obtain ⟨number, same⟩ := (NaturalOrdinalModel.member_naturals value.val).mp value.property
  exact ⟨receipt atPoint number, Subtype.ext ((receipt_value atPoint number).trans same)⟩

theorem witness_not_compatible :
    wide.{u}.map (loop point 1) (zeroWitness point) ≠ zeroWitness point :=
  advance_no_fixed_point _

theorem no_wide_section : ¬ Nonempty wide.{u}.sections := by
  rintro ⟨term⟩
  have fixed := term.property (loop point 1)
  exact advance_no_fixed_point (term.val point) fixed

theorem no_small_cover_section :
    ¬ Nonempty (free (E := context.{u}.base.Elements)).sections :=
  free_no_section_of_target_no_section wide zeroWitness no_wide_section

theorem projection_covers (atPoint : context.{u}.base.Elements) :
    Function.Surjective ((projection (E := context.base.Elements)).app atPoint) :=
  projection_surjective atPoint

/-- The actual covering projection has no natural splitting, despite being
surjective at every point and even mapping onto every wide natural witness. -/
theorem projection_not_split :
    ¬ ∃ split : NatTrans (terminal (E := context.{u}.base.Elements)) free,
      ∀ atPoint (value : (terminal (E := context.base.Elements)).obj atPoint),
        projection.app atPoint (split.app atPoint value) = value := by
  rintro ⟨split, _⟩
  exact no_small_cover_section ⟨sectionOfTerminalMap split⟩

end Advancing

namespace Varying

open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.ObservedGeneratedModel
open ContextualSeparationCollectionControls.Varying
open Mettapedia.TypeTheory.DisplayedContextualWitnessCover

def selected (atPoint : (Mettapedia.GSLT.ObservedGeneratedModel.context model worldCoding).base.Elements) : separated.family.obj atPoint :=
  ⟨positiveSection.val atPoint, rfl⟩

theorem covering_projection_retains_value (atPoint : (Mettapedia.GSLT.ObservedGeneratedModel.context model worldCoding).base.Elements) :
    (separated.model atPoint).value
        ((Mettapedia.TypeTheory.DisplayedContextualWitnessCover.projection separated.family).app atPoint (localLift separated.family atPoint (selected atPoint))) =
      (observedInput.model atPoint).value (positiveSection.val atPoint) := rfl

theorem old_value : (separated.model (observedPoint model worldCoding oldRaw)).value
    ((Mettapedia.TypeTheory.DisplayedContextualWitnessCover.projection separated.family).app _ (localLift separated.family _ (selected _))) = ∅ :=
  (covering_projection_retains_value _).trans old_section_value

theorem cyclic_later_value : (separated.model (observedPoint model worldCoding newRaw)).value
    ((Mettapedia.TypeTheory.DisplayedContextualWitnessCover.projection separated.family).app _ (localLift separated.family _ (selected _))) = HSet.quineAtom :=
  (covering_projection_retains_value _).trans new_section_value

theorem material_values_vary : (separated.model (observedPoint model worldCoding oldRaw)).value
    ((Mettapedia.TypeTheory.DisplayedContextualWitnessCover.projection separated.family).app _ (localLift separated.family _ (selected _))) ≠
      (separated.model (observedPoint model worldCoding newRaw)).value
        ((Mettapedia.TypeTheory.DisplayedContextualWitnessCover.projection separated.family).app _ (localLift separated.family _ (selected _))) := by
  rw [old_value, cyclic_later_value]
  exact HSet.empty_ne_quineAtom

end Varying

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWitnessCoverControls
