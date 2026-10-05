import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebras
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebrasControls

/-!
# Reachable material subcoalgebra and retained receipt controls

The genuine reachable coalgebra contains the initially empty value and a
cyclic future child in the infinite observed material family. Its monic
inclusion and its small generator's covering map satisfy the complete
future-coalgebra comparisons. Two authored branch tags supply distinct
generator receipts with the same reachable value. Consequently a value
decoder cannot reconstruct every source receipt; this does not deny the
possibility of a one-sided section of a covering map.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebrasControls

open _root_.CategoryTheory
open ContextualGeneratedCoalgebrasControls
open ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev reachable := ContextualReachableCoalgebras.reachable wide allCoalgebra seed
abbrev reachCover := ContextualReachableCoalgebras.cover wide allCoalgebra branchEnumerations seed
abbrev reachCoalgebra := ContextualReachableCoalgebras.coalgebra wide allCoalgebra branchEnumerations seed
abbrev inclusion := ContextualReachableCoalgebras.inclusion wide allCoalgebra seed

def oldValue : reachable.obj initialPoint := reachCover.app initialPoint rootReceipt

def cyclicValue : reachable.obj (observedPoint model worldCoding futureRaw) :=
  reachCover.app (observedPoint model worldCoding futureRaw) newCyclicReceipt

theorem oldValue_empty : oldValue.val.val = ∅ := root_material_value

theorem cyclicValue_quine : cyclicValue.val.val = HSet.quineAtom := new_cyclic_material_value

theorem genuine_future_child :
    (reachCoalgebra.app initialPoint oldValue).val.holds
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩, cyclicValue⟩ :=
  (ContextualReachableCoalgebras.cover_future_iff wide allCoalgebra branchEnumerations seed initialPoint
    rootReceipt ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ cyclicValue).mpr
      ⟨newCyclicReceipt, generated_cyclic_future, rfl⟩

theorem actual_monic_inclusion_square :
    reachCoalgebra.comp (CoveredFuturePowerFunctor.imageHom inclusion) = inclusion.comp allCoalgebra :=
  ContextualReachableCoalgebras.inclusion_square wide allCoalgebra branchEnumerations seed

theorem actual_generated_cover_square :
    (ContextualGeneratedCoalgebras.generatedCoalgebra wide allCoalgebra branchEnumerations seed).comp
      (CoveredFuturePowerFunctor.imageHom reachCover) = reachCover.comp reachCoalgebra :=
  ContextualReachableCoalgebras.cover_square wide allCoalgebra branchEnumerations seed

theorem actual_cover_onto (point : actualContext.base.Elements) : Function.Surjective (reachCover.app point) :=
  ContextualReachableCoalgebras.cover_surjective wide allCoalgebra branchEnumerations seed point

theorem actual_inclusion_injective (point : actualContext.base.Elements) : Function.Injective (inclusion.app point) :=
  ContextualReachableCoalgebras.inclusion_injective wide allCoalgebra seed point

def taggedReceipt (tag : Bool) : generated.obj (observedPoint model worldCoding futureRaw) :=
  ContextualGeneratedCoalgebras.childReceipt wide allCoalgebra branchEnumerations seed rootPath
    ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ (futureArgument, tag)

theorem taggedReceipt_distinct : taggedReceipt true ≠ taggedReceipt false := by
  intro same
  exact taggedChild_distinct (congrArg Sigma.fst same)

theorem tagged_cover_equal :
    reachCover.app (observedPoint model worldCoding futureRaw) (taggedReceipt true) =
      reachCover.app (observedPoint model worldCoding futureRaw) (taggedReceipt false) := Subtype.ext rfl

theorem cover_not_injective :
    ¬ Function.Injective (reachCover.app (observedPoint model worldCoding futureRaw)) :=
  fun injective => taggedReceipt_distinct (injective tagged_cover_equal)

/-- A two-sided receipt decoder is impossible for this cover. The theorem
does not assert that all covering maps lack one-sided sections. -/
theorem no_value_decoder_reconstructs_all_receipts :
    ¬ ∃ decode : reachable.obj (observedPoint model worldCoding futureRaw) →
          generated.obj (observedPoint model worldCoding futureRaw),
      ∀ receipt, decode (reachCover.app (observedPoint model worldCoding futureRaw) receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  exact taggedReceipt_distinct
    ((recovers (taggedReceipt true)).symm.trans
      ((congrArg decode tagged_cover_equal).trans (recovers (taggedReceipt false))))

theorem varying_reachable_material_model :
    oldValue.val.val = ∅ ∧ cyclicValue.val.val = HSet.quineAtom ∧
      (reachCoalgebra.app initialPoint oldValue).val.holds
        ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩, cyclicValue⟩ ∧
      ¬ Function.Injective (reachCover.app (observedPoint model worldCoding futureRaw)) :=
  ⟨oldValue_empty, cyclicValue_quine, genuine_future_child, cover_not_injective⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebrasControls
