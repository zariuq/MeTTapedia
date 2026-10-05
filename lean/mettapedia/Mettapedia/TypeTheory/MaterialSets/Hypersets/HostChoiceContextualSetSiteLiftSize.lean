import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructivePowerFinalityObstruction

/-!
# A genuinely new set at every successor-site world

The lower set carrier is small at the successor branch bound. Its full
future Russell predicate therefore has a constructed truth-subtype cover.
The upper inverse structure assembles its embedded image into an actual
upper set. A local constructive diagonal argument excludes every lower
value from that reading, proving that the model embedding is proper at
every world, independently of cardinal arithmetic or a selected inverse.

This compares the actual optional contextual models. It does not identify
all upper sets with lifted lower codes or add a native universe calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSize

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open CoveredFuturePowerFamilies CoveredFuturePowerFunctor PowerClassPresheafBaseChange
open HostChoiceContextualSetSiteLift HostChoiceContextualSetInterpretation

universe u t

/-- Naturality turns one alleged Russell value into compatible readings
at all its actual futures, so even a single such value is impossible. -/
theorem russell_cannot_be_value {E : Type t} [Category.{t} E] (A : E ⥤ Type t)
    (coalgebra : NaturalHom A (family A)) (point : E) (value : A.obj point) :
    coalgebra.app point value ≠ ConstructivePowerFinalityObstruction.russellPower A coalgebra point := by
  intro alleged
  have reading {target : E} (arrow : point ⟶ target) :
      coalgebra.app target (A.map arrow value) =
        ConstructivePowerFinalityObstruction.russellPower A coalgebra target :=
    (coalgebra.naturality arrow value).symm.trans
      ((congrArg (restrictPower A arrow) alleged).trans
        (ConstructivePowerFinalityObstruction.russellPower_restrict A coalgebra arrow))
  have absent {target : E} (arrow : point ⟶ target) :
      ¬ (coalgebra.app target (A.map arrow value)).val.holds
        (current A target (A.map arrow value)) := by
    intro member
    have diagonal := member
    rw [reading arrow] at diagonal
    have identity := diagonal target (𝟙 target)
    change ¬ (coalgebra.app target (A.map (𝟙 target) (A.map arrow value))).val.holds
      (current A target (A.map (𝟙 target) (A.map arrow value))) at identity
    rw [A.map_id_apply] at identity
    exact identity member
  have atRoot : ¬ (coalgebra.app point value).val.holds (current A point value) := by
    simpa only [A.map_id_apply] using absent (𝟙 point)
  apply atRoot
  rw [alleged]
  intro target arrow
  exact absent arrow

variable {D : Type u} [Category.{u} D]

theorem predicate_image_injective (point : UpperSite (D := D)) :
    Function.Injective (imagePower (embedding (D := D)) point) := by
  intro first second same
  apply Subtype.ext
  apply Predicate.ext
  rintro ⟨future, child⟩
  have agrees : (imagePower embedding point first).val.holds
      ⟨future, embedding.app future.1 child⟩ ↔
    (imagePower embedding point second).val.holds
      ⟨future, embedding.app future.1 child⟩ :=
    Iff.of_eq (congrArg (fun power : Power upperSets point =>
      power.val.holds ⟨future, embedding.app future.1 child⟩) same)
  constructor
  · intro available
    obtain ⟨original, observed, admitted⟩ := agrees.mp ⟨child, rfl, available⟩
    have originals := embedding_injective future.1 observed
    simpa only [originals] using admitted
  · intro available
    obtain ⟨original, observed, admitted⟩ := agrees.mpr ⟨child, rfl, available⟩
    have originals := embedding_injective future.1 observed
    simpa only [originals] using admitted

noncomputable def newRussellSet : (upperSets (D := D)).sections :=
  Finality.assemble.mapSection
    ((imageHom embedding).mapSection
      (ConstructivePowerFinalityObstruction.russellSection source sourceCoalgebra))

theorem newRussellSet_reading (point : UpperSite (D := D)) :
    Finality.unfold.app point (newRussellSet.val point) =
      imagePower embedding point
        (ConstructivePowerFinalityObstruction.russellPower source sourceCoalgebra point) :=
  Finality.unfold_assemble point _

theorem newRussellSet_not_embedded (point : UpperSite (D := D)) (original : source.obj point) :
    embedding.app point original ≠ newRussellSet.val point := by
  intro same
  apply russell_cannot_be_value source sourceCoalgebra point original
  apply predicate_image_injective point
  have square := congrArg (fun operation : NaturalHom source (family upperSets) =>
    operation.app point original) embedding_square
  exact square.trans
    ((congrArg (Finality.unfold.app point) same).trans (newRussellSet_reading point))

theorem embedding_not_surjective (point : UpperSite (D := D)) :
    ¬ Function.Surjective (embedding.app point) := by
  intro covers
  obtain ⟨original, same⟩ := covers (newRussellSet.val point)
  exact newRussellSet_not_embedded point original same

theorem embedding_is_proper (point : UpperSite (D := D)) :
    Function.Injective (embedding.app point) ∧ ¬ Function.Surjective (embedding.app point) :=
  ⟨embedding_injective point, embedding_not_surjective point⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSize
