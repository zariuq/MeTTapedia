import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation
import Mettapedia.TypeTheory.PresheafSiteLift

/-!
# The actual contextual set model on a successor site

Worlds and actual arrows are raised by the explicit site category. The
lower set coalgebra is transported with all its future indices. Each
original receipt is explicitly raised to the successor branch bound;
existential covers are eliminated only into their existence proofs.

The upper model's final readout constructs an actual embedding. Reflection
of future bisimulation proves injectivity, and the full coalgebra square
identifies every upper member of an embedded set as an embedded lower
member at the same actual future arrow. External host Choice is inherited
from the two actual final models; it is not a native foundation rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLift

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open PowerClassPresheafBaseChange
open HostChoiceContextualSetInterpretation

universe u
variable {D : Type u} [Category.{u} D]

abbrev UpperSite := PresheafSiteLift.Site D
abbrev lowerSets : D ⥤ Type (u+1) := Finality.sets (D := D)
abbrev upperSets : UpperSite (D := D) ⥤ Type (u+2) := Finality.sets (D := UpperSite (D := D))

/-- The old set values, retaining their complete maps on the genuinely raised site. -/
def source : UpperSite (D := D) ⥤ Type (u+1) :=
  PresheafSiteLift.compose PresheafSiteLift.Site.downFunctor lowerSets

def lowerFutures (point : UpperSite (D := D)) :
    Future.Objects point ⥤ Future.Objects point.down where
  obj future := ⟨future.1.down, future.2.down⟩
  map move := ⟨move.1.down, congrArg ULift.down move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def lowerArguments (point : UpperSite (D := D)) :
    Arguments source point ⥤ Arguments lowerSets point.down where
  obj argument := ⟨(lowerFutures point).obj argument.1, argument.2⟩
  map step := ⟨(lowerFutures point).map step.1, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def sourcePredicate (point : UpperSite (D := D)) (parent : source.obj point) : Predicate source point where
  holds argument := (Finality.unfold.app point.down parent).val.holds ((lowerArguments point).obj argument)
  closed move available := (Finality.unfold.app point.down parent).val.closed ((lowerArguments point).map move) available

/-- This raises supplied original receipts; it never selects them from a
propositional cover. -/
def raisedEnumeration (point : UpperSite (D := D)) (parent : source.obj point)
    (enumeration : Enumeration (Finality.unfold.app point.down parent).val) :
    Enumeration (sourcePredicate point parent) where
  Carrier future := ULift.{u+1,u} (enumeration.Carrier ((lowerFutures point).obj future))
  value future receipt := enumeration.value ((lowerFutures point).obj future) receipt.down
  covered future argument := by
    constructor
    · intro available
      obtain ⟨receipt, same⟩ := (enumeration.covered ((lowerFutures point).obj future) argument).mp available
      exact ⟨ULift.up receipt, same⟩
    · rintro ⟨receipt, same⟩
      exact (enumeration.covered ((lowerFutures point).obj future) argument).mpr ⟨receipt.down, same⟩

def sourcePower (point : UpperSite (D := D)) (parent : source.obj point) : Power source point :=
  ⟨sourcePredicate point parent, by
    obtain ⟨enumeration⟩ := (Finality.unfold.app point.down parent).property
    exact ⟨raisedEnumeration point parent enumeration⟩⟩

def sourceCoalgebra : NaturalHom (source (D := D)) (family source) where
  app := sourcePower
  naturality {first second} step parent := by
    apply Subtype.ext
    apply Predicate.ext
    intro argument
    exact Iff.of_eq (congrArg (fun power : Power lowerSets second.down =>
      power.val.holds ((lowerArguments second).obj argument))
      (Finality.unfold.naturality step.down parent))

theorem source_future (point target : UpperSite (D := D)) (arrow : point ⟶ target)
    (parent : source.obj point) (child : source.obj target) :
    (sourceCoalgebra.app point parent).val.holds ⟨⟨target, arrow⟩, child⟩ ↔
      FutureMember arrow.down child parent := Iff.rfl

/-- Reflection uses every original future, with its actual raised arrow. -/
theorem source_bisimulation_reflects {point : UpperSite (D := D)} {first second : source.obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar sourceCoalgebra point first second) :
    ContextualCoalgebraBisimulation.Bisimilar (Finality.unfold (D := D)) point.down first second := by
  let relation := fun (oldPoint : D) (left right : lowerSets.obj oldPoint) =>
    ContextualCoalgebraBisimulation.Bisimilar sourceCoalgebra
      (PresheafSiteLift.Site.upFunctor.obj oldPoint) left right
  apply ContextualCoalgebraBisimulation.greatest Finality.unfold (relation := relation)
  · exact {
      stable := fun {_ _} step {_ _} admitted =>
        ContextualCoalgebraBisimulation.bisimilar_stable sourceCoalgebra
          (PresheafSiteLift.Site.upFunctor.map step) admitted
      forth := fun {_ _ _} admitted future {_} available =>
        (ContextualCoalgebraBisimulation.bisimilar_isBisimulation sourceCoalgebra).forth admitted
          ⟨PresheafSiteLift.Site.upFunctor.obj future.1, PresheafSiteLift.Site.upFunctor.map future.2⟩ available
      back := fun {_ _ _} admitted future {_} available =>
        (ContextualCoalgebraBisimulation.bisimilar_isBisimulation sourceCoalgebra).back admitted
          ⟨PresheafSiteLift.Site.upFunctor.obj future.1, PresheafSiteLift.Site.upFunctor.map future.2⟩ available }
  · exact related

theorem lower_separated : ContextualCoalgebraQuotient.BehaviorallySeparated (Finality.unfold (D := D)) := by
  intro point first second related
  have observed := ContextualCoalgebraBisimulation.bisimilar_preserved Finality.unfold
    (HostChoiceContextualCoalgebraFinality.lower (ContextualSmallCoalgebraGenerators.quotient (D := D)))
    ContextualSmallCoalgebraGenerators.quotientCoalgebra
    (HostChoiceContextualCoalgebraFinality.lower_square ContextualSmallCoalgebraGenerators.quotientCoalgebra) related
  apply ULift.ext
  exact ContextualSmallCoalgebraGenerators.quotient_separated point first.down second.down observed

theorem source_separated : ContextualCoalgebraQuotient.BehaviorallySeparated (sourceCoalgebra (D := D)) :=
  fun _ _ _ related => lower_separated _ _ _ (source_bisimulation_reflects related)

/-- The existing upper final readout is applied to the constructed raised
lower coalgebra. This is a map between actual contextual set models. -/
noncomputable def embedding : NaturalHom (source (D := D)) upperSets :=
  (HostChoiceContextualCoalgebraFinality.readout sourceCoalgebra).comp
    (HostChoiceContextualCoalgebraFinality.raise.{u+1,0,u+2}
      (ContextualSmallCoalgebraGenerators.quotient (D := UpperSite (D := D))))

theorem embedding_square :
    sourceCoalgebra.comp (imageHom (embedding (D := D))) = embedding.comp Finality.unfold :=
  ContextualSmallCoalgebraComparisons.compose_square _ _ _ _ _
    (HostChoiceContextualCoalgebraFinality.readout_square sourceCoalgebra)
    (HostChoiceContextualCoalgebraFinality.raise_square.{u+1,0,u+2}
      ContextualSmallCoalgebraGenerators.quotientCoalgebra)

theorem embedding_kernel (point : UpperSite (D := D)) (first second : source.obj point) :
    embedding.app point first = embedding.app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar sourceCoalgebra point first second := by
  constructor
  · intro same
    exact (HostChoiceContextualCoalgebraFinality.readout_kernel sourceCoalgebra point first second).mp
      (congrArg ULift.down same)
  · intro related
    exact congrArg ULift.up
      ((HostChoiceContextualCoalgebraFinality.readout_kernel sourceCoalgebra point first second).mpr related)

theorem embedding_injective (point : UpperSite (D := D)) : Function.Injective (embedding.app point) :=
  fun _ _ same => source_separated point _ _ ((embedding_kernel point _ _).mp same)

/-- Every upper future member of an embedded lower set comes from a lower
member at the identical original context and arrow. -/
theorem future_member_image {point target : UpperSite (D := D)} (arrow : point ⟶ target)
    (parent : source.obj point) (child : upperSets.obj target) :
    FutureMember arrow child (embedding.app point parent) ↔
      ∃ original : source.obj target, embedding.app target original = child ∧
        FutureMember arrow.down original parent :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth sourceCoalgebra embedding Finality.unfold
    embedding_square point parent ⟨target, arrow⟩ child

theorem future_member_embedding_iff {point target : UpperSite (D := D)} (arrow : point ⟶ target)
    (parent : source.obj point) (child : source.obj target) :
    FutureMember arrow (embedding.app target child) (embedding.app point parent) ↔
      FutureMember arrow.down child parent := by
  constructor
  · intro available
    obtain ⟨original, same, belongs⟩ := (future_member_image arrow parent (embedding.app target child)).mp available
    exact embedding_injective target same ▸ belongs
  · intro available
    exact (future_member_image arrow parent (embedding.app target child)).mpr ⟨child, rfl, available⟩

theorem current_member_image (point : UpperSite (D := D)) (parent : source.obj point) (child : upperSets.obj point) :
    Member point child (embedding.app point parent) ↔
      ∃ original : source.obj point, embedding.app point original = child ∧ Member point.down original parent :=
  future_member_image (𝟙 point) parent child

theorem current_member_embedding_iff (point : UpperSite (D := D)) (parent child : source.obj point) :
    Member point (embedding.app point child) (embedding.app point parent) ↔ Member point.down child parent :=
  future_member_embedding_iff (𝟙 point) parent child

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLift
