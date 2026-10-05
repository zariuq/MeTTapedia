import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCollectionGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection

/-!
# Constructed successor receipts for the material coalgebra recipient

The all-small-coalgebra material recipient has a class carrier in `Type
(u+1)` and an actual collecting graph at bound `u+1`. Its graph and member
inverse construct every fibre dictionary on the successor context. The
whole future coalgebra there has explicit truth-subtype receipts in that
same successor universe.

Every original context and arrow is retained by the proved successor-site
comparison. The original `u`-covered coalgebra is pulled back as a complete
future predicate; its successor receipts are constructed directly, without
selecting one of its propositionally existing original-bound covers.

Dependent formation and separation use these actual dictionaries. This
raises the receipt bound, and does not turn relative original-bound
recipient universality into full finality for the larger power functor.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveMaterialRecipientModel

open CategoryTheory ContextualGeneratedUniverse PowerClassPresheafBaseChange
open Mettapedia.TypeTheory ContextualWitnessCover

universe u

section ReceiptRestriction

variable {D : Type u} [Category.{u} D]
variable {E : Type (u + 1)} [Category.{u + 1} E]
variable (change : E ⥤ D) (A : D ⥤ Type (u + 1))

/-- The source values already have the successor size; only their actual
context is changed. -/
def restrictedFamily : E ⥤ Type (u + 1) := PresheafSiteLift.compose change A

def futureBelow (point : E) (future : Future.Objects point) : Future.Objects (change.obj point) :=
  ⟨change.obj future.1, change.map future.2⟩

variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))

def restrictedPredicate (point : E) (value : (restrictedFamily change A).obj point) :
    CoveredFuturePowerFamilies.Predicate (restrictedFamily change A) point where
  holds argument := (coalgebra.app (change.obj point) value).val.holds
    ⟨futureBelow change point argument.1, argument.2⟩
  closed {first second} move available := by
    let lowerFirst : CoveredFuturePowerFamilies.Arguments A (change.obj point) :=
      ⟨futureBelow change point first.1, first.2⟩
    let lowerSecond : CoveredFuturePowerFamilies.Arguments A (change.obj point) :=
      ⟨futureBelow change point second.1, second.2⟩
    let lowerArrow : lowerFirst.1 ⟶ lowerSecond.1 :=
      ⟨change.map move.1.1,
        (change.map_comp first.1.2 move.1.1).symm.trans
          (congrArg (fun arrow => change.map arrow) move.1.2)⟩
    have values : A.map (change.map move.1.1) first.2 = second.2 := move.2
    exact (coalgebra.app (change.obj point) value).val.closed
      (⟨lowerArrow, values⟩ : lowerFirst ⟶ lowerSecond) available

theorem restrictedPredicate_restrict {first second : E} (step : first ⟶ second)
    (value : (restrictedFamily change A).obj first) :
    CoveredFuturePowerFamilies.restrict (restrictedFamily change A) step
      (restrictedPredicate change A coalgebra first value) =
    restrictedPredicate change A coalgebra second ((restrictedFamily change A).map step value) := by
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, argument⟩
  have same := congrArg (fun power : CoveredFuturePowerFamilies.Power A (change.obj second) =>
    power.val.holds ⟨futureBelow change second future, argument⟩)
    (coalgebra.naturality (change.map step) value)
  change (coalgebra.app (change.obj first) value).val.holds
    ⟨⟨change.obj future.1, change.map (step ≫ future.2)⟩, argument⟩ ↔ _
  rw [change.map_comp]
  exact iff_of_eq same

/-- All successor truth receipts are kept as data, uniformly at every
source value and every complete future. -/
def restrictedEnumeration (point : E) (value : (restrictedFamily change A).obj point) :
    CoveredFuturePowerFamilies.Enumeration (restrictedPredicate change A coalgebra point value) :=
  CoveredFuturePowerFamilies.smallEnumeration (restrictedPredicate change A coalgebra point value)

def restrictedCoalgebra : NaturalHom (restrictedFamily change A)
    (CoveredFuturePowerFamilies.family (restrictedFamily change A)) where
  app point value := ⟨restrictedPredicate change A coalgebra point value,
    ⟨restrictedEnumeration change A coalgebra point value⟩⟩
  naturality step value := Subtype.ext (restrictedPredicate_restrict change A coalgebra step value)

theorem restricted_truth (point : E) (value : (restrictedFamily change A).obj point)
    (future : Future.Objects point) (child : (restrictedFamily change A).obj future.1) :
    ((restrictedCoalgebra change A coalgebra).app point value).val.holds ⟨future, child⟩ ↔
      (coalgebra.app (change.obj point) value).val.holds
        ⟨futureBelow change point future, child⟩ := Iff.rfl

variable {B : D ⥤ Type (u + 1)} (operation : NaturalHom A B)

def restrictedHom : NaturalHom (restrictedFamily change A) (restrictedFamily change B) where
  app point := operation.app (change.obj point)
  naturality step value := operation.naturality (change.map step) value

/-- The whole future image square survives the actual context change.
Both child-image directions are compared at the same lowered arrow. -/
theorem restricted_square (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target) :
    (restrictedCoalgebra change A coalgebra).comp
        (CoveredFuturePowerFunctor.imageHom (restrictedHom change A operation)) =
      (restrictedHom change A operation).comp (restrictedCoalgebra change B target) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, child⟩
  have same := congrArg (fun map : NaturalHom A (CoveredFuturePowerFamilies.family B) =>
    (map.app (change.obj point) value).val.holds
      ⟨futureBelow change point future, child⟩) square
  exact iff_of_eq same

theorem restricted_isBisimulation {relation : ContextualCoalgebraBisimulation.Relation A}
    (bisimulation : ContextualCoalgebraBisimulation.IsBisimulation coalgebra relation) :
    ContextualCoalgebraBisimulation.IsBisimulation (restrictedCoalgebra change A coalgebra)
      (fun point left right => relation (change.obj point) left right) where
  stable {_ _} step {_ _} related := bisimulation.stable (change.map step) related
  forth {_ _ _} related future {_} available :=
    bisimulation.forth related (futureBelow change _ future) available
  back {_ _ _} related future {_} available :=
    bisimulation.back related (futureBelow change _ future) available

theorem restricted_bisimilar (point : E) {left right : (restrictedFamily change A).obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar coalgebra (change.obj point) left right) :
    ContextualCoalgebraBisimulation.Bisimilar (restrictedCoalgebra change A coalgebra) point left right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact ContextualCoalgebraBisimulation.greatest _
    (restricted_isBisimulation change A coalgebra bisimulation) related

end ReceiptRestriction

section Recipient

variable {C : Type u} [Category.{u} C] (context : LabelledContext C)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

/-- The constructed site comparison has all original futures. Thus it
reflects contextual bisimulation, rather than merely preserving it. -/
theorem bisimilar_iff_below (A : context.base.Elements ⥤ Type (u + 1))
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (left right : (restrictedFamily (PresheafSiteLift.elementsDown context.base) A).obj point) :
    ContextualCoalgebraBisimulation.Bisimilar
      (restrictedCoalgebra (PresheafSiteLift.elementsDown context.base) A coalgebra) point left right ↔
    ContextualCoalgebraBisimulation.Bisimilar coalgebra
      ((PresheafSiteLift.elementsDown context.base).obj point) left right := by
  constructor
  · intro related
    let relation : ContextualCoalgebraBisimulation.Relation A := fun world first second =>
      ContextualCoalgebraBisimulation.Bisimilar
        (restrictedCoalgebra (PresheafSiteLift.elementsDown context.base) A coalgebra)
        ((PresheafSiteLift.elementsUp context.base).obj world) first second
    have bisimulation : ContextualCoalgebraBisimulation.IsBisimulation coalgebra relation := {
      stable := by
        intro first second step left right related
        exact ContextualCoalgebraBisimulation.bisimilar_stable _
          ((PresheafSiteLift.elementsUp context.base).map step) related
      forth := by
        intro point left right related future child available
        exact (ContextualCoalgebraBisimulation.bisimilar_isBisimulation _).forth related
          ⟨(PresheafSiteLift.elementsUp context.base).obj future.1,
            (PresheafSiteLift.elementsUp context.base).map future.2⟩ available
      back := by
        intro point left right related future child available
        exact (ContextualCoalgebraBisimulation.bisimilar_isBisimulation _).back related
          ⟨(PresheafSiteLift.elementsUp context.base).obj future.1,
            (PresheafSiteLift.elementsUp context.base).map future.2⟩ available }
    exact ContextualCoalgebraBisimulation.greatest coalgebra bisimulation related
  · exact restricted_bisimilar (PresheafSiteLift.elementsDown context.base) A coalgebra point

def elementArrows (first second : context.base.Elements) : ArgumentCoding (first ⟶ second) :=
  (arrows first.1 second.1).subtype (fun step => context.base.map step first.2 = second.2)

abbrev classFamily := ContextualSmallCoalgebraMaterialCarrier.classFamily context.labels (elementArrows context arrows)
abbrev classCoalgebra := ContextualSmallCoalgebraMaterialCoalgebra.classCoalgebra context.labels (elementArrows context arrows)

/-- The collecting graph and its independent class/member inverse supply
an actual material dictionary at the successor graph bound. -/
def classModel (point : context.base.Elements) : PresentedType ((classFamily context arrows).obj point) where
  graph := ContextualSmallCoalgebraMaterialCarrier.carrierGraph context.labels (elementArrows context arrows) point
  decode := (ContextualSmallCoalgebraMaterialCarrier.memberEquiv context.labels (elementArrows context arrows) point).symm

theorem classModel_value (point : context.base.Elements) (value : (classFamily context arrows).obj point) :
    (classModel context arrows point).value value =
      ((ContextualSmallCoalgebraMaterialCarrier.classToMembers context.labels (elementArrows context arrows)).app point value).val := rfl

def recipient : MaterialFamily (ContextualSiteLiftMaterial.context context) where
  family := restrictedFamily (PresheafSiteLift.elementsDown context.base) (classFamily context arrows)
  model point := classModel context arrows ((PresheafSiteLift.elementsDown context.base).obj point)

theorem recipient_carrier (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((recipient context arrows).model point).carrier =
      ContextualSmallCoalgebraMaterialCarrier.carrier context.labels (elementArrows context arrows)
        ((PresheafSiteLift.elementsDown context.base).obj point) := rfl

theorem recipient_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (value : (recipient context arrows).family.obj point) :
    ((recipient context arrows).model point).value value =
      ((ContextualSmallCoalgebraMaterialCarrier.classToMembers context.labels (elementArrows context arrows)).app
        ((PresheafSiteLift.elementsDown context.base).obj point) value).val := rfl

theorem recipient_member_restrict {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((recipient context arrows).model first).carrier}) :
    ((recipient context arrows).model second).decode ((recipient context arrows).memberRestriction step member) =
      (classFamily context arrows).map ((PresheafSiteLift.elementsDown context.base).map step)
        (((recipient context arrows).model first).decode member) :=
  (recipient context arrows).memberRestriction_decode step member

def recipientCoalgebra : NaturalHom (recipient context arrows).family
    (CoveredFuturePowerFamilies.family (recipient context arrows).family) :=
  restrictedCoalgebra (PresheafSiteLift.elementsDown context.base) (classFamily context arrows)
    (classCoalgebra context arrows)

def recipientEnumerations : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration ((recipientCoalgebra context arrows).app point value).val :=
  restrictedEnumeration (PresheafSiteLift.elementsDown context.base) (classFamily context arrows)
    (classCoalgebra context arrows)

theorem recipient_future (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (value : (recipient context arrows).family.obj point) (future : Future.Objects point)
    (child : (recipient context arrows).family.obj future.1) :
    ((recipientCoalgebra context arrows).app point value).val.holds ⟨future, child⟩ ↔
      ((classCoalgebra context arrows).app ((PresheafSiteLift.elementsDown context.base).obj point) value).val.holds
        ⟨futureBelow (PresheafSiteLift.elementsDown context.base) point future, child⟩ := Iff.rfl

theorem recipient_separated : ContextualCoalgebraQuotient.BehaviorallySeparated (recipientCoalgebra context arrows) := by
  intro point first second related
  exact ContextualSmallCoalgebraMaterialCoalgebra.class_separated context.labels (elementArrows context arrows)
    _ first second ((bisimilar_iff_below context (classFamily context arrows) (classCoalgebra context arrows)
      point first second).mp related)

/-- The entire coded source is retained, including its original code and
occurrence. Restriction changes only its actual terminal context. -/
def codedSource := restrictedFamily (PresheafSiteLift.elementsDown context.base)
  (ContextualSmallCoalgebraGenerators.coproduct (D := context.base.Elements))

def codedCoalgebra : NaturalHom (codedSource context)
    (CoveredFuturePowerFamilies.family (codedSource context)) :=
  restrictedCoalgebra (PresheafSiteLift.elementsDown context.base)
    (ContextualSmallCoalgebraGenerators.coproduct (D := context.base.Elements))
    ContextualSmallCoalgebraGenerators.coproductCoalgebra

def codedReadout : NaturalHom (codedSource context) (recipient context arrows).family :=
  restrictedHom (PresheafSiteLift.elementsDown context.base)
    (ContextualSmallCoalgebraGenerators.coproduct (D := context.base.Elements))
    (ContextualSmallCoalgebraMaterialCarrier.classObservation context.labels (elementArrows context arrows))

theorem codedReadout_square :
    (codedCoalgebra context).comp (CoveredFuturePowerFunctor.imageHom (codedReadout context arrows)) =
      (codedReadout context arrows).comp (recipientCoalgebra context arrows) :=
  restricted_square (PresheafSiteLift.elementsDown context.base)
    (ContextualSmallCoalgebraGenerators.coproduct (D := context.base.Elements))
    ContextualSmallCoalgebraGenerators.coproductCoalgebra
    (ContextualSmallCoalgebraMaterialCarrier.classObservation context.labels (elementArrows context arrows))
    (classCoalgebra context arrows)
    (ContextualSmallCoalgebraMaterialCoalgebra.classObservation_square context.labels (elementArrows context arrows))

theorem codedReadout_kernel (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (first second : (codedSource context).obj point) :
    (codedReadout context arrows).app point first = (codedReadout context arrows).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar (codedCoalgebra context) point first second :=
  (ContextualSmallCoalgebraMaterialCarrier.classObservation_eq_iff context.labels (elementArrows context arrows)
    ((PresheafSiteLift.elementsDown context.base).obj point) first second).trans
      (bisimilar_iff_below context _ ContextualSmallCoalgebraGenerators.coproductCoalgebra point first second).symm

theorem codedReadout_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (source : (codedSource context).obj point) :
    ((recipient context arrows).model point).value ((codedReadout context arrows).app point source) =
      HSet.lift (ContextualSmallCoalgebraMaterialCarrier.readValue context.labels (elementArrows context arrows)
        ((PresheafSiteLift.elementsDown context.base).obj point) source) :=
  ContextualSmallCoalgebraMaterialCarrier.classObservation_value context.labels (elementArrows context arrows)
    ((PresheafSiteLift.elementsDown context.base).obj point) source

theorem pi_evaluation (body : MaterialFamily (recipient context arrows).extension)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (function : ((recipient context arrows).pi body (ContextualSiteLiftMaterial.arrows arrows)).family.obj point)
    (argument : PowerClassContextualMaterialization.FutureArguments (recipient context arrows).family point) :
    LabelledDependentProducts.evalValue
      ((recipient context arrows).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point)
      ((recipient context arrows).futureOutputs body point)
      ((((recipient context arrows).pi body (ContextualSiteLiftMaterial.arrows arrows)).model point).value function)
      argument = ((recipient context arrows).futureOutputs body point argument).value
        (function.app argument.1.1 argument.1.2 argument.2) :=
  (recipient context arrows).pi_evaluation body (ContextualSiteLiftMaterial.arrows arrows) point function argument

theorem sigma_first (body : MaterialFamily (recipient context arrows).extension)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (pair : ((recipient context arrows).sigma body).family.obj point) :
    HSet.fst ((((recipient context arrows).sigma body).model point).value pair) =
      ((recipient context arrows).model point).value pair.1 :=
  (recipient context arrows).sigma_first body point pair

theorem sigma_second (body : MaterialFamily (recipient context arrows).extension)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (pair : ((recipient context arrows).sigma body).family.obj point) :
    HSet.snd ((((recipient context arrows).sigma body).model point).value pair) =
      (body.model ⟨point.1, ⟨point.2, pair.1⟩⟩).value pair.2 :=
  (recipient context arrows).sigma_second body point pair

theorem identity_inhabited (left right : (recipient context arrows).family.sections)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    Nonempty (((recipient context arrows).identity left right).family.obj point) ↔
      left.val point = right.val point := by
  constructor
  · rintro ⟨witness⟩
    exact PresheafIdentityWitness.decode witness
  · intro same
    exact ⟨PresheafIdentityWitness.encode same⟩

end Recipient

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveMaterialRecipientModel
