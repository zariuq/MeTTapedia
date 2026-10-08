import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphFamilies
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialControls

/-!
# Retained source occurrences and their observed continuation readout

The actual raw successor family keeps its source nodes. Sending each
occurrence through the declared observed projection is natural and
surjective in each fibre, but supplies no selected inverse. Complete
compatible source sections therefore project to observed sections.

The authored growing instance has distinct Boolean occurrences with the
same observed continuation. A dependent native family retains that tag;
its incompatible fibres prohibit erasing the occurrences for that consumer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphOccurrences

open CategoryTheory Mettapedia.GSLT ContextualWitnessCover
open ContextualSmallFamilyUniverse ConstructiveObservedMaterialInterpretation

section Generic

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → ContextualCoalgebraLabelledGraph.State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

abbrev rawFamily := ContextualObservedGraphDiagram.successorFamily source

def observedFamily : A.Elements ⥤ Type u :=
  PresheafSiteLift.compose
    (elementMap (observedProjection worlds arrows source atoms atomCoding))
    (ContextualObservedGraphDiagram.successorFamily
      (observedCoalgebra worlds arrows source atoms atomCoding))

def project (point : A.Elements) (child : (rawFamily source).obj point) :
    (observedFamily worlds arrows source atoms atomCoding).obj point :=
  ⟨(observedProjection worlds arrows source atoms atomCoding).app point.1 child.val,
    (ConstructiveObservedMaterialFamilies.source_class_continuation_iff
      worlds arrows source atoms atomCoding point.1 point.2 _).mpr
        ⟨child.val, rfl, child.property⟩⟩

theorem project_transport {first second : A.Elements} (step : first ⟶ second)
    (child : (rawFamily source).obj first) :
    (observedFamily worlds arrows source atoms atomCoding).map step
      (project worlds arrows source atoms atomCoding first child) =
      project worlds arrows source atoms atomCoding second ((rawFamily source).map step child) := by
  apply Subtype.ext
  exact (observedProjection worlds arrows source atoms atomCoding).naturality step.1 child.val

def projection : NaturalHom (rawFamily source) (observedFamily worlds arrows source atoms atomCoding) where
  app := project worlds arrows source atoms atomCoding
  naturality := project_transport worlds arrows source atoms atomCoding

theorem project_surjective (point : A.Elements) :
    Function.Surjective (project worlds arrows source atoms atomCoding point) := by
  intro child
  obtain ⟨original, same, available⟩ :=
    (ConstructiveObservedMaterialFamilies.source_class_continuation_iff
      worlds arrows source atoms atomCoding point.1 point.2 child.val).mp child.property
  exact ⟨⟨original, available⟩, Subtype.ext same⟩

theorem project_kernel (point : A.Elements) (first second : (rawFamily source).obj point) :
    project worlds arrows source atoms atomCoding point first =
      project worlds arrows source atoms atomCoding point second ↔
      ContextualObservedCoalgebra.ObservedBisimilar source atoms point.1 first.val second.val := by
  constructor
  · intro same
    exact (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding
      point.1 first.val second.val).mp (congrArg Subtype.val same)
  · intro related
    exact Subtype.ext ((ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding
      point.1 first.val second.val).mpr related)

def projectSection (term : (rawFamily source).sections) :
    (observedFamily worlds arrows source atoms atomCoding).sections :=
  (projection worlds arrows source atoms atomCoding).mapSection term

theorem projectSection_receipt (term : (rawFamily source).sections) (point : A.Elements) :
    (projectSection worlds arrows source atoms atomCoding term).val point =
      project worlds arrows source atoms atomCoding point (term.val point) := rfl

end Generic

namespace Controls

open ConstructiveObservedMaterialControls PowerClassPresheafDescent.Controls

abbrev rawReceipts := rawFamily dynamics

def taskPoint (stage : Nat) : raw.Elements :=
  ⟨world stage, stageValue stage 0 (by omega) false⟩

def receipt (stage index : Nat) (positive : 0 < index) (bound : index < stage+1)
    (tag : Bool) : rawReceipts.obj (taskPoint stage) :=
  ⟨stageValue stage index bound tag, Or.inr ⟨rfl, positive⟩⟩

theorem receipts_distinct (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    receipt stage index positive bound false ≠ receipt stage index positive bound true := by
  intro same
  exact Bool.false_ne_true (congrArg (fun child => child.val.2) same)

theorem projected_receipts_equal (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    project worlds arrows dynamics atoms atomCoding (taskPoint stage) (receipt stage index positive bound false) =
      project worlds arrows dynamics atoms atomCoding (taskPoint stage) (receipt stage index positive bound true) :=
  (project_kernel worlds arrows dynamics atoms atomCoding _ _ _).mpr
    (equal_indices_observed _ _ _ rfl)

def taskContexts : Nat ⥤ raw.Elements where
  obj stage := taskPoint (stage+1)
  map step := CategoryOfElements.homMk _ _
    ((homOfLE (Nat.succ_le_succ (leOfHom step))).op.op)
    (Prod.ext (Fin.ext rfl) rfl)
  map_id _ := CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _)
  map_comp _ _ := CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _)

def futureReceipts : Nat ⥤ Type := PresheafSiteLift.compose taskContexts rawReceipts

def futureObserved : Nat ⥤ Type := PresheafSiteLift.compose taskContexts
  (observedFamily worlds arrows dynamics atoms atomCoding)

def futureProjection : NaturalHom futureReceipts futureObserved where
  app stage := project worlds arrows dynamics atoms atomCoding (taskContexts.obj stage)
  naturality step child := project_transport worlds arrows dynamics atoms atomCoding (taskContexts.map step) child

def receiptSection (tag : Bool) : futureReceipts.sections :=
  ⟨fun stage => receipt (stage+1) 1 (by omega) (by omega) tag, by
    intro first second step
    exact Subtype.ext (Prod.ext (Fin.ext rfl) rfl)⟩

theorem whole_sections_distinct : receiptSection false ≠ receiptSection true := by
  intro same
  exact receipts_distinct 1 1 (by omega) (by omega)
    (congrArg (fun term : futureReceipts.sections => term.val 0) same)

theorem whole_sections_identified : futureProjection.mapSection (receiptSection false) =
    futureProjection.mapSection (receiptSection true) := by
  apply Subtype.ext
  funext stage
  exact projected_receipts_equal (stage+1) 1 (by omega) (by omega)

def nativeBody : (total rawReceipts).Elements ⥤ Type where
  obj point := {_unit : PUnit.{1} // point.2.2.val.2 = false}
  map {first second} step := TypeCat.ofHom fun term =>
    ⟨term.val, by
      have tags : first.2.2.val.2 = second.2.2.val.2 :=
        congrArg (fun value : (total rawReceipts).obj second.1 => value.2.val.2) step.2
      exact tags ▸ term.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro term
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro term
    exact Subtype.ext rfl

def bodyPoint (stage index : Nat) (positive : 0 < index) (bound : index < stage+1)
    (tag : Bool) : (total rawReceipts).Elements :=
  ⟨world stage, ⟨(taskPoint stage).2, receipt stage index positive bound tag⟩⟩

def falseReceiptTerm (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    nativeBody.obj (bodyPoint stage index positive bound false) := ⟨PUnit.unit, rfl⟩

theorem trueReceipt_empty (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    ¬ Nonempty (nativeBody.obj (bodyPoint stage index positive bound true)) := by
  rintro ⟨impossible⟩
  exact (by decide : true ≠ false) impossible.property

theorem dependent_receipts_do_not_descend (stage index : Nat)
    (positive : 0 < index) (bound : index < stage+1) :
    project worlds arrows dynamics atoms atomCoding (taskPoint stage) (receipt stage index positive bound false) =
      project worlds arrows dynamics atoms atomCoding (taskPoint stage) (receipt stage index positive bound true) ∧
    ¬ Nonempty (nativeBody.obj (bodyPoint stage index positive bound false) ≃
      nativeBody.obj (bodyPoint stage index positive bound true)) := by
  refine ⟨projected_receipts_equal stage index positive bound, ?_⟩
  rintro ⟨comparison⟩
  exact trueReceipt_empty stage index positive bound ⟨comparison (falseReceiptTerm stage index positive bound)⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphOccurrences
