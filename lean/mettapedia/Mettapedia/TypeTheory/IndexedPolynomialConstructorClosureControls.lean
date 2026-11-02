import Mettapedia.TypeTheory.IndexedPolynomialConstructorClosure
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace

/-!
# Registered data-dependent slot controls

The existing indexed Vector registry supplies the shapes and source order.
Its zero, one and two-position layers test the generated algebra directly.
Active child order and inactive padding remain observable independently.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorClosureControls

open IndexedPositiveContainer

noncomputable section

def presentation := IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
  VectorControl.orderedFinitary VectorControl.code

abbrev Payload (environment : Description.Env VectorControl.interface.Value []) :=
  Σ index, presentation.polynomial.Shape environment index
abbrev Target (environment : Description.Env VectorControl.interface.Value []) := RecursiveSpace.Tree (Payload environment)

def pack (environment : Description.Env VectorControl.interface.Value []) : Payload environment → Payload environment := id
def empty (environment : Description.Env VectorControl.interface.Value []) : Target environment := RecursiveSpace.bottom
def construct (environment : Description.Env VectorControl.interface.Value [])
    (tag : Nat) (payload : Payload environment) (children : Nat → Target environment) : Target environment :=
  RecursiveSpace.construct tag payload children

theorem payloads_faithful : ∀ environment, Function.Injective (pack environment) := fun _ _ _ same => same
theorem fields_faithful : ∀ environment tag payload children otherTag otherPayload otherChildren,
    construct environment tag payload children = construct environment otherTag otherPayload otherChildren →
      payload = otherPayload ∧ children = otherChildren := by
  intro _ _ _ _ _ _ _ same
  exact ((RecursiveSpace.construct_injective _ _ _ _ _ _).mp same).2

theorem shape_separation : EncodedShapeSeparation presentation pack construct :=
  EncodedShapeSeparation.of_raw presentation pack construct fields_faithful

def algebra := constructorAlgebra presentation pack empty construct
def representation := constructorRepresentation presentation pack empty construct payloads_faithful shape_separation

def zeroValue : Target VectorControl.environment := algebra.act VectorControl.environment ()
  ⟨VectorControl.shapeAt 0, fun position => Fin.elim0 (VectorControl.positionEquiv 0 position)⟩
def oneValue : Target VectorControl.environment := algebra.act VectorControl.environment ()
  ⟨VectorControl.shapeAt 1, fun _ => zeroValue⟩

theorem zero_generated : Algebra.Generated algebra VectorControl.environment () zeroValue :=
  Algebra.generated_closed algebra VectorControl.environment () (VectorControl.shapeAt 0) _
    (fun position => Fin.elim0 (VectorControl.positionEquiv 0 position))

theorem one_generated : Algebra.Generated algebra VectorControl.environment () oneValue :=
  Algebra.generated_closed algebra VectorControl.environment () (VectorControl.shapeAt 1) _ (fun _ => zero_generated)

theorem zero_ne_one : zeroValue ≠ oneValue := by
  intro same
  have layers := constructorAlgebra_injective presentation pack empty construct payloads_faithful shape_separation
    VectorControl.environment () same
  have shapes := congrArg Sigma.fst layers
  have lengths := congrArg (fun shape => shape.1) shapes
  change (0 : Nat) = 1 at lengths
  cases lengths

theorem one_ne_bottom : oneValue ≠ empty VectorControl.environment :=
  RecursiveSpace.construct_ne_bottom _ _ _

theorem bottom_not_generated : ¬ ConstructorFamily presentation pack empty construct VectorControl.environment
    (empty VectorControl.environment) :=
  constructorFamily_refuses_empty presentation pack empty construct
    (fun _ _ _ _ => RecursiveSpace.construct_ne_bottom _ _ _) VectorControl.environment

def foreignTag : Target VectorControl.environment :=
  construct VectorControl.environment 7 ⟨(), VectorControl.shapeAt 0⟩ (fun _ => empty VectorControl.environment)

theorem foreign_tag_refused : ¬ ConstructorFamily presentation pack empty construct VectorControl.environment foreignTag := by
  rintro ⟨index, generated⟩
  obtain ⟨shape, children, equation⟩ := generated_constructorRoot presentation pack empty construct
    VectorControl.environment index foreignTag generated
  have tags := ((RecursiveSpace.construct_injective _ _ _ _ _ _).mp equation).1
  change (7 : Nat) = 0 at tags
  cases tags

def hiddenChildren : Nat → Target VectorControl.environment := fun slot => if slot = 0 then zeroValue else oneValue

theorem hidden_padding_refused :
    ¬ (presentation.coding (VectorControl.shapeAt 1)).Canonical (empty VectorControl.environment) hiddenChildren := by
  intro canonical
  have absent : (presentation.coding (VectorControl.shapeAt 1)).decode 1 = none := by
    apply (IndexedPositiveContainer.RecursiveSpaceRepresentation.code_padding_iff
      VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt 1) 1).mpr
    simpa only [IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_ordered_length] using Nat.le_refl 1
  have same := canonical 1 absent
  change oneValue = empty VectorControl.environment at same
  exact one_ne_bottom same

def malformedValue : Target VectorControl.environment :=
  construct VectorControl.environment 0 ⟨(), VectorControl.shapeAt 1⟩ hiddenChildren

theorem hidden_child_refused : ¬ ConstructorFamily presentation pack empty construct VectorControl.environment malformedValue := by
  intro generated
  obtain ⟨index, shape, children, equation, _, canonical⟩ :=
    (constructorFamily_fixed presentation pack empty construct payloads_faithful shape_separation
      VectorControl.environment malformedValue).mp generated
  obtain ⟨_, payloads, branches⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp equation
  cases index
  have shapes := eq_of_heq (Sigma.mk.inj payloads).2
  cases shapes
  rw [← branches] at canonical
  exact hidden_padding_refused canonical

def childrenInOrder (position : Code.Position VectorControl.code (VectorControl.shapeAt 2)) : Target VectorControl.environment :=
  if (VectorControl.positionEquiv 2 position).val = 0 then zeroValue else oneValue
def childrenReversed (position : Code.Position VectorControl.code (VectorControl.shapeAt 2)) : Target VectorControl.environment :=
  if (VectorControl.positionEquiv 2 position).val = 0 then oneValue else zeroValue

theorem children_order_retained :
    algebra.act VectorControl.environment () ⟨VectorControl.shapeAt 2, childrenInOrder⟩ ≠
      algebra.act VectorControl.environment () ⟨VectorControl.shapeAt 2, childrenReversed⟩ := by
  intro same
  have layers := constructorAlgebra_injective presentation pack empty construct payloads_faithful shape_separation
    VectorControl.environment () same
  have children : childrenInOrder = childrenReversed := eq_of_heq (Sigma.mk.inj layers).2
  have first := congrFun children ((VectorControl.positionEquiv 2).symm ⟨0, by decide⟩)
  simp only [childrenInOrder, childrenReversed, Equiv.apply_symm_apply, Fin.val_mk] at first
  exact zero_ne_one first

theorem two_children_generated :
    Algebra.Generated algebra VectorControl.environment ()
      (algebra.act VectorControl.environment () ⟨VectorControl.shapeAt 2, childrenInOrder⟩) := by
  apply Algebra.generated_closed algebra VectorControl.environment () (VectorControl.shapeAt 2) childrenInOrder
  intro position
  unfold childrenInOrder
  split
  · exact zero_generated
  · exact one_generated

theorem family_fixed (value : Target VectorControl.environment) :
    ConstructorFamily presentation pack empty construct VectorControl.environment value ↔
      GuardedConstructorStep presentation pack empty construct VectorControl.environment
        (ConstructorFamily presentation pack empty construct VectorControl.environment) value :=
  constructorFamily_fixed presentation pack empty construct payloads_faithful shape_separation _ value

namespace PartialPayload

abbrev Point (environment : Description.Env VectorControl.interface.Value []) :=
  Σ index, presentation.polynomial.Shape environment index
abbrev Payload (environment : Description.Env VectorControl.interface.Value []) := Option (Point environment)
abbrev Target (environment : Description.Env VectorControl.interface.Value []) := RecursiveSpace.Tree (Point environment)

def pack (environment : Description.Env VectorControl.interface.Value []) : Point environment → Payload environment := some
def empty (environment : Description.Env VectorControl.interface.Value []) : Target environment := RecursiveSpace.bottom
def construct (environment : Description.Env VectorControl.interface.Value [])
    (tag : Nat) (payload : Payload environment) (children : Nat → Target environment) : Target environment :=
  match payload with
  | none => RecursiveSpace.bottom
  | some point => RecursiveSpace.construct tag point children

theorem payloads_faithful : ∀ environment, Function.Injective (pack environment) := by
  intro _ _ _ same
  exact Option.some.inj same

theorem shape_separation : EncodedShapeSeparation presentation pack construct := by
  intro environment first second children otherChildren same
  obtain ⟨_, payloads, branches⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
  exact ⟨congrArg some payloads, branches⟩

def algebra := constructorAlgebra presentation pack empty construct
def representation := constructorRepresentation presentation pack empty construct payloads_faithful shape_separation

def zeroValue : Target VectorControl.environment := algebra.act VectorControl.environment ()
  ⟨VectorControl.shapeAt 0, fun position => Fin.elim0 (VectorControl.positionEquiv 0 position)⟩
def oneValue : Target VectorControl.environment := algebra.act VectorControl.environment ()
  ⟨VectorControl.shapeAt 1, fun _ => zeroValue⟩

theorem zero_generated : Algebra.Generated algebra VectorControl.environment () zeroValue :=
  Algebra.generated_closed algebra VectorControl.environment () (VectorControl.shapeAt 0) _
    (fun position => Fin.elim0 (VectorControl.positionEquiv 0 position))

theorem one_generated : Algebra.Generated algebra VectorControl.environment () oneValue :=
  Algebra.generated_closed algebra VectorControl.environment () (VectorControl.shapeAt 1) _ (fun _ => zero_generated)

theorem zero_ne_one : zeroValue ≠ oneValue := by
  intro same
  have layers := constructorAlgebra_injective presentation pack empty construct payloads_faithful shape_separation
    VectorControl.environment () same
  have shapes := congrArg Sigma.fst layers
  have lengths := congrArg (fun shape => shape.1) shapes
  change (0 : Nat) = 1 at lengths
  cases lengths

theorem zero_ne_bottom : zeroValue ≠ empty VectorControl.environment :=
  RecursiveSpace.construct_ne_bottom _ _ _

theorem raw_separation_refused :
    ¬ ∀ environment tag payload children otherTag otherPayload otherChildren,
      construct environment tag payload children = construct environment otherTag otherPayload otherChildren →
        payload = otherPayload ∧ children = otherChildren := by
  intro claimed
  have branches := (claimed VectorControl.environment 0 none (fun _ => empty VectorControl.environment)
    0 none (fun _ => zeroValue) rfl).2
  exact zero_ne_bottom (congrFun branches 0).symm

theorem family_fixed (value : Target VectorControl.environment) :
    ConstructorFamily presentation pack empty construct VectorControl.environment value ↔
      GuardedConstructorStep presentation pack empty construct VectorControl.environment
        (ConstructorFamily presentation pack empty construct VectorControl.environment) value :=
  constructorFamily_fixed presentation pack empty construct payloads_faithful shape_separation _ value

theorem family_is_least (value : Target VectorControl.environment) :
    ConstructorFamily presentation pack empty construct VectorControl.environment value ↔
      ∀ property : Target VectorControl.environment → Prop,
        (∀ point, GuardedConstructorStep presentation pack empty construct VectorControl.environment property point → property point) →
          property value :=
  constructorFamily_iff_closed_predicates presentation pack empty construct payloads_faithful shape_separation _ value

#print axioms representation
#print axioms zero_ne_one
#print axioms raw_separation_refused
#print axioms family_is_least
end PartialPayload

#print axioms hidden_padding_refused
#print axioms hidden_child_refused
#print axioms children_order_retained
#print axioms family_fixed

end
end Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorClosureControls
