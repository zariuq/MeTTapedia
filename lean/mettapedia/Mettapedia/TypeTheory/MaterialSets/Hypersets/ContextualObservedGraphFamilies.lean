import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphDiagram
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialFamilies

/-!
# Actual observed continuation families in the contextual graph universe

The existing structured observation determines its class coalgebra. Its
literal pointed values enter the varying graph universe, with exactly the
declared observed equivalence as their literal-equality kernel. Material
matching is a different readout: successor edges alone do not reconstruct
the class's declared atomic observations.

The existing authored continuation family is compared with independently
formed graph-successor receipts. The comparison retains its full action
on context arrows and gives inverse maps on whole compatible sections.
The actual original-small fibres are displayed over the existing raised
parameter site; no source representative or cover inverse is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphFamilies

open CategoryTheory Mettapedia.GSLT
open ContextualWitnessCover ContextualGraphDiagrams
open ConstructiveObservedMaterialInterpretation

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → ContextualCoalgebraLabelledGraph.State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

abbrev classes := observedClasses worlds arrows source atoms atomCoding
abbrev classSource := observedCoalgebra worlds arrows source atoms atomCoding
abbrev parameters := ConstructiveObservedMaterialFamilies.parameters worlds arrows source atoms atomCoding
abbrev native := (ConstructiveObservedMaterialFamilies.continuations worlds arrows source atoms atomCoding).native

def readout : NaturalHom A (values D) :=
  (observedProjection worlds arrows source atoms atomCoding).comp
    (ContextualObservedGraphDiagram.pointing (classSource worlds arrows source atoms atomCoding))

theorem literal_kernel (point : D) (first second : A.obj point) :
    (readout worlds arrows source atoms atomCoding).app point first =
      (readout worlds arrows source atoms atomCoding).app point second ↔
      ContextualObservedCoalgebra.ObservedBisimilar source atoms point first second := by
  change (ContextualObservedGraphDiagram.pointing (classSource worlds arrows source atoms atomCoding)).app point
      ((observedProjection worlds arrows source atoms atomCoding).app point first) =
    (ContextualObservedGraphDiagram.pointing (classSource worlds arrows source atoms atomCoding)).app point
      ((observedProjection worlds arrows source atoms atomCoding).app point second) ↔ _
  rw [ContextualObservedGraphDiagram.literal_kernel]
  exact ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding point first second

def classParameter : (parameters worlds arrows source atoms atomCoding).Elements ⥤
    (classes worlds arrows source atoms atomCoding).Elements where
  obj point := ⟨point.1.down, point.2.1⟩
  map step := CategoryOfElements.homMk _ _ step.1.down (congrArg Prod.fst step.2)
  map_id _ := rfl
  map_comp _ _ := rfl

def successors : (parameters worlds arrows source atoms atomCoding).Elements ⥤ Type u :=
  PresheafSiteLift.compose (classParameter worlds arrows source atoms atomCoding)
    (ContextualObservedGraphDiagram.successorFamily (classSource worlds arrows source atoms atomCoding))

def continuationEquiv (point : (parameters worlds arrows source atoms atomCoding).Elements) :
    (native worlds arrows source atoms atomCoding).obj point ≃
      (successors worlds arrows source atoms atomCoding).obj point where
  toFun child := ⟨child.val.down, child.property⟩
  invFun child := ⟨⟨child.val⟩, child.property⟩
  left_inv child := by
    rcases child with ⟨⟨child⟩, available⟩
    rfl
  right_inv _ := rfl

theorem continuation_transport
    {first second : (parameters worlds arrows source atoms atomCoding).Elements}
    (step : first ⟶ second) (child : (native worlds arrows source atoms atomCoding).obj first) :
    continuationEquiv worlds arrows source atoms atomCoding second
      ((native worlds arrows source atoms atomCoding).map step child) =
      (successors worlds arrows source atoms atomCoding).map step
        (continuationEquiv worlds arrows source atoms atomCoding first child) := by
  apply Subtype.ext
  rfl

def sections : (native worlds arrows source atoms atomCoding).sections ≃
    (successors worlds arrows source atoms atomCoding).sections where
  toFun term := ⟨fun point => continuationEquiv worlds arrows source atoms atomCoding point (term.val point), by
    intro first second step
    exact (continuation_transport worlds arrows source atoms atomCoding step (term.val first)).symm.trans
      (congrArg (continuationEquiv worlds arrows source atoms atomCoding second) (term.property step))⟩
  invFun term := ⟨fun point => (continuationEquiv worlds arrows source atoms atomCoding point).symm (term.val point), by
    intro first second step
    apply (continuationEquiv worlds arrows source atoms atomCoding second).injective
    rw [continuation_transport, Equiv.apply_symm_apply, term.property, Equiv.apply_symm_apply]⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (continuationEquiv worlds arrows source atoms atomCoding point).symm_apply_apply _
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (continuationEquiv worlds arrows source atoms atomCoding point).apply_symm_apply _

def member (point : (parameters worlds arrows source atoms atomCoding).Elements)
    (child : (successors worlds arrows source atoms atomCoding).obj point) :
    ContextualRealizedGraphs.Member
      ((ContextualObservedGraphDiagram.pointing (classSource worlds arrows source atoms atomCoding)).app
        point.1.down child.val)
      ((ContextualObservedGraphDiagram.pointing (classSource worlds arrows source atoms atomCoding)).app
        point.1.down point.2.1) :=
  ContextualObservedGraphDiagram.successorMembership (classSource worlds arrows source atoms atomCoding)
    point.1.down point.2.1 child

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphFamilies
