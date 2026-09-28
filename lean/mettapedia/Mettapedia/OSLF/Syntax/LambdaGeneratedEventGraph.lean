import Mettapedia.OSLF.Syntax.LambdaLexExponentialComparison
import Mettapedia.OSLF.Syntax.EventGraphImageTransport
import Mettapedia.OSLF.Syntax.LambdaDerivationGraph

/-!
# Authored lambda firing events in the generated program interpretation

The retained derivation graph and the reduction subobject carry different
information. We transport the graph through the checked source-to-generated
program isomorphism, identify its categorical endpoint image with the
generated reduction subobject, and retain the two distinct firings of an
omega self-loop. The result connects the function-object comparison and the
operational graph at the same Chapter 7 program carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaGeneratedEventGraph

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaDerivationGraph
open Mettapedia.OSLF.Binding.LambdaLexExponentialComparison
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.EventGraphSlice
open Mettapedia.OSLF.Binding.EventGraphImageTransport

/-- The authored proof-relevant lambda graph with endpoints interpreted as
generated programs. Its event presheaf is not quotiented. -/
noncomputable def generatedGraph :
    FreePresheafEventExtension.Graph generatedPrograms :=
  changeVertex programsGeneratedIso graph

/-- Vertex transport changes program endpoints but leaves every firing
derivation and its substitution action intact. -/
theorem generated_events_unchanged :
    generatedGraph.edge = eventPresheaf := rfl

/-- The authored graph as an arrow into the chosen source product. -/
noncomputable def sourceProductSlice : Over (Programs ⨯ Programs) :=
  Over.mk (endpoints ≫ productIso.inv)

/-- Its endpoint arrow is the intrinsic sorted endpoint map followed by the
checked comparison with the categorical product. -/
theorem sourceProductSlice_hom :
    sourceProductSlice.hom = endpoints ≫ productIso.inv := rfl

/-- The categorical image of the authored event arrow is exactly the
previously proved least scoped reduction subobject. -/
theorem sourceProductSlice_image :
    imageSubobject sourceProductSlice.hom = reductionSubobject := by
  change imageSubobject (endpoints ≫ productIso.symm.hom) =
    Subobject.mk (LambdaReductionSubobject.reduction.ι ≫
      productIso.symm.hom)
  rw [imageSubobject_postIso endpoints productIso.symm]
  rw [imageSubobject_eq_range, range_endpoints_eq_reduction]
  rfl

/-- The same retained graph over the chosen product of generated programs. -/
noncomputable def generatedProductSlice :
    Over (generatedPrograms ⨯ generatedPrograms) :=
  Over.mk (endpoints ≫ productIso.inv ≫ endpointTransport.hom)

/-- The generated graph's endpoint arrow transports the original endpoint
arrow through the source-to-generated program isomorphism. -/
theorem generatedProductSlice_hom :
    generatedProductSlice.hom =
      sourceProductSlice.hom ≫ endpointTransport.hom := rfl

/-- The retained derivation graph's paired endpoint map is the existing
intrinsic sorted endpoint map read as a pointwise pair. -/
theorem authoredEndpointMap :
    endpointMap graph = endpoints ≫ sortedPairsIso.hom := by
  ext X event <;> rfl

/-- The source slice above is the actual graph-to-product-slice image of the
authored proof-relevant graph. -/
theorem sourceProductSlice_is_graphSlice :
    sourceProductSlice.hom =
      ((graphProductSliceEquivalence Programs).functor.obj graph).hom := by
  change endpoints ≫ productIso.inv =
    endpointMap graph ≫
      (FunctorToTypes.binaryProductIso Programs Programs).inv
  rw [authoredEndpointMap]
  change endpoints ≫ sortedPairsIso.hom ≫
      (FunctorToTypes.binaryProductIso Programs Programs).inv =
    (endpoints ≫ sortedPairsIso.hom) ≫
      (FunctorToTypes.binaryProductIso Programs Programs).inv
  exact (Category.assoc _ _ _).symm

/-- The generated slice's arrow is the actual source/target map of the
generated graph in the chosen binary-product representation. -/
theorem generatedProductSlice_is_graphSlice :
    generatedProductSlice.hom =
      ((graphProductSliceEquivalence generatedPrograms).functor.obj
        generatedGraph).hom := by
  change endpoints ≫ productIso.inv ≫ endpointTransport.hom =
    endpointMap (changeVertex programsGeneratedIso graph) ≫
      (FunctorToTypes.binaryProductIso generatedPrograms generatedPrograms).inv
  rw [endpointMap_changeVertex]
  change endpoints ≫ productIso.inv ≫ endpointTransport.hom =
    (endpointMap graph ≫ pairMap programsGeneratedIso.hom) ≫
      (FunctorToTypes.binaryProductIso generatedPrograms generatedPrograms).inv
  rw [Category.assoc,
    pairMap_toChosen_natural programsGeneratedIso.hom,
    authoredEndpointMap]
  simp [endpointTransport, productIso, Category.assoc]
  rw [← Category.assoc endpoints sortedPairsIso.hom
    ((FunctorToTypes.binaryProductIso Programs Programs).inv ≫
      prod.map programsGeneratedIso.hom programsGeneratedIso.hom)]
  rfl

/-- Taking the categorical image of the retained generated graph recovers
exactly the generated reduction predicate. Events remain available before
the image operation. -/
theorem generatedProductSlice_image :
    imageSubobject generatedProductSlice.hom =
      generatedReductionSubobject := by
  calc
    imageSubobject generatedProductSlice.hom =
        imageSubobject
          ((graphProductSliceEquivalence generatedPrograms).functor.obj
            generatedGraph).hom :=
              congrArg
                (fun f : eventPresheaf ⟶
                    generatedPrograms ⨯ generatedPrograms =>
                  imageSubobject f)
                generatedProductSlice_is_graphSlice
    _ = (Subobject.map endpointTransport.hom).obj
          (imageSubobject
            ((graphProductSliceEquivalence Programs).functor.obj
              graph).hom) :=
                EventGraphImageTransport.graphProductSlice_image_changeVertex
                  programsGeneratedIso graph
    _ = (Subobject.map endpointTransport.hom).obj
          (imageSubobject sourceProductSlice.hom) := by
            exact congrArg
              (fun f : eventPresheaf ⟶ Programs ⨯ Programs =>
                (Subobject.map endpointTransport.hom).obj
                  (imageSubobject f))
              sourceProductSlice_is_graphSlice.symm
    _ = (Subobject.map endpointTransport.hom).obj reductionSubobject := by
          rw [sourceProductSlice_image]
    _ = generatedReductionSubobject := rfl

/-- Generated programs have an actual retained firing at a specified pair
of transported endpoints exactly when the authored four-clause step holds.
This is a statement about event existence, before proof erasure to an image. -/
theorem generated_firing_iff_step (X : Base)
    (left right : Term sig X.unop.vars .term) :
    (∃ event : generatedGraph.edge.obj X,
      generatedGraph.source.app X event =
        programsGeneratedIso.hom.app X left ∧
      generatedGraph.target.app X event =
        programsGeneratedIso.hom.app X right) ↔
      LambdaContextualRung.Step X.unop.vars left right := by
  constructor
  · rintro ⟨event, sourceEq, targetEq⟩
    change programsGeneratedIso.hom.app X (source event) =
      programsGeneratedIso.hom.app X left at sourceEq
    change programsGeneratedIso.hom.app X (target event) =
      programsGeneratedIso.hom.app X right at targetEq
    have sourceEq' := componentInjective programsGeneratedIso X sourceEq
    have targetEq' := componentInjective programsGeneratedIso X targetEq
    have step := denotes event
    rw [sourceEq', targetEq'] at step
    exact step
  · intro step
    obtain ⟨event, sourceEq, targetEq⟩ := event_exists_of_step step
    refine ⟨event, ?_, ?_⟩
    · change programsGeneratedIso.hom.app X (source event) =
        programsGeneratedIso.hom.app X left
      rw [sourceEq]
    · change programsGeneratedIso.hom.app X (target event) =
        programsGeneratedIso.hom.app X right
      rw [targetEq]

/-- Two distinct source derivations of the Ω self-loop remain distinct in
the generated event carrier, despite having identical transported endpoints. -/
theorem generated_omega_tickets_distinct :
    (leftOmegaEvent : generatedGraph.edge.obj
      (Opposite.op ⟨([] : Ctx sig)⟩)) ≠ rightOmegaEvent :=
  omega_events_distinct

theorem generated_omega_tickets_same_endpoints :
    generatedProductSlice.hom.app
        (Opposite.op ⟨([] : Ctx sig)⟩) leftOmegaEvent =
      generatedProductSlice.hom.app
        (Opposite.op ⟨([] : Ctx sig)⟩) rightOmegaEvent := by
  have sourceSame : endpoints.app
        (Opposite.op ⟨([] : Ctx sig)⟩) leftOmegaEvent =
      endpoints.app
        (Opposite.op ⟨([] : Ctx sig)⟩) rightOmegaEvent := by
    rcases omega_events_same_endpoints with ⟨sourceEq, targetEq⟩
    exact congrArg
      (fun pair : Term sig [] .term × Term sig [] .term =>
        (⟨Srt.term, pair⟩ : BinderLocalPremise.rootPairs sig []))
      (Prod.ext sourceEq targetEq)
  change (endpoints ≫ productIso.inv ≫ endpointTransport.hom).app
      (Opposite.op ⟨([] : Ctx sig)⟩) leftOmegaEvent =
    (endpoints ≫ productIso.inv ≫ endpointTransport.hom).app
      (Opposite.op ⟨([] : Ctx sig)⟩) rightOmegaEvent
  exact congrArg
    (fun pair => (productIso.inv ≫ endpointTransport.hom).app
      (Opposite.op ⟨([] : Ctx sig)⟩) pair) sourceSame

/-- The generated event-to-endpoint arrow is not monic. Its image is the
reduction subobject; the event object itself retains occurrence identity. -/
theorem generatedProductSlice_not_mono :
    ¬ Mono generatedProductSlice.hom := by
  intro mono
  let X : Base := Opposite.op ⟨([] : Ctx sig)⟩
  have componentMono : Mono (generatedProductSlice.hom.app X) :=
    (NatTrans.mono_iff_mono_app _).mp mono X
  have injective : Function.Injective
      (generatedProductSlice.hom.app X) :=
    (mono_iff_injective _).mp componentMono
  exact generated_omega_tickets_distinct
    (injective generated_omega_tickets_same_endpoints)

/-- Every retained generated firing factors through the endpoint image
that represents the scoped reduction predicate. -/
theorem generated_firing_factors_reduction :
    generatedReductionSubobject.Factors generatedProductSlice.hom := by
  rw [← generatedProductSlice_image]
  exact imageSubobject_factors_comp_self generatedProductSlice.hom
    (𝟙 generatedProductSlice.left)

end Mettapedia.OSLF.Binding.LambdaGeneratedEventGraph
