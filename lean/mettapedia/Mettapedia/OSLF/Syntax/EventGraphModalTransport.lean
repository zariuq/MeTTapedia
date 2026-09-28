import Mettapedia.OSLF.Syntax.EventGraphImageMorphism
import Mettapedia.OSLF.Syntax.OperationalImageReflection
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# OSLF may-observations of proof-relevant graph maps

At each substitution context, the endpoint image of an event graph supplies
an extensional GSLT step relation. A graph morphism transports individual
events and therefore preserves the generated may-step modality. This is the
forward direction only: target firings need not come from the source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphModalTransport

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.EventGraphImageMorphism
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {base : Type*} [Category base]

/-- The existing GSLT/OSLF generator applied to the endpoint observation at
one context. The firing graph remains available separately. -/
def theoryAt (G : EventGraph base) (X : base) : Mettapedia.GSLT.GSLT :=
  equalityGSLT (G.vertex.obj X)
    (fun source target => (source, target) ∈ (reductionImage G).obj X)

/-- Every graph map preserves endpoint-image steps, with no coverage,
injectivity or reflection hypothesis. -/
theorem step_map {G H : EventGraph base} (f : EventGraphHom G H)
    (X : base) (source target : G.vertex.obj X)
    (step : (theoryAt G X).Step source target) :
    (theoryAt H X).Step (f.vertexMap.app X source)
      (f.vertexMap.app X target) := by
  obtain ⟨event, endpoints⟩ := step
  have commutes := congrArg
    (fun arrow : G.edge ⟶ FunctorToTypes.prod H.vertex H.vertex =>
      arrow.app X event) (endpointMap_morphism f)
  change (pairMap f.vertexMap).app X
      ((endpointMap (asFixed G)).app X event) =
    (endpointMap (asFixed H)).app X (f.edgeMap.app X event)
    at commutes
  refine ⟨f.edgeMap.app X event, ?_⟩
  rw [endpoints] at commutes
  exact commutes.symm

/-- Forward transport of the generated OSLF diamond. The predicate is
pulled back along the program map; a source may-success gives a target
may-success. No converse is asserted. -/
theorem diamond_map {G H : EventGraph base} (f : EventGraphHom G H)
    (X : base) (predicate : H.vertex.obj X → Prop)
    (source : G.vertex.obj X)
    (mayStep : gsltDiamond (theoryAt G X)
      (fun target => predicate (f.vertexMap.app X target)) source) :
    gsltDiamond (theoryAt H X) predicate
      (f.vertexMap.app X source) := by
  obtain ⟨target, step, holds⟩ :=
    (gsltDiamond_spec (theoryAt G X) _ source).mp mayStep
  exact (gsltDiamond_spec (theoryAt H X) _ _).mpr
    ⟨f.vertexMap.app X target, step_map f X source target step, holds⟩

namespace NoninjectiveControl

open Mettapedia.OSLF.Binding.OperationalImageReflection.NoninjectiveControl

private def stage : Index := Discrete.mk PUnit.unit

/-- The target of a state-collapsing graph map has a may-step. -/
theorem target_may :
    gsltDiamond (theoryAt target stage)
      (fun candidate => candidate = PUnit.unit) PUnit.unit := by
  apply (gsltDiamond_singleton_iff_step (theoryAt target stage) _ _).mpr
  exact target_step

/-- That target may-step does not reflect at the chosen source state,
despite surjectivity on events and exact endpoint coverage. -/
theorem source_not_may :
    ¬ gsltDiamond (theoryAt source stage)
      (fun candidate => candidate = true) true := by
  intro may
  exact source_no_step
    ((gsltDiamond_singleton_iff_step (theoryAt source stage) _ _).mp may)

/-- Forward modal preservation is strictly weaker than pointwise reflection
even for a graph map surjective on firing occurrences. -/
theorem forward_not_reflecting :
    (∀ X, Function.Surjective (collapse.edgeMap.app X)) ∧
    gsltDiamond (theoryAt target stage)
      (fun candidate => candidate = PUnit.unit) PUnit.unit ∧
    ¬ gsltDiamond (theoryAt source stage)
      (fun candidate => candidate = true) true :=
  ⟨collapse_event_surjective, target_may, source_not_may⟩

end NoninjectiveControl

end Mettapedia.OSLF.Binding.EventGraphModalTransport
