import Mettapedia.OSLF.Syntax.CategoricalEventObservations
import Mettapedia.OSLF.Syntax.ContextualReductionSubobject
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Modal observation of retained authored firings

At a closed context, the endpoint image of the proof-relevant authored event
graph induces exactly the existing OSLF may-step modality. The image forgets
which rule occurrence fired; the graph and its substitution action remain
available to history-sensitive consumers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.PresentationEventModalComparison

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Binding.ContextualReductionSubobject

variable {S : Signature}

/-- The generated OSLF diamond can be read from the endpoint image of the
authored event graph. This comparison uses the closed-context image theorem;
it makes no claim that the image remembers individual firing occurrences. -/
theorem diamond_iff_endpoint_image (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (predicate : Term S [] sort → Prop)
    (source : Term S [] sort) :
    gsltDiamond (presentation.toExtensionalGSLTAt sort) predicate source ↔
      ∃ target : Term S [] sort,
        (stepSubfunctor presentation sort).obj
          (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx S)))
          (Quotient.mk (eqSetoid presentation.eqs [] sort) source,
            Quotient.mk (eqSetoid presentation.eqs [] sort) target) ∧
        predicate target := by
  refine (gsltDiamond_spec (presentation.toExtensionalGSLTAt sort)
    predicate source).trans ?_
  apply exists_congr
  intro target
  exact and_congr_left fun _ =>
    (closed_membership_iff_stepModE presentation sort source target).symm

/-- For a fixed authored target, the singleton diamond is precisely
membership of its endpoint pair in the reduction image. -/
theorem singleton_diamond_iff_endpoint_image
    (presentation : UnpositionedPresentation S) (sort : S.Srt)
    (source target : Term S [] sort) :
    gsltDiamond (presentation.toExtensionalGSLTAt sort)
      (fun candidate => candidate = target) source ↔
      (stepSubfunctor presentation sort).obj
        (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx S)))
        (Quotient.mk (eqSetoid presentation.eqs [] sort) source,
          Quotient.mk (eqSetoid presentation.eqs [] sort) target) := by
  exact (gsltDiamond_singleton_iff_step
      (presentation.toExtensionalGSLTAt sort) source target).trans
    (closed_membership_iff_stepModE presentation sort source target).symm

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.EventGraphSlice.RhoExample
open Mettapedia.OSLF.Binding.CategoricalEventObservations
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents

/-- In the authored rho model, freely observing the retained event graph
recovers the established reduction subobject, not a new operational rule. -/
theorem image_observation_is_rho_reduction :
    (imageObservation states sourceProductEventSlice).reduction =
      sourceReductionSubobject :=
  sourceProductImage_eq_reduction

/-- Authored COMM is visible to the generated OSLF may-step modality. -/
theorem communication_diamond :
    gsltDiamond (rho.toUnpositioned.toExtensionalGSLTAt Srt.pr)
      (fun candidate => candidate = commTarget)
      (parT commInput commOutput) := by
  exact (singleton_diamond_iff_endpoint_image rho.toUnpositioned Srt.pr
    (parT commInput commOutput) commTarget).mpr
      ContextualReductionSubobject.RhoExample.source_order_communication_member

/-- Structural equations without a communication rule create no modal
successor. This separates equations from operational firings. -/
theorem static_has_no_diamond (predicate : Term sig [] Srt.pr)
    (source : Term sig [] Srt.pr) :
    ¬ gsltDiamond (rhoStatic.toExtensionalGSLTAt Srt.pr)
      (fun candidate => candidate = predicate) source := by
  intro h
  have step : rhoStatic.StepModE source predicate :=
    (closed_membership_iff_stepModE rhoStatic Srt.pr source predicate).mp
      ((singleton_diamond_iff_endpoint_image rhoStatic Srt.pr source predicate).mp h)
  exact rhoStatic_has_no_step source predicate step

end RhoExample

end Mettapedia.OSLF.Binding.PresentationEventModalComparison
