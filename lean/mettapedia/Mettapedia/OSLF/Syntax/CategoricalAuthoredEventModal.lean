import Mettapedia.OSLF.Syntax.CategoricalAuthoredEventPaths
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Modal observation of individual authored firing events

In the `Type` target, the event graph generates the ordinary OSLF may-step
modality by existentially observing its endpoints. Model maps carry concrete
firing witnesses forward, hence preserve may-observations. The converse
requires an additional lifting condition and is not asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredEventModal

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u
variable {S : Signature} {schema : List (MetaArity S)}
variable {equations : EquationPresentation S schema}
variable {rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)}
variable {X Y : PresentedModel (D := Type u) equations rules}

/-- The OSLF/GSLT one-step observation of a proof-relevant authored model.
It forgets which event produced the displayed endpoints. -/
def theoryOf (X : PresentedModel (D := Type u) equations rules) :
    Mettapedia.GSLT.GSLT :=
  equalityGSLT X.base.carrier.program
    (fun source target =>
      ∃ event : X.event, X.endpoints event = (source, target))

theorem step_iff_event (X : PresentedModel (D := Type u) equations rules)
    (source target : X.base.carrier.program) :
    (theoryOf X).Step source target ↔
      ∃ event : X.event, X.endpoints event = (source, target) :=
  Iff.rfl

/-- The generated may-observation holds precisely when there is an actual
firing whose target satisfies the predicate. -/
theorem diamond_iff_event (X : PresentedModel (D := Type u) equations rules)
    (predicate : X.base.carrier.program → Prop)
    (source : X.base.carrier.program) :
    gsltDiamond (theoryOf X) predicate source ↔
      ∃ target : X.base.carrier.program,
        ∃ event : X.event,
          X.endpoints event = (source, target) ∧ predicate target := by
  refine (gsltDiamond_spec (theoryOf X) predicate source).trans ?_
  constructor
  · rintro ⟨target, ⟨event, endpoints⟩, holds⟩
    exact ⟨target, event, endpoints, holds⟩
  · rintro ⟨target, event, endpoints, holds⟩
    exact ⟨target, ⟨event, endpoints⟩, holds⟩

/-- Every lawful model interpretation transports the particular witness of
a may-step. Target-only events need not be reflected. -/
theorem diamond_map (f : PresentedModel.Hom X Y)
    (predicate : Y.base.carrier.program → Prop)
    (source : X.base.carrier.program)
    (may : gsltDiamond (theoryOf X)
      (fun target => predicate (f.base.program target)) source) :
    gsltDiamond (theoryOf Y) predicate
      (f.base.program source) := by
  obtain ⟨target, event, endpoints, holds⟩ :=
    (diamond_iff_event X _ _).mp may
  have square := congrArg
    (fun arrow : X.event ⟶ EndpointPairs Y.base.binding Y.base.carrier =>
      arrow event) f.endpoints_comm
  change Y.endpoints (f.event event) =
    f.base.endpointMap (X.endpoints event) at square
  rw [endpoints] at square
  exact (diamond_iff_event Y _ _).mpr
    ⟨f.base.program target, f.event event, square, holds⟩

end Mettapedia.OSLF.Binding.CategoricalAuthoredEventModal
