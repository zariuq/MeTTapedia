import Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses
import Mettapedia.CategoryTheory.RelativeClosedConjunctiveHomEquivalence
import Mettapedia.GSLT.Core.AuthoredClosedTheory
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Actual program and reduction data in a closed generated extension

A finite-limit closed map transports the reduction monomorphism through
its canonical product comparison. The actual chosen subobject has an earned
isomorphism to the mapped event object, and its two endpoint readings give
a genuine program-theory map. Applying this to the generated base inclusion
retains each independently authored rule, selected position and rely input.

This constructs the program/reduction layer of the conjunctive extension;
it introduces no modal generator or operational adequacy assertion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open ProgramReductionTheory
open RelativeClosedConjunctive.HomEquivalence

universe k

variable (source : Theory.{k,k}) (target : LambdaTheory.{k,k})
variable (closedMap : LambdaTheoryMap source.closed target)

def endpoints : closedMap.functor.obj source.Event ⟶
    closedMap.functor.obj source.program ⨯ closedMap.functor.obj source.program :=
  closedMap.functor.map source.reduction.arrow ≫
    prodComparison closedMap.functor source.program source.program

instance endpoints_mono : Mono (endpoints source target closedMap) := by
  unfold endpoints
  infer_instance

def mappedTheory : Theory.{k,k} where
  closed := target
  program := closedMap.functor.obj source.program
  reduction := Subobject.mk (endpoints source target closedMap)

def eventComparison : (mappedTheory source target closedMap).Event ≅ closedMap.functor.obj source.Event :=
  Subobject.underlyingIso (endpoints source target closedMap)

theorem complete_endpoint_reading :
    (eventComparison source target closedMap).inv ≫ (mappedTheory source target closedMap).reduction.arrow =
      endpoints source target closedMap :=
  Subobject.underlyingIso_arrow (endpoints source target closedMap)

theorem complete_source_reading :
    (eventComparison source target closedMap).inv ≫ (mappedTheory source target closedMap).source =
      closedMap.functor.map source.source := by
  change (eventComparison source target closedMap).inv ≫
    ((mappedTheory source target closedMap).reduction.arrow ≫ prod.fst) = _
  rw [← Category.assoc, complete_endpoint_reading]
  change (closedMap.functor.map source.reduction.arrow ≫
    prodComparison closedMap.functor source.program source.program) ≫ prod.fst =
      closedMap.functor.map (source.reduction.arrow ≫ prod.fst)
  rw [Category.assoc, prodComparison_fst, closedMap.functor.map_comp]

theorem complete_target_reading :
    (eventComparison source target closedMap).inv ≫ (mappedTheory source target closedMap).target =
      closedMap.functor.map source.target := by
  change (eventComparison source target closedMap).inv ≫
    ((mappedTheory source target closedMap).reduction.arrow ≫ prod.snd) = _
  rw [← Category.assoc, complete_endpoint_reading]
  change (closedMap.functor.map source.reduction.arrow ≫
    prodComparison closedMap.functor source.program source.program) ≫ prod.snd =
      closedMap.functor.map (source.reduction.arrow ≫ prod.snd)
  rw [Category.assoc, prodComparison_snd, closedMap.functor.map_comp]

def mapping : Map source (mappedTheory source target closedMap) where
  closed := closedMap
  program := Iso.refl _
  reduction := (eventComparison source target closedMap).inv
  source := (complete_source_reading source target closedMap).trans (Category.comp_id _).symm
  target := (complete_target_reading source target closedMap).trans (Category.comp_id _).symm

theorem complete_reduction_retained :
    IsIso (mapping source target closedMap).reduction := by
  change IsIso (eventComparison source target closedMap).inv
  infer_instance

def generatedTheory : Theory.{k,k} :=
  mappedTheory source (freeObject source.closed).closed (unitMap source.closed)

def generatedInclusion : Map source (generatedTheory source) :=
  mapping source (freeObject source.closed).closed (unitMap source.closed)

theorem generated_program :
    (generatedTheory source).program = (unitMap source.closed).functor.obj source.program := rfl

theorem generated_event_comparison :
    Nonempty ((generatedTheory source).Event ≅ (unitMap source.closed).functor.obj source.Event) :=
  ⟨eventComparison source (freeObject source.closed).closed (unitMap source.closed)⟩

def authoredRule (rule : AuthoredClosedTheory.Rule source) : AuthoredClosedTheory.Rule (generatedTheory source) :=
  AuthoredClosedTheory.Rule.transport (generatedInclusion source) rule

def selectedPosition {rule : AuthoredClosedTheory.Rule source} (position : AuthoredClosedTheory.Position rule) :
    AuthoredClosedTheory.Position (authoredRule source rule) :=
  AuthoredClosedTheory.Position.transport (generatedInclusion source) position

theorem authored_action_readout (rule : AuthoredClosedTheory.Rule source) :
    (authoredRule source rule).action = (unitMap source.closed).functor.map rule.action ≫
      (eventComparison source (freeObject source.closed).closed (unitMap source.closed)).inv := rfl

theorem selected_rely_input_readout {rule : AuthoredClosedTheory.Rule source}
    (position : AuthoredClosedTheory.Position rule) :
    (selectedPosition source position).relies = (unitMap source.closed).functor.map position.relies := rfl

theorem selected_focus_readout {rule : AuthoredClosedTheory.Rule source}
    (position : AuthoredClosedTheory.Position rule) :
    (selectedPosition source position).focus = (unitMap source.closed).functor.map position.focus := rfl

theorem selected_context_readout {rule : AuthoredClosedTheory.Rule source}
    (position : AuthoredClosedTheory.Position rule) :
    (selectedPosition source position).plug =
      inv (prodComparison (unitMap source.closed).functor position.environment position.carrier) ≫
        (unitMap source.closed).functor.map position.plug := by
  change inv (prodComparison (unitMap source.closed).functor position.environment position.carrier) ≫
    ((unitMap source.closed).functor.map position.plug ≫ 𝟙 _) = _
  rw [Category.comp_id]

def authoredPresentation (presentation : AuthoredClosedTheory.Presentation.{k,k,k} source) :
    AuthoredClosedTheory.Presentation.{k,k,k} (generatedTheory source) :=
  presentation.transport (generatedInclusion source)

theorem authored_rule_origins_retained (presentation : AuthoredClosedTheory.Presentation.{k,k,k} source) :
    (authoredPresentation source presentation).RuleOrigin = presentation.RuleOrigin := rfl

theorem authored_position_origins_retained (presentation : AuthoredClosedTheory.Presentation.{k,k,k} source)
    (origin : presentation.RuleOrigin) :
    (authoredPresentation source presentation).PositionOrigin origin = presentation.PositionOrigin origin := rfl

end Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension
