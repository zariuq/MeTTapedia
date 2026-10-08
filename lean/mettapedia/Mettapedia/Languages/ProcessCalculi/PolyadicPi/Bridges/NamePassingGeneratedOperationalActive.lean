import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalBeta

/-!
# Generated evidence for the three authored active positions

Application evaluates the supplied edge at its private call channel.
Definition evaluates a complete reference-bound edge function while the
stored value remains outside that binder. Carrier evaluates its supplied
active body beside the unchanged server. Actual parallel and restriction
evidence generators earn both whole continuation endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open NamePassingContinuationOperations NamePassingContinuationValues
open NamePassingContinuationFunctionValues (call_postcomposition)

universe k

abbrev continuations := ordinary.{k}.names ⟶[Target] category.edge
abbrev boundContinuations := ordinary.{k}.names ⟶[Target] continuations

def endpoint (side : Bool) : category.{k}.edge ⟶ ordinary.processes :=
  if side then target else source

def functionEndpoint (side : Bool) : continuations.{k} ⟶ ordinary.termObject :=
  (ihom ordinary.names).map (endpoint side)

theorem parallel_endpoint (side : Bool) : BindingClosedGeneratedOperationalClosure.parallel.{k} ≫ endpoint side =
    lift (fst category.edge ordinary.processes ≫ endpoint side) (snd category.edge ordinary.processes) ≫
      ordinary.parallel := by
  cases side with
  | false =>
      change BindingClosedGeneratedOperationalClosure.parallel ≫
        (category.source ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) = _
      rw [← Category.assoc, BindingClosedGeneratedOperationalClosure.parallel_source]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
  | true =>
      change BindingClosedGeneratedOperationalClosure.parallel ≫
        (category.target ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) = _
      rw [← Category.assoc, BindingClosedGeneratedOperationalClosure.parallel_target]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl

theorem restriction_endpoint (side : Bool) : BindingClosedGeneratedOperationalClosure.restriction.{k} ≫ endpoint side =
    (ihom ordinary.names).map (endpoint side) ≫ ordinary.fresh := by
  cases side with
  | false => exact restriction_source
  | true => exact restriction_target

theorem supplied_parallel_endpoint (side : Bool) {Z : Target.{k}}
    (receipt : Z ⟶ category.edge) (frame : Z ⟶ ordinary.processes) :
    (lift receipt frame ≫ BindingClosedGeneratedOperationalClosure.parallel) ≫ endpoint side =
      lift (receipt ≫ endpoint side) frame ≫ ordinary.parallel := by
  rw [Category.assoc, parallel_endpoint, ← Category.assoc, comp_lift]
  simp only [lift_fst_assoc, lift_snd]

theorem supplied_restriction_endpoint (side : Bool) {Z : Target.{k}}
    (body : Z ⊗ ordinary.names ⟶ category.edge) :
    (abstraction body ≫ BindingClosedGeneratedOperationalClosure.restriction) ≫ endpoint side =
      bindFresh ordinary (body ≫ endpoint side) := by
  rw [Category.assoc, restriction_endpoint, ← Category.assoc, abstraction_postcomposition]
  rfl

abbrev applicationDomain := continuations.{k} ⊗ ordinary.names
abbrev applicationOuter := applicationDomain.{k} ⊗ ordinary.names
abbrev applicationInner := applicationOuter.{k} ⊗ ordinary.names

def applicationFunction : applicationInner.{k} ⟶ continuations :=
  fst applicationOuter ordinary.names ≫ fst applicationDomain ordinary.names ≫ fst continuations ordinary.names
def applicationArgument : applicationInner.{k} ⟶ ordinary.names :=
  fst applicationOuter ordinary.names ≫ fst applicationDomain ordinary.names ≫ snd continuations ordinary.names
def applicationResult : applicationInner.{k} ⟶ ordinary.names :=
  fst applicationOuter ordinary.names ≫ snd applicationDomain ordinary.names

def applicationChild : applicationInner.{k} ⟶ category.edge :=
  lift (call applicationFunction (snd applicationOuter ordinary.names))
    (lift (snd applicationOuter ordinary.names) (lift applicationArgument applicationResult) ≫ ordinary.send) ≫
      BindingClosedGeneratedOperationalClosure.parallel

def applicationReaction : applicationOuter.{k} ⟶ category.edge :=
  abstraction applicationChild ≫ BindingClosedGeneratedOperationalClosure.restriction

def application : applicationDomain.{k} ⟶ continuations := abstraction applicationReaction

def applicationEndpoint (side : Bool) : applicationDomain.{k} ⟶ ordinary.termObject :=
  lift (fst continuations ordinary.names ≫ functionEndpoint side) (snd continuations ordinary.names) ≫
    ordinary.application

theorem applicationChild_endpoint (side : Bool) : applicationChild.{k} ≫ endpoint side =
    lift (call (applicationFunction ≫ functionEndpoint side) (snd applicationOuter ordinary.names))
      (lift (snd applicationOuter ordinary.names) (lift applicationArgument applicationResult) ≫ ordinary.send) ≫
        ordinary.parallel := by
  rw [applicationChild, supplied_parallel_endpoint, call_postcomposition]
  rfl

theorem applicationReaction_endpoint (side : Bool) : applicationReaction.{k} ≫ endpoint side =
    call (fst applicationDomain ordinary.names ≫ applicationEndpoint side) (snd applicationDomain ordinary.names) := by
  rw [applicationReaction, supplied_restriction_endpoint, applicationChild_endpoint]
  have value : fst applicationDomain ordinary.names ≫ applicationEndpoint side =
      lift ((fst applicationDomain ordinary.names ≫ fst continuations ordinary.names) ≫ functionEndpoint side)
        (fst applicationDomain ordinary.names ≫ snd continuations ordinary.names) ≫ ordinary.application := by
    simp only [applicationEndpoint, comp_lift_assoc, Category.assoc]
  rw [value, application_value]
  apply congrArg (bindFresh ordinary)
  simp only [applicationFunction, applicationArgument, applicationResult, Category.assoc]

theorem application_endpoint (side : Bool) : application.{k} ≫ functionEndpoint side = applicationEndpoint side := by
  rw [application, functionEndpoint, abstraction_postcomposition, applicationReaction_endpoint]
  exact abstraction_evaluation (applicationEndpoint side)

abbrev definitionDomain := ordinary.{k}.termObject ⊗ boundContinuations
abbrev definitionOuter := definitionDomain.{k} ⊗ ordinary.names
abbrev definitionInner := definitionOuter.{k} ⊗ ordinary.names

def definitionBody : definitionInner.{k} ⟶ boundContinuations :=
  fst definitionOuter ordinary.names ≫ fst definitionDomain ordinary.names ≫ snd ordinary.termObject boundContinuations
def definitionStored : definitionInner.{k} ⟶ ordinary.termObject :=
  fst definitionOuter ordinary.names ≫ fst definitionDomain ordinary.names ≫ fst ordinary.termObject boundContinuations
def definitionResult : definitionInner.{k} ⟶ ordinary.names :=
  fst definitionOuter ordinary.names ≫ snd definitionDomain ordinary.names

def definitionChild : definitionInner.{k} ⟶ category.edge :=
  lift (call (call definitionBody (snd definitionOuter ordinary.names)) definitionResult)
    (lift (snd definitionOuter ordinary.names) definitionStored ≫ ordinary.input ≫ ordinary.replication) ≫
      BindingClosedGeneratedOperationalClosure.parallel

def definitionReaction : definitionOuter.{k} ⟶ category.edge :=
  abstraction definitionChild ≫ BindingClosedGeneratedOperationalClosure.restriction

def definition : definitionDomain.{k} ⟶ continuations := abstraction definitionReaction

def definitionEndpoint (side : Bool) : definitionDomain.{k} ⟶ ordinary.termObject :=
  lift (fst ordinary.termObject boundContinuations)
    (snd ordinary.termObject boundContinuations ≫ (ihom ordinary.names).map (functionEndpoint side)) ≫
      ordinary.definition

theorem definitionChild_endpoint (side : Bool) : definitionChild.{k} ≫ endpoint side =
    lift
      (call (call (definitionBody ≫ (ihom ordinary.names).map (functionEndpoint side))
        (snd definitionOuter ordinary.names)) definitionResult)
      (lift (snd definitionOuter ordinary.names) definitionStored ≫ ordinary.input ≫ ordinary.replication) ≫
        ordinary.parallel := by
  rw [definitionChild, supplied_parallel_endpoint, call_postcomposition, call_postcomposition]
  rfl

theorem definitionReaction_endpoint (side : Bool) : definitionReaction.{k} ≫ endpoint side =
    call (fst definitionDomain ordinary.names ≫ definitionEndpoint side) (snd definitionDomain ordinary.names) := by
  rw [definitionReaction, supplied_restriction_endpoint, definitionChild_endpoint]
  have value : fst definitionDomain ordinary.names ≫ definitionEndpoint side =
      lift (fst definitionDomain ordinary.names ≫ fst ordinary.termObject boundContinuations)
        ((fst definitionDomain ordinary.names ≫ snd ordinary.termObject boundContinuations) ≫
          (ihom ordinary.names).map (functionEndpoint side)) ≫ ordinary.definition := by
    simp only [definitionEndpoint, comp_lift_assoc, Category.assoc]
  rw [value, definition_value]
  apply congrArg (bindFresh ordinary)
  simp only [definitionBody, definitionStored, definitionResult, Category.assoc]

theorem definition_endpoint (side : Bool) : definition.{k} ≫ functionEndpoint side = definitionEndpoint side := by
  rw [definition, functionEndpoint, abstraction_postcomposition, definitionReaction_endpoint]
  exact abstraction_evaluation (definitionEndpoint side)

abbrev carrierDomain := ordinary.{k}.names ⊗ (ordinary.termObject ⊗ continuations)
abbrev carrierOuter := carrierDomain.{k} ⊗ ordinary.names

def carrierName : carrierOuter.{k} ⟶ ordinary.names :=
  fst carrierDomain ordinary.names ≫ fst ordinary.names (ordinary.termObject ⊗ continuations)
def carrierStored : carrierOuter.{k} ⟶ ordinary.termObject :=
  fst carrierDomain ordinary.names ≫ snd ordinary.names (ordinary.termObject ⊗ continuations) ≫
    fst ordinary.termObject continuations
def carrierBody : carrierOuter.{k} ⟶ continuations :=
  fst carrierDomain ordinary.names ≫ snd ordinary.names (ordinary.termObject ⊗ continuations) ≫
    snd ordinary.termObject continuations

def carrierChild : carrierOuter.{k} ⟶ category.edge :=
  lift (call carrierBody (snd carrierDomain ordinary.names))
    (lift carrierName carrierStored ≫ ordinary.input) ≫ BindingClosedGeneratedOperationalClosure.parallel

def carrier : carrierDomain.{k} ⟶ continuations := abstraction carrierChild

def carrierEndpoint (side : Bool) : carrierDomain.{k} ⟶ ordinary.termObject :=
  lift (fst ordinary.names (ordinary.termObject ⊗ continuations))
    (lift (snd ordinary.names (ordinary.termObject ⊗ continuations) ≫ fst ordinary.termObject continuations)
      (snd ordinary.names (ordinary.termObject ⊗ continuations) ≫ snd ordinary.termObject continuations ≫
        functionEndpoint side)) ≫ ordinary.carrier

theorem carrierChild_endpoint (side : Bool) : carrierChild.{k} ≫ endpoint side =
    call (fst carrierDomain ordinary.names ≫ carrierEndpoint side) (snd carrierDomain ordinary.names) := by
  rw [carrierChild, supplied_parallel_endpoint, call_postcomposition]
  have value : fst carrierDomain ordinary.names ≫ carrierEndpoint side =
      lift carrierName (lift carrierStored (carrierBody ≫ functionEndpoint side)) ≫ ordinary.carrier := by
    simp only [carrierEndpoint, carrierName, carrierStored, carrierBody, comp_lift_assoc, comp_lift, Category.assoc]
  rw [value, carrier_value]
  rfl

theorem carrier_endpoint (side : Bool) : carrier.{k} ≫ functionEndpoint side = carrierEndpoint side := by
  rw [carrier, functionEndpoint, abstraction_postcomposition, carrierChild_endpoint]
  exact abstraction_evaluation (carrierEndpoint side)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational
