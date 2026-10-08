import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalFetch
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationFunctionValues
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalClosure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralLaws

/-!
# Complete generated beta evidence

Binary COMM receives the independent argument and return inputs. Its actual
edge is abstracted in a private name and transported through the generated
restriction evidence operation. Authored structural equations earn both
whole endpoints, including elimination of the unused private target binder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open NamePassingContinuationOperations NamePassingContinuationValues

universe k

abbrev betaDomain := ordinary.{k}.boundBodyObject ⊗ ordinary.names
abbrev betaOuter := betaDomain.{k} ⊗ ordinary.names
abbrev betaInner := betaOuter.{k} ⊗ ordinary.names

def betaFunction : betaInner.{k} ⟶ ordinary.boundBodyObject :=
  fst betaOuter ordinary.names ≫ fst betaDomain ordinary.names ≫ fst ordinary.boundBodyObject ordinary.names
def betaArgument : betaInner.{k} ⟶ ordinary.names :=
  fst betaOuter ordinary.names ≫ fst betaDomain ordinary.names ≫ snd ordinary.boundBodyObject ordinary.names
def betaResult : betaInner.{k} ⟶ ordinary.names :=
  fst betaOuter ordinary.names ≫ snd betaDomain ordinary.names
def betaPrivate : betaInner.{k} ⟶ ordinary.names := snd betaOuter ordinary.names

def betaChild : betaInner.{k} ⟶ category.edge :=
  BindingClosedGeneratedCommunicationReadout.binary betaPrivate betaArgument betaResult
    (NamePassingContinuationFunctionValues.receiver ordinary betaFunction)

def betaReaction : betaOuter.{k} ⟶ category.edge :=
  abstraction betaChild ≫ BindingClosedGeneratedOperationalClosure.restriction

def beta : betaDomain.{k} ⟶ (ordinary.names ⟶[Target] category.edge) := abstraction betaReaction

def betaSource : betaDomain.{k} ⟶ ordinary.termObject :=
  lift (fst ordinary.boundBodyObject ordinary.names ≫ ordinary.abstraction)
    (snd ordinary.boundBodyObject ordinary.names) ≫ ordinary.application

def betaTarget : betaDomain.{k} ⟶ ordinary.termObject :=
  call (fst ordinary.boundBodyObject ordinary.names) (snd ordinary.boundBodyObject ordinary.names)

def betaSourceBody : betaInner.{k} ⟶ ordinary.processes :=
  lift (call (betaFunction ≫ ordinary.abstraction) betaPrivate)
    (lift betaPrivate (lift betaArgument betaResult) ≫ ordinary.send) ≫ ordinary.parallel

def betaTargetBody : betaOuter.{k} ⟶ ordinary.processes :=
  call (call (fst betaDomain ordinary.names ≫ fst ordinary.boundBodyObject ordinary.names)
    (fst betaDomain ordinary.names ≫ snd ordinary.boundBodyObject ordinary.names))
    (snd betaDomain ordinary.names)

theorem betaChild_source : betaChild.{k} ≫ source = betaSourceBody := by
  rw [betaChild, BindingClosedGeneratedCommunicationReadout.binary_source]
  rw [← NamePassingContinuationFunctionValues.abstraction_value]
  exact BindingClosedStructuralLaws.parallel_comm binding
    BindingClosedGeneratedOperationalModel.structural_schemas _ _

theorem betaChild_target : betaChild.{k} ≫ target = fst betaOuter ordinary.names ≫ betaTargetBody := by
  rw [betaChild, BindingClosedGeneratedCommunicationReadout.binary_target,
    ← NamePassingBindingClosedSchemas.call_as_evaluation,
    NamePassingContinuationFunctionValues.receiver_evaluation]
  simp only [betaFunction, betaArgument, betaResult, betaTargetBody, call, comp_lift_assoc]

theorem restriction_source : BindingClosedGeneratedOperationalClosure.restriction.{k} ≫ source =
    (ihom ordinary.names).map source ≫ ordinary.fresh := by
  change BindingClosedGeneratedOperationalClosure.restriction ≫
      (category.source ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) = _
  rw [← Category.assoc, BindingClosedGeneratedOperationalClosure.private_source]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem restriction_target : BindingClosedGeneratedOperationalClosure.restriction.{k} ≫ target =
    (ihom ordinary.names).map target ≫ ordinary.fresh := by
  change BindingClosedGeneratedOperationalClosure.restriction ≫
      (category.target ≫ BindingClosedGeneratedOperationalModel.processComparison.inv) = _
  rw [← Category.assoc, BindingClosedGeneratedOperationalClosure.private_target]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem fresh_unused {Z : Target.{k}} (process : Z ⟶ ordinary.processes) :
    bindFresh ordinary (fst Z ordinary.names ≫ process) = process := by
  have unused := BindingClosedStructuralLaws.private_unused binding
    BindingClosedGeneratedOperationalModel.structural_schemas process
  unfold bindFresh abstraction
  rw [exchange, lift_fst_assoc]
  exact unused

theorem betaReaction_source : betaReaction.{k} ≫ source = bindFresh ordinary betaSourceBody := by
  rw [betaReaction, Category.assoc, restriction_source, ← Category.assoc,
    abstraction_postcomposition, betaChild_source]
  rfl

theorem betaReaction_target : betaReaction.{k} ≫ target = betaTargetBody := by
  rw [betaReaction, Category.assoc, restriction_target, ← Category.assoc,
    abstraction_postcomposition, betaChild_target]
  exact fresh_unused betaTargetBody

theorem betaSource_value : call (fst betaDomain.{k} ordinary.names ≫ betaSource)
    (snd betaDomain ordinary.names) = bindFresh ordinary betaSourceBody := by
  have complete : fst betaDomain ordinary.names ≫ betaSource =
      lift ((fst betaDomain ordinary.names ≫ fst ordinary.boundBodyObject ordinary.names) ≫ ordinary.abstraction)
        (fst betaDomain ordinary.names ≫ snd ordinary.boundBodyObject ordinary.names) ≫ ordinary.application := by
    simp only [betaSource, comp_lift_assoc, Category.assoc]
  rw [complete, application_value]
  apply congrArg (bindFresh ordinary)
  simp only [betaSourceBody, betaFunction, betaArgument, betaResult, betaPrivate, call,
    Category.assoc]

theorem betaTarget_value : betaTargetBody.{k} =
    call (fst betaDomain ordinary.names ≫ betaTarget) (snd betaDomain ordinary.names) := by
  unfold betaTargetBody betaTarget
  rw [← call_natural]

theorem beta_source : beta.{k} ≫ (ihom ordinary.names).map source = betaSource := by
  rw [beta, abstraction_postcomposition, betaReaction_source, ← betaSource_value]
  exact abstraction_evaluation betaSource

theorem beta_target : beta.{k} ≫ (ihom ordinary.names).map target = betaTarget := by
  rw [beta, abstraction_postcomposition, betaReaction_target]
  rw [betaTarget_value]
  exact abstraction_evaluation betaTarget

theorem beta_substitution {W : Target.{k}} (change : W ⟶ betaDomain) :
    change ≫ beta = abstraction (change ▷ ordinary.names ≫ betaReaction) :=
  abstraction_natural change betaReaction

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational
