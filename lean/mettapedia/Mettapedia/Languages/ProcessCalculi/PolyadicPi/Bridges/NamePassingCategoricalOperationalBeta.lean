import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalFetch
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalEquations

/-!
# Complete native beta evidence from binary COMM and private descent

An arbitrary supplied function of argument and return is received by the
actual binary protocol. A retained firing is curried in the private name,
descended through the authored scope rule and curried in the public return.
The structural endpoint comparisons retain the complete function section.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open NamePassingContinuationOperations NamePassingCategoricalCompiler

attribute [local irreducible] Mettapedia.OSLF.Binding.BindingEquationQuotientModel.operation

private def receivedBody (O : Operations Ambient) :
    (O.boundBodyObject ⊗ O.names) ⊗ (O.names ⊗ O.names) ⟶ O.processes :=
  call (call
    (fst (O.boundBodyObject ⊗ O.names) (O.names ⊗ O.names) ≫ fst O.boundBodyObject O.names)
    (snd (O.boundBodyObject ⊗ O.names) (O.names ⊗ O.names) ≫ fst O.names O.names))
    (snd (O.boundBodyObject ⊗ O.names) (O.names ⊗ O.names) ≫ snd O.names O.names)

private def applicationBody (O : Operations Ambient) :
    ((O.termObject ⊗ O.names) ⊗ O.names) ⊗ O.names ⟶ O.processes :=
  lift
    (call (fst ((O.termObject ⊗ O.names) ⊗ O.names) O.names ≫
      fst (O.termObject ⊗ O.names) O.names ≫ fst O.termObject O.names)
      (snd ((O.termObject ⊗ O.names) ⊗ O.names) O.names))
    (lift (snd ((O.termObject ⊗ O.names) ⊗ O.names) O.names)
      (lift (fst ((O.termObject ⊗ O.names) ⊗ O.names) O.names ≫
        fst (O.termObject ⊗ O.names) O.names ≫ snd O.termObject O.names)
        (fst ((O.termObject ⊗ O.names) ⊗ O.names) O.names ≫
          snd (O.termObject ⊗ O.names) O.names)) ≫ O.send) ≫ O.parallel

private theorem received_current (O : Operations Ambient) (world : Base)
    (function : O.boundBodyObject.obj world) (channel : O.names.obj world) :
    ((O.abstraction.app world function).app world (𝟙 world)) channel =
      O.receive.app world (channel,
        (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
          (receivedBody O)).app world (function,channel)) := by
  unfold Operations.abstraction
  rw [abstraction_current]
  rfl

private theorem application_current (O : Operations Ambient) (world : Base)
    (function : O.termObject.obj world) (argument result : O.names.obj world) :
    ((O.application.app world (function,argument)).app world (𝟙 world)) result =
      O.fresh.app world
        ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
          (applicationBody O)).app world ((function,argument),result)) := by
  unfold Operations.application
  rw [abstraction_current]
  rfl

attribute [local irreducible] Operations.abstraction Operations.application

abbrev betaDomain : Ambient := operations.boundBodyObject ⊗ operations.names
abbrev betaOuter : Ambient := betaDomain ⊗ operations.names
abbrev betaInner : Ambient := betaOuter ⊗ operations.names

def betaFunction : betaInner ⟶ operations.boundBodyObject :=
  fst betaOuter operations.names ≫ fst betaDomain operations.names ≫
    fst operations.boundBodyObject operations.names

def betaArgument : betaInner ⟶ operations.names :=
  fst betaOuter operations.names ≫ fst betaDomain operations.names ≫
    snd operations.boundBodyObject operations.names

def betaResult : betaInner ⟶ operations.names :=
  fst betaOuter operations.names ≫ snd betaDomain operations.names

def betaPrivate : betaInner ⟶ operations.names := snd betaOuter operations.names

/-- Both received names remain independent positions in the complete body. -/
def betaReceiver : betaInner ⟶ CategoricalOperational.binaryBodies :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (call
      (call (fst betaInner (operations.names ⊗ operations.names) ≫ betaFunction)
        (snd betaInner (operations.names ⊗ operations.names) ≫
          fst operations.names operations.names))
      (snd betaInner (operations.names ⊗ operations.names) ≫
        snd operations.names operations.names))

def betaRequest : betaInner ⟶
    operations.names ⊗ (operations.names ⊗
      (operations.names ⊗ CategoricalOperational.binaryBodies)) :=
  lift betaPrivate (lift betaArgument (lift betaResult betaReceiver))

def betaChild : betaInner ⟶ events :=
  betaRequest ≫ CategoricalOperational.binaryCommunication

def betaReaction : betaOuter ⟶ events :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaChild ≫
    CategoricalOperational.privateDescent

def beta : betaDomain ⟶ operations.names.functorHom events :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaReaction

def betaSource : betaDomain ⟶ operations.termObject :=
  lift (fst operations.boundBodyObject operations.names ≫ operations.abstraction)
    (snd operations.boundBodyObject operations.names) ≫ operations.application

def betaTarget : betaDomain ⟶ operations.termObject :=
  call (fst operations.boundBodyObject operations.names)
    (snd operations.boundBodyObject operations.names)

def betaCallBody : betaInner ⟶ operations.processes :=
  call (betaFunction ≫ operations.abstraction) betaPrivate

def betaTransmit : betaInner ⟶ operations.processes :=
  lift betaPrivate (lift betaArgument betaResult) ≫ operations.send

def betaSourceBody : betaInner ⟶ operations.processes :=
  lift betaCallBody betaTransmit ≫ operations.parallel

def betaTargetBody : betaOuter ⟶ operations.processes :=
  call (call (fst betaDomain operations.names ≫
      fst operations.boundBodyObject operations.names)
    (fst betaDomain operations.names ≫ snd operations.boundBodyObject operations.names))
    (snd betaDomain operations.names)

theorem betaReceiver_current (world : Base) (parameter : betaInner.obj world)
    (argument result : operations.names.obj world) :
    ((betaReceiver.app world parameter).app world (𝟙 world)) (argument,result) =
      (((betaFunction.app world parameter).app world (𝟙 world)) argument).app
        world (𝟙 world) result := by
  unfold betaReceiver
  rw [abstraction_current]
  rfl

theorem betaCallBody_current (world : Base) (parameter : betaInner.obj world) :
    betaCallBody.app world parameter = operations.receive.app world
      (betaPrivate.app world parameter,betaReceiver.app world parameter) := by
  unfold betaCallBody call
  change ((operations.abstraction.app world (betaFunction.app world parameter)).app
    world (𝟙 world)) (betaPrivate.app world parameter) = _
  rw [received_current]
  have comparison :
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        (receivedBody operations)).app world
          (betaFunction.app world parameter,betaPrivate.app world parameter) =
        betaReceiver.app world parameter := by
    apply Functor.functorHom_ext
    intro future change
    apply ConcreteCategory.hom_ext
    intro arguments
    rfl
  exact congrArg (fun receiver : CategoricalOperational.binaryBodies.obj world =>
    operations.receive.app world (betaPrivate.app world parameter,receiver)) comparison

theorem betaChild_source (world : Base) (parameter : betaInner.obj world) :
    source.app world (betaChild.app world parameter) =
      betaSourceBody.app world parameter := by
  change source.app world (CategoricalOperational.binaryEvent world
    (betaPrivate.app world parameter) (betaArgument.app world parameter)
    (betaResult.app world parameter) (betaReceiver.app world parameter)) = _
  rw [CategoricalOperational.binaryEvent_source]
  change operations.parallel.app world
    (betaTransmit.app world parameter,operations.receive.app world
      (betaPrivate.app world parameter,betaReceiver.app world parameter)) = _
  rw [← betaCallBody_current]
  exact CategoricalOperationalEquations.parallel_current world _ _

theorem betaChild_target (world : Base) (parameter : betaInner.obj world) :
    target.app world (betaChild.app world parameter) =
      betaTargetBody.app world ((fst betaOuter operations.names).app world parameter) := by
  change target.app world (CategoricalOperational.binaryEvent world
    (betaPrivate.app world parameter) (betaArgument.app world parameter)
    (betaResult.app world parameter) (betaReceiver.app world parameter)) = _
  rw [CategoricalOperational.binaryEvent_target, betaReceiver_current]
  rfl

/-- Scope descent preserves the entire independently formed source body. -/
theorem betaReaction_source : betaReaction ≫ source =
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaSourceBody ≫
      operations.fresh := by
  change (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaChild ≫
    CategoricalOperational.privateDescent) ≫ source = _
  rw [Category.assoc, CategoricalOperational.privateDescent_source, ← Category.assoc]
  congr 1
  exact complete_abstraction_endpoint betaChild source
    (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaSourceBody)
    (fun world parameter privateName =>
      (betaChild_source world (parameter,privateName)).trans
        (abstraction_current betaSourceBody world parameter privateName).symm)

/-- The target's unused private binder disappears by the actual authored
equation, rather than by removing it from the event construction. -/
theorem betaReaction_target : betaReaction ≫ target = betaTargetBody := by
  change (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaChild ≫
    CategoricalOperational.privateDescent) ≫ target = _
  rw [Category.assoc, CategoricalOperational.privateDescent_target, ← Category.assoc]
  have complete := complete_abstraction_endpoint betaChild target
    (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
      (fst betaOuter operations.names ≫ betaTargetBody))
    (fun world parameter privateName =>
      (betaChild_target world (parameter,privateName)).trans
        (abstraction_current (fst betaOuter operations.names ≫ betaTargetBody)
          world parameter privateName).symm)
  rw [complete]
  exact CategoricalOperationalEquations.fresh_vacuous betaTargetBody

theorem betaSource_current (world : Base) (parameter : betaOuter.obj world) :
    ((betaSource.app world parameter.1).app world (𝟙 world)) parameter.2 =
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction betaSourceBody ≫
        operations.fresh).app world parameter := by
  rcases parameter with ⟨⟨function,argument⟩,result⟩
  change ((operations.application.app world
    (operations.abstraction.app world function,argument)).app world (𝟙 world)) result = _
  rw [application_current]
  have comparison :
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        (applicationBody operations)).app world
          ((operations.abstraction.app world function,argument),result) =
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
        betaSourceBody).app world ((function,argument),result) := by
    apply Functor.functorHom_ext
    intro future change
    apply ConcreteCategory.hom_ext
    intro privateName
    change operations.parallel.app future
      ((((operations.termObject.map change (operations.abstraction.app world function)).app
        future (𝟙 future)) privateName,
        operations.send.app future (privateName,operations.names.map change argument,
          operations.names.map change result))) =
      operations.parallel.app future
      ((((operations.abstraction.app future
        (operations.boundBodyObject.map change function)).app future (𝟙 future)) privateName,
        operations.send.app future (privateName,operations.names.map change argument,
          operations.names.map change result)))
    exact congrArg (fun term : operations.termObject.obj future =>
      operations.parallel.app future
        ((term.app future (𝟙 future)) privateName,
          operations.send.app future (privateName,operations.names.map change argument,
            operations.names.map change result)))
      (operations.abstraction.naturality_apply change function).symm
  exact congrArg (operations.fresh.app world) comparison

/-- The complete source arrow is the authored application of the supplied
abstraction, at every future world and supplied return name. -/
theorem beta_source : beta ≫ (ihom operations.names).map source = betaSource := by
  apply complete_abstraction_endpoint betaReaction source betaSource
  intro world parameter result
  have endpoints := congrArg
    (fun arrow : betaOuter ⟶ operations.processes => arrow.app world (parameter,result))
    betaReaction_source
  exact endpoints.trans (betaSource_current world (parameter,result)).symm

/-- The complete target is application of the original two-argument
function; its argument and return positions remain distinct. -/
theorem beta_target : beta ≫ (ihom operations.names).map target = betaTarget := by
  apply complete_abstraction_endpoint betaReaction target betaTarget
  intro world parameter result
  have endpoints := congrArg
    (fun arrow : betaOuter ⟶ operations.processes => arrow.app world (parameter,result))
    betaReaction_target
  exact endpoints

theorem beta_source_current (world : Base) (parameter : betaDomain.obj world)
    (result : operations.names.obj world) :
    source.app world (betaReaction.app world (parameter,result)) =
      (betaSource.app world parameter).app world (𝟙 world) result := by
  have endpoints := congrArg
    (fun arrow : betaOuter ⟶ operations.processes => arrow.app world (parameter,result))
    betaReaction_source
  exact endpoints.trans (betaSource_current world (parameter,result)).symm

theorem beta_target_current (world : Base) (parameter : betaDomain.obj world)
    (result : operations.names.obj world) :
    target.app world (betaReaction.app world (parameter,result)) =
      (betaTarget.app world parameter).app world (𝟙 world) result :=
  congrArg (fun arrow : betaOuter ⟶ operations.processes =>
    arrow.app world (parameter,result)) betaReaction_target

/-- The curried receipt retains its complete future event, not just the two
endpoint classes of the present firing. -/
theorem beta_future (world future : Base) (change : world ⟶ future)
    (parameter : betaDomain.obj world) (result : operations.names.obj future) :
    ((beta.app world parameter).app future change) result =
      betaReaction.app future (betaDomain.map change parameter,result) := rfl

theorem betaChild_substitution {world future : Base} (change : world ⟶ future)
    (parameter : betaInner.obj world) :
    events.map change (betaChild.app world parameter) =
      betaChild.app future (betaInner.map change parameter) :=
  receipt_substitution betaChild change parameter

theorem betaReaction_substitution {world future : Base} (change : world ⟶ future)
    (parameter : betaOuter.obj world) :
    events.map change (betaReaction.app world parameter) =
      betaReaction.app future (betaOuter.map change parameter) :=
  receipt_substitution betaReaction change parameter

theorem beta_substitution {world future : Base} (change : world ⟶ future)
    (parameter : betaDomain.obj world) :
    (operations.names.functorHom events).map change (beta.app world parameter) =
      beta.app future (betaDomain.map change parameter) :=
  receipt_substitution beta change parameter

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational
