import Mettapedia.Languages.LambdaCalculus.NamePassingOperationalDiagram
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.OperationalDiagram
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenEquations

/-!
# Actual target event trees for every open source occurrence

Beta constructs a binary COMM below the private call name; fetch constructs
a unary COMM with the supplied stored body. Both distinct receiver positions
and the ambient return binder are retained. Active source positions map to
the independently defined parallel and scope descent trees. The endpoint
comparisons use the existing opening and structural laws, rather than an
assumed compiler simulation or equality of constructors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalEvents

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation

abbrev SourceEvent (Γ : Ctx NamePassing.Presentation.signature) :=
  NamePassing.OperationalDiagram.Event Γ
abbrev TargetEvent (Δ : Ctx sig) := OperationalDiagram.Event Δ

def betaReaction {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    OperationalDiagram.Reaction Δ :=
  .restriction (.binary (.var .zero) (weaken (interpretName argument environment)) (weaken result)
    (interpret body ((environment.substitute weakening).substitute weakening).lift (.var (.succ .zero))))

def betaEvent {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    TargetEvent Δ where
  source := interpret (NamePassing.Presentation.application (NamePassing.Presentation.abstraction body) argument)
    environment result
  target := interpret (inst body argument) environment result
  reaction := betaReaction body argument environment result
  source_readout := by
    simp only [NamePassing.Presentation.application, NamePassing.Presentation.abstraction,
      interpret, betaReaction, OperationalDiagram.Reaction.source]
    change StructuralEq (nu (par _ _)) (nu (par _ _))
    exact .nu (.parComm _ _)
  target_readout := by
    change StructuralEq (nu (openPair _ _ _)) _
    rw [beta_endpoint]
    exact .nuUnused _

def fetchEvent {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (name : NamePassing.Presentation.Name Γ) (value : NamePassing.Presentation.Program Γ)
    (environment : Environment Γ Δ) (result : Name Δ) : TargetEvent Δ where
  source := interpret (NamePassing.Presentation.carrier name value (NamePassing.Presentation.reference name))
    environment result
  target := interpret value environment result
  reaction := .unary (interpretName name environment) result
    (interpret value (environment.substitute weakening) (.var .zero))
  source_readout := by
    simp only [NamePassing.Presentation.carrier, NamePassing.Presentation.reference,
      interpret, OperationalDiagram.Reaction.source]
    exact .refl _
  target_readout := by
    change StructuralEq (inst (interpret value (environment.substitute weakening) (.var .zero)) result) _
    rw [interpret_open_result]
    exact .refl _

def mapEvent : {Γ : Ctx NamePassing.Presentation.signature} → {Δ : Ctx sig} →
    SourceEvent Γ → Environment Γ Δ → Name Δ → TargetEvent Δ
  | _, _, .beta body argument, environment, result => betaEvent body argument environment result
  | _, _, .fetch name value, environment, result => fetchEvent name value environment result
  | _, _, .application argument before, environment, result =>
      (mapEvent before (environment.substitute weakening) (.var .zero)).parallelLeft
        (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result)) |>.restriction
  | _, _, .definition value before, environment, result =>
      (mapEvent before environment.lift (weaken result)).parallelLeft
        (rep (inp1 (.var .zero)
          (interpret value ((environment.substitute weakening).substitute weakening) (.var .zero)))) |>.restriction
  | _, _, .carrier name value before, environment, result =>
      (mapEvent before environment result).parallelLeft
        (inp1 (interpretName name environment)
          (interpret value (environment.substitute weakening) (.var .zero)))

theorem source_readout {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (event : SourceEvent Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    (mapEvent event environment result).source = interpret event.source environment result := by
  induction event generalizing Δ with
  | beta => rfl
  | fetch => rfl
  | application argument before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft, OperationalDiagram.Event.restriction,
        NamePassing.OperationalDiagram.Event.source, NamePassing.Presentation.application, interpret]
      exact congrArg (fun p => nu (par p
        (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result))))
          (ih (environment.substitute weakening) (.var .zero))
  | definition value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft, OperationalDiagram.Event.restriction,
        NamePassing.OperationalDiagram.Event.source, NamePassing.Presentation.definition, interpret]
      exact congrArg (fun p => nu (par p (rep (inp1 (.var .zero)
        (interpret value ((environment.substitute weakening).substitute weakening) (.var .zero))))))
          (ih environment.lift (weaken result))
  | carrier name value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft,
        NamePassing.OperationalDiagram.Event.source, NamePassing.Presentation.carrier, interpret]
      exact congrArg (fun p => par p (inp1 (interpretName name environment)
        (interpret value (environment.substitute weakening) (.var .zero)))) (ih environment result)

theorem target_readout {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (event : SourceEvent Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    (mapEvent event environment result).target = interpret event.target environment result := by
  induction event generalizing Δ with
  | beta => rfl
  | fetch => rfl
  | application argument before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft, OperationalDiagram.Event.restriction,
        NamePassing.OperationalDiagram.Event.target, NamePassing.Presentation.application, interpret]
      exact congrArg (fun p => nu (par p
        (out2 (.var .zero) (weaken (interpretName argument environment)) (weaken result))))
          (ih (environment.substitute weakening) (.var .zero))
  | definition value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft, OperationalDiagram.Event.restriction,
        NamePassing.OperationalDiagram.Event.target, NamePassing.Presentation.definition, interpret]
      exact congrArg (fun p => nu (par p (rep (inp1 (.var .zero)
        (interpret value ((environment.substitute weakening).substitute weakening) (.var .zero))))))
          (ih environment.lift (weaken result))
  | carrier name value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft,
        NamePassing.OperationalDiagram.Event.target, NamePassing.Presentation.carrier, interpret]
      exact congrArg (fun p => par p (inp1 (interpretName name environment)
        (interpret value (environment.substitute weakening) (.var .zero)))) (ih environment result)

theorem actual_communication {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (event : SourceEvent Γ) (environment : Environment Γ Δ) (result : Name Δ) :
    StepModulo (interpret event.source environment result) (interpret event.target environment result) := by
  have actual := (mapEvent event environment result).sound
  rw [source_readout, target_readout] at actual
  exact actual

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalEvents
