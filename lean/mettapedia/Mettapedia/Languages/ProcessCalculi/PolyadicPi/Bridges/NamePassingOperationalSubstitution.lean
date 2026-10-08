import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalEvents

/-!
# Complete occurrence transport under target substitution

The full reaction tree commutes with substitution. The binary beta receiver
keeps its argument and return positions through all three ambient binders;
active positions retain both their supplied reaction and their process frame.
Together with the independently checked endpoint interpretation this earns
equality of the complete structurally enveloped events.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalEvents

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation

theorem beta_body_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ)) (environment : Environment Γ Δ)
    (assigned : Sub sig Δ Θ) :
    bind (liftSub assigned [.nm, .nm, .nm])
        (interpret body ((environment.substitute weakening).substitute weakening).lift (.var (.succ .zero))) =
      interpret body (((environment.substitute assigned).substitute weakening).substitute weakening).lift
        (.var (.succ .zero)) := by
  rw [liftSub_cons assigned .nm [.nm, .nm], interpret_target_substitution,
    Environment.lift_substitute, liftSub_cons assigned .nm [.nm],
    Environment.weaken_substitute, Environment.weaken_substitute]
  rfl

theorem beta_reaction_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: Γ))
    (argument : NamePassing.Presentation.Name Γ) (environment : Environment Γ Δ)
    (result : Name Δ) (assigned : Sub sig Δ Θ) :
    (betaReaction body argument environment result).substitute assigned =
      betaReaction body argument (environment.substitute assigned) (bind assigned result) := by
  simp only [betaReaction, OperationalDiagram.Reaction.substitute]
  rw [bind_weaken, bind_weaken, interpretName_substitute]
  apply congrArg OperationalDiagram.Reaction.restriction
  apply congrArg (OperationalDiagram.Reaction.binary (.var .zero)
    (weaken (interpretName argument (environment.substitute assigned))) (weaken (bind assigned result)))
  rw [liftSub_cons (liftSub assigned [.nm]) .nm [.nm],
    ← liftSub_cons assigned .nm [.nm], ← liftSub_cons assigned .nm [.nm, .nm]]
  exact beta_body_substitution body environment assigned

theorem reaction_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (event : SourceEvent Γ) (environment : Environment Γ Δ) (result : Name Δ)
    (assigned : Sub sig Δ Θ) :
    (mapEvent event environment result).reaction.substitute assigned =
      (mapEvent event (environment.substitute assigned) (bind assigned result)).reaction := by
  induction event generalizing Δ Θ with
  | beta body argument => exact beta_reaction_substitution body argument environment result assigned
  | fetch name value =>
      simp only [mapEvent, fetchEvent, OperationalDiagram.Reaction.substitute]
      rw [interpretName_substitute, interpret_target_substitution, Environment.weaken_substitute]
      rfl
  | application argument before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft,
        OperationalDiagram.Event.restriction, OperationalDiagram.Reaction.substitute]
      rw [ih, Environment.weaken_substitute]
      apply congrArg OperationalDiagram.Reaction.restriction
      apply congrArg (OperationalDiagram.Reaction.parallelLeft
        (mapEvent before ((environment.substitute assigned).substitute weakening) (.var .zero)).reaction)
      change out2 (.var .zero)
        (bind (liftSub assigned [.nm]) (weaken (interpretName argument environment)))
        (bind (liftSub assigned [.nm]) (weaken result)) = _
      rw [bind_weaken, bind_weaken, interpretName_substitute]
  | definition value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft,
        OperationalDiagram.Event.restriction, OperationalDiagram.Reaction.substitute]
      rw [ih, Environment.lift_substitute, bind_weaken]
      apply congrArg OperationalDiagram.Reaction.restriction
      apply congrArg (OperationalDiagram.Reaction.parallelLeft
        (mapEvent before (environment.substitute assigned).lift (weaken (bind assigned result))).reaction)
      change rep (inp1 (.var .zero)
        (bind (liftSub (liftSub assigned [.nm]) [.nm])
          (interpret value ((environment.substitute weakening).substitute weakening) (.var .zero)))) = _
      rw [interpret_target_substitution, Environment.weaken_substitute, Environment.weaken_substitute]
      rfl
  | carrier name value before ih =>
      simp only [mapEvent, OperationalDiagram.Event.parallelLeft, OperationalDiagram.Reaction.substitute]
      rw [ih]
      apply congrArg (OperationalDiagram.Reaction.parallelLeft
        (mapEvent before (environment.substitute assigned) (bind assigned result)).reaction)
      change inp1 (bind assigned (interpretName name environment))
        (bind (liftSub assigned [.nm]) (interpret value (environment.substitute weakening) (.var .zero))) = _
      rw [interpretName_substitute, interpret_target_substitution, Environment.weaken_substitute]
      rfl

/-- Equality includes both structural endpoint envelopes and the supplied
communication-position tree; no event is selected from mere existence. -/
theorem event_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (event : SourceEvent Γ) (environment : Environment Γ Δ) (result : Name Δ)
    (assigned : Sub sig Δ Θ) :
    (mapEvent event environment result).substitute assigned =
      mapEvent event (environment.substitute assigned) (bind assigned result) := by
  apply OperationalDiagram.Event.ext
  · change bind assigned (mapEvent event environment result).source = _
    rw [source_readout, source_readout, interpret_target_substitution]
  · change bind assigned (mapEvent event environment result).target = _
    rw [target_readout, target_readout, interpret_target_substitution]
  · exact reaction_substitution event environment result assigned

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalEvents
