import Mathlib

/-!
# Effect-broker noninterference

Source provenance: adapted from GödelClaw commit
`906793a7cba9245ce4f7f9f5b479c77088fd1805`; only module packaging and
taxonomy-facing names were changed during integration.

An effect broker is not an authority boundary if a later observer evaluates
the command value which the broker withheld.  This model isolates the runtime
failure in which a command list was admitted as data, correctly withheld after
a new stimulus, and then reduced by an attention update.

The repair passes only a finite parse-outcome tag to attention.  The command
remains data until, and unless, the broker admits it.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference

abbrev Command := Nat

structure Runtime where
  effects : List Command
deriving Repr, DecidableEq

def perform (command : Command) (runtime : Runtime) : Runtime :=
  { runtime with effects := runtime.effects ++ [command] }

/-- The broker itself is correct: a revoked turn leaves the world unchanged. -/
def broker (admitted : Bool) (command : Command)
    (runtime : Runtime) : Runtime :=
  if admitted then perform command runtime else runtime

/-- The defective observer reduces command data after the broker decision. -/
def eagerAttention (command : Command) (runtime : Runtime) : Runtime :=
  perform command runtime

def deployedStep (admitted : Bool) (command : Command)
    (runtime : Runtime) : Runtime :=
  eagerAttention command (broker admitted command runtime)

inductive ParseOutcome where
  | noCommands
  | commandsParsed
deriving Repr, DecidableEq

/-- Attention needs only this tag; observing it has no host effect. -/
def inertAttention (_outcome : ParseOutcome) (runtime : Runtime) : Runtime :=
  runtime

def repairedStep (admitted : Bool) (command : Command)
    (outcome : ParseOutcome) (runtime : Runtime) : Runtime :=
  inertAttention outcome (broker admitted command runtime)

def WithheldNoninterference
    (step : Bool → Command → Runtime → Runtime) : Prop :=
  ∀ command runtime, step false command runtime = runtime

theorem broker_withholding_is_noninterfering :
    WithheldNoninterference broker := by
  intro command runtime
  rfl

/-- A correct broker cannot compensate for a post-broker evaluator which has
the same command authority. -/
theorem deployed_step_violates_withheld_noninterference :
    ¬ WithheldNoninterference deployedStep := by
  intro purported
  have := purported 1 ⟨[]⟩
  simp [deployedStep, broker, eagerAttention, perform] at this

theorem repaired_step_preserves_withheld_noninterference
    (outcome : ParseOutcome) :
    ∀ command runtime,
      repairedStep false command outcome runtime = runtime := by
  intro command runtime
  rfl

/-- Admitted commands retain their ordinary authority; the repair is not a
one-command prohibition or a general restriction on effects. -/
theorem repaired_admitted_command_still_runs
    (command : Command) (runtime : Runtime) (outcome : ParseOutcome) :
    repairedStep true command outcome runtime = perform command runtime := by
  rfl

#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference.deployed_step_violates_withheld_noninterference
#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference.repaired_step_preserves_withheld_noninterference
#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference.repaired_admitted_command_still_runs

end Mettapedia.CognitiveArchitecture.Agent.EffectBrokerNoninterference
