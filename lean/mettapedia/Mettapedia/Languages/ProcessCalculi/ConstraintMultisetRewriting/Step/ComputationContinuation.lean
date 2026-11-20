import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationConservativity

/-!
# Continuing a computation with a typed publication

An actual computational run supplies its complete final configuration. A later
typed consumer may publish at a different declared type. This is a separate
source schema and publication, rather than pretending that the change of type
is a reduction of the earlier term. The ordinary full step and the typed source
publication have exactly the same result for this schema.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull TypedPublication
open NativeTypesOnTheStep.Computing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  {qualified : Qualified S} {presentation : AlgebraicParallel.SchemaPresentation S.R}

def RunProfile.finalConfiguration {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) : Configuration (S := S) where
  state := run.last
  active := profile.execution.last.active
  present := by
    rw [profile.exact_endpoint]
    exact profile.execution.last.present
  consistent := by
    rw [profile.exact_endpoint]
    exact profile.execution.last.consistent

namespace Continuation

variable (configuration : Configuration (S := S)) (output : TotalTerm configuration.state.frame)

def schema : DependentProgram.Schema S.levels Nat configuration.state.frame :=
  ⟨.nil configuration.state.frame, [configuration.state.label configuration.active], [],
    [Make.ofRow output], [], [], []⟩

def choice (target : Nat) : DependentProgram.Pick (schema configuration output) :=
  ⟨⟨[configuration.active], [], [target]⟩, rfl⟩

theorem outputs_typed (made : Make (schema configuration output).helpers.frame)
    (member : made ∈ (schema configuration output).makes) : made.WellTyped := by
  obtain rfl := List.mem_singleton.mp member
  exact Make.ofRow_wellTyped output

theorem compile_eq (target : Nat) :
    (schema configuration output).compile (choice configuration output target) =
      ComputationResources.firing S.levels configuration.state configuration.active target output := rfl

theorem full_admitted (target : Nat) (fresh : target ∉ configuration.state.present) :
    (step S.levels Nat).Admits
      (ComputationResources.firing S.levels configuration.state configuration.active target output) :=
  (ComputationResources.admitted_iff S.levels _ _ _ _).mpr
    ⟨configuration.present, fresh, configuration.consistent⟩

theorem source_admitted (target : Nat) (fresh : target ∉ configuration.state.present) :
    (schema configuration output).Admits (choice configuration output target) := by
  apply ((schema configuration output).compile_admits_iff (choice configuration output target)).mp
  rw [compile_eq]
  exact full_admitted configuration output target fresh

def application (target : Nat) : Application S.levels Nat configuration.state :=
  FrameTyped.application (schema configuration output) (outputs_typed configuration output)
    (choice configuration output target)

theorem publication_admitted (target : Nat) (fresh : target ∉ configuration.state.present) :
    (realizationStep S.levels Nat).Admits (application configuration output target) :=
  (FrameTyped.admits_iff _ _ _).mpr (source_admitted configuration output target fresh)

theorem publication_result (target : Nat) (fresh : target ∉ configuration.state.present) :
    (realizationStep S.levels Nat).result (application configuration output target)
        (publication_admitted configuration output target fresh) =
      (step S.levels Nat).toStep.result
        (ComputationResources.firing S.levels configuration.state configuration.active target output)
        (full_admitted configuration output target fresh) := by
  dsimp only [application]
  rw [FrameTyped.result_eq (schema configuration output) (outputs_typed configuration output)
    (choice configuration output target) (source_admitted configuration output target fresh)]
  symm
  have result := (schema configuration output).compile_result
    (choice configuration output target) (source_admitted configuration output target fresh)
  exact result

def fullRun (target : Nat) (fresh : target ∉ configuration.state.present) :
    (step S.levels Nat).toStep.Run configuration.state :=
  .cons (ComputationResources.firing S.levels configuration.state configuration.active target output)
    (full_admitted configuration output target fresh) (.nil _)

theorem fullRun_output (target : Nat) (fresh : target ∉ configuration.state.present) :
    (fullRun configuration output target fresh).last.label target = output :=
  ComputationResources.result_label S.levels _ _ _ _ (full_admitted configuration output target fresh)

theorem fullRun_target (target : Nat) (fresh : target ∉ configuration.state.present) :
    target ∈ (fullRun configuration output target fresh).last.present :=
  ComputationResources.target_present S.levels _ _ _ _ (full_admitted configuration output target fresh)

end Continuation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Continuation.publication_result
