import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-!
# Exact execution controls for persistent and linear environments

The source self-application program performs two distinct fetch events from
the same retained definition. Its target uses the ordinary unary/binary
communication semantics and the actual translated endpoints. A one-shot
carrier is instead consumed, and a fetched enclosing reference crosses a
fresh nested-definition scope without aliasing that fresh name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

def omegaValue : Expr [] := .lam (.app (.var .zero) .zero)
def loopingDefinition : Expr [] := .defn omegaValue (.app (.var .zero) .zero)
def releasedCall : Expr [] :=
  .defn omegaValue (.app (NamePassing.weaken omegaValue) .zero)

def closedNames : Ren sig [] [Srt.nm] := fun _ name => nomatch name
def returnName : Var [Srt.nm] .nm := .zero

theorem first_fetch :
    NamePassing.Environment.Step .environmentFetch loopingDefinition releasedCall :=
  .environmentFetch omegaValue (.app .zero (.here .zero (NamePassing.weaken omegaValue)))

theorem retained_reference_called :
    NamePassing.Environment.Step .beta releasedCall loopingDefinition :=
  .defn omegaValue (.beta (.app (.var .zero) .zero) .zero)

/-- The lookup below the application's private channel reaches the enclosing
server and retains the definition at the actual translated endpoint. -/
theorem private_channel_fetch_executes :
    StepModulo (compile loopingDefinition closedNames returnName)
      (compile releasedCall closedNames returnName) :=
  step_preserved first_fetch closedNames returnName

theorem released_call_executes :
    StepModulo (compile releasedCall closedNames returnName)
      (compile loopingDefinition closedNames returnName) :=
  step_preserved retained_reference_called closedNames returnName

theorem same_definition_fetches_twice :
    StepModulo (compile loopingDefinition closedNames returnName)
        (compile releasedCall closedNames returnName) ∧
      StepModulo (compile releasedCall closedNames returnName)
        (compile loopingDefinition closedNames returnName) ∧
      StepModulo (compile loopingDefinition closedNames returnName)
        (compile releasedCall closedNames returnName) :=
  ⟨private_channel_fetch_executes, released_call_executes, private_channel_fetch_executes⟩

def nestedDefinitions : Expr [] :=
  .defn omegaValue (.defn (.var .zero) (.var (.succ .zero)))
def enclosingValueReleased : Expr [] :=
  .defn omegaValue (.defn (.var .zero) (NamePassing.weaken (NamePassing.weaken omegaValue)))

theorem nested_source_lookup :
    NamePassing.Environment.Step .environmentFetch nestedDefinitions enclosingValueReleased :=
  .environmentFetch omegaValue
    (.defn (.var .zero) (.here (.succ .zero)
      (NamePassing.weaken (NamePassing.weaken omegaValue))))

theorem nested_scope_lookup_executes :
    StepModulo (compile nestedDefinitions closedNames returnName)
      (compile enclosingValueReleased closedNames returnName) :=
  step_preserved nested_source_lookup closedNames returnName

/-- A linear declaration answers the application and is consumed. -/
theorem contextual_carrier_consumed :
    StepModulo
      (translate (.carrier returnName (NamePassing.weaken omegaValue)
        (.app (.var returnName) returnName)) returnName)
      (translate (.app (NamePassing.weaken omegaValue) returnName) returnName) :=
  carrier_fetch_preserved
    (.app returnName (.here returnName (NamePassing.weaken omegaValue)))
    (fun _ x => x) returnName

/-- A selected environment fetch cannot return an arbitrary process in place
of the compiled stored expression, even with the server retained. -/
theorem selected_wrong_return_rejected :
    ¬ Step
      (par (par (out1 (.var returnName) (.var returnName))
        (listener omegaValue closedNames returnName))
        (server omegaValue closedNames returnName))
      (par (out1 (.var returnName) (.var returnName))
        (server omegaValue closedNames returnName)) := by
  intro firing
  have equal := (persistent_firing_iff omegaValue closedNames returnName returnName
    (out1 (.var returnName) (.var returnName))).mp firing
  cases equal

def closedValue : Expr [Srt.nm, Srt.nm] :=
  NamePassing.weaken (NamePassing.weaken omegaValue)

def distinctReference : Expr [Srt.nm, Srt.nm] :=
  .carrier .zero closedValue (.var (.succ .zero))

def collapseNames : Ren sig [Srt.nm, Srt.nm] [Srt.nm] := fun _ name =>
  match name with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible

/-- Distinct references do not communicate in the source. -/
theorem distinct_reference_has_no_source_event {kind : NamePassing.Environment.Action}
    {target : Expr [Srt.nm, Srt.nm]} :
    ¬ NamePassing.Environment.Step kind distinctReference target := by
  intro step
  cases step with
  | carrierFetch name value fetch => cases fetch
  | carrier name value step => cases step

/-- An arbitrary noninjective name map can introduce a target communication.
Forward preservation alone therefore supplies no unrestricted reflection. -/
theorem collapsing_references_introduces_target_event :
    StepModulo (compile distinctReference collapseNames returnName)
      (compile closedValue collapseNames returnName) := by
  change StepModulo
    (par (out1 (.var returnName) (.var returnName))
      (listener closedValue collapseNames returnName))
    (compile closedValue collapseNames returnName)
  exact (fetch_preserved (.zero : Var [Srt.nm, Srt.nm] .nm)
    closedValue collapseNames returnName).toModulo

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls
