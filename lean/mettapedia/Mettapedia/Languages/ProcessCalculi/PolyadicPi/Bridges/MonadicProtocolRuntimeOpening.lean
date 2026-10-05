import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeWitness
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleUpdate
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningTracing

/-!
# Opening the actual supplied firing of a closed tuple runtime

The source telescope and the occurrence registry's private telescope are
opened through the existing origin-preserving communication theorem. The
selected input and output, primitive arity and supplied target are retained.
Safety follows from the actual guarded runtime heads; it is not a restriction
on which target execution may be supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeOpening

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities RuntimeState RuntimeActors RuntimeWitness ScopedActiveFrontier
open ActiveMarking ActiveGuardedBodies ScopedCommunicationInversion ActiveHeaderInvariant

def scopeMarks {Label : Type} (origin : Label) : ∀ {Γ Δ : Ctx sig}
    (scope : Scope Γ Δ), ScopeMarks Label scope
  | _, _, .nil => .nil
  | _, _, .bind rest => .bind origin (scopeMarks origin rest)

theorem scope_fits {Label : Type} (origin : Label) : ∀ {Γ Δ : Ctx sig}
    (scope : Scope Γ Δ) {body : Proc Δ} {marks : ActiveMarking.Tree Label},
    Fits marks body → Fits ((scopeMarks origin scope).close marks) (scope.close body)
  | _, _, .nil, _, _, fitted => fitted
  | _, _, .bind rest, _, _, fitted => .nu origin (scope_fits origin rest fitted)

theorem scope_safe : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ),
    ScopedOpening.Safe body → ScopedOpening.Safe (scope.close body)
  | _, _, .nil, _, safe => safe
  | _, _, .bind rest, body, safe => by
      simpa only [Scope.close, nu, ScopedOpening.Safe] using scope_safe rest body safe

def fullScope {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    Scope Γ (World witness.n witness.world) := witness.scope.append (privateScope witness.n)

def closedAssembly {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) : Proc Γ :=
  (fullScope witness).close (assembly witness.registry (parallel witness.frame))

def closedMarks {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    ActiveMarking.Tree (RuntimeActors.Origin witness.n) :=
  (scopeMarks (RuntimeActors.Origin.suspended : RuntimeActors.Origin witness.n)
    (fullScope witness)).close (assemblyMarks witness.registry witness.frame)

theorem canonical_equation {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    StructuralEq target (closedAssembly witness) := by
  rw [closedAssembly, fullScope, Scope.close_append]
  exact witness.target.trans (witness.scope.congr ((privateScope witness.n).congr
    (registry_equation witness.registry (parallel witness.frame) witness.live)))

theorem closed_fits {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    Fits (closedMarks witness) (closedAssembly witness) :=
  scope_fits (RuntimeActors.Origin.suspended : RuntimeActors.Origin witness.n)
    (fullScope witness) (assembly_fits witness.registry witness.frame)

theorem closed_safe {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    ScopedOpening.Safe (closedAssembly witness) :=
  scope_safe (fullScope witness) _ (ScopedOpening.safe_of_vacuous _
    (RuntimeIdleUpdate.assembly_unused witness.registry witness.frame witness.heads))

/-- Even an independently supplied marked exposure retains its selected
occurrences through both original restriction telescopes. -/
theorem open_given {Γ : Ctx sig} {source current after : Proc Γ}
    (witness : Witness source current)
    (actual : Exposure (closedAssembly witness) after)
    (given : TracedExposure (closedMarks witness) actual) :
    ∃ returned : Proc (World witness.n witness.world),
      ∃ opened : Exposure (assembly witness.registry (parallel witness.frame)) returned,
        ∃ traced : TracedExposure (assemblyMarks witness.registry witness.frame) opened,
          traced.continuation.inputOrigin = given.continuation.inputOrigin ∧
          traced.continuation.outputOrigin = given.continuation.outputOrigin ∧
          inputHeader opened.selected = inputHeader actual.selected ∧
          StructuralEq after (witness.scope.close ((privateScope witness.n).close returned)) := by
  obtain ⟨returned, opened, traced, input, output, arity, endpoint⟩ :=
    ScopedOpeningTracing.open_scope_traced
      (scopeMarks (RuntimeActors.Origin.suspended : RuntimeActors.Origin witness.n) (fullScope witness))
      (assembly witness.registry (parallel witness.frame)) (assemblyMarks witness.registry witness.frame)
      (assembly_fits witness.registry witness.frame) actual given (closed_safe witness)
  rw [fullScope, Scope.close_append] at endpoint
  exact ⟨returned, opened, traced, input, output, arity, endpoint⟩

/-- Every actual equation-saturated runtime step has a traced firing of its
open assembly and the same supplied closed endpoint. -/
theorem expose {Γ : Ctx sig} {source current after : Proc Γ}
    (witness : Witness source current) (firing : StepModulo current after) :
    ∃ returned : Proc (World witness.n witness.world),
      ∃ opened : Exposure (assembly witness.registry (parallel witness.frame)) returned,
        ∃ _traced : TracedExposure (assemblyMarks witness.registry witness.frame) opened,
          StructuralEq after (witness.scope.close ((privateScope witness.n).close returned)) := by
  have canonical := modulo_source_equation (canonical_equation witness).symm firing
  obtain ⟨actual, ⟨given⟩⟩ := modulo_step_has_traced_origins .suspended (closed_fits witness) canonical
  obtain ⟨returned, opened, traced, _, _, _, endpoint⟩ := open_given witness actual given
  exact ⟨returned, opened, traced, endpoint⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeOpening
