import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationWork

/-!
# Private nested observations in authored Need evaluation

A `select` return owns a private frontier. Each turn advances one child work
item; recursively nested observations advance a finite nesting chain rather
than finishing a child query inside one call. Satisfaction closes the private
observation, while its unconsumed computation remains archived with the parent.
It does not certify closure of that child computation.

The source uses rich Need worlds; the target uses the independently defined
receipt-erased execution machine. Both preserve return stacks and captured
bindings. Nested observations are pure barriers: their branch caches are
private and do not replace the caller's heap. Foreign effects and leases of
another observation's handle are outside this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeObservationScopes

open NativeEquationNeed
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.BranchingTemporal

abbrev Core := NeedExecution.CoreMachine Origin Local Resume Rule Atom Empty String Empty

def delimiter : Control Local Resume Atom Empty String →
    Option (Nat × Atom × Environment)
  | .run (.arguments (.constructor "select") []
      [.grounded (.int (.ofNat requested)), body] environment) _ =>
      some (requested, body, environment)
  | _ => none

def observation (requested : Nat) (values : List Atom) (childClosed : Bool) : Atom :=
  .expression [.symbol "Observation", .expression values,
    .expression [.symbol "satisfied", .grounded (.bool (decide (requested ≤ values.length)))],
    .expression [.symbol "closed", .grounded (.bool childClosed)]]

inductive SourceWork where
  | native (machine : NativeMachine) (archived : List SourceWork)
  | scope (parent : NativeMachine) (requested : Nat)
      (children : List SourceWork) (values : List Atom) (archived : List SourceWork)

inductive CoreWork where
  | native (machine : Core) (archived : List CoreWork)
  | scope (parent : Core) (requested : Nat)
      (children : List CoreWork) (values : List Atom) (archived : List CoreWork)

def erase : SourceWork → CoreWork
  | .native machine archived => .native (NeedExecution.eraseMachine machine) (archived.map erase)
  | .scope parent requested children values archived =>
      .scope (NeedExecution.eraseMachine parent) requested (children.map erase) values
        (archived.map erase)

def sourceEmit : SourceWork → Option Outcome
  | .native machine _ => NeedReference.haltedOutcome machine
  | .scope _ _ _ _ _ => none

def coreEmit : CoreWork → Option Outcome
  | .native machine _ => NeedExecution.haltedOutcome machine
  | .scope _ _ _ _ _ => none

theorem emit_erases (work : SourceWork) : coreEmit (erase work) = sourceEmit work := by
  cases work <;> simp only [erase, coreEmit, sourceEmit, NeedExecution.haltedOutcome_erase]

def sourceChild (parent : NativeMachine) (body : Atom) (environment : Environment) : NativeMachine :=
  { parent with world := parent.world.fork 0, control := .run (.evaluate body environment) [] }

def coreChild (parent : Core) (body : Atom) (environment : Environment) : Core :=
  { parent with world := parent.world.fork 0, control := .run (.evaluate body environment) [] }

def sourceReturn (parent : NativeMachine) (outcome : Outcome) : NativeMachine :=
  match parent.control with
  | .run _ stack => NeedReference.finished parent parent.world (.returned outcome stack) 0 0 0 0
  | _ => parent

def coreReturn (parent : Core) (outcome : Outcome) : Core :=
  match parent.control with
  | .run _ stack =>
      { parent with control := .returned outcome stack, work := parent.work.bump 0 0 0 0 }
  | _ => parent

theorem child_erases (parent : NativeMachine) (body : Atom) (environment : Environment) :
    NeedExecution.eraseMachine (sourceChild parent body environment) =
      coreChild (NeedExecution.eraseMachine parent) body environment := rfl

theorem return_erases (parent : NativeMachine) (outcome : Outcome) :
    NeedExecution.eraseMachine (sourceReturn parent outcome) =
      coreReturn (NeedExecution.eraseMachine parent) outcome := by
  rcases parent with ⟨world, control, work⟩
  cases control <;> rfl

/-- Independent source turn. A private observation takes one source item from
its FIFO frontier, retains all its children, and records only completed values.
Retryable failure remains a failure return instead of a shortage certificate. -/
def sourceStep (program : Program) : SourceWork → List SourceWork
  | .native machine archived =>
      match delimiter machine.control with
      | some (requested, body, environment) =>
          [.scope machine requested [.native (sourceChild machine body environment) []] [] archived]
      | none => (NeedReference.step (specification program) machine).map
          (fun next => .native next archived)
  | current@(.scope parent requested children values archived) =>
      match children with
      | [] => [.native (sourceReturn parent (.value (observation requested values true)))
          (current :: archived)]
      | first :: rest =>
          if requested ≤ values.length then
            [.native (sourceReturn parent (.value (observation requested values false)))
              (current :: archived)]
          else
            let pending := rest ++ sourceStep program first
            match sourceEmit first with
            | some (.value value) => [.scope parent requested pending (values ++ [value]) archived]
            | some faultOutcome => [.native (sourceReturn parent faultOutcome) (current :: archived)]
            | none => [.scope parent requested pending values archived]

/-- Target turn uses the receipt-erased native executor. It has its own
transition definition, not a target reduction defined as a source image. -/
def coreStep (program : Program) : CoreWork → List CoreWork
  | .native machine archived =>
      match delimiter machine.control with
      | some (requested, body, environment) =>
          [.scope machine requested [.native (coreChild machine body environment) []] [] archived]
      | none => (NeedExecution.step (specification program) machine).map
          (fun next => .native next archived)
  | current@(.scope parent requested children values archived) =>
      match children with
      | [] => [.native (coreReturn parent (.value (observation requested values true)))
          (current :: archived)]
      | first :: rest =>
          if requested ≤ values.length then
            [.native (coreReturn parent (.value (observation requested values false)))
              (current :: archived)]
          else
            let pending := rest ++ coreStep program first
            match coreEmit first with
            | some (.value value) => [.scope parent requested pending (values ++ [value]) archived]
            | some faultOutcome => [.native (coreReturn parent faultOutcome) (current :: archived)]
            | none => [.scope parent requested pending values archived]

/-- Whole-list equality preserves physical child occurrences, captured return
obligations, private frontiers and archived residuals in both directions. -/
theorem step_erases (program : Program) (work : SourceWork) :
    (sourceStep program work).map erase = coreStep program (erase work) := by
  cases work with
  | native machine archived =>
      simp only [sourceStep, erase, coreStep,
        show (NeedExecution.eraseMachine machine).control = machine.control from rfl]
      cases found : delimiter machine.control with
      | none =>
          simp only [List.map_map, Function.comp_def, erase]
          rw [← NativeEquationNeed.native_step_erases program machine, List.map_map]
          rfl
      | some description =>
          rcases description with ⟨requested, body, environment⟩
          simp [erase, child_erases]
  | scope parent requested children values archived =>
      cases children with
      | nil => simp [sourceStep, erase, coreStep, return_erases]
      | cons first rest =>
          unfold sourceStep coreStep
          simp only [erase, List.map_cons]
          split
          next complete => simp [erase, return_erases]
          next unfinished =>
            have firstIH := step_erases program first
            rw [← emit_erases first]
            cases emitted : coreEmit (erase first) with
            | none => simp [erase, List.map_append, firstIH]
            | some outcome =>
                cases outcome <;> simp [erase, List.map_append, firstIH, return_erases]

def sourceSystem (program : Program) : BranchingSystem SourceWork Outcome :=
  ⟨sourceEmit, sourceStep program⟩

def coreSystem (program : Program) : BranchingSystem CoreWork Outcome :=
  ⟨coreEmit, coreStep program⟩

theorem step_no_invention (program : Program) (source : SourceWork) (target : CoreWork)
    (member : target ∈ coreStep program (erase source)) :
    ∃ next ∈ sourceStep program source, erase next = target := by
  rw [← step_erases] at member
  exact List.mem_map.mp member

theorem generated_lifts (program : Program) (roots : List SourceWork)
    (target : CoreWork) (generated : Generated (coreSystem program) (roots.map erase) target) :
    ∃ source, Generated (sourceSystem program) roots source ∧ erase source = target := by
  induction generated with
  | root member =>
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ⟨source, .root sourceMember, rfl⟩
  | @successor parent child _ member ih =>
      obtain ⟨source, allowed, rfl⟩ := ih
      obtain ⟨next, sourceMember, same⟩ := step_no_invention program source child member
      exact ⟨next, .successor allowed sourceMember, same⟩

/-- Revising an archived private observation retains its prefix, pending
children and original parent return. It does not rebuild the original body. -/
def sourceDemand (requested : Nat) : SourceWork → Option SourceWork
  | .scope parent _ children values archived =>
      some (.scope parent requested children values archived)
  | .native _ _ => none

def coreDemand (requested : Nat) : CoreWork → Option CoreWork
  | .scope parent _ children values archived =>
      some (.scope parent requested children values archived)
  | .native _ _ => none

theorem revised_demand_erases (requested : Nat) (work : SourceWork) :
    (sourceDemand requested work).map erase = coreDemand requested (erase work) := by
  cases work <;> simp [sourceDemand, coreDemand, erase]

/-- Splitting resumed work retains the whole private state, not only the
answers already delivered. The independent source and target continue from
their current frontiers. -/
theorem source_scope_resume_exact (program : Program) (first second : Nat)
    (state : Mettapedia.GSLT.Core.InferenceControl.Snapshot SourceWork Outcome Unit) :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.run (sourceSystem program)
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
      (first + second) state =
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.run (sourceSystem program)
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst) second
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run (sourceSystem program)
        (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
        first state) := Mettapedia.GSLT.Core.InferenceControl.Snapshot.run_add _ _ _ _ _

namespace Controls

open NativeEquationNeed.Controls

def program : Program := NativeEquationNeed.Controls.program ++
  [⟨"nested", [], call "select" [integer 3, call "integers" [integer 0]]⟩]

def execute (term : Atom) (requested allowance : Nat) :=
  Mettapedia.GSLT.Core.DemandExecution.run (coreSystem program)
    (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast requested) allowance
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
      [.native (NeedExecution.eraseMachine (initial term)) []])

def observed (term : Atom) (requested allowance : Nat) : List Outcome :=
  (execute term requested allowance).search.events.map Emission.value

set_option maxRecDepth 20000 in
example : observed (call "nested") 1 3000 =
    [.value (observation 3 [integer 0, integer 1, integer 2] false)] := by decide +kernel

/- Zero demand does not force the private body, and completion of the scope
does not fabricate a closure certificate for that untouched computation. -/
set_option maxRecDepth 20000 in
example : observed (call "select" [integer 0, call "integers" [integer 0]]) 1 100 =
    [.value (observation 0 [] false)] := by decide +kernel

example : delimiter (.run (.arguments (.constructor "select") []
    [integer (-1), call "integers" [integer 0]] []) []) = none := rfl

def firstScopeRun :=
  Mettapedia.GSLT.Core.DemandExecution.run (sourceSystem program)
    (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast 1) 3000
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst)
      [.native (initial (call "nested")) []])

/-- This is an archive taken from an actual completed source scope, including
its captured caller and still-live recursive stream. -/
def retainedScope : Option SourceWork := do
  let event ← firstScopeRun.search.events.head?
  match event.origin with
  | .native _ (archived :: _) => some archived
  | _ => none

set_option maxRecDepth 20000 in
example :
    let revised := (retainedScope.bind (sourceDemand 5)).toList
    let resumed := Mettapedia.GSLT.Core.InferenceControl.Snapshot.run (sourceSystem program)
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst) 3000
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
        (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed Scheduler.breadthFirst) revised)
    resumed.search.events.map Emission.value =
      [.value (observation 5 [integer 0, integer 1, integer 2, integer 3, integer 4] false)] :=
  by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeObservationScopes
