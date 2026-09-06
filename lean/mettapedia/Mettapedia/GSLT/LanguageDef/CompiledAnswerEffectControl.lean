import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.ObservationDemandControl
import Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

/-!
# Scheduler-neutral control for compiled answer effects

`CompiledAnswerEffectProgram` separates deterministic islands from answer
control.  This module connects that program to the existing
occurrence-preserving control interface rather than giving the compiled
machine its own traversal policy.

Each live occurrence is a residual program.  A `pure` occurrence emits once,
`zero` disappears, `choice` exposes two successor occurrences, and `perform`
advances through one deterministic operation.  The controller may choose any
occurrence-preserving schedule.  Completed runs agree at occurrence-bag level;
ordered streams remain a finer, explicitly controller-dependent observation.

The physical adapter is partial.  Declining a deterministic operation returns
`none` to the enclosing evaluator; it never turns the residual program into
semantic zero.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectControl

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectProgram

universe u

/-- The semantic expansion of one residual answer-effect program. -/
def system {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    BranchingSystem (Program Op Answer) Answer where
  emit
    | .pure answer => some answer
    | .zero | .choice _ _ | .perform _ _ => none
  successors
    | .pure _ | .zero => []
    | .choice left right => [left, right]
    | .perform operation next => [next (semantics operation)]

@[simp] theorem system_emit_pure {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    (answer : Answer) :
    (system semantics).emit (.pure answer) = some answer :=
  rfl

@[simp] theorem system_emit_zero {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    (system semantics).emit (.zero : Program Op Answer) = none :=
  rfl

@[simp] theorem system_successors_choice {Op : Type → Type}
    {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    (left right : Program Op Answer) :
    (system semantics).successors (.choice left right) = [left, right] :=
  rfl

@[simp] theorem system_successors_perform {Op : Type → Type}
    {Answer : Type u} {Response : Type}
    (semantics : {Result : Type} → Op Result → Result)
    (operation : Op Response) (next : Response → Program Op Answer) :
    (system semantics).successors (.perform operation next) =
      [next (semantics operation)] :=
  rfl

/-- The finite number of residual occurrences authorized by a program after
deterministic operations have been interpreted. -/
def rank {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    Program Op Answer → Nat
  | .pure _ | .zero => 1
  | .choice left right => 1 + rank semantics left + rank semantics right
  | .perform operation next => 1 + rank semantics (next (semantics operation))

/-- Every answer-effect program is a finite branching process.  One control
step consumes exactly the selected occurrence and exposes its residual work. -/
def descentCertificate {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    DescentCertificate (system (Answer := Answer) semantics) where
  rank := rank semantics
  unfold := by
    intro program
    cases program <;> simp [rank, system, foldRanks, Nat.add_assoc]

/-- The occurrence-bag denotation of a residual program is an additive
invariant of one control expansion. -/
def additiveDenotation {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    AdditiveDenotation (system (Answer := Answer) semantics) where
  value program := Program.denote bagEffect semantics program
  unfold := by
    intro program
    cases program <;>
      simp [system, Program.denote, optionBag, foldValues, bagEffect]

/-- Any occurrence-preserving controller completes a finite compiled program
within its structural rank.  This is a termination fact about the answer
program, not a fairness assumption about arbitrary cyclic search. -/
theorem controller_completes_at_rank {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    {Memory : Type*}
    (controller : Controller (Program Op Answer) Answer Memory)
    (program : Program Op Answer) :
    (Snapshot.run (system semantics) controller (rank semantics program)
      (Snapshot.initial controller [program])).search.frontier = [] := by
  have completed :=
    Snapshot.run_completes_at_rank (system semantics) controller
      (descentCertificate semantics) (Snapshot.initial controller [program])
  simpa [descentCertificate, Snapshot.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.initial, foldRanks] using completed

/-- At completion, every controller realizes exactly the compiled program's
occurrence bag.  DFS, FIFO, adaptive, portfolio, and later parallel policies
are therefore realizations of one observation, not separate semantics. -/
theorem controller_exact_bag {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    {Memory : Type*}
    (controller : Controller (Program Op Answer) Answer Memory)
    (program : Program Op Answer) :
    eventBag
        (Snapshot.run (system semantics) controller (rank semantics program)
          (Snapshot.initial controller [program])).search.events =
      Program.denote bagEffect semantics program := by
  have observed := Snapshot.completed_run_denotation
    (system semantics) controller (additiveDenotation semantics)
      [program] (rank semantics program)
      (controller_completes_at_rank semantics controller program)
  simpa [additiveDenotation, foldValues] using observed

/-- Two completed control strategies may expose different streams but cannot
change the exact occurrence bag of a compiled finite program. -/
theorem controllers_exact_bag {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    {FirstMemory SecondMemory : Type*}
    (first : Controller (Program Op Answer) Answer FirstMemory)
    (second : Controller (Program Op Answer) Answer SecondMemory)
    (program : Program Op Answer) :
    eventBag
        (Snapshot.run (system semantics) first (rank semantics program)
          (Snapshot.initial first [program])).search.events =
      eventBag
        (Snapshot.run (system semantics) second (rank semantics program)
          (Snapshot.initial second [program])).search.events := by
  rw [controller_exact_bag semantics first program,
    controller_exact_bag semantics second program]

/-- Controller execution of compiled source is both preserving and
reflecting at the occurrence-bag observation.  This composes source
compilation adequacy with the frontier accounting law. -/
theorem compiled_source_controller_exact_bag
    {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    {Memory : Type*}
    (controller : Controller (Program Op Answer) Answer Memory)
    (source : Source Op Answer) :
    eventBag
        (Snapshot.run (system semantics) controller
          (rank semantics (Source.compile source))
          (Snapshot.initial controller [Source.compile source])).search.events =
      Source.denote bagEffect semantics source := by
  calc
    _ = Program.denote bagEffect semantics (Source.compile source) :=
      controller_exact_bag semantics controller (Source.compile source)
    _ = Source.denote bagEffect semantics source :=
      Source.compile_adequate bagEffect semantics source

/-! ## Observation-indexed activation -/

/-- Conservative branching classification after deterministic operations have
been interpreted.  A syntactic choice remains general even when a later
observer might contract its answers. -/
def hasChoice {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response) :
    Program Op Answer → Bool
  | .pure _ | .zero => false
  | .choice _ _ => true
  | .perform operation next => hasChoice semantics (next (semantics operation))

def branchAuthority {Op : Type → Type} {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    (program : Program Op Answer) : BranchAuthority :=
  if hasChoice semantics program then .general else .singlePath

/-- Observation demand determines readout and permissible activation through
the shared dispatcher.  The compiled program contributes only its branching
fact; it does not choose a traversal policy. -/
def controlPlan {Op : Type → Type} {Answer : Type u} {Guard : Type*}
    (semantics : {Response : Type} → Op Response → Response)
    (demand : ObservationDemand Guard) (batch : BatchAuthority)
    (program : Program Op Answer) : Plan :=
  dispatch demand (branchAuthority semantics program) batch

@[simp] theorem branchAuthority_choice {Op : Type → Type}
    {Answer : Type u}
    (semantics : {Response : Type} → Op Response → Response)
    (left right : Program Op Answer) :
    branchAuthority semantics (.choice left right) = .general :=
  rfl

/-- First-answer demand limits observation but does not authorize choosing one
branch in advance. -/
theorem first_choice_remains_controlled {Op : Type → Type}
    {Answer : Type u} {Guard : Type*}
    (semantics : {Response : Type} → Op Response → Response)
    (guard : Option Guard) (left right : Program Op Answer) :
    controlPlan semantics
        ({ completion := .first, guard := guard } : ObservationDemand Guard)
        .singletonOnly (.choice left right) =
      { readout := .first, activation := .controlled } :=
  rfl

/-- A complete bag and a separate serializability certificate permit bulk
activation without selecting a scheduler. -/
theorem complete_bag_choice_may_bulk {Op : Type → Type}
    {Answer : Type u} {Guard : Type*}
    (semantics : {Response : Type} → Op Response → Response)
    (guard : Option Guard) (left right : Program Op Answer) :
    controlPlan semantics
        ({ completion := .completeBag, guard := guard } :
          ObservationDemand Guard)
        .serializable (.choice left right) =
      { readout := .completeBag, activation := .bulk } :=
  rfl

/-- Ordered-stream observation keeps a genuine choice under controlled
activation even when its effects are otherwise serializable. -/
theorem ordered_choice_remains_controlled {Op : Type → Type}
    {Answer : Type u} {Guard : Type*}
    (semantics : {Response : Type} → Op Response → Response)
    (guard : Option Guard) (left right : Program Op Answer) :
    controlPlan semantics
        ({ completion := .orderedStream, guard := guard } :
          ObservationDemand Guard)
        .serializable (.choice left right) =
      { readout := .orderedStream, activation := .controlled } :=
  rfl

/-! ## Partial physical expansion -/

/-- The observation made by one admitted physical expansion. -/
structure Expansion (Node Answer : Type*) where
  emit : Option Answer
  successors : List Node

/-- A physical provider may advance one deterministic operation or decline
the optimized route.  Answer control itself is always available. -/
def expand? {Op : Type → Type}
    {semantics : {Response : Type} → Op Response → Response}
    (realizer : Realizer Op semantics) {Answer : Type u} :
    Program Op Answer → Option (Expansion (Program Op Answer) Answer)
  | .pure answer => some ⟨some answer, []⟩
  | .zero => some ⟨none, []⟩
  | .choice left right => some ⟨none, [left, right]⟩
  | .perform operation next =>
      match realizer.run? operation with
      | none => none
      | some response => some ⟨none, [next response]⟩

/-- Every admitted physical expansion is exactly the semantic expansion.  It
neither invents an answer nor changes the residual occurrences. -/
theorem expand?_sound {Op : Type → Type}
    {semantics : {Response : Type} → Op Response → Response}
    (realizer : Realizer Op semantics) {Answer : Type u}
    (program : Program Op Answer)
    (expansion : Expansion (Program Op Answer) Answer)
    (executed : expand? realizer program = some expansion) :
    expansion.emit = (system semantics).emit program ∧
      expansion.successors = (system semantics).successors program := by
  cases program with
  | pure answer =>
      simp [expand?] at executed
      subst expansion
      simp [system]
  | zero =>
      simp [expand?] at executed
      subst expansion
      simp [system]
  | choice left right =>
      simp [expand?] at executed
      subst expansion
      simp [system]
  | @perform Response operation next =>
      simp only [expand?] at executed
      cases result : realizer.run? operation with
      | none => simp [result] at executed
      | some response =>
          simp [result] at executed
          subst expansion
          have exactResponse := realizer.sound operation response result
          subst response
          simp [system]

/-! ## Executable observation boundaries -/

def twoAnswers : Program Probe Bool :=
  .choice (.pure false) (.pure true)

def duplicateAnswers : Program Probe Nat :=
  .choice (.pure 7) (.pure 7)

/-- A breadth-first controller retains source choice order in this finite
example. -/
theorem breadthFirst_twoAnswers_stream :
    (Snapshot.run (system probeSemantics)
      (Controller.fixed Scheduler.breadthFirst) 3
      (Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
        [twoAnswers])).search.events.map Emission.value = [false, true] := by
  rfl

/-- A different occurrence-preserving controller exposes a different stream. -/
theorem reverse_twoAnswers_stream :
    (Snapshot.run (system probeSemantics)
      (Controller.fixed Scheduler.reverseBreadthFirst) 3
      (Snapshot.initial (Controller.fixed Scheduler.reverseBreadthFirst)
        [twoAnswers])).search.events.map Emission.value = [true, false] := by
  rfl

/-- Stream order is controller-visible while the completed occurrence bag is
controller-invariant. -/
theorem streams_differ_bags_agree :
    (Snapshot.run (system probeSemantics)
      (Controller.fixed Scheduler.breadthFirst) 3
      (Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
        [twoAnswers])).search.events.map Emission.value ≠
      (Snapshot.run (system probeSemantics)
        (Controller.fixed Scheduler.reverseBreadthFirst) 3
        (Snapshot.initial (Controller.fixed Scheduler.reverseBreadthFirst)
          [twoAnswers])).search.events.map Emission.value ∧
    eventBag
        (Snapshot.run (system probeSemantics)
          (Controller.fixed Scheduler.breadthFirst) 3
          (Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
            [twoAnswers])).search.events =
      eventBag
        (Snapshot.run (system probeSemantics)
          (Controller.fixed Scheduler.reverseBreadthFirst) 3
          (Snapshot.initial (Controller.fixed Scheduler.reverseBreadthFirst)
            [twoAnswers])).search.events := by
  constructor
  · rw [breadthFirst_twoAnswers_stream, reverse_twoAnswers_stream]
    decide
  · exact controllers_exact_bag probeSemantics
      (Controller.fixed Scheduler.breadthFirst)
      (Controller.fixed Scheduler.reverseBreadthFirst) twoAnswers

/-- Equal answer values from distinct choice occurrences retain multiplicity. -/
theorem duplicate_occurrences_remain_two :
    Program.denote bagEffect probeSemantics duplicateAnswers =
      ({7, 7} : Multiset Nat) := by
  rfl

/-- Negative physical boundary: an unavailable deterministic operation
declines.  It is not admitted as an expansion with no answers. -/
theorem unavailable_expansion_declines :
    expand? partialProbeRealizer
        (Program.perform Probe.unavailable fun _ => Program.pure (9 : Nat)) =
      none ∧
    Program.denote bagEffect probeSemantics
        (Program.perform Probe.unavailable fun _ => Program.pure (9 : Nat)) =
      ({9} : Multiset Nat) := by
  constructor <;> rfl

#print axioms descentCertificate
#print axioms controller_completes_at_rank
#print axioms controller_exact_bag
#print axioms controllers_exact_bag
#print axioms compiled_source_controller_exact_bag
#print axioms first_choice_remains_controlled
#print axioms complete_bag_choice_may_bulk
#print axioms ordered_choice_remains_controlled
#print axioms expand?_sound
#print axioms streams_differ_bags_agree
#print axioms duplicate_occurrences_remain_two
#print axioms unavailable_expansion_declines

end Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectControl
