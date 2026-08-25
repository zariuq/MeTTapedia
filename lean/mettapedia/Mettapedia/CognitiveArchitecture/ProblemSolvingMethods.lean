import Mathlib.Logic.Embedding.Basic

/-!
# Proof-relevant problem-solving-method registries

This file isolates a reusable architecture-neutral notion of a registry of
problem-solving methods (PSMs).  A registry carries two kinds of evidence:

* evidence that a method is admitted; and
* evidence that the method realizes a particular problem/solution pair.

Both are `Type`-valued.  A registry extension therefore embeds old receipts
instead of retaining only their propositional support.  This is the weakest
interface that distinguishes invention from retention without imposing a
particular program language, scheduler, authorization policy, or target
architecture.

Özkural's Omega architecture uses an open-ended PSM library in this sense, but
the definition below is not Omega-specific.  In particular, a tool
authorization broker is not a PSM registry merely because both mention named
capabilities; a bridge must provide the evidence-preserving maps below.
-/

namespace Mettapedia.CognitiveArchitecture.ProblemSolvingMethods

universe uProblem uSolution uMethod uAdmission uRealization

/-- A proof-relevant registry of problem-solving methods. -/
structure Registry
    (Problem : Type uProblem) (Solution : Type uSolution) (Method : Type uMethod) where
  /-- Evidence that a method is currently admitted. -/
  Admission : Method → Type uAdmission
  /-- Evidence that a method realizes a problem/solution pair. -/
  Realization : Method → Problem → Solution → Type uRealization
  /-- Executed methods must be admitted by the same registry. -/
  realizationAdmission : ∀ {method problem solution},
    Realization method problem solution → Admission method

/-- An extension retains old admission and realization receipts injectively.

The embeddings forbid an extension from silently deduplicating distinct old
receipts.  It may still add new methods or new realizations. -/
structure Extension
    {Problem : Type uProblem} {Solution : Type uSolution} {Method : Type uMethod}
    (before after : Registry Problem Solution Method) where
  admission : ∀ method, before.Admission method ↪ after.Admission method
  realization : ∀ method problem solution,
    before.Realization method problem solution ↪ after.Realization method problem solution

namespace Extension

/-- Every registry extends itself without changing receipts. -/
def refl (registry : Registry Problem Solution Method) : Extension registry registry where
  admission _ := Function.Embedding.refl _
  realization _ _ _ := Function.Embedding.refl _

/-- Evidence-retaining registry extension is transitive. -/
def trans {first second third : Registry Problem Solution Method}
    (left : Extension first second) (right : Extension second third) :
    Extension first third where
  admission method := (left.admission method).trans (right.admission method)
  realization method problem solution :=
    (left.realization method problem solution).trans
      (right.realization method problem solution)

end Extension

/-- A receipt that a method was genuinely invented and retained.

The method had no admission receipt before, has one afterward, and all earlier
registry evidence survives through an extension. -/
structure InventionReceipt
    {Problem : Type uProblem} {Solution : Type uSolution} {Method : Type uMethod}
    (before after : Registry Problem Solution Method) (method : Method) where
  extension : Extension before after
  absentBefore : IsEmpty (before.Admission method)
  admittedAfter : after.Admission method

/-- An already-admitted method cannot count as newly invented in the unchanged
registry. -/
theorem no_invention_without_new_admission
    {registry : Registry Problem Solution Method} {method : Method}
    (admitted : registry.Admission method) :
    IsEmpty (InventionReceipt registry registry method) :=
  ⟨fun receipt => receipt.absentBefore.false admitted⟩

/-! ## Multiple reference machines and retained experience -/

/-- A family of reference machines with machine-indexed program languages and
proof-relevant executions. -/
structure ReferenceMachineFamily
    (Machine : Type uMethod) (Input : Type uProblem) (Output : Type uSolution) where
  /-- Programs may have genuinely different types for different machines. -/
  Program : Machine → Type uAdmission
  /-- Execution receipts retain which machine and program produced an output. -/
  Run : ∀ machine, Program machine → Input → Output → Type uRealization

/-- One retained execution from a reference-machine family. -/
structure Experience
    {Machine : Type uMethod} {Input : Type uProblem} {Output : Type uSolution}
    (family : ReferenceMachineFamily Machine Input Output) where
  machine : Machine
  program : family.Program machine
  input : Input
  output : Output
  run : family.Run machine program input output

/-- Algorithmic memory over one or more reference machines.

`Transfer source target candidate` is deliberately relational: a memory may
retain several target programs, none, or evidence from several transfer
procedures. -/
structure MultiMachineMemory
    {Machine : Type uMethod} {Input : Type uProblem} {Output : Type uSolution}
    (family : ReferenceMachineFamily Machine Input Output) where
  Retained : Experience family → Type uAdmission
  Transfer : Experience family → ∀ target, family.Program target → Type uRealization

/-- The memory demonstrably contains experience from distinct reference
machines.  This is a property of a particular memory, not baked into the
general interface. -/
def UsesMultipleMachines
    {Machine : Type uMethod} {Input : Type uProblem} {Output : Type uSolution}
    {family : ReferenceMachineFamily Machine Input Output}
    (memory : MultiMachineMemory family) : Prop :=
  ∃ first second : Experience family,
    Nonempty (memory.Retained first) ∧
    Nonempty (memory.Retained second) ∧
    first.machine ≠ second.machine

/-! ## Positive and negative canaries -/

inductive ToyMethod where
  | inherited
  | invented
  deriving DecidableEq

private def beforeAdmission : ToyMethod → Type
  | .inherited => Unit
  | .invented => Empty

private def afterAdmission : ToyMethod → Type
  | .inherited => Unit
  | .invented => Unit

private def beforeRealization : ToyMethod → Unit → Bool → Type
  | .inherited, _, _ => Unit
  | .invented, _, _ => Empty

private def afterRealization (_ : ToyMethod) (_ : Unit) (_ : Bool) : Type := Unit

def beforeRegistry : Registry Unit Bool ToyMethod where
  Admission := beforeAdmission
  Realization := beforeRealization
  realizationAdmission := by
    intro method _problem _solution _receipt
    cases method
    · trivial
    · exact Empty.elim _receipt

def afterRegistry : Registry Unit Bool ToyMethod where
  Admission := afterAdmission
  Realization := afterRealization
  realizationAdmission := by
    intro method _problem _solution _receipt
    cases method <;> trivial

/-- The toy registry genuinely invents and retains one new method while
embedding every old receipt. -/
def inventedMethodReceipt :
    InventionReceipt beforeRegistry afterRegistry ToyMethod.invented where
  extension := {
    admission := fun method => by
      cases method
      · exact Function.Embedding.refl Unit
      · exact ⟨Empty.elim, fun value => Empty.elim value⟩
    realization := fun method _ _ => by
      cases method
      · exact Function.Embedding.refl Unit
      · exact ⟨Empty.elim, fun value => Empty.elim value⟩ }
  absentBefore := ⟨Empty.elim⟩
  admittedAfter := ()

/-- Negative control: the inherited method was already admitted. -/
theorem inheritedMethod_not_invented_in_place :
    IsEmpty (InventionReceipt beforeRegistry beforeRegistry ToyMethod.inherited) :=
  no_invention_without_new_admission ()

inductive ToyMachine where
  | first
  | second
  deriving DecidableEq

def toyMachineFamily : ReferenceMachineFamily ToyMachine Unit Bool where
  Program := fun _ => Unit
  Run := fun _ _ _ _ => Unit

def firstExperience : Experience toyMachineFamily where
  machine := .first
  program := ()
  input := ()
  output := false
  run := ()

def secondExperience : Experience toyMachineFamily where
  machine := .second
  program := ()
  input := ()
  output := true
  run := ()

def toyMultiMachineMemory : MultiMachineMemory toyMachineFamily where
  Retained := fun _ => Unit
  Transfer := fun _ _ _ => Unit

/-- Positive control: retained executions really come from distinct machines. -/
theorem toyMemory_usesMultipleMachines :
    UsesMultipleMachines toyMultiMachineMemory := by
  exact ⟨firstExperience, secondExperience, ⟨()⟩, ⟨()⟩, by decide⟩

def singletonMachineFamily : ReferenceMachineFamily Unit Unit Bool where
  Program := fun _ => Unit
  Run := fun _ _ _ _ => Unit

def singletonMachineMemory : MultiMachineMemory singletonMachineFamily where
  Retained := fun _ => Unit
  Transfer := fun _ _ _ => Unit

/-- Negative control: a family with only one reference machine cannot witness
HAM-style multiple-machine retention. -/
theorem singletonMemory_not_usesMultipleMachines :
    ¬ UsesMultipleMachines singletonMachineMemory := by
  rintro ⟨first, second, _, _, distinct⟩
  exact distinct (Subsingleton.elim first.machine second.machine)

#print axioms no_invention_without_new_admission
#print axioms toyMemory_usesMultipleMachines
#print axioms singletonMemory_not_usesMultipleMachines

end Mettapedia.CognitiveArchitecture.ProblemSolvingMethods
