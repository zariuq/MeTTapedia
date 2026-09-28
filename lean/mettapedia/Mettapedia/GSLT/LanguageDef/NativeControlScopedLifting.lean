import Mettapedia.GSLT.LanguageDef.NativeControlOnce

/-!
# Scope-transparent entry into local code

A local code table names controls of an existing `CProgram`.  Entering an
outlined control pushes its continuation frame in the current activation's
scope.  It does not begin another activation.  Consequently a cut in that code
has exactly the scope it had before outlining, including when pending work is
represented by host nodes.

`local_then_run` proves exact full-state equality after one administrative entry
step and an arbitrary finite source run.  Base instructions are embedded step
for step, so this result applies to programs already extended with host goals or
local `once` delimiters.  It neither constructs a free-variable capture layout
nor proves source-language elaboration or a C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlScopedLifting

open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.LanguageDef.HostGoals.Scopes
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

inductive Control (K F : Type) (n : Nat) where
  | base (control : K)
  | local (address : Fin n) (frame : F)
  deriving DecidableEq

inductive Call (BaseCall : Type) (n : Nat) where
  | base (call : BaseCall)
  | local (address : Fin n)
  deriving DecidableEq

variable {C K BaseCall F A : Type} {n : Nat}

def liftInstruction : CInstruction BaseCall F A K →
    CInstruction (Call BaseCall n) F A (Control K F n)
  | .ret a => .ret a
  | .fail => .fail
  | .call c f => .call (.base c) f
  | .tail c => .tail (.base c)
  | .enter c f => .enter (.base c) f
  | .cut k => .cut (.base k)

/-- Local entry uses `enter`: the already captured activation and its cut scope
are retained.  Base calls keep their original activation behavior. -/
def program (P : CProgram C K BaseCall F A) (table : Fin n → K) :
    CProgram C (Control K F n) (Call BaseCall n) F A where
  inspect
    | .base k => liftInstruction (P.inspect k)
    | .local address frame => .enter (.local address) frame
  branches context
    | .base call => (P.branches context call).map fun next => (next.1, .base next.2)
    | .local address => [(context, .base (table address))]
  resume context frame answer :=
    ((P.resume context frame answer).1, .base (P.resume context frame answer).2)

def embedTask (t : CTask C K F) : CTask C (Control K F n) F :=
  ⟨t.context, .base t.control, t.returns, t.scope⟩

def embedState (s : CState C K F A) : CState C (Control K F n) F A :=
  ⟨s.frontier.map embedTask, s.emitted⟩

/-- Embedding changes neither the number nor the order of alternatives beneath
a cut scope. -/
theorem keepBelow_map (scope : Option Nat) (tasks : List (CTask C K F)) :
    keepBelow scope (tasks.map (embedTask (n := n))) =
      (keepBelow scope tasks).map embedTask := by
  cases scope with
  | none => rfl
  | some scope => simp [keepBelow, List.map_drop]

/-- Exact correspondence includes return scopes and the pending frontier, not
just the values emitted by a base instruction. -/
theorem expand_embed (P : CProgram C K BaseCall F A) (table : Fin n → K)
    (t : CTask C K F) (rest : List (CTask C K F)) :
    cexpand (program P table) (embedTask t) (rest.map embedTask) =
      ((cexpand P t rest).1.map embedTask, (cexpand P t rest).2) := by
  cases instruction : P.inspect t.control with
  | ret value =>
      cases frames : t.returns with
      | nil => simp [cexpand, program, embedTask, liftInstruction, instruction, frames]
      | cons frame frames =>
          rcases frame with ⟨frame, scope⟩
          simp [cexpand, program, embedTask, liftInstruction, *]
  | fail => simp [cexpand, program, embedTask, liftInstruction, instruction]
  | call callee frame =>
      simp [cexpand, program, embedTask, liftInstruction, instruction, List.map_map,
        Function.comp_def]
  | tail callee =>
      simp [cexpand, program, embedTask, liftInstruction, instruction, List.map_map,
        Function.comp_def]
  | enter callee frame =>
      simp [cexpand, program, embedTask, liftInstruction, instruction, List.map_map,
        Function.comp_def]
  | cut next =>
      simp only [cexpand, program, embedTask, instruction, liftInstruction, keepBelow_map,
        List.map_cons]

/-- Every step from an embedded source state is exactly the embedded source
step.  This equality supplies both preservation and no-invention. -/
theorem step_embed (P : CProgram C K BaseCall F A) (table : Fin n → K)
    (s : CState C K F A) :
    cstep (program P table) (embedState s) = embedState (cstep P s) := by
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons t rest =>
      simp only [embedState, List.map_cons, cstep_cons, expand_embed]

/-- Finite runs from embedded states preserve all contexts, continuations,
scopes, alternatives and answer occurrences exactly. -/
theorem run_embed (P : CProgram C K BaseCall F A) (table : Fin n → K) :
    ∀ (fuel : Nat) (s : CState C K F A),
      repeats (cstep (program P table)) fuel (embedState s) =
        embedState (repeats (cstep P) fuel s)
  | 0, _ => rfl
  | fuel + 1, s => by
      simp only [repeats, step_embed]
      exact run_embed P table fuel (cstep P s)

/-- One administrative step enters local code in the existing activation.
Even the stored scope in the pushed return frame is unchanged. -/
theorem local_entry (P : CProgram C K BaseCall F A) (table : Fin n → K)
    (context : C) (address : Fin n) (frame : F) (returns : List (F × Option Nat))
    (scope : Option Nat) (rest : List (CTask C (Control K F n) F))
    (emitted : List (C × A)) :
    cstep (program P table)
      ⟨⟨context, .local address frame, returns, scope⟩ :: rest, emitted⟩ =
      ⟨⟨context, .base (table address), (frame, scope) :: returns, scope⟩ :: rest, emitted⟩ := by
  simp [cstep, cexpand, program]

/-- Transparent outlining costs exactly one local entry step.  After it, any
finite run is the exact embedded source run, including all cut and host state. -/
theorem local_then_run (P : CProgram C K BaseCall F A) (table : Fin n → K)
    (context : C) (address : Fin n) (frame : F) (returns : List (F × Option Nat))
    (scope : Option Nat) (rest : List (CTask C K F)) (emitted : List (C × A)) (fuel : Nat) :
    repeats (cstep (program P table)) (fuel + 1)
      ⟨⟨context, .local address frame, returns, scope⟩ :: rest.map embedTask, emitted⟩ =
      embedState (repeats (cstep P) fuel
        ⟨⟨context, table address, (frame, scope) :: returns, scope⟩ :: rest, emitted⟩) := by
  simp only [repeats, local_entry]
  simpa only [embedState, embedTask, List.map_cons] using
    run_embed P table fuel
      ⟨⟨context, table address, (frame, scope) :: returns, scope⟩ :: rest, emitted⟩

namespace Controls

inductive Code where
  | give (value : Nat)
  | cut (value : Nat)
  deriving DecidableEq

def base : CProgram Nat Code Unit Unit Nat where
  inspect
    | .give n => .ret n
    | .cut n => .cut (.give n)
  branches context _ := [(context, .give 11)]
  resume context _ answer := (context, .give answer)

def cutTable : Fin 1 → Code := fun _ => .cut 0

def sourceAlternative : CTask Nat Code Unit := ⟨8, .give 9, [], some 1⟩
def sourceOutside : CTask Nat Code Unit := ⟨100, .give 99, [], none⟩

def cutInitial : CState Nat (Control Code Unit 1) Unit Nat :=
  ⟨[⟨7, .local 0 (), [], some 1⟩, embedTask sourceAlternative, embedTask sourceOutside], []⟩

/-- The outlined body cuts the same enclosing alternative as the source code,
then returns through its added local continuation. -/
theorem transparent_cut :
    repeats (cstep (program base cutTable)) 5 cutInitial =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

/-- The tempting replacement starts a new activation at local entry. -/
def opaqueCall (P : CProgram C K BaseCall F A) (table : Fin n → K) :
    CProgram C (Control K F n) (Call BaseCall n) F A :=
  { program P table with inspect := fun control => match control with
      | .base k => liftInstruction (P.inspect k)
      | .local address frame => .call (.local address) frame }

/-- With `call`, the body's cut stops above the enclosing alternative, which
therefore emits an extra answer. -/
theorem fresh_call_scope_is_wrong :
    repeats (cstep (opaqueCall base cutTable)) 6 cutInitial =
      ⟨[], [(7, 0), (8, 9), (100, 99)]⟩ := by rfl

/-- Tail entry also starts a fresh activation and additionally omits the local
continuation.  It cannot implement transparent local outlining. -/
def opaqueTail (P : CProgram C K BaseCall F A) (table : Fin n → K) :
    CProgram C (Control K F n) (Call BaseCall n) F A :=
  { program P table with inspect := fun control => match control with
      | .base k => liftInstruction (P.inspect k)
      | .local address _ => .tail (.local address) }

theorem fresh_tail_scope_is_wrong :
    repeats (cstep (opaqueTail base cutTable)) 5 cutInitial =
      ⟨[], [(7, 0), (8, 9), (100, 99)]⟩ := by rfl

def host : Host (Nat × Unit) Nat (Nat × Nat) where
  start _ := 0
  pull n := .yield (n + 7, n) (n + 1)

def hosted := withHostCut base (fun _ => true) host

def hostCutTable : Fin 1 → Node Code Nat Nat := fun _ => .run (.cut 0)

def pendingHost : CTask Nat (Node Code Nat Nat) Unit :=
  ⟨0, .host 1, [], some 1⟩
def hostedAlternative : CTask Nat (Node Code Nat Nat) Unit :=
  ⟨8, .run (.give 9), [], some 1⟩
def hostedOutside : CTask Nat (Node Code Nat Nat) Unit :=
  ⟨100, .run (.give 99), [], none⟩

/-- Transparent outlining still cuts the residual host node and native
alternative together, while retaining the outer frontier. -/
theorem transparent_cut_through_host :
    repeats (cstep (program hosted hostCutTable)) 5
      ⟨[⟨7, .local 0 (), [], some 1⟩, embedTask pendingHost,
        embedTask hostedAlternative, embedTask hostedOutside], []⟩ =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

def onceHosted := NativeControlOnce.program hosted

def onceTable : Fin 1 → NativeControlOnce.Control (Node Code Nat Nat) Nat :=
  fun _ => .run (.answer 0)

def oncePendingHost :
    CTask Nat (NativeControlOnce.Control (Node Code Nat Nat) Nat) (NativeControlOnce.Frame Unit) :=
  ⟨0, .run (.host 1), [(.first, some 1)], some 1⟩

def onceAlternative :
    CTask Nat (NativeControlOnce.Control (Node Code Nat Nat) Nat) (NativeControlOnce.Frame Unit) :=
  ⟨8, .run (.run (.give 9)), [], some 1⟩

def onceOutside :
    CTask Nat (NativeControlOnce.Control (Node Code Nat Nat) Nat) (NativeControlOnce.Frame Unit) :=
  ⟨100, .run (.run (.give 99)), [], none⟩

/-- The same local-table construction composes with the proved `once` adapter
over a host-extended program.  Its local first-answer frame commits at the
original delimiter and removes pending work in both representations. -/
theorem transparent_once_through_host :
    repeats (cstep (program onceHosted onceTable)) 5
      ⟨[⟨7, .local 0 .first, [], some 1⟩, embedTask oncePendingHost,
        embedTask onceAlternative, embedTask onceOutside], []⟩ =
      ⟨[], [(7, 0), (100, 99)]⟩ := by rfl

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlScopedLifting
