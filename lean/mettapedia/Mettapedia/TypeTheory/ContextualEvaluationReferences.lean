import Mettapedia.TypeTheory.ContextualComputationKleisli

/-!
# Origin and evaluation references over contextual computations

Two independently selected space references are a reader environment over the
existing state/choice/intent program. Changing the evaluation reference is a
scoped environment operation, not a heap write or a transaction. The laws hold
before selecting a handler for effects. Concrete isolated-world executions
then distinguish origin from evaluation, restoration from rollback, and a
saved answer from a fresh read.

This is a candidate semantic component. It does not select the meaning of a
surface `&self`, make raw syntax a closure, or establish an object-language
typing/substitution bridge. An origin reference is supplied explicitly; code
storage location does not automatically determine it. No runtime allocation,
history retention, or per-operation environment copying follows from this
mathematical reader representation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualEvaluationReferences

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe u

structure References (Space : Type u) where
  origin : Space
  evaluation : Space
deriving DecidableEq

abbrev Computation (Space State Answer Intent : Type u) :=
  References Space → Program State Answer Intent

section General

variable {Space State Answer Other Last Intent : Type u}

def pure (answer : Answer) : Computation Space State Answer Intent :=
  fun _ => .pure answer

def bind (program : Computation Space State Answer Intent)
    (next : Answer → Computation Space State Other Intent) :
    Computation Space State Other Intent :=
  fun refs => (program refs).bind (fun answer => next answer refs)

theorem bind_pure (program : Computation Space State Answer Intent) :
    bind program pure = program := by
  funext refs
  exact ContextualComputationKleisli.Program.bind_pure (program refs)

theorem bind_assoc (program : Computation Space State Answer Intent)
    (next : Answer → Computation Space State Other Intent)
    (later : Other → Computation Space State Last Intent) :
    bind (bind program next) later =
      bind program (fun answer => bind (next answer) later) := by
  funext refs
  exact ContextualComputationKleisli.Program.bind_assoc (program refs)
    (fun answer => next answer refs) (fun answer => later answer refs)

def withReferences (change : References Space → References Space)
    (program : Computation Space State Answer Intent) :
    Computation Space State Answer Intent :=
  fun refs => program (change refs)

def atSpace (target : Space) (program : Computation Space State Answer Intent) :
    Computation Space State Answer Intent :=
  withReferences (fun refs => { refs with evaluation := target }) program

def fromOrigin (origin : Space) (program : Computation Space State Answer Intent) :
    Computation Space State Answer Intent :=
  withReferences (fun refs => { refs with origin := origin }) program

/-- Scope includes the continuation only when that continuation is inside it. -/
theorem local_bind (change : References Space → References Space)
    (program : Computation Space State Answer Intent)
    (next : Answer → Computation Space State Other Intent) :
    withReferences change (bind program next) =
      bind (withReferences change program) (fun answer => withReferences change (next answer)) := rfl

theorem local_comp (outer inner : References Space → References Space)
    (program : Computation Space State Answer Intent) :
    withReferences outer (withReferences inner program) =
      withReferences (inner ∘ outer) program := rfl

/-- An inner evaluation target takes precedence for its own body. -/
theorem atSpace_nested (outer inner : Space)
    (program : Computation Space State Answer Intent) :
    atSpace outer (atSpace inner program) = atSpace inner program := rfl

/-- The two coordinate changes commute, including on effectful programs. -/
theorem origin_evaluation_commute (origin target : Space)
    (program : Computation Space State Answer Intent) :
    fromOrigin origin (atSpace target program) =
      atSpace target (fromOrigin origin program) := rfl

/-- A continuation outside the scope receives the caller's references. The
program's heap effects still sequence through the existing Program.bind. -/
theorem outside_continuation (target : Space)
    (program : Computation Space State Answer Intent)
    (next : Answer → Computation Space State Other Intent) (refs : References Space) :
    bind (atSpace target program) next refs =
      (program { refs with evaluation := target }).bind
        (fun answer => next answer refs) := rfl

def readAt (select : References Space → Space) (query : State → Space → Answer) :
    Computation Space State Answer Intent :=
  fun refs => .read (fun state => .pure (query state (select refs)))

/-- Resolve a role to its current reference value, without reading its contents.
Carrying this result differs from carrying a computation that resolves later. -/
def referenceValue (select : References Space → Space) :
    Computation Space State Space Intent :=
  fun refs => .pure (select refs)

/-- Reading through a freshly resolved reference agrees with direct role use.
This is equality of effect programs, not just one displayed answer. -/
theorem bind_reference_read (select : References Space → Space)
    (query : State → Space → Answer) :
    bind (referenceValue select) (fun saved => readAt (fun _ => saved) query) =
      (readAt select query : Computation Space State Answer Intent) := rfl

/-- Later relocation changes the evaluation role, not a reference value
already handed to a continuation. Contents are still read at the later time. -/
theorem captured_reference_survives_relocation (select : References Space → Space)
    (target : Space) (query : State → Space → Answer) :
    bind (referenceValue select)
      (fun saved => atSpace target (readAt (fun _ => saved) query)) =
      (readAt select query : Computation Space State Answer Intent) := rfl

/-- Changing where a computation runs cannot redirect its origin read. -/
theorem atSpace_read_origin (target : Space) (query : State → Space → Answer) :
    atSpace target (readAt References.origin query :
      Computation Space State Answer Intent) = readAt References.origin query := rfl

theorem atSpace_read_evaluation (target : Space) (query : State → Space → Answer)
    (refs : References Space) :
    atSpace target (readAt References.evaluation query :
      Computation Space State Answer Intent) refs =
      .read (fun state => .pure (query state target)) := rfl

end General

/-! ## Executions with distinct named spaces and mutable contents -/

namespace Examples

inductive Space where
  | home | field | remote
deriving DecidableEq

abbrev Heap := Space → Nat
abbrev C (Answer : Type) := Computation Space Heap Answer Nat

def initial : Heap
  | .home => 17
  | .field => 23
  | .remote => 31

def refs : References Space := ⟨.home, .home⟩

def originRead : C Nat := readAt References.origin (fun heap space => heap space)
def currentRead : C Nat := readAt References.evaluation (fun heap space => heap space)

def bothReads : C (Nat × Nat) :=
  bind originRead fun origin => bind currentRead fun current => pure (origin, current)

def answers {A : Type} (program : C A) (frame : References Space) (heap : Heap) : List A :=
  (runWorlds (program frame) heap).map (fun result => result.answer)

theorem relocated_reads_both_spaces :
    answers (atSpace .field bothReads) refs initial = [(17, 23)] := rfl

def nested : C (Nat × Nat × Nat) :=
  atSpace .field <| bind currentRead fun before =>
    bind (atSpace .remote currentRead) fun inside =>
      bind currentRead fun after => pure (before, inside, after)

theorem nested_restores_evaluation :
    answers nested refs initial = [(23, 31, 23)] := rfl

def writeCurrent (value : Nat) : C Unit :=
  fun frame => .read fun heap =>
    .write (fun space => if space = frame.evaluation then value else heap space) (.pure ())

def writeAndReturn : C Nat :=
  bind (atSpace .field (writeCurrent 99)) fun _ => currentRead

theorem scope_restoration_does_not_rollback :
    answers writeAndReturn refs initial = [17] ∧
      (runWorlds (writeAndReturn refs) initial).map
        (fun result => result.state .field) = [99] := ⟨rfl, rfl⟩

def savedAndFresh : C (Nat × Nat) :=
  atSpace .field <| bind currentRead fun saved =>
    bind (writeCurrent 99) fun _ =>
      bind currentRead fun fresh => pure (saved, fresh)

theorem fixed_value_and_live_space_coexist :
    answers savedAndFresh refs initial = [(23, 99)] := rfl

/-- Equal initial reads do not license replacing a later live read by the
saved answer across an intervening write. -/
def substitutedSaved : C (Nat × Nat) :=
  atSpace .field <| bind currentRead fun saved =>
    bind (writeCurrent 99) fun _ => pure (saved, saved)

theorem fresh_read_is_not_saved_value :
    answers savedAndFresh refs initial ≠ answers substitutedSaved refs initial := by
  decide

/-- Capture the current reference in field, then use it after entering remote. -/
def capturedReferenceRead : C Nat :=
  atSpace .field <| bind (referenceValue References.evaluation) fun saved =>
    atSpace .remote (readAt (fun _ => saved) (fun heap space => heap space))

/-- Carrying the current-read computation instead resolves its role in remote. -/
def delayedReferenceRead : C Nat := atSpace .field (atSpace .remote currentRead)

theorem captured_reference_is_not_delayed_role :
    answers capturedReferenceRead refs initial = [23] ∧
      answers delayedReferenceRead refs initial = [31] ∧
      answers capturedReferenceRead refs initial ≠ answers delayedReferenceRead refs initial := by
  exact ⟨rfl, rfl, by decide⟩

/-- Saving a reference does not freeze the contents to which it points. -/
def savedReferenceFreshContents : C Nat :=
  atSpace .field <| bind (referenceValue References.evaluation) fun saved =>
    bind (writeCurrent 99) fun _ =>
      atSpace .remote (readAt (fun _ => saved) (fun heap space => heap space))

theorem saved_reference_retains_live_contents :
    answers savedReferenceFreshContents refs initial = [99] := rfl

/-- The origin-only projection cannot supply the promised two-space answer. -/
theorem origin_only_insufficient :
    ¬ ∃ recover : Space → List (Nat × Nat),
      ∀ frame, recover frame.origin = answers bothReads frame initial := by
  rintro ⟨recover, correct⟩
  have first := correct ⟨.home, .field⟩
  have second := correct ⟨.home, .remote⟩
  have impossible : [(17, 23)] = ([(17, 31)] : List (Nat × Nat)) :=
    first.symm.trans second
  contradiction

/-- Neither does the evaluation-only projection retain the origin read. -/
theorem evaluation_only_insufficient :
    ¬ ∃ recover : Space → List (Nat × Nat),
      ∀ frame, recover frame.evaluation = answers bothReads frame initial := by
  rintro ⟨recover, correct⟩
  have first := correct ⟨.home, .field⟩
  have second := correct ⟨.remote, .field⟩
  have impossible : [(17, 23)] = ([(31, 23)] : List (Nat × Nat)) :=
    first.symm.trans second
  contradiction

end Examples

#print axioms bind_pure
#print axioms bind_assoc
#print axioms local_bind
#print axioms local_comp
#print axioms atSpace_nested
#print axioms origin_evaluation_commute
#print axioms outside_continuation
#print axioms bind_reference_read
#print axioms captured_reference_survives_relocation
#print axioms atSpace_read_origin
#print axioms atSpace_read_evaluation
#print axioms Examples.relocated_reads_both_spaces
#print axioms Examples.nested_restores_evaluation
#print axioms Examples.scope_restoration_does_not_rollback
#print axioms Examples.fixed_value_and_live_space_coexist
#print axioms Examples.fresh_read_is_not_saved_value
#print axioms Examples.captured_reference_is_not_delayed_role
#print axioms Examples.saved_reference_retains_live_contents
#print axioms Examples.origin_only_insufficient
#print axioms Examples.evaluation_only_insufficient

end Mettapedia.TypeTheory.ContextualEvaluationReferences
