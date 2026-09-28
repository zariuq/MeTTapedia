import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.Logic.LP.Substitution

/-!
# Native collection and element frames

An answer carries the branch store in which its value must be read.  A collection
frame exports that answer before its next pull restores the caller checkpoint.
The cursor and the copy supply survive this rollback.  The reverse-accumulator
implementation is related to the existing recursive `HostCalls.collect`, with
exact bounded resumption and a distinct suspended outcome.

The checkpoint concerns logical bindings.  `Effects` additionally threads a
persistent world through every pull and retains it at exhaustion and at pause.
Its refinement preserves that world without reordering host effects.  Fault
outcomes and resource cleanup require their own protocol operations; they are
not supplied here.  A suspended host cursor must retain its branch state.  Its total pull is a bounded host step,
not a promise that a search will finish.  Concrete C stores and copying operations
must realize this interface.

The element frame enumerates an already evaluated list.  PeTTa's translator
instead evaluates each alternative of a syntactically literal `superpose`; those
two paths must remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlCollection

open Mettapedia.GSLT.LanguageDef.HostCalls

section Collection

variable {HState Store Value Frozen : Type}

/-- A live collector retains the caller checkpoint, search continuation, copy
identity supply, and reverse accumulation buffer. -/
structure Frame (HState Store Frozen : Type) where
  checkpoint : Store
  cursor : HState
  nextCopy : Nat
  reversed : List Frozen

/-- Exhaustion publishes one collection; a paused collector retains its cursor. -/
inductive Outcome (HState Store Frozen : Type) where
  | paused (frame : Frame HState Store Frozen)
  | complete (caller : Store) (answers : List Frozen) (nextCopy : Nat)

/-- Exported answers are resolved in their branch store.  Each occurrence gets
a separate copy identity, including repeated values.  A suspension consumes no
copy identity.  The next pull receives the saved caller checkpoint again. -/
def exportingPull (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (checkpoint : Store)
    (state : HState × Nat) : Pull (HState × Nat) Frozen :=
  match pull state.1 checkpoint with
  | .done => .done
  | .yield answer rest =>
      .yield (exportAnswer state.2 answer.2 answer.1) (rest, state.2 + 1)
  | .suspend rest => .suspend (rest, state.2)

/-- A native accumulator frame.  The host state owns the residual branch
continuations; every call receives the checkpoint, while the answer is exported
using the store returned by that branch. -/
def run (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    Nat → Frame HState Store Frozen → Outcome HState Store Frozen
  | 0, frame => .paused frame
  | n + 1, frame =>
      match pull frame.cursor frame.checkpoint with
      | .done => .complete frame.checkpoint frame.reversed.reverse frame.nextCopy
      | .yield answer rest =>
          run pull exportAnswer n { frame with
            cursor := rest
            nextCopy := frame.nextCopy + 1
            reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }
      | .suspend rest => run pull exportAnswer n { frame with cursor := rest }

def resume (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (fuel : Nat) :
    Outcome HState Store Frozen → Outcome HState Store Frozen
  | .paused frame => run pull exportAnswer fuel frame
  | .complete caller answers nextCopy => .complete caller answers nextCopy

/-- Only a completed collection is observable as a value. -/
def published : Outcome HState Store Frozen → Option (List Frozen)
  | .paused _ => none
  | .complete _ answers _ => some answers

def callerStore : Outcome HState Store Frozen → Store
  | .paused frame => frame.checkpoint
  | .complete caller _ _ => caller

/-- Reverse accumulation has exactly the recursive collector's result, including
order and multiplicity, and publishes under exactly the same fuel condition. -/
theorem run_published (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen),
      published (run pull exportAnswer fuel frame) =
        (collect (exportingPull pull exportAnswer frame.checkpoint) fuel
          (frame.cursor, frame.nextCopy)).map (frame.reversed.reverse ++ ·)
  | 0, _ => rfl
  | n + 1, frame => by
      cases pulled : pull frame.cursor frame.checkpoint with
      | done => simp [run, published, collect, exportingPull, pulled]
      | suspend rest =>
          simpa only [run, collect, exportingPull, pulled] using
            run_published pull exportAnswer n { frame with cursor := rest }
      | yield answer rest =>
          rw [run, pulled, run_published]
          simp only [collect, exportingPull, pulled, Option.map_map,
            List.reverse_cons, List.append_assoc, List.singleton_append,
            Function.comp_def]

/-- Collection restores the caller's logical store, both at a pause and at
completion.  The residual host cursor is retained separately. -/
theorem run_callerStore (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen),
      callerStore (run pull exportAnswer fuel frame) = frame.checkpoint
  | 0, _ => rfl
  | n + 1, frame => by
      cases pulled : pull frame.cursor frame.checkpoint with
      | done => simp [run, pulled, callerStore]
      | suspend rest =>
          simpa only [run, pulled] using
            run_callerStore pull exportAnswer n { frame with cursor := rest }
      | yield answer rest =>
          simpa only [run, pulled] using
            run_callerStore pull exportAnswer n { frame with
              cursor := rest
              nextCopy := frame.nextCopy + 1
              reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }

/-- Pausing and resuming performs exactly the same work as one longer run;
neither answers nor copy identities are replayed. -/
theorem run_add (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (first rest : Nat) (frame : Frame HState Store Frozen),
      run pull exportAnswer (first + rest) frame =
        resume pull exportAnswer rest (run pull exportAnswer first frame)
  | 0, _, _ => by simp [run, resume]
  | n + 1, rest, frame => by
      rw [Nat.succ_add]
      cases pulled : pull frame.cursor frame.checkpoint with
      | done => simp [run, pulled, resume]
      | suspend cursor =>
          simpa only [run, pulled] using
            run_add pull exportAnswer n rest { frame with cursor := cursor }
      | yield answer cursor =>
          simpa only [run, pulled] using
            run_add pull exportAnswer n rest { frame with
              cursor := cursor
              nextCopy := frame.nextCopy + 1
              reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }

def copySupply : Outcome HState Store Frozen → Nat
  | .paused frame => frame.nextCopy
  | .complete _ _ supply => supply

def bufferLength : Outcome HState Store Frozen → Nat
  | .paused frame => frame.reversed.length
  | .complete _ answers _ => answers.length

/-- Every added occurrence uses exactly one fresh copy identity. -/
theorem run_copySupply (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen),
      copySupply (run pull exportAnswer fuel frame) + frame.reversed.length =
        frame.nextCopy + bufferLength (run pull exportAnswer fuel frame)
  | 0, _ => rfl
  | n + 1, frame => by
      cases pulled : pull frame.cursor frame.checkpoint with
      | done => simp [run, pulled, copySupply, bufferLength]
      | suspend rest =>
          simpa only [run, pulled] using
            run_copySupply pull exportAnswer n { frame with cursor := rest }
      | yield answer rest =>
          have ih := run_copySupply pull exportAnswer n { frame with
            cursor := rest
            nextCopy := frame.nextCopy + 1
            reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }
          simp only [List.length_cons] at ih
          simp only [run, pulled]
          omega

/-- The empty initial buffer yields precisely `collect`, rather than a prefix or
a set of its answers. -/
theorem collect_frame_exact (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (fuel : Nat)
    (checkpoint : Store) (cursor : HState) (supply : Nat) :
    published (run pull exportAnswer fuel ⟨checkpoint, cursor, supply, []⟩) =
      collect (exportingPull pull exportAnswer checkpoint) fuel (cursor, supply) := by
  simp [run_published]

/-- The reference copying operation over a completed list of branch answers. -/
def copyAnswers (exportAnswer : Nat → Store → Value → Frozen) :
    Nat → List (Value × Store) → List Frozen
  | _, [] => []
  | supply, answer :: rest =>
      exportAnswer supply answer.2 answer.1 :: copyAnswers exportAnswer (supply + 1) rest

theorem copyAnswers_length (exportAnswer : Nat → Store → Value → Frozen)
    (supply : Nat) (answers : List (Value × Store)) :
    (copyAnswers exportAnswer supply answers).length = answers.length := by
  induction answers generalizing supply with
  | nil => rfl
  | cons answer rest ih => simp [copyAnswers, ih]

/-- Exporting each answer as it arrives equals exporting the completed recursive
collection.  The proof also reflects non-completion in both directions. -/
theorem collect_exporting (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (checkpoint : Store) :
    ∀ (fuel : Nat) (cursor : HState) (supply : Nat),
      collect (exportingPull pull exportAnswer checkpoint) fuel (cursor, supply) =
        (collect (fun cursor => pull cursor checkpoint) fuel cursor).map
          (copyAnswers exportAnswer supply)
  | 0, _, _ => rfl
  | n + 1, cursor, supply => by
      cases pulled : pull cursor checkpoint with
      | done => simp [collect, exportingPull, pulled, copyAnswers]
      | suspend rest =>
          simpa only [collect, exportingPull, pulled] using
            collect_exporting pull exportAnswer checkpoint n rest supply
      | yield answer rest =>
          simp only [collect, exportingPull, pulled]
          rw [collect_exporting]
          simp only [Option.map_map, Function.comp_def, copyAnswers]

/-- The accumulator implementation, with export before each rollback, is exactly
the source collection followed by occurrence-indexed copying. -/
theorem rollback_collection_exact (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (fuel : Nat)
    (checkpoint : Store) (cursor : HState) (supply : Nat) :
    published (run pull exportAnswer fuel ⟨checkpoint, cursor, supply, []⟩) =
      (collect (fun cursor => pull cursor checkpoint) fuel cursor).map
        (copyAnswers exportAnswer supply) := by
  rw [collect_frame_exact, collect_exporting]

end Collection

/-! ## Collection with a persistent world -/

namespace Effects

variable {HState Store World Value Frozen : Type}

/-- The recursive source collector threads the world even through suspension
and exhaustion, and restores only the logical checkpoint between pulls. -/
def collectWorld (pull : HState → Store → World → World × Pull HState (Value × Store))
    (checkpoint : Store) : Nat → HState → World → World × Option (List (Value × Store))
  | 0, _, world => (world, none)
  | n + 1, cursor, world =>
      match pull cursor checkpoint world with
      | (nextWorld, .done) => (nextWorld, some [])
      | (nextWorld, .suspend rest) => collectWorld pull checkpoint n rest nextWorld
      | (nextWorld, .yield answer rest) =>
          let result := collectWorld pull checkpoint n rest nextWorld
          (result.1, result.2.map (answer :: ·))

/-- The collector's reverse buffer and cursor survive a pause, as does the
persistent world.  Only the logical store is restored from the checkpoint. -/
def run (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    Nat → Frame HState Store Frozen → World → World × Outcome HState Store Frozen
  | 0, frame, world => (world, .paused frame)
  | n + 1, frame, world =>
      match pull frame.cursor frame.checkpoint world with
      | (nextWorld, .done) =>
          (nextWorld, .complete frame.checkpoint frame.reversed.reverse frame.nextCopy)
      | (nextWorld, .yield answer rest) =>
          run pull exportAnswer n { frame with
            cursor := rest
            nextCopy := frame.nextCopy + 1
            reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed } nextWorld
      | (nextWorld, .suspend rest) =>
          run pull exportAnswer n { frame with cursor := rest } nextWorld

def resume (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (fuel : Nat) :
    World × Outcome HState Store Frozen → World × Outcome HState Store Frozen
  | (world, .paused frame) => run pull exportAnswer fuel frame world
  | (world, .complete caller answers supply) => (world, .complete caller answers supply)

def observed (result : World × Outcome HState Store Frozen) : World × Option (List Frozen) :=
  (result.1, published result.2)

/-- Streaming export into a reverse buffer preserves both the full collection
observation and the persistent world of the independent recursive source run.
At a pause, this equality still preserves the world reached so far. -/
theorem run_observed
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen) (world : World),
      observed (run pull exportAnswer fuel frame world) =
        let source := collectWorld pull frame.checkpoint fuel frame.cursor world
        (source.1, source.2.map
          (fun answers => frame.reversed.reverse ++ copyAnswers exportAnswer frame.nextCopy answers))
  | 0, _, _ => rfl
  | n + 1, frame, world => by
      cases pulled : pull frame.cursor frame.checkpoint world with
      | mk nextWorld observation =>
          cases observation with
          | done => simp [run, observed, published, collectWorld, pulled, copyAnswers]
          | suspend rest =>
              simpa only [run, collectWorld, pulled] using
                run_observed pull exportAnswer n { frame with cursor := rest } nextWorld
          | yield answer rest =>
              simp only [run, collectWorld, pulled]
              rw [run_observed]
              simp only [Option.map_map, Function.comp_def, copyAnswers,
                List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Checkpoint rollback never means rolling back the persistent world. -/
theorem run_callerStore
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen) (world : World),
      callerStore (run pull exportAnswer fuel frame world).2 = frame.checkpoint
  | 0, _, _ => rfl
  | n + 1, frame, world => by
      cases pulled : pull frame.cursor frame.checkpoint world with
      | mk nextWorld observation =>
          cases observation with
          | done => simp [run, pulled, callerStore]
          | suspend rest =>
              simpa only [run, pulled] using
                run_callerStore pull exportAnswer n { frame with cursor := rest } nextWorld
          | yield answer rest =>
              simpa only [run, pulled] using
                run_callerStore pull exportAnswer n { frame with
                  cursor := rest
                  nextCopy := frame.nextCopy + 1
                  reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }
                  nextWorld

/-- World effects do not consume or rewind answer-copy identities. -/
theorem run_copySupply
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen) (world : World),
      copySupply (run pull exportAnswer fuel frame world).2 + frame.reversed.length =
        frame.nextCopy + bufferLength (run pull exportAnswer fuel frame world).2
  | 0, _, _ => rfl
  | n + 1, frame, world => by
      cases pulled : pull frame.cursor frame.checkpoint world with
      | mk nextWorld observation =>
          cases observation with
          | done => simp [run, pulled, copySupply, bufferLength]
          | suspend rest =>
              simpa only [run, pulled] using
                run_copySupply pull exportAnswer n { frame with cursor := rest } nextWorld
          | yield answer rest =>
              have ih := run_copySupply pull exportAnswer n { frame with
                cursor := rest
                nextCopy := frame.nextCopy + 1
                reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }
                nextWorld
              simp only [List.length_cons] at ih
              simp only [run, pulled]
              omega

/-- Resumption retains exactly the world and the search/collector state reached
at the interruption.  No host effect is replayed. -/
theorem run_add
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (first rest : Nat) (frame : Frame HState Store Frozen) (world : World),
      run pull exportAnswer (first + rest) frame world =
        resume pull exportAnswer rest (run pull exportAnswer first frame world)
  | 0, _, _, _ => by simp [run, resume]
  | n + 1, rest, frame, world => by
      rw [Nat.succ_add]
      cases pulled : pull frame.cursor frame.checkpoint world with
      | mk nextWorld observation =>
          cases observation with
          | done => simp [run, pulled, resume]
          | suspend cursor =>
              simpa only [run, pulled] using
                run_add pull exportAnswer n rest { frame with cursor := cursor } nextWorld
          | yield answer cursor =>
              simpa only [run, pulled] using
                run_add pull exportAnswer n rest { frame with
                  cursor := cursor
                  nextCopy := frame.nextCopy + 1
                  reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed }
                  nextWorld

/-- With no previous answers, the exact source-to-frame comparison retains the
final world as well as the copied answer occurrences. -/
theorem rollback_collection_exact
    (pull : HState → Store → World → World × Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) (fuel : Nat)
    (checkpoint : Store) (cursor : HState) (supply : Nat) (world : World) :
    observed (run pull exportAnswer fuel ⟨checkpoint, cursor, supply, []⟩ world) =
      let source := collectWorld pull checkpoint fuel cursor world
      (source.1, source.2.map (copyAnswers exportAnswer supply)) := by
  simp [run_observed]

/-- A host with no world effects embeds in the world-aware interface. -/
def liftPull (pull : HState → Store → Pull HState (Value × Store))
    (cursor : HState) (checkpoint : Store) (world : World) :
    World × Pull HState (Value × Store) := (world, pull cursor checkpoint)

theorem run_liftPull (pull : HState → Store → Pull HState (Value × Store))
    (exportAnswer : Nat → Store → Value → Frozen) :
    ∀ (fuel : Nat) (frame : Frame HState Store Frozen) (world : World),
      run (liftPull pull) exportAnswer fuel frame world =
        (world, NativeControlCollection.run pull exportAnswer fuel frame)
  | 0, _, _ => rfl
  | n + 1, frame, world => by
      cases pulled : pull frame.cursor frame.checkpoint with
      | done => simp [run, liftPull, NativeControlCollection.run, pulled]
      | suspend rest =>
          simpa only [run, liftPull, NativeControlCollection.run, pulled] using
            run_liftPull pull exportAnswer n { frame with cursor := rest } world
      | yield answer rest =>
          simpa only [run, liftPull, NativeControlCollection.run, pulled] using
            run_liftPull pull exportAnswer n { frame with
              cursor := rest
              nextCopy := frame.nextCopy + 1
              reversed := exportAnswer frame.nextCopy answer.2 answer.1 :: frame.reversed } world

theorem collectWorld_liftPull (pull : HState → Store → Pull HState (Value × Store))
    (checkpoint : Store) :
    ∀ (fuel : Nat) (cursor : HState) (world : World),
      collectWorld (liftPull pull) checkpoint fuel cursor world =
        (world, collect (fun state => pull state checkpoint) fuel cursor)
  | 0, _, _ => rfl
  | n + 1, cursor, world => by
      cases pulled : pull cursor checkpoint with
      | done => simp [collectWorld, liftPull, collect, pulled]
      | suspend rest =>
          simpa only [collectWorld, liftPull, collect, pulled] using
            collectWorld_liftPull pull checkpoint n rest world
      | yield answer rest =>
          simp [collectWorld, liftPull, collect, pulled, collectWorld_liftPull]

end Effects

section Elements

variable {Value : Type}

/-- Dynamic `superpose` enumerates a list value without evaluating its members. -/
def elementPull : List Value → Pull (List Value) Value
  | [] => .done
  | value :: rest => .yield value rest

/-- The element frame has exactly the list's finite prefixes. -/
theorem element_delivered : ∀ (fuel : Nat) (values : List Value),
    HostGoals.delivered elementPull fuel values = values.take fuel
  | 0, _ => by simp [HostGoals.delivered]
  | n + 1, [] => by simp [HostGoals.delivered, elementPull]
  | n + 1, value :: rest => by
      simp [HostGoals.delivered, elementPull, element_delivered n rest]

/-- Including the final exhaustion pull produces the original list exactly. -/
theorem element_collect (values : List Value) :
    collect elementPull (values.length + 1) values = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simpa [collect, elementPull] using congrArg (Option.map (value :: ·)) ih

/-- Omitting the exhaustion pull cannot publish a completed collection. -/
theorem element_not_complete (values : List Value) :
    collect elementPull values.length values = none := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [collect, elementPull, ih]

/-- The literal-list translation evaluates each alternative as a computation.
This finite observation describes the `build_superpose_branches` disjunction,
not the dynamic member operation. -/
def literalAnswers {Expr : Type} (evaluate : Expr → List Value) : List Expr → List Value
  | [] => []
  | expr :: rest => evaluate expr ++ literalAnswers evaluate rest

theorem literalAnswers_eq_flatMap {Expr : Type} (evaluate : Expr → List Value)
    (expressions : List Expr) :
    literalAnswers evaluate expressions = expressions.flatMap evaluate := by
  induction expressions with
  | nil => rfl
  | cons expr rest ih => simp [literalAnswers, ih]

/-- Literal and dynamic forms coincide when each element evaluates to itself. -/
theorem literalAnswers_of_values (values : List Value) :
    literalAnswers (fun value => [value]) values = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [literalAnswers, ih]

end Elements

/-! ## Copies with occurrence-local variable identities -/

section FreshCopies

open Mettapedia.Logic.LP

/-- Change only the variable carrier of an existing first-order signature. -/
abbrev withVariables (σ : LPSignature) (Variables : Type*) : LPSignature :=
  { σ with vars := Variables }

/-- A structural variable renaming preserves every constructor and child. -/
def renameTerm {σ : LPSignature} {Variables : Type*} (rename : σ.vars → Variables) :
    Term σ → Term (withVariables σ Variables)
  | .var varName => .var (rename varName)
  | .const constant => .const constant
  | .app function arguments => .app function (fun i => renameTerm rename (arguments i))

theorem renameTerm_variables {σ : LPSignature} {Variables : Type*}
    [DecidableEq σ.vars] [DecidableEq Variables] (rename : σ.vars → Variables)
    (term : Term σ) (varName : Variables) :
    varName ∈ (renameTerm rename term).freeVars ↔
      ∃ original ∈ term.freeVars, rename original = varName := by
  induction term with
  | var original => simp [renameTerm, Term.freeVars, eq_comm]
  | const constant => simp [renameTerm, Term.freeVars]
  | app function arguments ih =>
      simp only [renameTerm, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, h⟩
        obtain ⟨original, occurs, renamed⟩ := (ih i).mp h
        exact ⟨original, ⟨i, occurs⟩, renamed⟩
      · rintro ⟨original, ⟨i, occurs⟩, renamed⟩
        exact ⟨i, (ih i).mpr ⟨original, occurs, renamed⟩⟩

/-- Caller variables and copied answer variables occupy disjoint carriers.  The
copy scope identifies an answer occurrence, not its value or its source variable. -/
abbrev copySignature (σ : LPSignature) : LPSignature :=
  withVariables σ (Sum σ.vars (Nat × σ.vars))

def callerTerm {σ : LPSignature} (term : Term σ) : Term (copySignature σ) :=
  renameTerm Sum.inl term

def freshCopy {σ : LPSignature} (scope : Nat) (term : Term σ) : Term (copySignature σ) :=
  renameTerm (fun varName => Sum.inr (scope, varName)) term

/-- Erasing copy ownership recovers the original constructor tree and variable
sharing; it is not a runtime operation that reconnects variables. -/
def eraseCopy {σ : LPSignature} : Term (copySignature σ) → Term σ
  | .var (.inl varName) => .var varName
  | .var (.inr (_, varName)) => .var varName
  | .const constant => .const constant
  | .app function arguments => .app function (fun i => eraseCopy (arguments i))

theorem eraseCopy_freshCopy {σ : LPSignature} (scope : Nat) (term : Term σ) :
    eraseCopy (freshCopy scope term) = term := by
  induction term with
  | var varName => rfl
  | const constant => rfl
  | app function arguments ih =>
      simp only [freshCopy, renameTerm, eraseCopy]
      congr 1
      funext i
      exact ih i

/-- Freshening cannot collapse distinct term structures or distinct variables
inside one answer. -/
theorem freshCopy_injective {σ : LPSignature} (scope : Nat) :
    Function.Injective (freshCopy (σ := σ) scope) :=
  Function.LeftInverse.injective (eraseCopy_freshCopy scope)

/-- Collected variables are disjoint from every caller variable. -/
theorem freshCopy_caller_disjoint {σ : LPSignature} [DecidableEq σ.vars]
    (scope : Nat) (answer caller : Term σ) :
    Disjoint (freshCopy scope answer).freeVars (callerTerm caller).freeVars := by
  rw [Finset.disjoint_left]
  intro varName inAnswer inCaller
  obtain ⟨original, _, copied⟩ :=
    (renameTerm_variables (fun v => Sum.inr (scope, v)) answer varName).mp inAnswer
  obtain ⟨other, _, external⟩ :=
    (renameTerm_variables Sum.inl caller varName).mp inCaller
  cases copied.trans external.symm

/-- Different occurrences never share free variables, even if their answers
were the same term before copying. -/
theorem freshCopies_disjoint {σ : LPSignature} [DecidableEq σ.vars]
    {first second : Nat} (different : first ≠ second) (left right : Term σ) :
    Disjoint (freshCopy first left).freeVars (freshCopy second right).freeVars := by
  rw [Finset.disjoint_left]
  intro varName inLeft inRight
  obtain ⟨original, _, copied⟩ :=
    (renameTerm_variables (fun v => Sum.inr (first, v)) left varName).mp inLeft
  obtain ⟨other, _, external⟩ :=
    (renameTerm_variables (fun v => Sum.inr (second, v)) right varName).mp inRight
  have same := Sum.inr.inj (copied.trans external.symm)
  exact different (congrArg Prod.fst same)

/-- A later substitution at the caller only changes its own variables. -/
def callerSubstitution {σ : LPSignature} (substitution : Subst σ) :
    Subst (copySignature σ)
  | .inl varName => callerTerm (substitution varName)
  | .inr owned => .var (.inr owned)

/-- A copied answer is independent of later caller bindings. -/
theorem callerSubstitution_freshCopy {σ : LPSignature} (substitution : Subst σ)
    (scope : Nat) (term : Term σ) :
    (callerSubstitution substitution).applyTerm (freshCopy scope term) = freshCopy scope term := by
  induction term with
  | var varName => rfl
  | const constant => rfl
  | app function arguments ih =>
      simp only [freshCopy, renameTerm, Subst.applyTerm]
      congr 1
      funext i
      exact ih i

/-- Export after applying the branch's substitution, retaining sharing among
the free variables that remain.  This is a concrete substitution-store model;
an implementation with links must first implement the corresponding resolution. -/
def exportTerm {σ : LPSignature} (scope : Nat) (substitution : Subst σ)
    (term : Term σ) : Term (copySignature σ) :=
  freshCopy scope (substitution.applyTerm term)

theorem exportTerm_caller_independent {σ : LPSignature}
    (caller branch : Subst σ) (scope : Nat) (term : Term σ) :
    (callerSubstitution caller).applyTerm (exportTerm scope branch term) =
      exportTerm scope branch term :=
  callerSubstitution_freshCopy caller scope (branch.applyTerm term)

end FreshCopies

/-! ## Positive and negative controls -/

namespace Controls

open Mettapedia.Logic.LP

/-- Each branch increments its input store.  The second branch must see the
checkpoint again, rather than the first branch's increment. -/
def incrementingBranches : Nat → Nat → Pull Nat (Nat × Nat)
  | 0, saved => .yield (0, saved + 1) 1
  | 1, saved => .yield (0, saved + 1) 2
  | _, _ => .done

def readBranchStore (_scope branch _value : Nat) : Nat := branch

theorem rollback_two_branches :
    published (run incrementingBranches readBranchStore 3 ⟨7, 0, 0, []⟩) = some [8, 8] ∧
      callerStore (run incrementingBranches readBranchStore 3 ⟨7, 0, 0, []⟩) = 7 := by
  decide

/-- An intentionally incorrect collector carries the branch store forward. -/
def withoutRollback : Nat → Nat → Nat → Option (List Nat)
  | 0, _, _ => none
  | n + 1, cursor, current =>
      match incrementingBranches cursor current with
      | .done => some []
      | .suspend rest => withoutRollback n rest current
      | .yield answer rest => (withoutRollback n rest answer.2).map (answer.2 :: ·)

theorem missing_rollback_changes_answers :
    withoutRollback 3 0 7 = some [8, 9] ∧
      withoutRollback 3 0 7 ≠
        published (run incrementingBranches readBranchStore 3 ⟨7, 0, 0, []⟩) := by
  decide

/-- Resolving an answer after rollback reads the wrong store. -/
theorem export_after_rollback_is_wrong :
    published (run incrementingBranches (fun _ _ _ => 7) 3 ⟨7, 0, 0, []⟩) = some [7, 7] ∧
      published (run incrementingBranches (fun _ _ _ => 7) 3 ⟨7, 0, 0, []⟩) ≠
        published (run incrementingBranches readBranchStore 3 ⟨7, 0, 0, []⟩) := by
  decide

def delayedBranches : Nat → Nat → Pull Nat (Nat × Nat)
  | 0, _ => .suspend 1
  | 1, saved => .yield (2, saved) 2
  | 2, saved => .yield (2, saved) 3
  | _, _ => .done

def copyIdentity (scope _store value : Nat) : Nat × Nat := (scope, value)

/-- Suspension is not exhaustion and does not consume a copy identity.  After
resumption the duplicate values remain two independently copied occurrences. -/
theorem suspension_and_duplicate_occurrences :
    published (run delayedBranches copyIdentity 1 ⟨5, 0, 10, []⟩) = none ∧
      copySupply (run delayedBranches copyIdentity 1 ⟨5, 0, 10, []⟩) = 10 ∧
      published (run delayedBranches copyIdentity 4 ⟨5, 0, 10, []⟩) =
        some [(10, 2), (11, 2)] ∧
      copySupply (run delayedBranches copyIdentity 4 ⟨5, 0, 10, []⟩) = 12 := by
  decide

/-- Dropping the residual cursor at a pause would lose real answers. -/
theorem suspension_is_not_empty_collection :
    published (run delayedBranches copyIdentity 1 ⟨5, 0, 10, []⟩) ≠ some [] ∧
      published (resume delayedBranches copyIdentity 3
        (run delayedBranches copyIdentity 1 ⟨5, 0, 10, []⟩)) = some [(10, 2), (11, 2)] := by
  decide

/-- Effect markers are recorded on suspension, on both answers, and on final
exhaustion.  Each answer observes how much persistent work already happened. -/
def effectfulBranches : Nat → Nat → List Nat → List Nat × Pull Nat (Nat × Nat)
  | 0, _, world => (world ++ [10], .suspend 1)
  | 1, saved, world => (world ++ [20], .yield (world.length, saved + 1) 2)
  | 2, saved, world => (world ++ [30], .yield (world.length, saved + 1) 3)
  | _, _, world => (world ++ [40], .done)

def readValue (_scope _store value : Nat) : Nat := value

/-- The final exhaustion effect remains observable, and the caller's logical
bindings are restored without deleting any persistent effect. -/
theorem persistent_world_survives_collection :
    Effects.observed (Effects.run effectfulBranches readValue 4 ⟨7, 0, 0, []⟩ []) =
      ([10, 20, 30, 40], some [1, 2]) ∧
      callerStore (Effects.run effectfulBranches readValue 4 ⟨7, 0, 0, []⟩ []).2 = 7 := by
  decide

/-- A pause retains effects that occurred before any answer; resuming does not
repeat those effects or forget them. -/
theorem persistent_world_survives_pause :
    Effects.observed (Effects.run effectfulBranches readValue 1 ⟨7, 0, 0, []⟩ []) =
      ([10], none) ∧
      Effects.observed (Effects.resume effectfulBranches readValue 3
        (Effects.run effectfulBranches readValue 1 ⟨7, 0, 0, []⟩ [])) =
        ([10, 20, 30, 40], some [1, 2]) := by
  decide

/-- Treating the persistent world as part of the rollback checkpoint loses
effects and changes answers that depend on earlier effects. -/
theorem rolling_back_world_is_wrong :
    Effects.observed
      (Effects.run (fun cursor saved _ => effectfulBranches cursor saved []) readValue
        4 ⟨7, 0, 0, []⟩ ([] : List Nat)) = ([40], some [0, 0]) ∧
      Effects.observed
        (Effects.run (fun cursor saved _ => effectfulBranches cursor saved []) readValue
          4 ⟨7, 0, 0, []⟩ ([] : List Nat)) ≠
        Effects.observed (Effects.run effectfulBranches readValue 4 ⟨7, 0, 0, []⟩ []) := by
  decide

theorem element_duplicates :
    collect elementPull 5 [1, 2, 2, 3] = some [1, 2, 2, 3] := by
  decide

/-- A literal alternative may compute several answers, while the already
evaluated dynamic list returns its member itself. -/
theorem literal_dynamic_distinction :
    literalAnswers (fun n : Nat => [n, n + 1]) [2] = [2, 3] ∧
      collect elementPull 2 [2] = some [2] ∧
      literalAnswers (fun n : Nat => [n, n + 1]) [2] ≠ [2] := by
  decide

abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 2

def repeatedVariable : Term signature := .app () (fun _ => .var 0)

def bindFive : Subst signature := Subst.single 0 (.const 5)

/-- Both occurrences of a source variable receive the same fresh identity. -/
theorem copy_keeps_internal_sharing :
    freshCopy 3 repeatedVariable =
      .app () (fun _ => .var (.inr (3, 0))) := rfl

/-- Later caller substitution does not reach the fresh variables in the pair. -/
theorem later_binding_keeps_copy :
    (callerSubstitution bindFive).applyTerm (freshCopy 3 repeatedVariable) =
      .app () (fun _ => .var (.inr (3, 0))) := by
  rw [callerSubstitution_freshCopy, copy_keeps_internal_sharing]

/-- Keeping caller variable identities instead of copying would turn that pair
into `(5, 5)` after the caller is bound. -/
theorem retained_caller_alias_is_wrong :
    (callerSubstitution bindFive).applyTerm (callerTerm repeatedVariable) =
      .app () (fun _ => .const 5) ∧
      (callerSubstitution bindFive).applyTerm (callerTerm repeatedVariable) ≠
        callerTerm repeatedVariable := by
  constructor
  · rfl
  · intro same
    have children := Term.app.inj same
    have first := congrFun (eq_of_heq children.2) 0
    cases first

/-- Two occurrences of the same answer, each carrying the branch substitution
in which its free variables remain unbound. -/
def repeatedTermBranches : Nat → Subst signature →
    Pull Nat (Term signature × Subst signature)
  | 0, branch => .yield (repeatedVariable, branch) 1
  | 1, branch => .yield (repeatedVariable, branch) 2
  | _, _ => .done

/-- The actual collecting algorithm produces two separately owned copies while
preserving repeated-variable sharing inside each copy. -/
theorem collection_copies_per_occurrence :
    published (run repeatedTermBranches exportTerm 3
      ⟨Subst.id signature, 0, 8, []⟩) =
        some [freshCopy 8 repeatedVariable, freshCopy 9 repeatedVariable] := by
  simp [run, repeatedTermBranches, exportTerm, Subst.applyTerm_id, published]

/-- Collection leaves the caller store available unchanged; a later write to
that caller cannot bind either answer's private variables. -/
theorem collection_copies_survive_caller_binding :
    (published (run repeatedTermBranches exportTerm 3
      ⟨Subst.id signature, 0, 8, []⟩)).map
        (List.map (callerSubstitution bindFive).applyTerm) =
      some [freshCopy 8 repeatedVariable, freshCopy 9 repeatedVariable] := by
  rw [collection_copies_per_occurrence]
  simp [callerSubstitution_freshCopy]

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlCollection
