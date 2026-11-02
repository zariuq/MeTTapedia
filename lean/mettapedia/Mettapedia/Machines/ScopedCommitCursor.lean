import Mettapedia.Machines.ScopedCommitSelection
import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor

/-!
# Delimited source selection through the common cursor

The source is `ScopedCommit`'s finite effectful search. The target is the
independently implemented bounded cursor client. Its provider performs one
source answer observation per pull, returning the actual continuation and
world. The exact comparison includes answers, intermediate world and live
continuation. At exhaustion the client retains a terminal host state; decoding
that state uses the empty continuation rather than polling it again.

The adapter does not bound work inside a source pull: source primitive actions
are total and the source plan is finite. It does not establish cancellation or
native C lifetime safety. Those obligations remain separate from selection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommitCursor

open ScopedCommit
open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull)
open NativeControlBoundedCursor

variable {Local World : Type}

/-- Poll the existing source stream once, retaining its actual failure
continuation and the world produced while finding this answer. -/
def pull (search : World → Answers Local World) (world : World) :
    World × Pull (World → Answers Local World) Local :=
  match search world with
  | .stop final => (final, .done)
  | .more value here residual => (here, .yield value residual)

/-- An exhausted cursor has no residual source computation. A limit or
budget pause still owns the actual continuation carried by its provider. -/
def sourceView (snapshot : Snapshot (World → Answers Local World) World Local) :
    List Local × World × (World → Answers Local World) :=
  (snapshot.answers, snapshot.world,
    match snapshot.stop with
    | .exhausted => stopAnswers
    | .limit | .budget => snapshot.cursor)

theorem sourceView_prefix (earlier : List Local)
    (snapshot : Snapshot (World → Answers Local World) World Local) :
    sourceView (snapshot.prefix earlier) =
      (earlier ++ (sourceView snapshot).1,
        (sourceView snapshot).2.1, (sourceView snapshot).2.2) := rfl

/-- Enough polls for the requested answers gives exactly the source
selection. No poll is made after the last requested answer. -/
theorem collector_selection (demand : Nat) (search : World → Answers Local World)
    (world : World) :
    sourceView (collectBounded pull demand demand search world).2 =
      selectFrom demand search world := by
  induction demand generalizing search world with
  | zero => rfl
  | succ demand ih =>
    cases produced : search world with
    | stop final => simp [collectBounded, pull, produced, sourceView, selectFrom]
    | more value here residual =>
      simp only [collectBounded, pull, produced, sourceView_prefix, selectFrom]
      rw [ih]
      rfl

/-- Run the actual common cursor, whose reversed accumulator and retained
packet are independently implemented from source `selectFrom`. -/
def execute (demand : Nat) (search : World → Answers Local World) (world : World) :=
  Cursor.advance (NativeControlEffectCursor.provider pull) (client Local) (fun _ _ => 1)
    demand (packet pull demand search world [])

/-- Preservation and reflection are one exact observation equality, including
the live source continuation. The target's pending publication does not make
another host poll. -/
theorem execution_selection (demand : Nat) (search : World → Answers Local World)
    (world : World) :
    sourceView (readout pull (execute demand search world).2) =
      selectFrom demand search world := by
  have exactRead := readout_exact pull demand demand search world []
  have observed := congrArg (fun result => sourceView result.2) exactRead
  simpa only [execute, List.reverse_nil, sourceView_prefix, List.nil_append,
    Prod.mk.eta] using observed.trans (collector_selection demand search world)

/-- Every claimed cursor selection is a source selection, and conversely.
The retained continuation is part of the equality, not an assumed certificate. -/
theorem execution_iff (demand : Nat) (search : World → Answers Local World)
    (world : World) (selection : List Local × World × (World → Answers Local World)) :
    sourceView (readout pull (execute demand search world).2) = selection ↔
      selectFrom demand search world = selection := by
  rw [execution_selection]

/-- The source `once` observation agrees with the one-answer cursor. The
source delimiter discards its residual; the cursor retains it for its owner. -/
theorem once_observation (body : Body Local World) (state : Local) (world : World) :
    let snapshot := readout pull (execute 1 (stream body state) world).2
    (snapshot.answers, snapshot.world) = run (once body) state world := by
  have exactSelection := execution_selection 1 (stream body state) world
  have observed := congrArg (fun selection => (selection.1, selection.2.1)) exactSelection
  rw [run_once_eq_select]
  exact observed

/-- Resuming the actual cursor's retained source continuation preserves all
answers and final effects of the original search, without restarting it. -/
theorem execution_then_resume (body : Body Local World) (state : Local)
    (demand : Nat) (world : World) :
    let selected := sourceView (readout pull (execute demand (stream body state) world).2)
    (selected.1 ++ (resume selected.2.2 selected.2.1).1,
      (resume selected.2.2 selected.2.1).2) = run body state world := by
  dsimp only
  rw [execution_selection]
  exact select_then_resume body state demand world

/-- Consecutive demands compose through the actual retained continuation;
their combined source view agrees with one combined quota. -/
theorem execution_add (first second : Nat) (search : World → Answers Local World)
    (world : World) :
    let earlier := sourceView (readout pull (execute first search world).2)
    let later := sourceView (readout pull (execute second earlier.2.2 earlier.2.1).2)
    (earlier.1 ++ later.1, later.2.1, later.2.2) =
      sourceView (readout pull (execute (first + second) search world).2) := by
  simp only [execution_selection, selectFrom_add]

/-- A read-only source plan supports a precise conservative resumption
policy: keep the prefix, and resume only at the world of the pause. This law
does not license reuse after an arbitrary change to source dependencies. -/
theorem currency_checked_resumption [DecidableEq World] (body : Body Local World)
    (readOnly : ReadOnly body) (state : Local) (demand : Nat) (world now : World) :
    resumeIfCurrent
      (sourceView (readout pull (execute demand (stream body state) world).2)) now =
      ((run body state world).1.take demand,
        if now = world then some ((run body state world).1.drop demand, world) else none) := by
  rw [execution_selection]
  exact resumeIfCurrent_determined body readOnly state demand world now

end Mettapedia.Machines.ScopedCommitCursor
