import Mettapedia.GSLT.Distinction.PublicationBlocks

/-!
# Controls for module publication blocks

* **An initialization that prints and then fails** (`prints_then_fails`,
  `restart_replays_print`).  The print and the fault stay visible, nothing is
  bound or linked, and a second attempt changes nothing; a cleanup that
  restarts the initialization prints again.
* **A partial link after a failed reservation** (`partial_link_control`).  An
  installer that binds the exports one by one and stops at the first taken
  name leaves a partial token bound while reporting failure; the atomic attempt
  leaves the registry unchanged.
* **A replayed completed effect on retry** (`retry_after_release`,
  `replayed_effect_control`).  A reservation refused for lack of capacity keeps
  the finished initialization staged; after capacity is released the retry
  publishes it with no new event.  A retry that restarts the initialization
  commits the print a second time while the exported tokens agree.
* **Repeated import publishing twice** (`two_importers_one_publication`,
  `double_publication_control`).  Two importers share one publication: one
  initialization, one binding, two links.  An import that ignores the
  published list runs the initialization and publishes twice.
* **Exact resumption** (`split_fuel_same_session`): an import paused after one
  step and resumed is the uninterrupted import.
* **A stale callback identity after session closure**
  (`stale_callback_control`, `stale_call_visible`).  A retained handle of a
  closed session resolves to nothing even after a new session reuses its
  serial, and its call is refused with a visible fault; a resolver keyed by the
  serial alone dispatches it to the new session's callback.
* **A retained callback called after another module becomes active**
  (`owner_not_active_module`).  The table runs the callback with its owner; a
  resolver that uses the active module runs a different callback.
* **The observation of a module** (`failed_observation`,
  `refused_observation`, `other_module_extends_trace`).  A failed
  initialization is a final faulted observation that a second attempt keeps; a
  refused reservation is incomplete, not failed, and finishes after release
  with no new event; importing another module extends the session's trace, so a
  module's observation is prefix-faithful for the attempts at that module only.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.PublicationBlocks.Controls

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics.OrderedDemand (Event answers)
open Session

/-- Two exported names. -/
inductive Sym where
  | a
  | b
  deriving DecidableEq

/-- Foreign effects. -/
inductive Fx where
  | print
  | write
  deriving DecidableEq

/-- Initialization phases. -/
inductive Phase where
  | start
  | middle
  | done
  deriving DecidableEq

abbrev Ev := InitEvent Sym ℕ Fx Unit

abbrev TestSession := Session Phase ℕ Sym ℕ Fx Unit

/-- An empty registry with the given capacity. -/
def emptyRegistry (capacity : ℕ) : Registry ℕ Sym ℕ :=
  ⟨fun _ => none, [], [], capacity⟩

/-- A fresh session. -/
def fresh (capacity : ℕ) : TestSession :=
  ⟨emptyRegistry capacity, [], fun _ => .idle⟩

/-- Every module starts at the same phase. -/
def start : ℕ → Phase := fun _ => .start

/-! ## An initialization that prints and then fails -/

/-- Print, then fail. -/
def printsThenFails : Machine Phase Ev Unit Empty where
  step
    | .start => some (.publish [.effect .print] .middle)
    | .middle => some (.fail [.fault ()])
    | .done => some (.finish ())

/-- **The print and the fault stay visible; nothing is bound or linked; a second
attempt changes nothing.** -/
def printedOnce : TestSession :=
  importStep printsThenFails start 5 0 7 (fresh 4)

theorem prints_then_fails :
    printedOnce.visible = [.effect .print, .fault ()] ∧ printedOnce.registry.binding .a = none ∧
      printedOnce.registry.links = [] ∧ printedOnce.registry.published = [] ∧
      (importStep printsThenFails start 5 0 7 printedOnce).visible = [.effect .print, .fault ()] := by
  decide

/-- A cleanup that resets the stage and retries replays the print. -/
def restartStep (init : Machine Phase Ev Unit Empty) (fuel : ℕ) (importer module : ℕ)
    (session : TestSession) : TestSession :=
  importStep init start fuel importer module (session.setStage module .idle)

theorem restart_replays_print :
    (restartStep printsThenFails 5 0 7 printedOnce).visible =
      [.effect .print, .fault (), .effect .print, .fault ()] := by
  decide

/-! ## A partial link after a failed reservation -/

/-- Print, export `a ↦ 1` and `b ↦ 2`, finish. -/
def exportsTwo : Machine Phase Ev Unit Empty where
  step
    | .start => some (.publish [.effect .print] .middle)
    | .middle => some (.publish [.answer (.a, 1), .answer (.b, 2)] .done)
    | .done => some (.finish ())

/-- A registry in which `b` is already bound by module 3. -/
def bTaken : Registry ℕ Sym ℕ :=
  ⟨fun name => if name = .b then some (3, 9) else none, [], [3], 4⟩

/-- An installer that binds exports one at a time and stops at the first taken
name, reporting failure. -/
def installEach (module : ℕ) : Registry ℕ Sym ℕ → List (Sym × ℕ) → Registry ℕ Sym ℕ × Bool
  | registry, [] => (registry, true)
  | registry, (name, token) :: rest =>
      if (registry.binding name).isNone then
        installEach module
          { registry with binding := fun query =>
              if query = name then some (module, token) else registry.binding query } rest
      else (registry, false)

/-- **Partial link control.**  The one-by-one installer fails at `b` with `a`
already bound; the atomic attempt keeps the export staged and binds nothing. -/
theorem partial_link_control :
    (installEach 7 bTaken [(.a, 1), (.b, 2)]).2 = false ∧
      (installEach 7 bTaken [(.a, 1), (.b, 2)]).1.binding .a = some (7, 1) ∧
      (importStep exportsTwo start 5 0 7 ⟨bTaken, [], fun _ => .idle⟩).registry.binding .a = none ∧
      (importStep exportsTwo start 5 0 7 ⟨bTaken, [], fun _ => .idle⟩).registry.links = [] ∧
      (importStep exportsTwo start 5 0 7 ⟨bTaken, [], fun _ => .idle⟩).visible =
        [.effect .print, .answer (.a, 1), .answer (.b, 2)] := by
  decide

/-! ## A replayed completed effect on retry -/

/-- Release reservation capacity: an external event. -/
def release (amount : ℕ) (session : TestSession) : TestSession :=
  { session with registry := { session.registry with capacity := session.registry.capacity + amount } }

/-- The first attempt finishes the initialization but no capacity is left. -/
def refusedOnce : TestSession := importStep exportsTwo start 5 0 7 (fresh 0)

/-- **The retry after release publishes the staged exports with no new
event.** -/
theorem retry_after_release :
    refusedOnce.registry.binding .a = none ∧
      refusedOnce.visible = [.effect .print, .answer (.a, 1), .answer (.b, 2)] ∧
      (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).visible =
        [.effect .print, .answer (.a, 1), .answer (.b, 2)] ∧
      (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).registry.binding .a = some (7, 1) ∧
      (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).registry.binding .b = some (7, 2) ∧
      (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).registry.links = [(0, 7)] := by
  decide

/-- **Replayed effect control.**  Restarting the initialization on retry commits
the print twice, while the exported tokens of the two retries agree. -/
theorem replayed_effect_control :
    (restartStep exportsTwo 5 0 7 (release 2 refusedOnce)).visible =
        [.effect .print, .answer (.a, 1), .answer (.b, 2),
          .effect .print, .answer (.a, 1), .answer (.b, 2)] ∧
      (restartStep exportsTwo 5 0 7 (release 2 refusedOnce)).registry.binding .a =
        (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).registry.binding .a := by
  decide

/-! ## Repeated import -/

/-- Two importers of module 7. -/
def twoImporters : TestSession :=
  importStep exportsTwo start 5 1 7 (importStep exportsTwo start 5 0 7 (fresh 4))

/-- **Two importers share one publication**: one initialization, one binding of
each token, two links. -/
theorem two_importers_one_publication :
    twoImporters.visible = [.effect .print, .answer (.a, 1), .answer (.b, 2)] ∧
      twoImporters.registry.published = [7] ∧
      twoImporters.registry.binding .a = some (7, 1) ∧
      twoImporters.registry.links = [(0, 7), (1, 7)] ∧
      (importStep exportsTwo start 5 1 7 twoImporters).registry.links = [(0, 7), (1, 7)] := by
  decide

/-- An import that ignores the published list: it always runs the
initialization to completion and installs without a reservation. -/
def naiveImport (init : Machine Phase Ev Unit Empty) (fuel : ℕ) (importer module : ℕ)
    (session : TestSession) : TestSession :=
  let ran := init.run fuel (start module)
  { session with
    registry := (session.registry.install module (answers ran.1)).link importer module
    visible := session.visible ++ ran.1 }

/-- **Double publication control.**  Importing twice without the published list
publishes the module twice and runs its print twice. -/
theorem double_publication_control :
    (naiveImport exportsTwo 5 1 7 (naiveImport exportsTwo 5 0 7 (fresh 4))).registry.published =
        [7, 7] ∧
      (naiveImport exportsTwo 5 1 7 (naiveImport exportsTwo 5 0 7 (fresh 4))).visible =
        [.effect .print, .answer (.a, 1), .answer (.b, 2),
          .effect .print, .answer (.a, 1), .answer (.b, 2)] := by
  decide

/-! ## Exact resumption -/

/-- **An import paused after one step and resumed is the uninterrupted
import**, here observed on its trace, bindings and links. -/
theorem split_fuel_same_session :
    importStep exportsTwo start 4 0 7 (importStep exportsTwo start 1 0 7 (fresh 4)) =
      importStep exportsTwo start 5 0 7 (fresh 4) ∧
    (importStep exportsTwo start 1 0 7 (fresh 4)).visible = [.effect .print] ∧
    (importStep exportsTwo start 5 0 7 (fresh 4)).visible =
      [.effect .print, .answer (.a, 1), .answer (.b, 2)] :=
  ⟨importStep_add exportsTwo start 1 4 0 7 (fresh 4), by decide, by decide⟩

/-! ## Callback identity -/

/-- Session `0` registered serial `0` for module `1`; it was closed; session `1`
registered serial `0` for module `2`. -/
def reusedTable : CallbackTable ℕ ℕ Fx :=
  ((((⟨[0], []⟩ : CallbackTable ℕ ℕ Fx).register ⟨0, 0⟩ 1 .print).closeSession 0).openSession 1).register
    ⟨1, 0⟩ 2 .write

/-- A resolver keyed by the serial alone. -/
def resolveBySerial (table : CallbackTable ℕ ℕ Fx) (serial : ℕ) : Option (ℕ × Fx) :=
  (table.entries.find? fun entry => entry.1.serial = serial).map Prod.snd

/-- **Stale callback control.**  The retained handle of the closed session
resolves to nothing; resolving by serial alone dispatches it to the new
session's callback. -/
theorem stale_callback_control :
    reusedTable.resolve? ⟨0, 0⟩ = none ∧ reusedTable.resolve? ⟨1, 0⟩ = some (2, .write) ∧
      resolveBySerial reusedTable 0 = some (2, .write) := by
  decide

/-- A caller that calls a retained callback, then publishes an answer and
finishes. -/
def caller (handle : CallbackId ℕ) : Machine Phase (Event ℕ Fx Unit) Unit (CallbackId ℕ) where
  step
    | .start => some (.call handle .middle)
    | .middle => some (.publish [.answer 1] .done)
    | .done => some (.finish ())

/-- Visible call and reply events; a fault reply skips the continuation's
publication. -/
def protocol : Callback Phase (Event ℕ Fx Unit) (CallbackId ℕ) ℕ Unit where
  callEvent _ := .effect .write
  replyEvent
    | .returned _ => .answer 0
    | .faulted _ => .fault ()
    | .cancelled => .fault ()
  resume saved
    | .returned _ => saved
    | _ => .done

/-- A callback runs its own effect, then returns. -/
def runHandler (_owner : ℕ) (effect : Fx) : List (Event ℕ Fx Unit) × Reply ℕ Unit :=
  ([.effect effect], .returned 0)

/-- **A live callback runs its own effect; a stale one is refused visibly.** -/
theorem stale_call_visible :
    ((caller ⟨1, 0⟩).close protocol (tableEnvironment reusedTable runHandler ())).run 3 .start =
        ([.effect .write, .effect .write, .answer 0, .answer 1], .finished ()) ∧
      ((caller ⟨0, 0⟩).close protocol (tableEnvironment reusedTable runHandler ())).run 3 .start =
        ([.effect .write, .fault ()], .finished ()) := by
  constructor <;> rfl

/-- The effect a callback commits names the module it runs with. -/
def moduleHandler (owner : ℕ) (_effect : Fx) : List (Event ℕ ℕ Unit) × Reply ℕ Unit :=
  ([.effect owner], .returned 0)

/-- A resolver that runs a callback with the module active at the call. -/
def activeEnvironment (table : CallbackTable ℕ ℕ Fx) (active : ℕ) :
    Environment (CallbackId ℕ) (Event ℕ ℕ Unit) ℕ Unit := fun id =>
  match table.resolve? id with
  | some (_, handler) => moduleHandler active handler
  | none => ([], .faulted ())

/-- **A retained callback runs with its owner, not with the active module.**
After module `5` becomes active, the table runs session `1`'s callback with its
owner `2`; the active-module resolver runs it with `5`. -/
theorem owner_not_active_module :
    tableEnvironment reusedTable moduleHandler () ⟨1, 0⟩ = ([.effect 2], .returned 0) ∧
      activeEnvironment reusedTable 5 ⟨1, 0⟩ = ([.effect 5], .returned 0) := by
  constructor <;> rfl

/-! ## The observation of a module -/

/-- **A failed publication is a final, faulted observation**, and a second
attempt keeps it. -/
theorem failed_observation :
    printedOnce.observe 7 = ⟨[.effect .print, .fault ()], .faulted⟩ ∧
      (importStep printsThenFails start 5 0 7 printedOnce).observe 7 = printedOnce.observe 7 := by
  decide

/-- **A refused reservation is not a failure**: the staged publication is
incomplete, and the retry after capacity is released finishes with the same
trace. -/
theorem refused_observation :
    refusedOnce.observe 7 = ⟨[.effect .print, .answer (.a, 1), .answer (.b, 2)], .incomplete⟩ ∧
      (importStep exportsTwo start 5 0 7 (release 2 refusedOnce)).observe 7 =
        ⟨[.effect .print, .answer (.a, 1), .answer (.b, 2)], .finished ()⟩ := by
  decide

/-- **The observation is that of the attempts at its module.**  Module `7` is
published, so its observation is final; importing module `8` afterwards extends
the session's visible trace, and the new observation of module `7` no longer
has the final one as a prefix. -/
theorem other_module_extends_trace :
    ((importStep exportsTwo start 5 0 7 (fresh 4)).observe 7).status = .finished () ∧
      ¬ ((importStep exportsTwo start 5 0 7 (fresh 4)).observe 7).Prefix
        ((importStep printsThenFails start 5 0 8 (importStep exportsTwo start 5 0 7 (fresh 4))).observe 7) := by
  have finished : ((importStep exportsTwo start 5 0 7 (fresh 4)).observe 7).status = .finished () := by
    decide
  refine ⟨finished, fun prefixed => ?_⟩
  have same := prefixed.2 (by rw [finished]; trivial)
  revert same
  decide

end Mettapedia.GSLT.Distinction.PublicationBlocks.Controls
