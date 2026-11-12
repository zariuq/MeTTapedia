import Mettapedia.Machines.Cursor.LetPlacement
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

/-!
# Read views, production demand and evaluation phase are separate axes

An opened computation retains its provider and current world. Capturing an
entry view does not execute the code or materialize its answers. Eager
preparation instead drains the actual producer and retains all its results.
Both can use the same captured read view, yet differ in work and effects.

This model uses the existing finite shared-world search and its answer-demand
driver. Internal divergence and callback work require the separate resumable
producer model; the answer quota is not an internal work budget. The opening
meter counts materialized answers, not all steps needed to produce them.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetEvaluationProfiles

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open Mettapedia.Languages.MeTTa.ContextualTransform

variable {World View Bindings Answer : Type}

abbrev Code (View World Bindings : Type) := (World → View) → Search World Bindings

structure Session (World Bindings : Type) where
  world : World
  producer : Search World Bindings
  openingAnswers : Nat

def captured (code : Code View World Bindings) (view : World → View) (world : World) :
    Session World Bindings :=
  ⟨world, code (fun _ => view world), 0⟩

def live (code : Code View World Bindings) (view : World → View) (world : World) :
    Session World Bindings := ⟨world, code view, 0⟩

def prepared (code : Code View World Bindings) (view : World → View) (world : World) :
    Session World Bindings :=
  let collected := (code (fun _ => view world) world).drain
  ⟨collected.2, Search.superpose collected.1, collected.1.length⟩

def disturb (edit : World → World) (session : Session World Bindings) : Session World Bindings :=
  { session with world := edit session.world }

def observe (amount : Nat) (session : Session World Bindings)
    (body : Bindings → Search World Answer) : List Answer × World :=
  let chosen := PeTTaTransformDemand.select amount (session.producer.bind body) session.world
  (chosen.1, chosen.2.1)

/-- The semantic projection deliberately excludes the opening account. -/
def semantics (session : Session World Bindings) : World × Search World Bindings :=
  (session.world, session.producer)

def pureChoices (generate : View → List Bindings) : Code View World Bindings :=
  fun read world => Search.superpose (generate (read world)) world

/-- A captured view can be evaluated later. For a total pure choice
generator this preserves the complete producer, even with several answers.
It says nothing about equal opening work or heap residency. -/
theorem captured_pure_preparation (generate : View → List Bindings)
    (view : World → View) (world : World) :
    semantics (prepared (pureChoices generate) view world) =
      semantics (captured (pureChoices generate) view world) := by
  simp only [semantics, prepared, pureChoices, Search.drain_superpose, captured]
  rfl

theorem captured_pure_observation (generate : View → List Bindings)
    (view : World → View) (world : World) (edit : World → World)
    (body : Bindings → Search World Answer) (amount : Nat) :
    observe amount (disturb edit (prepared (pureChoices generate) view world)) body =
      observe amount (disturb edit (captured (pureChoices generate) view world)) body := by
  simp only [observe, disturb, prepared, pureChoices, Search.drain_superpose, captured]
  rfl

/-- Every produced answer pays at eager opening, while a captured producer
has not yet been called. The two accounts can differ under zero demand. -/
theorem pure_opening_accounts (generate : View → List Bindings)
    (view : World → View) (world : World) :
    (prepared (pureChoices generate) view world).openingAnswers = (generate (view world)).length ∧
      (captured (pureChoices generate) view world).openingAnswers = 0 := by
  simp [prepared, pureChoices, captured]

theorem zero_demand_preserves_open_world (session : Session World Bindings)
    (body : Bindings → Search World Answer) :
    observe 0 session body = ([], session.world) := rfl

/-- Stability of a particular read, rather than syntactic closure, can
justify capturing its value across an intervening edit. -/
theorem one_read_stable (generate : View → List Bindings) (view : World → View)
    (world : World) (edit : World → World) (stable : view (edit world) = view world)
    (body : Bindings → Search World Answer) :
    ((captured (pureChoices generate) view world).producer.bind body) (edit world) =
      ((live (pureChoices generate) view world).producer.bind body) (edit world) := by
  simp only [captured, live, Search.bind, pureChoices, stable]

/-- A concrete frame condition earns read stability while another component
changes. No whole-world revision equality is required. -/
theorem disjoint_frame_read (generate : View → List Bindings) {Other : Type}
    (world : View × Other) (edit : Other → Other)
    (body : Bindings → Search (View × Other) Answer) :
    ((captured (pureChoices generate) Prod.fst world).producer.bind body) (world.1, edit world.2) =
      ((live (pureChoices generate) Prod.fst world).producer.bind body) (world.1, edit world.2) := by
  exact one_read_stable generate Prod.fst world (fun state => (state.1, edit state.2)) rfl body

namespace Controls

def returning (value : Nat) : Search Nat Nat := LetPlacement.yieldOne value
def readTwice : Code Nat Nat Nat := fun read world =>
  .answer (read world) world (fun next => .answer (read next) next .done)
def increment (value : Nat) (world : Nat) : Trace Nat Nat :=
  .answer value (world + 1) .done

theorem captured_view_can_still_be_lazy :
    observe 1 (disturb (fun _ => 42) (captured readTwice id 0)) returning = ([0], 42) ∧
      (captured readTwice id 0).openingAnswers = 0 := by decide

theorem changed_view_changes_live_result :
    observe 1 (disturb (fun _ => 42) (live readTwice id 0)) returning = ([42], 42) := by decide

theorem initial_read_agreement_does_not_cover_later_reads :
    observe 2 (captured readTwice id 0) increment = ([0, 0], 2) ∧
      observe 2 (live readTwice id 0) increment = ([0, 1], 2) := by decide

def effectful : Code Unit Nat Nat := fun _ world =>
  .answer 7 (world + 1) (fun next => .answer 8 (next + 1) .done)

theorem eager_and_deferred_differ_under_first_demand :
    observe 1 (prepared effectful (fun _ => ()) 0) returning = ([7], 2) ∧
      observe 1 (captured effectful (fun _ => ()) 0) returning = ([7], 1) := by decide

theorem zero_demand_does_not_undo_preparation :
    observe 0 (prepared effectful (fun _ => ()) 0) returning = ([], 2) ∧
      observe 0 (captured effectful (fun _ => ()) 0) returning = ([], 0) := by decide

theorem pure_nondeterminism_can_share_a_description :
    observe 2 (prepared (pureChoices (fun _ : Unit => [10, 20])) (fun _ => ()) 0) returning =
      ([10, 20], 0) ∧
      observe 2 (captured (pureChoices (fun _ : Unit => [10, 20])) (fun _ => ()) 0) returning =
        ([10, 20], 0) := by decide

end Controls

end Mettapedia.Machines.Cursor.LetEvaluationProfiles
