import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeReadout
import Mettapedia.CategoryTheory.PartialActionTree

/-!
# Retained event histories and coalgebraic unfolding

Actual labelled operational events concatenate only at matching endpoints.
Their histories retain every supplied occurrence origin. The complete
action word reads the exact endpoint in the independently constructed
cofree action tree, and this readout commutes with future-context maps.
An action-tree reading forgets event origins; it is not a history receipt
or a construction of a history monad.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeHistory

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.CategoryTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}
    {C : Type u} [Category.{u} C]
    (law : Law S Actions) (worlds : Cᵒᵖ ⥤ S.Families)
    (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)
    (Origins : Type u) (sort : S.Srt) (world : Cᵒᵖ)

/-- A typed function readout of the actual categorical operational coalgebra. -/
noncomputable def transition (source : S.Term (worlds.obj world) sort) (action : Actions sort) :
    Option (S.Term (worlds.obj world) sort) :=
  Operational.coalgebra law (steps.app world) PUnit.unit sort source action

/-- A real operational history retains events and their exact matched endpoints. -/
inductive History : S.Term (worlds.obj world) sort → S.Term (worlds.obj world) sort → Type u where
  | nil (source : S.Term (worlds.obj world) sort) : History source source
  | cons (event : EdgeReadout.Event law worlds steps Origins sort world)
      {endpoint : S.Term (worlds.obj world) sort} (tail : History event.target endpoint) :
      History event.source endpoint

namespace History

variable {law worlds steps Origins sort world}

def actions : {source endpoint : S.Term (worlds.obj world) sort} →
    History law worlds steps Origins sort world source endpoint → List (Actions sort)
  | _, _, .nil _ => []
  | _, _, .cons event tail => event.action :: tail.actions

def origins : {source endpoint : S.Term (worlds.obj world) sort} →
    History law worlds steps Origins sort world source endpoint → List Origins
  | _, _, .nil _ => []
  | _, _, .cons event tail => event.origin :: tail.origins

/-- Append genuine executions at their complete common endpoint. -/
def append {source middle endpoint : S.Term (worlds.obj world) sort} :
    History law worlds steps Origins sort world source middle →
      History law worlds steps Origins sort world middle endpoint →
        History law worlds steps Origins sort world source endpoint
  | .nil _, later => later
  | .cons event tail, later => .cons event (append tail later)

theorem nil_append {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    (History.nil source).append history = history := rfl

theorem append_nil {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    history.append (.nil endpoint) = history := by
  induction history with
  | nil => rfl
  | cons event tail ih => exact congrArg (History.cons event) ih

theorem append_assoc {source middle later endpoint : S.Term (worlds.obj world) sort}
    (first : History law worlds steps Origins sort world source middle)
    (second : History law worlds steps Origins sort world middle later)
    (third : History law worlds steps Origins sort world later endpoint) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => rfl
  | cons event tail ih => exact congrArg (History.cons event) (ih second)

theorem actions_append {source middle endpoint : S.Term (worlds.obj world) sort}
    (earlier : History law worlds steps Origins sort world source middle)
    (later : History law worlds steps Origins sort world middle endpoint) :
    (earlier.append later).actions = earlier.actions ++ later.actions := by
  induction earlier with
  | nil => rfl
  | cons event tail ih => simp [append, actions, ih]

theorem origins_append {source middle endpoint : S.Term (worlds.obj world) sort}
    (earlier : History law worlds steps Origins sort world source middle)
    (later : History law worlds steps Origins sort world middle endpoint) :
    (earlier.append later).origins = earlier.origins ++ later.origins := by
  induction earlier with
  | nil => rfl
  | cons event tail ih => simp [append, origins, ih]

/-- Map all actual events along the supplied future-context morphism. -/
noncomputable def map {future : Cᵒᵖ} (change : world ⟶ future) :
    {source endpoint : S.Term (worlds.obj world) sort} →
    History law worlds steps Origins sort world source endpoint →
      History law worlds steps Origins sort future
        (S.rename (worlds.map change) source) (S.rename (worlds.map change) endpoint)
  | _, _, .nil source => .nil (S.rename (worlds.map change) source)
  | _, _, .cons event tail => .cons (EdgeReadout.mapEvent law worlds steps change event)
      (map change tail)

theorem map_append {future : Cᵒᵖ} (change : world ⟶ future)
    {source middle endpoint : S.Term (worlds.obj world) sort}
    (earlier : History law worlds steps Origins sort world source middle)
    (later : History law worlds steps Origins sort world middle endpoint) :
    (earlier.append later).map change = (earlier.map change).append (later.map change) := by
  induction earlier with
  | nil => rfl
  | cons event tail ih =>
      exact congrArg (History.cons (EdgeReadout.mapEvent law worlds steps change event)) (ih later)

theorem actions_map {future : Cᵒᵖ} (change : world ⟶ future)
    {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    (history.map change).actions = history.actions := by
  induction history with
  | nil => rfl
  | cons event tail ih => simp only [map, actions, EdgeReadout.mapEvent, ih]

theorem origins_map {future : Cᵒᵖ} (change : world ⟶ future)
    {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    (history.map change).origins = history.origins := by
  induction history with
  | nil => rfl
  | cons event tail ih => simp only [map, origins, EdgeReadout.mapEvent, ih]

/-- Erasing to the action word still computes the exact supplied endpoint. -/
theorem run_readout {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    PartialActionTree.run (transition law worlds steps sort world)
      source history.actions = some endpoint := by
  induction history with
  | nil => rfl
  | cons event tail ih =>
      change PartialActionTree.run _ event.source (event.action :: tail.actions) = _
      rw [PartialActionTree.run_cons, transition, event.valid, Option.bind_some]
      exact ih

end History

/-- The complete coloured unfolding of the actual operational coalgebra. -/
noncomputable def unfolding (source : S.Term (worlds.obj world) sort) :
    PartialActionTree (Actions sort) (S.Term (worlds.obj world) sort) :=
  PartialActionTree.coiterate (transition law worlds steps sort world) id source

variable {law worlds steps Origins sort world}

/-- Every finite path, successful or not, commutes with actual future-context maps. -/
theorem run_future {future : Cᵒᵖ} (change : world ⟶ future)
    (source : S.Term (worlds.obj world) sort) (path : List (Actions sort)) :
    PartialActionTree.run (transition law worlds steps sort future)
        (S.rename (worlds.map change) source) path =
      (PartialActionTree.run (transition law worlds steps sort world)
        source path).map (S.rename (worlds.map change)) := by
  induction path generalizing source with
  | nil => rfl
  | cons action path ih =>
      rw [PartialActionTree.run_cons, PartialActionTree.run_cons,
        show transition law worlds steps sort future (S.rename (worlds.map change) source) action =
          (transition law worlds steps sort world source action).map (S.rename (worlds.map change)) from
        EdgeReadout.step_map law worlds steps change sort source action]
      cases reading : transition law worlds steps sort world source action with
      | none => rfl
      | some target =>
          simp only [Option.map_some, Option.bind_some]
          exact ih target

/-- The complete independently formed unfoldings satisfy the substitution square. -/
theorem unfolding_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (source : S.Term (worlds.obj world) sort) :
    PartialActionTree.map (S.rename (worlds.map change))
        (unfolding law worlds steps sort world source) =
      unfolding law worlds steps sort future (S.rename (worlds.map change) source) := by
  apply PartialActionTree.ext
  intro path
  simp only [unfolding, PartialActionTree.map_read, PartialActionTree.coiterate_read,
    run_future change, Option.map_id, id_eq]

/-- A retained native event history is a concrete path through the cofree tree. -/
theorem history_unfolding_readout {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    (unfolding law worlds steps sort world source).read history.actions = some endpoint := by
  simp only [unfolding, PartialActionTree.coiterate_read, history.run_readout, Option.map_some, id_eq]

/-- Construct a history from an independently supplied origin and successful path. -/
theorem history_exists_of_run (origin : Origins) (path : List (Actions sort))
    (source endpoint : S.Term (worlds.obj world) sort)
    (success : PartialActionTree.run (transition law worlds steps sort world)
      source path = some endpoint) :
    ∃ history : History law worlds steps Origins sort world source endpoint, history.actions = path := by
  induction path generalizing source with
  | nil =>
      have same : source = endpoint := Option.some.inj success
      subst endpoint
      exact ⟨.nil source, rfl⟩
  | cons action path ih =>
      cases reading : transition law worlds steps sort world source action with
      | none => simp [PartialActionTree.run_cons, reading] at success
      | some target =>
          have later : PartialActionTree.run
              (transition law worlds steps sort world) target path = some endpoint := by
            simpa only [PartialActionTree.run_cons, reading, Option.bind_some] using success
          obtain ⟨tail, word⟩ := ih target later
          let event : EdgeReadout.Event law worlds steps Origins sort world :=
            ⟨origin, source, action, target, reading⟩
          exact ⟨.cons event tail, congrArg (List.cons action) word⟩

/-- With a supplied origin, path success and actual history existence agree in both directions. -/
theorem run_iff_history (origin : Origins) (path : List (Actions sort))
    (source endpoint : S.Term (worlds.obj world) sort) :
    PartialActionTree.run (transition law worlds steps sort world)
        source path = some endpoint ↔
      ∃ history : History law worlds steps Origins sort world source endpoint, history.actions = path := by
  constructor
  · exact history_exists_of_run origin path source endpoint
  · rintro ⟨history, word⟩
    rw [← word]
    exact history.run_readout

/-- The exact endpoint reading survives future-context substitution. -/
theorem history_future_readout {future : Cᵒᵖ} (change : world ⟶ future)
    {source endpoint : S.Term (worlds.obj world) sort}
    (history : History law worlds steps Origins sort world source endpoint) :
    (unfolding law worlds steps sort future (S.rename (worlds.map change) source)).read
      history.actions = some (S.rename (worlds.map change) endpoint) := by
  rw [← history.actions_map change]
  exact history_unfolding_readout (history.map change)

end Mettapedia.OSLF.DeterministicGSOS.NativeHistory
