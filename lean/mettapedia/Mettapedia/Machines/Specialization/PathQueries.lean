import Mettapedia.Machines.Specialization.PathJoin
import Mettapedia.Machines.Cursor.EntryQueryTree

/-!
# Compiled paths in the ordered query algebra

These queries have fixed entry reads and a deterministic match on the
incoming key of a row. The observer keeps an exact row witness, in
authored order. A terminal predicate may reject a completed witness.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.PathQueries

open Mettapedia.Machines.Cursor.EntryQueryTree
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open PathJoin

variable {Key Row Space World : Type}

private theorem bind_answers {A B : Type} (values : List A) (following : A → List B) :
    (Search.superpose values : Search World A).bind (fun value => Search.superpose (following value)) =
      Search.superpose (values.flatMap following) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    funext world
    change (Search.superpose (following first) world).append
      ((Search.superpose rest).bind (fun value => Search.superpose (following value))) = _
    rw [ih]
    exact congrFun (append_superpose (following first) (rest.flatMap following)) world

def query (first : Space) : List Space → Query Space Unit
  | [] => .atom first ()
  | next :: rest => .seq (.atom first ()) (query next rest)

theorem dependencies_query (first : Space) (rest : List Space) :
    dependencies (query first rest) = first :: rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next later ih => simp [query, dependencies, ih]

variable [DecidableEq Key] (keys : EdgeKeys Key Row)

def matchRow (_ : Unit) (row : Row) (state : Key × List Row) : List (Key × List Row) :=
  if keys.source row = state.1 then [(keys.target row, state.2 ++ [row])] else []

def accept (finish : Key → Bool) (state : Key × List Row) : List (List Row) :=
  if finish state.1 then [state.2] else []

private theorem read_then {A : Type} (rows : List Row) (target : Key) (history : List Row)
    (following : Key × List Row → List A) :
    (rows.flatMap fun row => (matchRow keys () row (target, history)).flatMap following) =
      (rows.filter fun row => decide (keys.source row = target)).flatMap
        (fun row => following (keys.target row, history ++ [row])) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [List.flatMap_cons, ih]
    by_cases ready : keys.source row = target
    · simp [matchRow, ready]
    · simp [matchRow, ready]

theorem reference_query (entry : Space → List Row) (finish : Key → Bool)
    (first : Space) (rest : List Space) (start : Key) (history : List Row) :
    (evaluate (matchRow keys) entry (query first rest) (start, history)).flatMap (accept finish) =
      (reference keys finish ((first :: rest).map entry) start).map (history ++ ·) := by
  induction rest generalizing first start history with
  | nil =>
    simp only [query, evaluate, List.flatMap_assoc, read_then, List.map_cons,
      List.map_nil, reference_cons, List.map_flatMap]
    apply List.flatMap_congr
    intro row _
    by_cases ready : finish (keys.target row) = true
    · simp [accept, reference, paths, ready]
    · simp [accept, reference, paths, ready]
  | cons next later ih =>
    simp only [query, evaluate, List.flatMap_assoc, read_then, List.map_cons,
      reference_cons, List.map_flatMap]
    apply List.flatMap_congr
    intro row _
    rw [ih next (keys.target row) (history ++ [row])]
    simp [reference_cons, List.map_map, List.map_flatMap, Function.comp_def, List.append_assoc]

/-- With a retained entry read, a compiled path implements the full
ordered continuation observation, including the world's visibility at
every yielded answer. -/
theorem prepared_stream (tables : Tables Key Row)
    (entry : Space → List Row) (live : World → Space → List Row) (finish : Key → Bool)
    (first : Space) (rest : List Space) (start : Key) (history : List Row)
    (covers : ∀ world space, space ∈ first :: rest → live world space = entry space) :
    (stream (matchRow keys) live (query first rest) (start, history)).bind
        (fun state => Search.superpose (accept finish state)) =
      let indexes := (prepare keys tables finish ((first :: rest).map entry)).1
      Search.superpose ((execute keys tables finish indexes start).map (history ++ ·)) := by
  have covered : ∀ world space, space ∈ dependencies (query first rest) → live world space = entry space := by
    simpa only [dependencies_query] using covers
  rw [stream_entry _ entry live _ covered]
  rw [bind_answers (World := World) _ (accept finish), reference_query]
  exact congrArg (fun answers => Search.superpose (answers.map (history ++ ·)))
    ((prepare_correct keys tables finish ((first :: rest).map entry)).2 start).symm

namespace Controls

private def edges : EdgeKeys Nat (Nat × Nat) := ⟨Prod.fst, Prod.snd⟩

private def readership (openStore right : Bool) : List (Nat × Nat) :=
  if right then if openStore then [(1, 2)] else [] else [(0, 1), (0, 1)]

private def afterEdit (trace : Trace Bool (List (Nat × Nat))) : List (List (Nat × Nat)) :=
  match trace with
  | .done _ => []
  | .answer _ _ resume => (resume false).drain.1

theorem a_live_edit_after_yield_can_remove_a_later_answer :
    let scan := stream (matchRow edges) readership (query false [true]) (0, [])
    let live := scan.bind (fun row => Search.superpose (accept (fun _ => true) row))
    let captured := prepare edges functional (fun _ => true) ([(false : Bool), true].map (readership true))
    let prepared := Search.superpose (execute edges functional (fun _ => true) captured.1 0)
    afterEdit (live true) = [] ∧ afterEdit (prepared true) = [[(0, 1), (1, 2)]] := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.PathQueries
