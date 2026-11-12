import Mettapedia.Machines.Cursor.LetChoicePackets
import Mathlib.Data.List.Perm.Basic

/-!
# Outer and inner let placement

These are different compositions of the existing shared-world search. Outer
evaluation precedes candidate generation and shares the selected value across
that call. Inner evaluation occurs after each candidate has supplied bindings.
The laws compare constructed programs, rather than choosing a phase by fiat.

Pure singleton hoisting is valid for arbitrary candidate searches and
continuations. It is sufficient, not a universal necessary condition: one
known candidate allows arbitrary code, and bag observations can admit a
permutation of independent nondeterministic choices. Neither law erases
ordered observations, effects, or collection boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetPlacement

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

variable {World Row Value Answer : Type}

def yieldOne (value : Value) : Search World Value := fun world =>
  .answer value world .done

theorem yieldOne_eq_superpose (value : Value) :
    (yieldOne value : Search World Value) = Search.superpose [value] := by
  funext world
  simp [yieldOne, Search.superpose]

def outer (candidates : Search World Row) (code : Search World Value)
    (body : Row → Value → Search World Answer) : Search World Answer :=
  code.bind (fun value => candidates.bind (fun row => body row value))

def inner (candidates : Search World Row) (code : Row → Search World Value)
    (body : Row → Value → Search World Answer) : Search World Answer :=
  candidates.bind (fun row => (code row).bind (body row))

theorem append_done (trace : Trace World Answer) : trace.append .done = trace := by
  induction trace with
  | done world => rfl
  | answer value world later ih =>
      simp only [Trace.append]
      congr 1
      funext next
      exact ih next

theorem yield_bind (value : Value) (body : Value → Search World Answer) :
    (yieldOne value).bind body = body value := by
  funext world
  simp only [Search.bind, yieldOne, Trace.bind, append_done]

/-- Exactly one total, world-independent value can move across arbitrary
candidate generation and continuation effects, preserving the whole trace. -/
theorem singleton_hoist (candidates : Search World Row) (value : Value)
    (body : Row → Value → Search World Answer) :
    inner candidates (fun _ => yieldOne value) body = outer candidates (yieldOne value) body := by
  unfold inner outer
  simp only [yield_bind]

/-- Syntactic closure is not necessary: a row expression may have an earned
constant value even though the row occurs in its syntax. -/
theorem row_invariant_hoist (candidates : Search World Row) (expression : Row → Value)
    (value : Value) (invariant : ∀ row, expression row = value)
    (body : Row → Value → Search World Answer) :
    inner candidates (fun row => yieldOne (expression row)) body =
      outer candidates (yieldOne value) body := by
  simpa only [invariant] using singleton_hoist candidates value body

/-- A pure, known singleton candidate removes the placement distinction
even for an effectful or nondeterministic producer. -/
theorem one_candidate_hoist (row : Row) (code : Search World Value)
    (body : Row → Value → Search World Answer) :
    inner (yieldOne row) (fun _ => code) body = outer (yieldOne row) code body := by
  unfold inner outer
  simp only [yield_bind]

theorem superpose_append (left right : List Value) (world : World) :
    (Search.superpose left world).append (Search.superpose right) =
      Search.superpose (left ++ right) world := by
  induction left generalizing world with
  | nil => rfl
  | cons value rest ih =>
      simp only [Search.superpose, Trace.append, List.cons_append]
      congr 1
      funext next
      exact ih next

theorem superpose_bind (values : List Value) (choices : Value → List Answer) :
    (Search.superpose values : Search World Value).bind
        (fun value => Search.superpose (choices value)) =
      Search.superpose (values.flatMap choices) := by
  funext world
  induction values generalizing world with
  | nil => rfl
  | cons value rest ih =>
      simp only [Search.bind, Search.superpose, Trace.bind, List.flatMap_cons]
      change (Search.superpose (choices value) world).append
        (fun next => (Search.superpose rest next).bind
          (fun selected => Search.superpose (choices selected))) = _
      have tailEq : (fun next : World => (Search.superpose rest next).bind
          (fun selected => Search.superpose (choices selected))) =
          Search.superpose (rest.flatMap choices) := by
        funext next
        exact ih next
      rw [tailEq, superpose_append]

def innerMatrix (rows : List Row) (values : List Value) (combine : Row → Value → Answer) :
    List Answer := rows.flatMap (fun row => values.map (combine row))

def outerMatrix (rows : List Row) (values : List Value) (combine : Row → Value → Answer) :
    List Answer := values.flatMap (fun value => rows.map (fun row => combine row value))

theorem inner_matrix_source (rows : List Row) (values : List Value)
    (combine : Row → Value → Answer) :
    inner (Search.superpose rows) (fun _ => Search.superpose values)
        (fun row value => yieldOne (combine row value)) =
      (Search.superpose (innerMatrix rows values combine) : Search World Answer) := by
  have each (row : Row) :
      (Search.superpose values : Search World Value).bind
        (fun value => yieldOne (combine row value)) = Search.superpose (values.map (combine row)) := by
    simpa only [yieldOne_eq_superpose, ← List.map_eq_flatMap] using
      superpose_bind (World := World) values (fun value => [combine row value])
  simp only [inner, each]
  exact superpose_bind rows (fun row => values.map (combine row))

theorem outer_matrix_source (rows : List Row) (values : List Value)
    (combine : Row → Value → Answer) :
    outer (Search.superpose rows) (Search.superpose values)
        (fun row value => yieldOne (combine row value)) =
      (Search.superpose (outerMatrix rows values combine) : Search World Answer) := by
  have each (value : Value) :
      (Search.superpose rows : Search World Row).bind
        (fun row => yieldOne (combine row value)) =
          Search.superpose (rows.map (fun row => combine row value)) := by
    simpa only [yieldOne_eq_superpose, ← List.map_eq_flatMap] using
      superpose_bind (World := World) rows (fun row => [combine row value])
  simp only [outer, each]
  exact superpose_bind values (fun value => rows.map (fun row => combine row value))

/-- Independent pure alternatives can exchange enumeration axes under a bag
observation. The theorem does not identify their ordered streams. -/
theorem matrix_bag_agreement (rows : List Row) (values : List Value)
    (combine : Row → Value → Answer) :
    (innerMatrix rows values combine).Perm (outerMatrix rows values combine) := by
  induction rows with
  | nil => simp [innerMatrix, outerMatrix]
  | cons row rest ih =>
      change (values.map (combine row) ++ innerMatrix rest values combine).Perm
        (values.flatMap (fun value => combine row value :: rest.map (fun item => combine item value)))
      exact (ih.append_left _).trans (List.map_append_flatMap_perm values (combine row)
        (fun value => rest.map (fun item => combine item value)))

namespace Controls

def pairBody (row value : Nat) : Search Nat (Nat × Nat) := yieldOne (row, value)
def touch : Search Nat Nat := fun world => .answer 7 (world + 1) .done
def readState : Search Nat Nat := fun world => .answer world world .done
def incrementBody (row value : Nat) (world : Nat) : Trace Nat (Nat × Nat) :=
  .answer (row, value) (world + 1) .done

theorem outer_and_inner_effect_counts :
    (outer (Search.superpose [10, 20]) touch pairBody 0).drain = ([(10, 7), (20, 7)], 1) ∧
      (inner (Search.superpose [10, 20]) (fun _ => touch) pairBody 0).drain =
        ([(10, 7), (20, 7)], 2) := by decide

theorem zero_candidates_do_not_run_inner_code :
    (outer (Search.superpose []) touch pairBody 0).drain = ([], 1) ∧
      (inner (Search.superpose []) (fun _ => touch) pairBody 0).drain = ([], 0) := by decide

theorem read_only_is_not_stable_under_body_writes :
    (outer (Search.superpose [10, 20]) readState incrementBody 0).drain =
      ([(10, 0), (20, 0)], 2) ∧
      (inner (Search.superpose [10, 20]) (fun _ => readState) incrementBody 0).drain =
        ([(10, 0), (20, 1)], 2) := by decide

theorem an_open_expression_can_hoist (candidates : Search Nat Nat)
    (body : Nat → Nat → Search Nat Answer) :
    inner candidates (fun row => yieldOne (row - row + 7)) body =
      outer candidates (yieldOne 7) body := by
  exact row_invariant_hoist candidates (fun row => row - row + 7) 7 (by simp) body

theorem nondeterministic_order_differs :
    innerMatrix [10, 20] [1, 2] Prod.mk = [(10, 1), (10, 2), (20, 1), (20, 2)] ∧
      outerMatrix [10, 20] [1, 2] Prod.mk = [(10, 1), (20, 1), (10, 2), (20, 2)] := by decide

theorem duplicate_choices_are_preserved :
    innerMatrix [10, 10] [7, 7] Prod.mk = outerMatrix [10, 10] [7, 7] Prod.mk ∧
      (innerMatrix [10, 10] [7, 7] Prod.mk).length = 4 := by decide

def filteredBody (row value : Nat) : Search Nat (Nat × Nat) :=
  if (row == 10 && value == 2) || (row == 20 && value == 1) then yieldOne (row, value)
  else Search.superpose []

theorem first_answer_can_distinguish_pure_choice_order :
    (Search.once (inner (Search.superpose [10, 20]) (fun _ => Search.superpose [1, 2])
      filteredBody) 0).drain = ([(10, 2)], 0) ∧
      (Search.once (outer (Search.superpose [10, 20]) (Search.superpose [1, 2])
        filteredBody) 0).drain = ([(20, 1)], 0) := by decide

def collect (source : Search World Answer) : Search World (List Answer) := fun world =>
  let gathered := (source world).drain
  .answer gathered.1 gathered.2 .done

theorem collection_boundaries_distinguish_hoisting :
    ((Search.superpose [1, 2]).bind (fun value =>
      collect ((Search.superpose [10, 20]).bind (fun row => pairBody row value))) 0).drain.1 =
        [[(10, 1), (20, 1)], [(10, 2), (20, 2)]] ∧
      (collect (inner (Search.superpose [10, 20]) (fun _ => Search.superpose [1, 2])
        pairBody) 0).drain.1 = [[(10, 1), (10, 2), (20, 1), (20, 2)]] := by decide

def classifiedByClosure (closed : Bool) : Search Nat (Nat × Nat) :=
  if closed then outer (Search.superpose [10, 20]) touch pairBody
  else inner (Search.superpose [10, 20]) (fun _ => touch) pairBody

theorem closure_only_dispatch_is_not_uniform :
    (classifiedByClosure true 0).drain.2 = 1 ∧
      (classifiedByClosure false 0).drain.2 = 2 := by decide

def rowIfPresent : Search Bool Nat := fun present =>
  if present then .answer 10 present .done else .done present

def removeThenValue : Search Bool Nat := fun _ => .answer 7 false .done

/-- A singleton observed before executing the code is not the same as a
fixed pure candidate source: the code may destroy that candidate. -/
theorem one_initial_match_does_not_license_hoisting :
    (outer rowIfPresent removeThenValue
      (fun row value => yieldOne (row, value)) true).drain = ([], false) ∧
      (inner rowIfPresent (fun _ => removeThenValue)
        (fun row value => yieldOne (row, value)) true).drain = ([(10, 7)], false) := by decide

end Controls

end Mettapedia.Machines.Cursor.LetPlacement
