import Mettapedia.Machines.Cursor.Sequence

/-!
# Demand-triggered memoization is different from moving a choice

The source invokes a total, world-independent builder for each candidate.
The target invokes it on the first requested candidate and retains the value.
Both are actual providers of the existing cursor protocol. Cache correctness
is earned by construction and erased as proof data, not tested by another
runtime evaluation of the builder.

The cached value may be an immutable description of all alternatives. Sharing
that description does not select one alternative for every candidate. The
metric counts builder invocations, not its internal cost, allocations, fuel or
elapsed time. Stateful, generative and context-dependent builders need another
qualification; surface closure alone does not establish these hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetMemoization

variable {Row Value : Type}

structure Cell (build : Unit → Value) where
  saved : Option Value
  correct : ∀ value, saved = some value → value = build ()

def emptyCell (build : Unit → Value) : Cell build := by
  refine ⟨none, ?_⟩
  intro value impossible
  cases impossible

def fullCell (build : Unit → Value) : Cell build :=
  let value := build ()
  ⟨some value, fun _ equal => (Option.some.inj equal).symm⟩

def repeated (build : Unit → Value) : Provider (Sequence.protocol (Row × Value)) where
  State _ _ := List Row
  step rows _ := match rows with
    | [] => ⟨none, []⟩
    | row :: later => ⟨some (row, build ()), later⟩

def memoized (build : Unit → Value) : Provider (Sequence.protocol (Row × Value)) where
  State _ _ := List Row × Cell build
  step state _ := match state.1 with
    | [] => ⟨none, state⟩
    | row :: later => match state.2.saved with
      | some value => ⟨some (row, value), (later, state.2)⟩
      | none =>
          let value := build ()
          let built : Cell build := ⟨some value, fun _ equal => (Option.some.inj equal).symm⟩
          ⟨some (row, value), (later, built)⟩

def refinement (build : Unit → Value) : Hom (memoized (Row := Row) build) (repeated build) where
  map state := state.1
  step state request := by
    rcases state with ⟨rows, cell⟩
    cases rows with
    | nil => rfl
    | cons row later =>
        cases saved : cell.saved with
        | none => simp [memoized, repeated, saved]
        | some value =>
            simp only [memoized, repeated, saved, cell.correct value saved]

def repeatedCalls (build : Unit → Value) : Charge (repeated (Row := Row) build) :=
  fun rows _ => if rows.isEmpty then 0 else 1

def memoizedCalls (build : Unit → Value) : Charge (memoized (Row := Row) build) :=
  fun state _ => if state.1.isEmpty || state.2.saved.isSome then 0 else 1

def credit (build : Unit → Value) : Potential (memoized (Row := Row) build) :=
  fun state => if state.2.saved.isSome then 0 else 1

def start (build : Unit → Value) (rows : List Row) : (memoized (Row := Row) build).State () () :=
  (rows, emptyCell build)

/-- All ordered replies, duplicates and suspended continuations survive.
The consumer may decide its next request after inspecting previous results. -/
theorem observation {Return : Unit → Unit → Type} (build : Unit → Value)
    (C : Client (P := Sequence.protocol (Row × Value)) (Return := Return))
    (fuel : Nat) (state : Packet (memoized build) C ()) :
    (refinement build).outcome C
        (advance (memoized build) C (memoizedCalls build) fuel state).2 =
      (advance (repeated build) C (repeatedCalls build) fuel
        ((refinement build).packet C state)).2 :=
  Hom.advance C (refinement build) _ _ fuel state

/-- The actual saved-cell transition, rather than a supplied global bound,
accounts for the one possible future builder invocation. -/
theorem at_most_one_local (build : Unit → Value) :
    Amortized (refinement (Row := Row) build) (memoizedCalls build)
      (fun _ _ => 0) (credit build) := by
  intro base index state request
  rcases state with ⟨rows, cell⟩
  cases rows with
  | nil => simp only [memoizedCalls, memoized, credit, List.isEmpty_nil, Bool.true_or, ↓reduceIte,
      Nat.zero_add]; exact le_rfl
  | cons row later =>
      cases saved : cell.saved <;>
        simp [memoizedCalls, memoized, credit, saved]

theorem builder_calls_le_one {Return : Unit → Unit → Type} (build : Unit → Value)
    (C : Client (P := Sequence.protocol (Row × Value)) (Return := Return))
    (fuel : Nat) (state : Packet (memoized build) C ()) :
    (advance (memoized build) C (memoizedCalls build) fuel state).1 ≤ 1 := by
  have bound := advance_amortized C (refinement build) (memoizedCalls build)
    (fun _ _ => 0) (credit build) (at_most_one_local build) fuel state
  have zero : (advance (repeated build) C (fun _ _ => 0) fuel
      ((refinement build).packet C state)).1 = 0 := by
    generalize input : (refinement build).packet C state = packet
    clear input bound
    induction fuel generalizing packet with
    | zero => rfl
    | succ fuel ih =>
        rcases packet with ⟨index, control, rows⟩
        cases layer : C.str () index control with
        | mk shape children =>
            cases shape with
            | inl result => simp [advance, layer]
            | inr request =>
                simp only [advance, layer]
                simpa only [Nat.zero_add] using ih _
  rw [zero] at bound
  have initial : credit build state.2.2 ≤ 1 := by unfold credit; split <;> omega
  omega

theorem no_builder_without_candidate (build : Unit → Value) (cell : Cell build) :
    @memoizedCalls Row Value build () () ([], cell) () = 0 := rfl

theorem calls_dominate_locally (build : Unit → Value) :
    Amortized (refinement (Row := Row) build) (memoizedCalls build)
      (repeatedCalls build) (fun _ => 0) := by
  intro base index state request
  rcases state with ⟨rows, cell⟩
  cases rows with
  | nil => simp [memoizedCalls, repeatedCalls, refinement]
  | cons row later =>
      cases saved : cell.saved <;>
        simp [memoizedCalls, repeatedCalls, refinement, saved]

/-- Demand-triggered memoization never adds a builder invocation, including
zero candidates and clients which stop after their first requested row. -/
theorem calls_le_source {Return : Unit → Unit → Type} (build : Unit → Value)
    (C : Client (P := Sequence.protocol (Row × Value)) (Return := Return))
    (fuel : Nat) (state : Packet (memoized build) C ()) :
    (advance (memoized build) C (memoizedCalls build) fuel state).1 ≤
      (advance (repeated build) C (repeatedCalls build) fuel
        ((refinement build).packet C state)).1 :=
  advance_cost_le C (refinement build) (memoizedCalls build) (repeatedCalls build)
    (fun _ => 0) (calls_dominate_locally build) fuel state rfl

/-- Cache inspection is a separate coordinate: fewer builder invocations
alone do not prove lower instruction count or lower latency. -/
def cacheTests (build : Unit → Value) : Charge (memoized (Row := Row) build) :=
  fun state _ => if state.1.isEmpty then 0 else 1

def priced (build : Unit → Value) (builderPrice checkPrice writePrice : Nat) :
    Charge (memoized (Row := Row) build) := fun state request =>
  builderPrice * memoizedCalls build state request +
    checkPrice * cacheTests build state request +
    writePrice * memoizedCalls build state request

theorem first_request_price (build : Unit → Value) (row : Row) (later : List Row)
    (builderPrice checkPrice writePrice : Nat) :
    @priced Row Value build builderPrice checkPrice writePrice () ()
      (start build (row :: later)) () = builderPrice + checkPrice + writePrice := by
  simp [priced, memoizedCalls, cacheTests, start, emptyCell]

/-- With positive administration prices, this generic cache can be dearer
at the first request. A one-demand specialization may erase it instead. -/
theorem first_request_can_cost_more (build : Unit → Value) (row : Row) (later : List Row)
    (builderPrice checkPrice writePrice : Nat) (overhead : 0 < checkPrice + writePrice) :
    builderPrice < @priced Row Value build builderPrice checkPrice writePrice () ()
      (start build (row :: later)) () := by
  rw [first_request_price]
  omega

end Mettapedia.Machines.Cursor.LetMemoization
