import Mettapedia.Languages.MeTTa.TermView

/-!
# Retained candidate selections

An indexed consumer reads occurrences from an immutable catalog as needed.
The reference first copies the selected records and then consumes that list.
The two executions below are defined independently. Their equality retains
duplicate occurrences and the consumer's monadic sequencing, including state
and failure. The catalog must remain immutable throughout consumption.

This is a representation theorem, not a verification of C reference counting
or of a particular evaluator's instantiation of the consumer.
-/

namespace Mettapedia.Languages.MeTTa.CandidateSelectionRefinement

universe u v w z

/-- Consume selected occurrences directly, without constructing a record list. -/
def consumeSelection {Item : Type u} {State : Type v} {Index : Type w}
    {m : Type v → Type z} [Monad m]
    (step : State → Item → m State) (catalog : Index → Item) :
    List Index → State → m State
  | [], state => pure state
  | index :: rest, state => do
      let next ← step state (catalog index)
      consumeSelection step catalog rest next

/-- Direct indexed execution equals copying occurrences before execution.
No purity restriction is placed on the monadic consumer. -/
theorem consumeSelection_eq_materialized
    {Item : Type u} {State : Type v} {Index : Type w}
    {m : Type v → Type z} [Monad m]
    (step : State → Item → m State) (catalog : Index → Item)
    (indices : List Index) (state : State) :
    consumeSelection step catalog indices state =
      (indices.map catalog).foldlM step state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      simp only [consumeSelection, List.map_cons, List.foldlM_cons]
      simp only [ih]

/-- Selecting through an index map composes that map with the catalog lookup.
This preserves repeated indices rather than converting them into a set. -/
theorem consumeSelection_reindex
    {Item : Type u} {State : Type v} {Index NextIndex : Type w}
    {m : Type v → Type z} [Monad m]
    (step : State → Item → m State) (catalog : Index → Item)
    (select : NextIndex → Index) (indices : List NextIndex) (state : State) :
    consumeSelection step catalog (indices.map select) state =
      consumeSelection step (catalog ∘ select) indices state := by
  simp only [consumeSelection_eq_materialized, List.map_map]

/-- Changes outside the selected occurrences do not affect execution. -/
theorem consumeSelection_agrees_on
    {Item : Type u} {State : Type v} {Index : Type w}
    {m : Type v → Type z} [Monad m]
    (step : State → Item → m State) (left right : Index → Item)
    (indices : List Index) (state : State)
    (agree : ∀ index ∈ indices, left index = right index) :
    consumeSelection step left indices state =
      consumeSelection step right indices state := by
  rw [consumeSelection_eq_materialized, consumeSelection_eq_materialized]
  congr 1
  exact List.map_congr_left agree

/-- A live catalog supports indexed reads; an escaped projection owns precisely
its selected occurrence list after the catalog retires. -/
inductive CandidateView (Item : Type u) (Index : Type w) where
  | indexed (catalog : Index → Item) (indices : List Index)
  | owned (items : List Item)

/-- Retirement copies selected occurrences, including repeated indices. -/
def CandidateView.promote {Item : Type u} {Index : Type w} :
    CandidateView Item Index → CandidateView Item Index
  | .indexed catalog indices => .owned (indices.map catalog)
  | .owned items => .owned items

def CandidateView.consume {Item : Type u} {Index : Type w} {State : Type v}
    {m : Type v → Type z} [Monad m] (step : State → Item → m State) :
    CandidateView Item Index → State → m State
  | .indexed catalog indices, state => consumeSelection step catalog indices state
  | .owned items, state => items.foldlM step state

/-- Promotion changes the ownership representation without changing stateful
consumption, including the first fault and any effects retained in the monad. -/
theorem CandidateView.consume_promote
    {Item : Type u} {Index : Type w} {State : Type v}
    {m : Type v → Type z} [Monad m] (step : State → Item → m State)
    (view : CandidateView Item Index) (state : State) :
    view.promote.consume step state = view.consume step state := by
  cases view with
  | indexed catalog indices =>
      exact (consumeSelection_eq_materialized step catalog indices state).symm
  | owned items => rfl

/-- The same law applies to the existing occurrence-qualified term views.
Forcing selected views may be delayed until their consumer reads them. -/
theorem consumeTermViews_eq_materialized
    {Owner Revision Occurrence Plan Physical Update : Type}
    {store : Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra.BindingStore
      Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation.OpenEnvironment
      Physical Update}
    {projection : TermViewCompilation.PlanProjection Revision Occurrence Plan}
    {State Index : Type} {m : Type → Type} [Monad m]
    (step : State → Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation.OpenTerm → m State)
    (catalog : Index → TermViewCompilation.TermView
      Owner Revision Occurrence Plan Physical Update store projection)
    (indices : List Index) (state : State) :
    consumeSelection step (fun index => (catalog index).force) indices state =
      (indices.map fun index => (catalog index).force).foldlM step state :=
  consumeSelection_eq_materialized step _ indices state

/-- Repeated occurrences remain observable to a stateful counting consumer. -/
example : consumeSelection (m := Id) (fun (n value : Nat) => pure (n + value))
    (fun n : Nat => n + 1) [0, 0, 1] 0 = 4 := by rfl

/-- Deduplicating the selection would change that observation. -/
example : consumeSelection (m := Id) (fun (n value : Nat) => pure (n + value))
    (fun n : Nat => n + 1) [0, 0, 1] 0 ≠
    consumeSelection (m := Id) (fun (n value : Nat) => pure (n + value))
      (fun n : Nat => n + 1) [0, 1] 0 := by
  change (4 : Nat) ≠ 3
  decide

/-- A fault retains the state at the fault; later candidates are not consumed. -/
example : consumeSelection (m := Except (List Nat))
    (fun seen value => if value = 2 then .error (seen ++ [value])
      else .ok (seen ++ [value]))
    (fun n : Nat => n) [1, 2, 3] [] = .error [1, 2] := by decide

end Mettapedia.Languages.MeTTa.CandidateSelectionRefinement
