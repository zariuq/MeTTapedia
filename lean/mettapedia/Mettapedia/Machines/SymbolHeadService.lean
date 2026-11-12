import Mettapedia.Machines.SymbolHeadMemo
import Mettapedia.Machines.Cursor.QueryCore

/-!
# Scoped head recognition with a bounded memo and table lifecycle

The table-family cache and exact-key memo form one service. A rebuild resets
the memo; inserting a new name preserves already compiled positions. Its
representation invariant is established by cold construction and preserved
by every service command. The independent reference resolves names directly.

The verified-state adapter erases proof fields and supplies the existing
cursor protocol. Equal declared command tariffs compare inspection prefixes,
not the native cost of interning or recognition. Raw head queries address the
current table; retained references use SymbolTableHeadCache's owned interface.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SymbolHeadService

open SymbolTableHeadCache SymbolHeadMemo BoundedAdmissionCache

variable {Name Query : Type} [DecidableEq Name] {k : Nat}

structure State (Name : Type) (k : Nat) where
  table : Table Name
  compiled : Option (Cache k)
  memo : Memo k

def Valid (names : Fin k → Name) (state : State Name k) : Prop :=
  (∀ cache, state.compiled = some cache →
    Good state.table names cache ∧ ValidBanks (compute cache) state.memo) ∧
  Bounded 1 state.memo

def cold (table : Table Name) : State Name k := ⟨table, none, empty⟩

def rebuild (table : Table Name) (names : Fin k → Name) : State Name k :=
  ⟨table, compile table names, empty⟩

omit [DecidableEq Name] in
theorem cold_valid (table : Table Name) (names : Fin k → Name) : Valid names (cold table) := by
  constructor
  · intro cache found
    cases found
  · intro bank
    simp [cold, empty]

theorem rebuild_valid (table : Table Name) (names : Fin k → Name) :
    Valid names (rebuild table names) := by
  constructor
  · intro cache found
    exact ⟨compile_good table names cache found, empty_good cache⟩
  · intro bank
    simp [rebuild, empty]

def inspect (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (head : Nat) (question : Query) : Bool × State Name k :=
  match state.compiled with
  | some cache =>
      if cache.owner = state.table.owner then
        (lookup cache permits state.memo head question,
          { state with memo := retainHead cache state.memo head })
      else (source state.table names permits head question, rebuild state.table names)
  | none => (source state.table names permits head question, rebuild state.table names)

theorem inspect_valid (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (head : Nat) (question : Query) :
    Valid names (inspect names permits state head question).2 := by
  cases compiled : state.compiled with
  | none => simpa [inspect, compiled] using rebuild_valid state.table names
  | some cache =>
      obtain ⟨good, memo⟩ := valid.1 cache compiled
      simp only [inspect, compiled, good.1, ↓reduceIte]
      constructor
      · intro retained found
        have same : cache = retained := by simpa [compiled] using found
        subst retained
        exact ⟨good, retain_good cache state.memo memo head⟩
      · exact retain_bounded cache state.memo valid.2 head

theorem inspect_square (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (head : Nat) (question : Query) :
    ((inspect names permits state head question).1,
      (inspect names permits state head question).2.table) =
        (source state.table names permits head question, state.table) := by
  cases compiled : state.compiled with
  | none => simp [inspect, compiled, rebuild]
  | some cache =>
      obtain ⟨good, memo⟩ := valid.1 cache compiled
      simp [inspect, compiled, good.1,
        scoped_lookup_exact state.table names permits cache good state.memo memo head question]

def step (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) : Command Name Query → Reply × State Name k
  | .inspect head question =>
      let next := inspect names permits state head question
      (.classified next.1, next.2)
  | .intern name =>
      let next := insertName state.table name
      (.interned (next.words.idxOf name + 1), { state with table := next })
  | .recreate address words => (.recreated, cold (recreate state.table address words))

theorem step_valid (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (command : Command Name Query) :
    Valid names (step names permits state command).2 := by
  cases command with
  | inspect head question => exact inspect_valid names permits state valid head question
  | intern name =>
      refine ⟨?_, valid.2⟩
      intro cache found
      obtain ⟨good, memo⟩ := valid.1 cache found
      exact ⟨insertion_preserves_cache state.table names cache good name, memo⟩
  | recreate address words => exact cold_valid _ names

theorem service_square (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (command : Command Name Query) :
    sourceStep names permits state.table command =
      ((step names permits state command).1, (step names permits state command).2.table) := by
  cases command with
  | inspect head question =>
      exact congrArg (fun observed => (Reply.classified observed.1, observed.2))
        (inspect_square names permits state valid head question).symm
  | intern name => rfl
  | recreate address words => rfl

theorem adaptive_exact (names : Fin k → Name) (permits : Fin k → Query → Bool)
    {Answer : Type} (program : ReadOnlyQuery.Program (Command Name Query) Reply Answer)
    (state : State Name k) (valid : Valid names state) :
    QueryState.run (sourceStep names permits) program state.table =
      OperatorChoice.ObserverContracts.eraseObservation State.table
        (QueryState.run (step names permits) program state) :=
  OperatorChoice.ObserverContracts.run_erasure_on
    (step names permits) (sourceStep names permits) State.table (Valid names)
    (fun current good command => step_valid names permits current good command)
    (fun current good command => service_square names permits current good command)
    program state valid

def checkedStep (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : { state : State Name k // Valid names state }) (command : Command Name Query) :
    Reply × { state : State Name k // Valid names state } :=
  let next := step names permits state.val command
  (next.1, ⟨next.2, step_valid names permits state.val state.property command⟩)

open Cursor.ReadOnlyQuery

def simulation (names : Fin k → Name) (permits : Fin k → Query → Bool) :
    Cursor.Hom (Sampled.provider (checkedStep names permits))
      (Sampled.provider (sourceStep names permits)) where
  map saved := (saved.1.val.table, saved.2)
  step saved command := by
    rcases saved with ⟨state, reads⟩
    have same := service_square names permits state.val state.property command
    simp only [Sampled.provider, checkedStep]
    rw [same]

theorem prefix_exact (names : Fin k → Name) (permits : Fin k → Query → Bool)
    {Answer : Type} (price : Command Name Query → Nat) (fuel : Nat)
    (program : ReadOnlyQuery.Program (Command Name Query) Reply Answer)
    (state : { state : State Name k // Valid names state })
    (reads : ReadOnlyQuery.Reads (Command Name Query) Reply) :
    let observed := Sampled.advance (checkedStep names permits) price fuel program state reads
    (observed.1, (simulation names permits).outcome client observed.2) =
      Sampled.advance (sourceStep names permits) price fuel program state.val.table reads := by
  exact (simulation names permits).advance_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel _

theorem resume_exact (names : Fin k → Name) (permits : Fin k → Query → Bool)
    {Answer : Type} (price : Command Name Query → Nat) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (Sampled.provider (checkedStep names permits))
      (client (Answer := Answer)) PUnit.unit) :
    let resumed := Sampled.resume (checkedStep names permits) price fuel previous
    (resumed.1, (simulation names permits).outcome client resumed.2) =
      Sampled.resume (sourceStep names permits) price fuel
        (previous.1, (simulation names permits).outcome client previous.2) := by
  exact (simulation names permits).resume_account client
    (Sampled.charge _ price) (Sampled.charge _ price) (fun _ _ => rfl) fuel previous

namespace Controls

def names := SymbolTableHeadCache.Controls.names
def permits := SymbolTableHeadCache.Controls.permits
def original := SymbolTableHeadCache.Controls.original
def replaced := SymbolTableHeadCache.Controls.replaced
def oldCache := SymbolTableHeadCache.Controls.retained
def oldMemo := retainHead oldCache empty 1
def nextCache : Cache 1 := ⟨replaced.owner, fun _ => 2⟩

theorem carrying_the_old_memo_changes_meaning :
    lookup nextCache permits oldMemo 1 2 = true ∧
      source replaced names permits 1 2 = false := by decide

def lifecycle : ReadOnlyQuery.Program (Command String Nat) Reply (List Reply) :=
  .read (.inspect 1 2) fun first =>
    .read (.inspect 1 2) fun warm =>
      .read (.recreate 9 ["other", "worker"]) fun _ =>
        .read (.inspect 1 2) fun next =>
          .read (.inspect 2 2) fun moved => .pure [first, warm, next, moved]

theorem recreation_resets_both_caches :
    (QueryState.run (step names permits) lifecycle (cold original)).answer =
      [.classified true, .classified true, .classified false, .classified true] := by decide

theorem missing_name_can_be_interned_after_a_negative_answer :
    (QueryState.run (step names permits) SymbolTableHeadCache.Controls.lifecycle
      (cold SymbolTableHeadCache.Controls.missing)).answer =
        [.classified false, .classified true, .classified false] := by decide

def initial : { state : State String 1 // Valid names state } :=
  ⟨cold original, cold_valid original names⟩
def cut := Sampled.advance (checkedStep names permits) (fun _ => 1) 3 lifecycle initial []
def finished := Sampled.resume (checkedStep names permits) (fun _ => 1) 3 cut

theorem pause_retains_recreated_table :
    cut.1 = 3 ∧ Sampled.completed? (checkedStep names permits) cut.2 = none ∧
      (Sampled.savedState (checkedStep names permits) cut.2).1.val.table.owner = (9, 2) := by decide

theorem resume_uses_current_meaning_without_recreation_replay :
    finished.1 = 5 ∧
      (Sampled.completed? (checkedStep names permits) finished.2).map (fun observed => observed.answer) =
        some [.classified true, .classified true, .classified false, .classified true] ∧
      (Sampled.savedState (checkedStep names permits) finished.2).1.val.table.owner = (9, 2) := by decide

end Controls

end Mettapedia.Machines.SymbolHeadService
