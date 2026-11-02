import Mettapedia.Machines.RelationTransferCoordinates

/-!
# Incremental take-over behind a publication boundary

The private worker retains original rows while recording successful transfers.
Its physical bag may temporarily contain extra copies. A compensated logical
bag excludes precisely those accepted occurrences, and is invariant at every
step. Only completed work may become available to fresh readers. Pausing is
not an empty answer; fatal termination is not recoverable refusal.

The model supplies the isolation and preparation contract. It does not prove
that every native reader participates in the same synchronization domain, or
that private buffers and captured views have been rooted by the C runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationTransferPublication

open RelationBagTransfer
variable {Fact : Type} [DecidableEq Fact]

structure Draft (Fact : Type) where
  past : List Fact
  accepted : List Bool
  todo : List Fact
  target : Target Fact
  deriving DecidableEq

def Draft.Valid (draft : Draft Fact) : Prop := draft.accepted.length = draft.past.length
def Draft.source (draft : Draft Fact) : List Fact := draft.past ++ draft.todo
def Draft.remaining (draft : Draft Fact) : List Fact := retained draft.past draft.accepted ++ draft.todo
def Draft.logical (draft : Draft Fact) : Store Fact := ⟨draft.remaining, draft.target⟩
def Draft.physical (draft : Draft Fact) : Store Fact := ⟨draft.source, draft.target⟩

def start (before : Store Fact) : Draft Fact := ⟨[], [], before.rows, before.target⟩

def step (choose : Nat → Fact → Action) (draft : Draft Fact) : Draft Fact :=
  match draft.todo with
  | [] => draft
  | fact :: rest =>
      let offered := offer (choose draft.past.length fact) draft.target fact
      ⟨draft.past ++ [fact], draft.accepted ++ [offered.1], rest, offered.2⟩

def advance : Nat → (Nat → Fact → Action) → Draft Fact → Draft Fact
  | 0, _, draft => draft
  | budget + 1, choose, draft => advance budget choose (step choose draft)

omit [DecidableEq Fact] in
theorem retained_append_one (past : List Fact) (mask : List Bool) (fact : Fact) (accepted : Bool)
    (size : mask.length = past.length) :
    retained (past ++ [fact]) (mask ++ [accepted]) =
      retained past mask ++ if accepted then [] else [fact] := by
  induction past generalizing mask with
  | nil => have empty : mask = [] := List.eq_nil_of_length_eq_zero size; subst mask; cases accepted <;> rfl
  | cons first rest ih =>
      cases mask with
      | nil => simp at size
      | cons kept mask =>
          have tail := ih mask (by simpa using size)
          cases kept <;> simp [retained, tail]

theorem step_valid (choose : Nat → Fact → Action) (draft : Draft Fact) (valid : draft.Valid) :
    (step choose draft).Valid := by
  change draft.accepted.length = draft.past.length at valid
  cases todo : draft.todo <;> simp [step, todo, Draft.Valid, valid]

theorem step_source (choose : Nat → Fact → Action) (draft : Draft Fact) :
    (step choose draft).source = draft.source := by
  cases todo : draft.todo <;> simp [step, todo, Draft.source, List.append_assoc]

theorem step_logical_bag (choose : Nat → Fact → Action) (draft : Draft Fact) (valid : draft.Valid) :
    (step choose draft).logical.bag = draft.logical.bag := by
  cases todo : draft.todo with
  | nil => simp [step, todo]
  | cons fact rest =>
      have retainedStep := retained_append_one draft.past draft.accepted fact
        (offer (choose draft.past.length fact) draft.target fact).1 valid
      simp only [step, todo, Draft.logical, Draft.remaining]
      rw [retainedStep]
      ext observed
      have offered := offer_count (choose draft.past.length fact) draft.target fact observed
      by_cases same : fact = observed
      · subst observed
        cases accepted : (offer (choose draft.past.length fact) draft.target fact).1 <;>
          simp [Store.bag, accepted, Target.count] at offered ⊢ <;> omega
      · cases accepted : (offer (choose draft.past.length fact) draft.target fact).1 <;>
          simp [Store.bag, accepted, Target.count, same] at offered ⊢ <;> omega

theorem advance_valid (budget : Nat) (choose : Nat → Fact → Action) (draft : Draft Fact)
    (valid : draft.Valid) : (advance budget choose draft).Valid := by
  induction budget generalizing draft with
  | zero => exact valid
  | succ budget ih => exact ih _ (step_valid choose draft valid)

theorem advance_source (budget : Nat) (choose : Nat → Fact → Action) (draft : Draft Fact) :
    (advance budget choose draft).source = draft.source := by
  induction budget generalizing draft with
  | zero => rfl
  | succ budget ih => rw [advance, ih, step_source]

theorem advance_logical_bag (budget : Nat) (choose : Nat → Fact → Action) (draft : Draft Fact)
    (valid : draft.Valid) : (advance budget choose draft).logical.bag = draft.logical.bag := by
  induction budget generalizing draft with
  | zero => rfl
  | succ budget ih =>
      rw [advance, ih _ (step_valid choose draft valid), step_logical_bag choose draft valid]

theorem step_todo_length (choose : Nat → Fact → Action) (draft : Draft Fact) :
    (step choose draft).todo.length = draft.todo.length - 1 := by
  cases todo : draft.todo <;> simp [step, todo]

theorem advance_todo_length (budget : Nat) (choose : Nat → Fact → Action) (draft : Draft Fact) :
    (advance budget choose draft).todo.length = draft.todo.length - budget := by
  induction budget generalizing draft with
  | zero => rfl
  | succ budget ih => rw [advance, ih, step_todo_length]; omega

theorem advance_add (first later : Nat) (choose : Nat → Fact → Action) (draft : Draft Fact) :
    advance (first + later) choose draft = advance later choose (advance first choose draft) := by
  induction first generalizing draft with
  | zero => simp [advance]
  | succ first ih => simpa only [Nat.succ_add, advance] using ih (step choose draft)

inductive Session (Fact : Type) where
  | available (store : Store Fact)
  | working (draft : Draft Fact)
  | halted (draft : Draft Fact)
  deriving DecidableEq

inductive Readout (Fact : Type) where
  | value (bag : Multiset Fact)
  | busy
  | terminated
  deriving DecidableEq

def observe : Session Fact → Readout Fact
  | .available store => .value store.bag
  | .working _ => .busy
  | .halted _ => .terminated

def begin (allocated : Bool) (before : Store Fact) : Session Fact :=
  if allocated then .working (start before) else .available before

def work (budget : Nat) (choose : Nat → Fact → Action) : Session Fact → Session Fact
  | .working draft => .working (advance budget choose draft)
  | other => other

def publish : Session Fact → Session Fact
  | .working draft => if draft.todo = [] then .available draft.logical else .working draft
  | other => other

def abort : Session Fact → Session Fact
  | .working draft => .halted draft
  | other => other

def Consistent (bag : Multiset Fact) : Session Fact → Prop
  | .available store => store.bag = bag
  | .working draft | .halted draft => draft.Valid ∧ draft.logical.bag = bag

omit [DecidableEq Fact] in
theorem begin_consistent (allocated : Bool) (before : Store Fact) :
    Consistent before.bag (begin allocated before) := by
  cases allocated <;> simp [begin, Consistent, start, Draft.Valid, Draft.logical, Draft.remaining, retained]

theorem work_consistent (budget : Nat) (choose : Nat → Fact → Action) (session : Session Fact)
    (bag : Multiset Fact) (valid : Consistent bag session) :
    Consistent bag (work budget choose session) := by
  cases session with
  | available store => exact valid
  | halted draft => exact valid
  | working draft =>
      exact ⟨advance_valid budget choose draft valid.1,
        (advance_logical_bag budget choose draft valid.1).trans valid.2⟩

omit [DecidableEq Fact] in
theorem publish_consistent (session : Session Fact) (bag : Multiset Fact)
    (valid : Consistent bag session) : Consistent bag (publish session) := by
  cases session with
  | available store => exact valid
  | halted draft => exact valid
  | working draft => by_cases done : draft.todo = [] <;> simp_all [publish, Consistent]

omit [DecidableEq Fact] in
theorem returned_value_is_original (session : Session Fact) (bag : Multiset Fact)
    (valid : Consistent bag session) (answer : Multiset Fact) (returned : observe session = .value answer) :
    answer = bag := by
  cases session <;> simp_all [observe, Consistent]

theorem enough_work_publishes (before : Store Fact) (choose : Nat → Fact → Action) (budget : Nat)
    (enough : before.rows.length ≤ budget) :
    observe (publish (work budget choose (begin true before))) = .value before.bag := by
  have valid := begin_consistent true before
  have final := work_consistent budget choose (begin true before) before.bag valid
  have done : (advance budget choose (start before)).todo = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [advance_todo_length]
    exact Nat.sub_eq_zero_of_le enough
  simp only [begin, ↓reduceIte, work, publish, done, ↓reduceIte, observe]
  exact congrArg Readout.value final.2

omit [DecidableEq Fact] in
theorem early_refusal_preserves_store (before : Store Fact) : begin false before = .available before := rfl

omit [DecidableEq Fact] in
theorem incomplete_is_not_exhaustion (draft : Draft Fact) (pending : draft.todo ≠ []) :
    observe (publish (.working draft)) = (.busy : Readout Fact) := by simp [publish, pending, observe]

omit [DecidableEq Fact] in
theorem fatal_is_not_rollback (draft : Draft Fact) :
    observe (abort (.working draft)) = (.terminated : Readout Fact) := rfl

def publishWithReader (before : Store Fact) (revision : Nat) (reader : CapturedRowReaders.Cursor Fact)
    (session : Session Fact) : Option (CapturedRowReaders.Store Fact × CapturedRowReaders.Cursor Fact) :=
  match publish session with
  | .available store => CapturedRowReaders.publish (before.view revision) reader (store.view revision).rows
  | .working _ | .halted _ => none

omit [DecidableEq Fact] in
theorem published_bag_and_captured_sequence (before : Store Fact) (revision : Nat)
    (reader : CapturedRowReaders.Cursor Fact) (session : Session Fact) (valid : Consistent before.bag session)
    (after : CapturedRowReaders.Store Fact) (saved : CapturedRowReaders.Cursor Fact)
    (accepted : publishWithReader before revision reader session = some (after, saved)) :
    (after.rows : Multiset Fact) = before.bag ∧
      CapturedRowReaders.remaining after saved = CapturedRowReaders.remaining (before.view revision) reader := by
  cases result : publish session with
  | working draft | halted draft => simp [publishWithReader, result] at accepted
  | available store =>
      have sameBag : store.bag = before.bag := by
        simpa only [result, Consistent] using publish_consistent session before.bag valid
      have installed : CapturedRowReaders.publish (before.view revision) reader (store.view revision).rows =
          some (after, saved) := by simpa only [publishWithReader, result] using accepted
      refine ⟨?_, CapturedRowReaders.publish_preserves _ _ _ _ _ installed⟩
      obtain ⟨retainedReader, _, same⟩ := Option.map_eq_some_iff.mp installed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simpa only [CapturedRowReaders.edit, Store.view, Store.bag, ← Multiset.coe_add,
        add_assoc] using sameBag

namespace Controls

def original : Store Nat := ⟨[7, 7, 9], ⟨[], [], true⟩⟩

theorem partial_physical_state_has_extra_copies :
    ((advance 1 (fun _ _ => .store) (start original)).physical.bag).count 7 = 3 ∧
    ((advance 1 (fun _ _ => .store) (start original)).logical.bag).count 7 = 2 := by decide

theorem paused_work_returns_no_empty_answer :
    observe (publish (work 1 (fun _ _ => .store) (begin true original))) = .busy := by decide

theorem completion_preserves_duplicate_occurrences :
    observe (publish (work 3 (fun _ _ => .store) (begin true original))) = .value original.bag :=
  enough_work_publishes original _ 3 (by decide)

theorem interrupted_private_work_is_not_refusal :
    observe (abort (work 1 (fun _ _ => .store) (begin true original))) = .terminated ∧
    observe (begin false original) = .value original.bag := by decide

end Controls
end Mettapedia.Machines.RelationTransferPublication
