import Mettapedia.Machines.Cursor.Fold

/-!
# Copying tails versus retained sequence views

An array-tail provider constructs the remaining array at every successful
pull. The independently implemented slice provider in `Sequence` retains its
backing array and advances an offset. Both implement the same protocol.

The meters count child visits: one for the delivered item, plus the remaining
tail length when that tail is copied or rescanned. They do not count allocator,
reference-counting, client, startup, or wall-clock costs. The model therefore
isolates a representation cost rather than predicting a runtime speed ratio.
The generic client laws include early stopping and suspended residuals.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

/-- A local equality of receipts transports through any adaptive client. -/
theorem Hom.advance_charge
    {Base : Type u} {Index : Base → Type u}
    {P : IndexedPolynomial.{u, u, u, u} Base Index}
    {Return : (base : Base) → Index base → Type u}
    {source target : Provider P}
    (C : Client (P := P) (Return := Return)) (h : Hom source target)
    (sourceCost : Charge source) (targetCost : Charge target)
    (localCharge : ∀ {base index} (state : source.State base index)
      (request : P.Shape base index), sourceCost state request = targetCost (h.map state) request)
    (fuel : Nat) {base : Base} (packet : Packet source C base) :
    (Cursor.advance source C sourceCost fuel packet).1 =
      (Cursor.advance target C targetCost fuel (h.packet C packet)).1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      change (Cursor.advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).1 =
        (Cursor.advance target C targetCost (fuel + 1) ⟨index, control, h.map state⟩).1
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [Cursor.advance, eq]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [Cursor.advance, eq]
              dsimp only [withHoles]
              rw [← h.step state request, localCharge]
              exact congrArg (fun n => targetCost (h.map state) request + n)
                (ih ⟨_, children (source.step state request).1, (source.step state request).2⟩)

namespace SequenceCost

variable (Item : Type)

/-- This provider actually constructs each array suffix, unlike an offset view. -/
def copying : Provider (Sequence.protocol Item) where
  State _ _ := Array Item
  step storage _ := match storage[0]? with
    | none => ⟨none, storage⟩
    | some first => ⟨some first, storage.extract 1 storage.size⟩

def copyingHom : Hom (copying Item) (Sequence.tails Item) where
  map storage := storage.toList
  step storage request := by
    rcases storage with ⟨values⟩
    cases values with
    | nil => simp [copying, Sequence.tails]
    | cons first rest => simp [copying, Sequence.tails, List.extract_eq_take_drop]

/-- Child visits in a successful copying pull: one head and every tail child. -/
def copyingVisits : Charge (copying Item) := fun storage _ => storage.size

/-- The same physical accounting expressed on the semantic list state. -/
def copyingReference : Charge (Sequence.tails Item) := fun items _ => items.length

/-- One child access for a successful view pull, including malformed-view behavior. -/
def viewVisits : Charge (Sequence.slices Item) := fun view _ =>
  if view.remaining = 0 then 0 else if (view.storage[view.offset]?).isSome then 1 else 0

theorem viewVisits_exact (view : Sequence.Slice Item) :
    viewVisits Item (base := ()) (index := ()) view () =
      Sequence.requested Item (base := ()) (index := ())
      ((Sequence.sliceHom Item).map (base := ()) (index := ()) view) () := by
  rcases view with ⟨storage, offset, remaining⟩
  cases remaining with
  | zero => simp [viewVisits, Sequence.requested, Sequence.sliceHom]
  | succ remaining =>
      cases found : storage[offset]? with
      | none =>
          have empty : storage.toList.drop offset = [] := by
            apply List.drop_eq_nil_iff.mpr
            simpa using (Array.getElem?_eq_none_iff.mp found)
          simp [viewVisits, Sequence.requested, Sequence.sliceHom, found, empty]
      | some value =>
          have listFound : storage.toList[offset]? = some value := by simpa using found
          obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp listFound
          have head := List.drop_eq_getElem_cons bound
          rw [equal] at head
          simp [viewVisits, Sequence.requested, Sequence.sliceHom, found, head]

/-- Every successful view pull avoids the tail traversal, for every client prefix. -/
theorem view_prefix_cost_le_copying
    {Return : Unit → Unit → Type}
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (Sequence.slices Item) C ()) :
    (advance (Sequence.slices Item) C (viewVisits Item) fuel packet).1 ≤
      (advance (Sequence.tails Item) C (copyingReference Item) fuel
        ((Sequence.sliceHom Item).packet C packet)).1 := by
  apply advance_cost_le C (Sequence.sliceHom Item) (viewVisits Item)
    (copyingReference Item) (fun _ => 0) ?_ fuel packet rfl
  intro base index state request
  cases base; cases index; cases request
  change viewVisits Item (base := ()) (index := ()) state () ≤
    copyingReference Item (base := ()) (index := ())
      ((Sequence.sliceHom Item).map (base := ()) (index := ()) state) ()
  apply Nat.le_trans (Nat.le_of_eq (viewVisits_exact Item state))
  generalize (Sequence.sliceHom Item).map (base := ()) (index := ()) state = values
  cases values <;> simp [Sequence.requested, copyingReference]

/-- Uncharged client observation, including its residual, is independent of
the physical tail representation. -/
theorem copying_observation
    {Return : Unit → Unit → Type}
    (C : Client (P := Sequence.protocol Item) (Return := Return))
    (fuel : Nat) (packet : Packet (copying Item) C ()) :
    (copyingHom Item).outcome C
      (advance (copying Item) C (copyingVisits Item) fuel packet).2 =
      (advance (Sequence.tails Item) C (Sequence.requested Item) fuel
        ((copyingHom Item).packet C packet)).2 :=
  Hom.advance C (copyingHom Item) _ _ fuel packet

/-- Exact tail-work recurrence; successful pulls visit lengths n, n-1, ... . -/
def prefixVisits : Nat → Nat → Nat
  | _, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, k + 1 => n + 1 + prefixVisits n k

def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + triangular n

theorem triangular_closed (n : Nat) :
    2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [triangular]; nlinarith

theorem prefix_exact_formula (n k : Nat) (within : k ≤ n) :
    2 * prefixVisits n k = k * (2 * n + 1 - k) := by
  induction k generalizing n with
  | zero => simp [prefixVisits]
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
          have bound : k ≤ n := by omega
          have inductionResult := ih n bound
          have sub : k ≤ 2 * n + 1 := by omega
          have sub' : k + 1 ≤ 2 * (n + 1) + 1 := by omega
          simp only [prefixVisits]
          have cancel := Nat.sub_add_cancel sub
          have cancel' := Nat.sub_add_cancel sub'
          nlinarith

variable {Item} {Accumulator : Type}

/-- Cost of a fold prefix on the reference state with the copying meter. -/
theorem fold_prefix_visits (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) (k : Nat)
    (within : k ≤ items.length) :
    (advance (Sequence.tails Item) (Fold.client consume) (copyingReference Item) k
      (Fold.start _ consume items initial)).1 = prefixVisits items.length k := by
  induction k generalizing items initial with
  | zero => simp [advance, prefixVisits]
  | succ k ih =>
      cases items with
      | nil => simp at within
      | cons first rest =>
          have bound : k ≤ rest.length := by simpa using within
          change rest.length + 1 +
            (advance (Sequence.tails Item) (Fold.client consume) (copyingReference Item) k
              (Fold.start _ consume rest (consume initial first))).1 = _
          rw [ih rest (consume initial first) bound]
          rfl

/-- Full traversal has triangular child-work, despite linear answer count. -/
theorem fold_complete_visits (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) :
    (advance (Sequence.tails Item) (Fold.client consume) (copyingReference Item)
      (items.length + 2) (Fold.start _ consume items initial)).1 =
      triangular items.length := by
  induction items generalizing initial with
  | nil => rfl
  | cons first rest ih =>
      change rest.length + 1 +
        (advance (Sequence.tails Item) (Fold.client consume) (copyingReference Item)
          (rest.length + 2) (Fold.start _ consume rest (consume initial first))).1 = _
      rw [ih]
      rfl

theorem copying_complete_visits (consume : Accumulator → Item → Accumulator)
    (storage : Array Item) (initial : Accumulator) :
    (advance (copying Item) (Fold.client consume) (copyingVisits Item)
      (storage.size + 2) (Fold.start _ consume storage initial)).1 =
      triangular storage.size := by
  rw [Hom.advance_charge (Fold.client consume) (copyingHom Item)
    (copyingVisits Item) (copyingReference Item) (by intros; rfl)]
  simpa [Hom.packet, copyingHom, Fold.start] using
    fold_complete_visits consume storage.toList initial

theorem copying_prefix_visits (consume : Accumulator → Item → Accumulator)
    (storage : Array Item) (initial : Accumulator) (k : Nat) (within : k ≤ storage.size) :
    (advance (copying Item) (Fold.client consume) (copyingVisits Item) k
      (Fold.start _ consume storage initial)).1 = prefixVisits storage.size k := by
  rw [Hom.advance_charge (Fold.client consume) (copyingHom Item)
    (copyingVisits Item) (copyingReference Item) (by intros; rfl)]
  simpa [Hom.packet, copyingHom, Fold.start] using
    fold_prefix_visits consume storage.toList initial k (by simpa using within)

/-- The demand meter counts only delivered children; exhaustion visits no child. -/
theorem fold_prefix_requested (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) (k : Nat) (within : k ≤ items.length) :
    (advance (Sequence.tails Item) (Fold.client consume) (Sequence.requested Item) k
      (Fold.start _ consume items initial)).1 = k := by
  induction k generalizing items initial with
  | zero => rfl
  | succ k ih =>
      cases items with
      | nil => simp at within
      | cons first rest =>
          have bound : k ≤ rest.length := by simpa using within
          change 1 +
            (advance (Sequence.tails Item) (Fold.client consume) (Sequence.requested Item) k
              (Fold.start _ consume rest (consume initial first))).1 = k + 1
          rw [ih rest (consume initial first) bound, Nat.add_comm]

theorem fold_complete_requested (consume : Accumulator → Item → Accumulator)
    (items : List Item) (initial : Accumulator) :
    (advance (Sequence.tails Item) (Fold.client consume) (Sequence.requested Item)
      (items.length + 2) (Fold.start _ consume items initial)).1 = items.length := by
  induction items generalizing initial with
  | nil => rfl
  | cons first rest ih =>
      change 1 +
        (advance (Sequence.tails Item) (Fold.client consume) (Sequence.requested Item)
          (rest.length + 2) (Fold.start _ consume rest (consume initial first))).1 = rest.length + 1
      rw [ih, Nat.add_comm]

def wholeView (storage : Array Item) : Sequence.Slice Item := ⟨storage, 0, storage.size⟩

theorem view_prefix_visits (consume : Accumulator → Item → Accumulator)
    (storage : Array Item) (initial : Accumulator) (k : Nat) (within : k ≤ storage.size) :
    (advance (Sequence.slices Item) (Fold.client consume) (viewVisits Item) k
      (Fold.start _ consume (wholeView storage) initial)).1 = k := by
  have whole : storage.toList.take storage.size = storage.toList := by
    simp only [← Array.length_toList, List.take_length]
  rw [Hom.advance_charge (Fold.client consume) (Sequence.sliceHom Item)
    (viewVisits Item) (Sequence.requested Item) (by
      intro base index state request
      cases base; cases index; cases request
      exact viewVisits_exact Item state)]
  simpa [Hom.packet, Sequence.sliceHom, Fold.start, wholeView, whole] using
    fold_prefix_requested consume storage.toList initial k (by simpa using within)

theorem view_complete_visits (consume : Accumulator → Item → Accumulator)
    (storage : Array Item) (initial : Accumulator) :
    (advance (Sequence.slices Item) (Fold.client consume) (viewVisits Item)
      (storage.size + 2) (Fold.start _ consume (wholeView storage) initial)).1 = storage.size := by
  have whole : storage.toList.take storage.size = storage.toList := by
    simp only [← Array.length_toList, List.take_length]
  rw [Hom.advance_charge (Fold.client consume) (Sequence.sliceHom Item)
    (viewVisits Item) (Sequence.requested Item) (by
      intro base index state request
      cases base; cases index; cases request
      exact viewVisits_exact Item state)]
  simpa [Hom.packet, Sequence.sliceHom, Fold.start, wholeView, whole] using
    fold_complete_requested consume storage.toList initial

/-- The same prefix is processed, while the copying meter charges every
successively shorter array. This is an exact formula, not an asymptotic assertion. -/
theorem representation_cost_separation (consume : Accumulator → Item → Accumulator)
    (storage : Array Item) (initial : Accumulator) (k : Nat) (within : k ≤ storage.size) :
    2 * (advance (copying Item) (Fold.client consume) (copyingVisits Item) k
        (Fold.start _ consume storage initial)).1 = k * (2 * storage.size + 1 - k) ∧
    (advance (Sequence.slices Item) (Fold.client consume) (viewVisits Item) k
        (Fold.start _ consume (wholeView storage) initial)).1 = k := by
  constructor
  · rw [copying_prefix_visits consume storage initial k within]
    exact prefix_exact_formula storage.size k within
  · exact view_prefix_visits consume storage initial k within

/-- Advancing a view retains the backing value, including on exhaustion.
This is an immutable-value law; native rooting is a separate obligation. -/
theorem view_retains_storage (view : Sequence.Slice Item) :
    ((Sequence.slices Item).step (base := ()) (index := ()) view ()).2.storage =
      view.storage := by
  rcases view with ⟨storage, offset, remaining⟩
  cases remaining <;> simp only [Sequence.slices]
  split <;> rfl

namespace Controls

theorem copy_three_items_visits_six :
    (advance (copying Nat) (Fold.client (· + ·)) (copyingVisits Nat) 5
      (Fold.start _ (· + ·) #[3, 3, 5] 0)).1 = 6 := by decide

theorem one_pull_is_already_linear_in_tail_size :
    prefixVisits 1000 1 = 1000 := rfl

theorem equal_answers_do_not_imply_equal_representation_cost :
    triangular 4 ≠ 4 := by decide

theorem view_three_items_visits_three :
    (advance (Sequence.slices Nat) (Fold.client (· + ·)) (viewVisits Nat) 5
      (Fold.start _ (· + ·) (wholeView #[3, 3, 5]) 0)).1 = 3 := by decide

/-- A tail can keep the remaining duplicate; uniqueness would be a different observation. -/
theorem duplicates_survive_one_pull :
    (Sequence.sliceHom Nat).map (base := ()) (index := ())
      ((Sequence.slices Nat).step (base := ()) (index := ())
        (wholeView #[3, 3, 5]) ()).2 = [3, 5] := rfl

/-- Parent flags cannot simply be reused for the tail: the flagged item may have left. -/
theorem parent_summary_is_not_tail_summary :
    ([true, false].any id) ≠ ([false].any id) := by decide

end Controls

#print axioms copyingHom
#print axioms view_prefix_cost_le_copying
#print axioms copying_observation
#print axioms prefix_exact_formula
#print axioms copying_complete_visits
#print axioms view_complete_visits
#print axioms representation_cost_separation
#print axioms view_retains_storage

end SequenceCost
end Mettapedia.Machines.Cursor
