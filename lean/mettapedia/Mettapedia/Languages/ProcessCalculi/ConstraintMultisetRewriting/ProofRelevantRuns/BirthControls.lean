import Mathlib.CategoryTheory.Category.Preorder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Fibred

/-!
# Control: births need frame automorphisms to interchange

Frames are numbers, ordered: a frame `n` has the names `Fin n`, and the only frame maps are the
inclusions `n ⟶ m` for `n ≤ m`. Each atom is a name with the kind of the birth that made it. Two
births of different kinds, `left` and `right`, run in both orders from nothing, over frame maps
`0 ⟶ 2`.

* `left_then_right`, `right_then_left`: both orders run.
* `first_name`, `first_name_not_second`, `orders_differ`: each order gives the first name to its
  first birth, so the two final states differ.
* `no_frame_automorphism`, `births_not_interchanged`: every frame map `2 ⟶ 2` is the identity, so no
  frame map carries one final state to the other. In a frame category without automorphisms the
  interchange of births is not available, not even up to the frames.

Positional frames record the order of births in the names. The interchange of helper firings in the
dependent frames is a square whose vertical side is the block exchange, a frame automorphism that
is not the identity (`point_exchange_ne_id`); positional frames have no such side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.BirthControls

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open _root_.CategoryTheory

/-- Two kinds of birth. -/
inductive Kind where
  | left | right
  deriving DecidableEq

open Kind

/-- Births of names of two kinds, over the ordered frames of numbers. -/
def births : IndexedSystem ℕ (fun _ => Set Bool) (fun n => Fin n × Kind) (fun _ => Kind) where
  know := fun _ known => known
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun step atom => (Fin.castLE (leOfHom step) atom.1, atom.2)
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a + 1
  extend := fun {a} _ => homOfLE (Nat.le_succ a)
  take := fun _ => 0
  read := fun _ => 0
  make := fun {a} kind => {(Fin.last a, kind)}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

/-- One birth, from any state. -/
theorem birth_fires (n : ℕ) (kind : Kind) (k : Set Bool) (Γ : Multiset (Fin n × Kind)) :
    births.Fires (a := n) kind k Γ (k ⊓ Set.univ)
      ({(Fin.last n, kind)} + births.carried (births.extend (a := n) kind) Γ) := by
  refine ⟨Γ, ?_, True.intro, rfl, ?_⟩
  · show Γ = (0 + 0) + Γ
    rw [zero_add, zero_add]
  · show {(Fin.last n, kind)} + births.carried (births.extend (a := n) kind) Γ =
      (births.carried (births.extend (a := n) kind) 0 + {(Fin.last n, kind)}) +
        births.carried (births.extend (a := n) kind) Γ
    rw [IndexedSystem.carried_zero, zero_add]

/-- The atoms after a birth of `first` and then a birth of `second`. -/
def after (first second : Kind) : Multiset (Fin 2 × Kind) :=
  {(Fin.last 1, second)} +
    (births.carried (births.extend (a := 1) second)
      ({(Fin.last 0, first)} +
        (births.carried (births.extend (a := 0) first) 0 : Multiset (Fin 1 × Kind))) :
      Multiset (Fin 2 × Kind))

theorem runs_in_order (first second : Kind) :
    births.Run 0 Set.univ 0 [⟨0, first⟩, ⟨1, second⟩] 2
      (births.extend (a := 0) first ≫ births.extend (a := 1) second ≫ 𝟙 2)
      (Set.univ ⊓ Set.univ ⊓ Set.univ) (after first second) :=
  IndexedSystem.Run.fire (birth_fires 0 first Set.univ 0)
    (IndexedSystem.Run.fire (birth_fires 1 second _ _) (IndexedSystem.Run.done (sys := births) _ _ _))

/-- `left` then `right` runs. -/
theorem left_then_right :
    births.Run 0 Set.univ 0 [⟨0, left⟩, ⟨1, right⟩] 2
      (births.extend (a := 0) left ≫ births.extend (a := 1) right ≫ 𝟙 2)
      (Set.univ ⊓ Set.univ ⊓ Set.univ) (after left right) :=
  runs_in_order left right

/-- `right` then `left` runs. -/
theorem right_then_left :
    births.Run 0 Set.univ 0 [⟨0, right⟩, ⟨1, left⟩] 2
      (births.extend (a := 0) right ≫ births.extend (a := 1) left ≫ 𝟙 2)
      (Set.univ ⊓ Set.univ ⊓ Set.univ) (after right left) :=
  runs_in_order right left

/-- The first name, carried into the frame `2`, with the kind of the first birth. -/
theorem after_eq (first second : Kind) :
    after first second = {(Fin.last 1, second)} + {((0 : Fin 2), first)} :=
  rfl

/-- Each order gives the first name to its first birth. -/
theorem first_name (first second : Kind) : ((0 : Fin 2), first) ∈ after first second := by
  rw [after_eq]
  exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))

/-- The second birth does not get the first name. -/
theorem first_name_not_second : ((0 : Fin 2), right) ∉ after left right := by
  rw [after_eq]
  decide

/-- **The two orders end in different states.** -/
theorem orders_differ : after left right ≠ after right left := by
  intro same
  exact first_name_not_second (same ▸ first_name right left)

/-- **Every frame map `2 ⟶ 2` is the identity**: the ordered frames have no automorphisms. -/
theorem no_frame_automorphism (f : (2 : ℕ) ⟶ 2) : f = 𝟙 2 :=
  Subsingleton.elim _ _

/-- **No frame map carries one final state to the other.** -/
theorem births_not_interchanged (f : (2 : ℕ) ⟶ 2) :
    births.carried f (after left right) ≠ after right left := by
  rw [no_frame_automorphism f, IndexedSystem.carried_id]
  exact orders_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.BirthControls
