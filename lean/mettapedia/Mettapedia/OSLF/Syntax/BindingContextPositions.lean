import Mettapedia.OSLF.Syntax.BindingSignatureABT

/-!
# Typed context variables and finite declaration positions

Every variable position carries its declared sort. Reading a finite position
and forgetting its sort are inverse operations, with explicit sort transport.
This metadata supports finite scope computations without requiring the set of
sorts itself to be finite or decidable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextPositions

variable {S : Signature}

def castSort {Γ : Ctx S} {first second : S.Srt} (same : first = second)
    (position : Var Γ first) : Var Γ second := same ▸ position

theorem castSort_heq {Γ : Ctx S} {first second : S.Srt} (same : first = second)
    (position : Var Γ first) : HEq (castSort same position) position := by cases same; rfl

theorem index_castSort {Γ : Ctx S} {first second : S.Srt} (same : first = second)
    (position : Var Γ first) : CommonABT.index (castSort same position) = CommonABT.index position := by
  cases same
  rfl

theorem castSort_succ {Γ : Ctx S} {first second binder : S.Srt} (same : first = second)
    (position : Var Γ first) :
    castSort same (Var.succ (t := binder) position) = Var.succ (castSort same position) := by
  cases same
  rfl

theorem map_castSort {Γ Δ : Ctx S} (mapping : Ren S Γ Δ) {first second : S.Srt}
    (same : first = second) (position : Var Γ first) :
    mapping second (castSort same position) = castSort same (mapping first position) := by
  cases same
  rfl

theorem map_castSort_heq {Γ Δ : Ctx S} (mapping : Ren S Γ Δ) {first second : S.Srt}
    (same : first = second) (position : Var Γ first) :
    HEq (mapping second (castSort same position)) (mapping first position) :=
  (map_castSort mapping same position).heq.trans (castSort_heq same (mapping first position))

def toSlot {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) : Fin Γ.length :=
  ⟨CommonABT.index position, CommonABT.index_lt position⟩

def ofSlot : (Γ : Ctx S) → (slot : Fin Γ.length) → Var Γ (Γ.get slot)
  | [], slot => Fin.elim0 slot
  | _ :: _, ⟨0, _⟩ => .zero
  | _ :: rest, ⟨index + 1, inside⟩ =>
      .succ (ofSlot rest ⟨index, Nat.lt_of_succ_lt_succ inside⟩)

theorem index_ofSlot : ∀ (Γ : Ctx S) (slot : Fin Γ.length), CommonABT.index (ofSlot Γ slot) = slot.val
  | [], slot => Fin.elim0 slot
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: rest, ⟨index + 1, inside⟩ =>
      congrArg Nat.succ (index_ofSlot rest ⟨index, Nat.lt_of_succ_lt_succ inside⟩)

theorem slot_sort : ∀ {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort), Γ.get (toSlot position) = sort
  | _, _, .zero => rfl
  | _, _, .succ position => slot_sort position

theorem ofSlot_toSlot : ∀ {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort),
    castSort (slot_sort position) (ofSlot Γ (toSlot position)) = position
  | _, _, .zero => rfl
  | _, _, .succ position => by
      change castSort (slot_sort position) (Var.succ (ofSlot _ (toSlot position))) = Var.succ position
      rw [castSort_succ]
      exact congrArg Var.succ (ofSlot_toSlot position)

theorem ofSlot_toSlot_heq {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) :
    HEq (ofSlot Γ (toSlot position)) position :=
  (castSort_heq _ _).symm.trans (ofSlot_toSlot position).heq

theorem toSlot_ofSlot (Γ : Ctx S) (slot : Fin Γ.length) : toSlot (ofSlot Γ slot) = slot :=
  Fin.ext (index_ofSlot Γ slot)

theorem map_index_ofSlot {Γ Δ : Ctx S} (mapping : Ren S Γ Δ) {sort : S.Srt} (position : Var Γ sort) :
    CommonABT.index (mapping _ (ofSlot Γ (toSlot position))) = CommonABT.index (mapping sort position) := by
  have same := congrArg (mapping sort) (ofSlot_toSlot position)
  rw [map_castSort (S := S) mapping (slot_sort position) (ofSlot Γ (toSlot position))] at same
  have indices := congrArg (CommonABT.index (S := S)) same
  simpa only [index_castSort] using indices

theorem sort_eq_of_equal_index {Γ : Ctx S} {first second : S.Srt}
    (left : Var Γ first) (right : Var Γ second) (same : CommonABT.index left = CommonABT.index right) :
    first = second := by
  have slots : toSlot left = toSlot right := Fin.ext same
  exact (slot_sort left).symm.trans ((congrArg Γ.get slots).trans (slot_sort right))

end Mettapedia.OSLF.Binding.ContextPositions
