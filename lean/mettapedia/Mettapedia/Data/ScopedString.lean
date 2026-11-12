import Mathlib.Data.String.Lemmas
import Mathlib.Data.List.TakeWhile
import Std.Data.String.ToNat

/-!
# String representation of activation-scoped identities

The final decimal suffix records the activation. Arbitrary separators and
digits in the original name are preserved. Different activations have disjoint
images; callers must scope source names as well as generated local names.
No reserved source spelling supplies freshness.
-/

set_option autoImplicit false

namespace Mettapedia.ScopedString

def encode (scope : Nat) (name : String) : String := name ++ "#" ++ Nat.repr scope

def scope? (identifier : String) : Option Nat :=
  (String.ofList ((identifier.toList.reverse.takeWhile (fun c => c != '#')).reverse)).toNat?

private theorem hash_not_repr (scope : Nat) : '#' ∉ (Nat.repr scope).toList := by
  intro present
  rw [Nat.toList_repr] at present
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) present
  contradiction

private theorem take_to_separator (left right : List Char)
    (clear : ∀ c ∈ left, c ≠ '#') :
    (left ++ '#' :: right).takeWhile (fun c => c != '#') = left := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
      have first := clear head (by simp)
      have tail := ih (fun c present => clear c (List.mem_cons_of_mem head present))
      simp [first,tail]

@[simp] theorem scope?_encode (scope : Nat) (name : String) :
    scope? (encode scope name) = some scope := by
  have prefixRead := take_to_separator (Nat.repr scope).toList.reverse name.toList.reverse
    (fun c present same => hash_not_repr scope (same ▸ List.mem_reverse.mp present))
  simp only [scope?,encode,String.toList_append,String.reduceToList,List.reverse_append,
    List.reverse_cons,List.singleton_append,List.append_assoc,
    prefixRead,List.reverse_reverse,String.ofList_toList,Nat.toNat?_repr]

theorem encode_equal_iff (leftScope rightScope : Nat) (leftName rightName : String) :
    encode leftScope leftName = encode rightScope rightName ↔
      leftScope = rightScope ∧ leftName = rightName := by
  constructor
  · intro same
    have scopes : some leftScope = some rightScope := by
      simpa using congrArg scope? same
    have equalScope := Option.some.inj scopes
    subst rightScope
    refine ⟨rfl,?_⟩
    apply (String.append_left_inj ("#" ++ Nat.repr leftScope)).mp
    simpa only [encode,String.append_assoc] using same
  · rintro ⟨rfl,rfl⟩; rfl

theorem encode_injective : Function.Injective (fun pair : Nat × String => encode pair.1 pair.2) := by
  rintro ⟨leftScope,leftName⟩ ⟨rightScope,rightName⟩ same
  obtain ⟨rfl,rfl⟩ := (encode_equal_iff _ _ _ _).mp same
  rfl

theorem different_scopes {leftScope rightScope : Nat} (different : leftScope ≠ rightScope)
    (leftName rightName : String) : encode leftScope leftName ≠ encode rightScope rightName := by
  intro same
  exact different ((encode_equal_iff _ _ _ _).mp same).1

/-- An identity already allocated below the next activation supply. -/
def Before (next : Nat) (identifier : String) : Prop :=
  ∃ scope < next, ∃ name, encode scope name = identifier

theorem before_mono {first later : Nat} (ordered : first ≤ later) {identifier : String}
    (allocated : Before first identifier) : Before later identifier := by
  obtain ⟨scope,earlier,name,rfl⟩ := allocated
  exact ⟨scope,by omega,name,rfl⟩

theorem new_identity_is_fresh {next : Nat} {identifier : String}
    (allocated : Before next identifier) (name : String) : encode next name ≠ identifier := by
  obtain ⟨scope,earlier,original,rfl⟩ := allocated
  exact different_scopes (by omega) name original

theorem new_identity_before_next (scope : Nat) (name : String) :
    Before (scope + 1) (encode scope name) := ⟨scope,by omega,name,rfl⟩

end Mettapedia.ScopedString
