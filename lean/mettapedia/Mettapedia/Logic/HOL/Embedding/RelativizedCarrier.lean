import Mathlib.Logic.Equiv.Defs

/-!
# Empty carriers inside inhabited representations

An inhabited representation need not make the represented carrier inhabited.
Padding supplies a representation for every type; the partial equivalence
relation excludes the padding point. Quantifiers are restricted to valid
representations, and function equality observes valid arguments only.

These are semantic carrier laws, not an import theorem for all of HOL.
In particular, ordinary HOL's unrestricted choice/inhabitation principles
cannot be transferred to every represented carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.RelativizedCarrier

universe u v

def Valid {A : Type u} : Option A → Prop
  | none => False
  | some _ => True

def Related {A : Type u} : Option A → Option A → Prop
  | some a, some b => a = b
  | _, _ => False

theorem related_symmetric {A : Type u} {x y : Option A}
    (h : Related x y) : Related y x := by
  cases x <;> cases y <;> simp_all [Related]

theorem related_transitive {A : Type u} {x y z : Option A}
    (h : Related x y) (k : Related y z) : Related x z := by
  cases x <;> cases y <;> cases z <;> simp_all [Related]

theorem valid_iff_self_related {A : Type u} (x : Option A) :
    Valid x ↔ Related x x := by cases x <;> simp [Valid, Related]

def carrierEquiv (A : Type u) : {x : Option A // Valid x} ≃ A where
  toFun x := match x with
    | ⟨some a, _⟩ => a
  invFun a := ⟨some a, trivial⟩
  left_inv x := by
    rcases x with ⟨x, h⟩
    cases x with
    | none => exact h.elim
    | some a => rfl
  right_inv _ := rfl

def Predicate {A : Type u} (P : A → Prop) : Option A → Prop
  | none => False
  | some a => P a

theorem forall_valid_iff {A : Type u} (P : A → Prop) :
    (∀ x : Option A, Valid x → Predicate P x) ↔ ∀ a, P a := by
  constructor
  · intro h a; exact h (some a) trivial
  · intro h x hx; cases x with
    | none => exact hx.elim
    | some a => exact h a

theorem exists_valid_iff {A : Type u} (P : A → Prop) :
    (∃ x : Option A, Valid x ∧ Predicate P x) ↔ ∃ a, P a := by
  constructor
  · rintro ⟨x, hx, hp⟩
    cases x with
    | none => exact hx.elim
    | some a => exact ⟨a, hp⟩
  · rintro ⟨a, h⟩; exact ⟨some a, trivial, h⟩

def ArrowRelated {A : Type u} {B : Type v} (f g : Option A → Option B) : Prop :=
  ∀ x y, Related x y → Related (f x) (g y)

/-- Functions are compared at real arguments. Arbitrary padding behaviour
does not become an observation of the represented function. -/
theorem map_arrowRelated_iff {A : Type u} {B : Type v} (f g : A → B) :
    ArrowRelated (Option.map f) (Option.map g) ↔ ∀ a, f a = g a := by
  constructor
  · intro h a; exact h (some a) (some a) rfl
  · intro h x y hxy
    cases x with
    | none => exact hxy.elim
    | some a => cases y with
      | none => exact hxy.elim
      | some b => cases hxy; exact h a

theorem empty_representation_inhabited : Nonempty (Option Empty) := ⟨none⟩

theorem empty_has_no_valid_representation : ¬ ∃ x : Option Empty, Valid x := by
  rintro ⟨x, hx⟩
  cases x with
  | none => exact hx
  | some e => exact e.elim

/-- A default element of the ambient representation is not a default element
of every represented carrier. -/
theorem unrestricted_choice_impossible :
    ¬ Nonempty ((A : Type) → (P : A → Prop) → A) := by
  rintro ⟨choose⟩
  exact (choose Empty (fun _ => True)).elim

/-- Evidence-carrying selection works without asserting inhabitedness of an
arbitrary type or importing a global choice operation. -/
def selectWitness {A : Type u} {P : A → Prop} (witness : {a : A // P a}) : A :=
  witness.val

theorem selectWitness_valid {A : Type u} {P : A → Prop} (witness : {a : A // P a}) :
    P (selectWitness witness) := witness.property

end Mettapedia.Logic.HOL.Embedding.RelativizedCarrier
