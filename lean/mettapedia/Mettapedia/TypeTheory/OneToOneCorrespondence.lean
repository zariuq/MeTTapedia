import Mathlib.Logic.Equiv.Defs

/-!
# One-to-one correspondences

Higher observational type theory takes the identity of two types to be a
one-to-one correspondence: a proof-relevant relation `R : A → B → Type` that is a
function in both directions, each `Σ b, R a b` and each `Σ a, R a b` being
contractible (Altenkirch, Kaposi and Shulman, *Towards Higher Observational Type
Theory*, TYPES 2022, §2).

This module gives the structure (`OneToOne`), with the contractions as data, and
compares it with equivalences:

* every correspondence gives an equivalence (`OneToOne.toEquiv`), and every
  equivalence gives the correspondence of its graph (`OneToOne.ofEquiv`);
* from equivalences, the round trip is the identity (`toEquiv_ofEquiv`);
* from correspondences, the round trip returns the graph of the forward
  function, which is fibrewise equivalent to the original relation
  (`relEquivGraph`).  Equality of the two relations would need univalence of
  the ambient universe, which Lean does not have.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory

universe u

/-- A one-to-one correspondence between two types: a proof-relevant relation
with a unique partner on each side. -/
structure OneToOne (X Y : Type u) where
  Rel : X → Y → Type u
  forward : (x : X) → (y : Y) × Rel x y
  forward_unique : ∀ x (pair : (y : Y) × Rel x y), pair = forward x
  backward : (y : Y) → (x : X) × Rel x y
  backward_unique : ∀ y (pair : (x : X) × Rel x y), pair = backward y

namespace OneToOne

variable {X Y : Type u}

/-- The equivalence of a correspondence: its forward and backward functions. -/
def toEquiv (c : OneToOne X Y) : X ≃ Y where
  toFun x := (c.forward x).1
  invFun y := (c.backward y).1
  left_inv x := by
    have := c.backward_unique (c.forward x).1 ⟨x, (c.forward x).2⟩
    exact (congrArg Sigma.fst this).symm
  right_inv y := by
    have := c.forward_unique (c.backward y).1 ⟨y, (c.backward y).2⟩
    exact (congrArg Sigma.fst this).symm

/-- The graph of a function, as a proof-relevant relation. -/
def Graph (f : X → Y) (x : X) (y : Y) : Type u :=
  ULift.{u} (PLift (f x = y))

instance Graph.instSubsingleton (f : X → Y) (x : X) (y : Y) : Subsingleton (Graph f x y) :=
  ⟨fun ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ => rfl⟩

/-- The correspondence of an equivalence: its graph. -/
def ofEquiv (e : X ≃ Y) : OneToOne X Y where
  Rel := Graph e
  forward x := ⟨e x, ⟨⟨rfl⟩⟩⟩
  forward_unique x pair := by
    obtain ⟨y, ⟨⟨h⟩⟩⟩ := pair
    subst h
    rfl
  backward y := ⟨e.symm y, ⟨⟨e.apply_symm_apply y⟩⟩⟩
  backward_unique y pair := by
    obtain ⟨x, ⟨⟨h⟩⟩⟩ := pair
    subst h
    exact Sigma.ext (e.symm_apply_apply x).symm
      (Subsingleton.helim (congrArg (fun z => Graph e z (e x)) (e.symm_apply_apply x).symm) _ _)

@[simp] theorem toEquiv_apply (c : OneToOne X Y) (x : X) : c.toEquiv x = (c.forward x).1 :=
  rfl

/-- **From equivalences, the round trip is the identity.** -/
theorem toEquiv_ofEquiv (e : X ≃ Y) : (ofEquiv e).toEquiv = e :=
  Equiv.ext fun _ => rfl

theorem cast_snd_of_eq {R : Y → Type u} {y : Y} {r : R y} {pair : (y : Y) × R y}
    (equal : (⟨y, r⟩ : (y : Y) × R y) = pair) :
    cast (congrArg R (congrArg Sigma.fst equal).symm) pair.2 = r := by
  subst equal
  rfl

/-- **From correspondences, the round trip is fibrewise equivalent**: each fibre
of the relation is equivalent to the fibre of the graph of the forward
function. -/
def relEquivGraph (c : OneToOne X Y) (x : X) (y : Y) :
    c.Rel x y ≃ Graph c.toEquiv x y where
  toFun r := ⟨⟨(congrArg Sigma.fst (c.forward_unique x ⟨y, r⟩)).symm⟩⟩
  invFun h := cast (congrArg (c.Rel x) h.down.down) (c.forward x).2
  left_inv r := cast_snd_of_eq (c.forward_unique x ⟨y, r⟩)
  right_inv _ := rfl

/-- The identity correspondence. -/
def refl (X : Type u) : OneToOne X X :=
  ofEquiv (Equiv.refl X)

end OneToOne

end Mettapedia.TypeTheory
