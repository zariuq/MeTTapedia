import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Finite-arity operation theories of lawful monads

An operation from arity `n` to arity `m` is an `m`-tuple of computations with
`n` free variables. Substitution is the opposite of Kleisli composition.
Arity addition supplies binary products, and arity zero is terminal. These
are genuine finite-product universal properties, not equations postulated
on a particular evaluator.

A handler preserving return and substitution induces a functor of operation
theories. It preserves the explicit projections and tupling. Whether such
computations are finitary, and which operational enrichment they carry, are
additional qualifications; neither property is imposed on arbitrary monads.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.FiniteOperationTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable (M : Type → Type u) [Monad M] [LawfulMonad M]

def objectOf (arity : Nat) : (KleisliCat M)ᵒᵖ := op (KleisliCat.mk M (Fin arity))

abbrev Theory := InducedCategory (KleisliCat M)ᵒᵖ (objectOf M)

abbrev arity (object : Theory M) : Nat := object
abbrev object (arity : Nat) : Theory M := arity

variable {M}

def terms {n m : Theory M} (operation : n ⟶ m) : Fin (arity M m) → M (Fin (arity M n)) :=
  operation.hom.unop

def ofTerms {n m : Theory M} (operation : Fin (arity M m) → M (Fin (arity M n))) : n ⟶ m :=
  InducedCategory.homMk
    (show KleisliCat.mk M (Fin (arity M m)) ⟶ KleisliCat.mk M (Fin (arity M n))
      from operation).op

@[simp] theorem terms_ofTerms {n m : Theory M}
    (operation : Fin (arity M m) → M (Fin (arity M n))) :
    terms (ofTerms operation) = operation := rfl

@[ext] theorem terms_ext {n m : Theory M} {first second : n ⟶ m}
    (same : ∀ index, terms first index = terms second index) : first = second := by
  apply InducedCategory.hom_ext
  exact Quiver.Hom.unop_inj (funext same)

@[simp] theorem terms_identity (n : Theory M) (index : Fin (arity M n)) :
    terms (𝟙 n) index = pure index := rfl

@[simp] theorem terms_compose {n m k : Theory M} (first : n ⟶ m) (second : m ⟶ k)
    (index : Fin (arity M k)) :
    terms (first ≫ second) index = terms second index >>= terms first := rfl

def firstProjection (n m : Nat) : object M (n + m) ⟶ object M n :=
  ofTerms fun index => pure (index.castAdd m)

def secondProjection (n m : Nat) : object M (n + m) ⟶ object M m :=
  ofTerms fun index => pure (index.natAdd n)

def tuple {n : Theory M} {m k : Nat} (first : n ⟶ object M m) (second : n ⟶ object M k) :
    n ⟶ object M (m + k) := ofTerms (Fin.addCases (terms first) (terms second))

@[simp] theorem tuple_first {n : Theory M} {m k : Nat}
    (first : n ⟶ object M m) (second : n ⟶ object M k) :
    tuple first second ≫ firstProjection m k = first := by
  apply terms_ext
  intro index
  simp [firstProjection, tuple]

@[simp] theorem tuple_second {n : Theory M} {m k : Nat}
    (first : n ⟶ object M m) (second : n ⟶ object M k) :
    tuple first second ≫ secondProjection m k = second := by
  apply terms_ext
  intro index
  simp [secondProjection, tuple]

theorem tuple_unique {n : Theory M} {m k : Nat}
    (first : n ⟶ object M m) (second : n ⟶ object M k)
    (combined : n ⟶ object M (m + k))
    (left : combined ≫ firstProjection m k = first)
    (right : combined ≫ secondProjection m k = second) : combined = tuple first second := by
  apply terms_ext
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro index
    have equality := congrArg (fun operation => terms operation index) left
    simpa [firstProjection, tuple] using equality
  · intro index
    have equality := congrArg (fun operation => terms operation index) right
    simpa [secondProjection, tuple] using equality

def productFan (n m : Nat) : BinaryFan (object M n) (object M m) :=
  BinaryFan.mk (firstProjection n m) (secondProjection n m)

def productIsLimit (n m : Nat) : IsLimit (productFan (M := M) n m) :=
  BinaryFan.IsLimit.mk _ (fun first second => tuple first second)
    (fun first second => tuple_first first second)
    (fun first second => tuple_second first second)
    (fun first second combined left right => tuple_unique first second combined left right)

def zeroIsTerminal : IsTerminal (object M 0) :=
  IsTerminal.ofUniqueHom (fun _ => ofTerms Fin.elim0) (by
    intro source morphism
    apply terms_ext
    intro index
    exact Fin.elim0 index)

variable {N : Type → Type v} [Monad N] [LawfulMonad N]

/-- A lawful handler maps operations in every arity, not just closed answers. -/
def handlerFunctor (handle : {A : Type} → M A → N A)
    (returns : ∀ {A : Type} (answer : A), handle (pure answer) = pure answer)
    (substitutes : ∀ {A B : Type} (computation : M A) (next : A → M B),
      handle (computation >>= next) = handle computation >>= fun answer => handle (next answer)) :
    Theory M ⥤ Theory N where
  obj n := object N (arity M n)
  map operation := ofTerms fun index => handle (terms operation index)
  map_id source := by
    apply terms_ext
    intro index
    exact returns index
  map_comp first second := by
    apply terms_ext
    intro index
    exact substitutes (terms second index) (terms first)

theorem handler_preserves_firstProjection
    (handle : {A : Type} → M A → N A)
    (returns : ∀ {A : Type} (answer : A), handle (pure answer) = pure answer)
    (substitutes : ∀ {A B : Type} (computation : M A) (next : A → M B),
      handle (computation >>= next) = handle computation >>= fun answer => handle (next answer))
    (n m : Nat) :
    (handlerFunctor handle returns substitutes).map (firstProjection n m) =
      firstProjection (M := N) n m := by
  apply terms_ext
  intro index
  exact returns (index.castAdd m)

theorem handler_preserves_secondProjection
    (handle : {A : Type} → M A → N A)
    (returns : ∀ {A : Type} (answer : A), handle (pure answer) = pure answer)
    (substitutes : ∀ {A B : Type} (computation : M A) (next : A → M B),
      handle (computation >>= next) = handle computation >>= fun answer => handle (next answer))
    (n m : Nat) :
    (handlerFunctor handle returns substitutes).map (secondProjection n m) =
      secondProjection (M := N) n m := by
  apply terms_ext
  intro index
  exact returns (index.natAdd n)

theorem handler_preserves_tuple
    (handle : {A : Type} → M A → N A)
    (returns : ∀ {A : Type} (answer : A), handle (pure answer) = pure answer)
    (substitutes : ∀ {A B : Type} (computation : M A) (next : A → M B),
      handle (computation >>= next) = handle computation >>= fun answer => handle (next answer))
    {n : Theory M} {m k : Nat} (first : n ⟶ object M m) (second : n ⟶ object M k) :
    (handlerFunctor handle returns substitutes).map (tuple first second) =
      tuple ((handlerFunctor handle returns substitutes).map first)
        ((handlerFunctor handle returns substitutes).map second) := by
  apply terms_ext
  intro index
  refine Fin.addCases ?_ ?_ index <;> intro index <;> simp [handlerFunctor, tuple]

end Mettapedia.CategoryTheory.FiniteOperationTheory
