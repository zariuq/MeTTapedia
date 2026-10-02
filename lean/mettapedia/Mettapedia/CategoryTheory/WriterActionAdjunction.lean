import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.CategoryTheory.MonadResolutionObstruction

/-!
# Writer accounts as free monoid actions

The target objects are Mathlib's independently specified monoid actions,
not algebras defined by referring to the writer monad.  Extension of a map
from generators gives the concrete free-forgetful adjunction.  Forgetting
retains the whole account-value pair; projecting away the account is a
different erasure.

This comparison supplies reusable account algebra.  It does not identify
resource-gated language transformations with writer enrichment.
-/

open CategoryTheory CategoryTheory.Category

namespace Mettapedia.CategoryTheory.WriterActionAdjunction

set_option autoImplicit false

universe u

variable (M : Type u) [Monoid M]

/-- A free action retains an arbitrary account together with its generator. -/
def freeObject (X : Type u) : Action (Type u) M where
  V := M × X
  ρ :=
    { toFun := fun account => TypeCat.ofHom fun pair =>
        (account * pair.1, pair.2)
      map_one' := by
        apply End.ext
        apply ConcreteCategory.ext_apply
        intro pair
        exact Prod.ext (one_mul pair.1) rfl
      map_mul' := by
        intro first second
        apply End.ext
        apply ConcreteCategory.ext_apply
        intro pair
        exact Prod.ext (mul_assoc first second pair.1) rfl }

/-- Generator maps preserve the entire account coordinate. -/
def freeFunctor : Type u ⥤ Action (Type u) M where
  obj := freeObject M
  map f :=
    { hom := TypeCat.ofHom fun pair => (pair.1, f pair.2)
      comm := fun _ => by ext pair; rfl }
  map_id := fun _ => by ext pair; rfl
  map_comp := fun _ _ => by ext pair; rfl

/-- Extend a generator map by the target's given monoid action. -/
def extend {X : Type u} (target : Action (Type u) M)
    (generator : X ⟶ target.V) : freeObject M X ⟶ target where
  hom := TypeCat.ofHom fun pair => (target.ρ pair.1) (generator pair.2)
  comm := by
    intro account
    ext pair
    exact congrArg (fun action : End target.V => action (generator pair.2))
      (target.ρ.map_mul account pair.1)

/-- Restrict an equivariant map to the unit-account generators. -/
def restrict {X : Type u} {target : Action (Type u) M}
    (mapping : freeObject M X ⟶ target) : X ⟶ target.V :=
  TypeCat.ofHom fun value => mapping.hom (1, value)

@[simp]
theorem restrict_extend {X : Type u} (target : Action (Type u) M)
    (generator : X ⟶ target.V) :
    restrict M (extend M target generator) = generator := by
  ext value
  change (target.ρ 1) (generator value) = generator value
  rw [target.ρ.map_one]
  rfl

@[simp]
theorem extend_restrict {X : Type u} {target : Action (Type u) M}
    (mapping : freeObject M X ⟶ target) :
    extend M target (restrict M mapping) = mapping := by
  ext pair
  rcases pair with ⟨account, value⟩
  have equivariant := congrArg
    (fun f : (M × X) ⟶ target.V => f (1, value)) (mapping.comm account)
  change mapping.hom (account * 1, value) =
    (target.ρ account) (mapping.hom (1, value)) at equivariant
  change (target.ρ account) (mapping.hom (1, value)) = mapping.hom (account, value)
  simpa only [mul_one] using equivariant.symm

/-- Every equivariant extension is uniquely fixed by its generator map. -/
theorem extension_unique {X : Type u} {target : Action (Type u) M}
    (generator : X ⟶ target.V) (mapping : freeObject M X ⟶ target)
    (onGenerators : restrict M mapping = generator) :
    mapping = extend M target generator := by
  rw [← onGenerators, extend_restrict]

/-- The concrete universal property, natural in generators and actions. -/
def homEquiv (X : Type u) (target : Action (Type u) M) :
    (freeObject M X ⟶ target) ≃ (X ⟶ target.V) where
  toFun := restrict M
  invFun := extend M target
  left_inv := extend_restrict M
  right_inv := restrict_extend M target

/-- Algebraic forgetting keeps the enlarged carrier of every free action. -/
def freeForgetAdjunction : freeFunctor M ⊣ Action.forget (Type u) M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv M
      homEquiv_naturality_left_symm := by
        intro first second target mapping generator
        ext pair
        rfl
      homEquiv_naturality_right := by
        intro source first second mapping after
        ext value
        rfl }

/-- The writer monad is induced by the independently specified action
adjunction; its carrier contains both the account and the value. -/
def writerMonad : CategoryTheory.Monad (Type u) :=
  (freeForgetAdjunction M).toMonad

@[simp]
theorem writer_obj (X : Type u) : (writerMonad M).obj X = (M × X) := rfl

@[simp]
theorem writer_unit_apply {X : Type u} (value : X) :
    (writerMonad M).η.app X value = (1, value) := rfl

@[simp]
theorem writer_multiplication_apply {X : Type u}
    (outer inner : M) (value : X) :
    (writerMonad M).μ.app X (outer, (inner, value)) =
      (outer * inner, value) := rfl

/-- Exact account erasure is separate from algebraic forgetting. -/
def eraseAccount : (writerMonad M).toFunctor ⟶ 𝟭 (Type u) where
  app _ := TypeCat.ofHom Prod.snd
  naturality := fun _ _ _ => by ext pair; rfl

/-- Returning then erasing is the identity, even for a nontrivial account
monoid.  This is a section-retraction law, not an identity free-forget round trip. -/
theorem erase_after_unit : (writerMonad M).η ≫ eraseAccount M = 𝟙 _ := by
  ext value
  rfl

/-- Flattening distinct nontrivial account factorizations loses information. -/
theorem multiplication_not_injective [Nontrivial M]
    {X : Type u} (value : X) :
    ¬ Function.Injective ((writerMonad M).μ.app X) := by
  intro injective
  obtain ⟨account, account_ne⟩ := exists_ne (1 : M)
  have nestedEquality : (1, (account, value)) = (account, (1, value)) := by
    apply injective
    change (1 * account, value) = (account * 1, value)
    rw [one_mul, mul_one]
  exact account_ne (congrArg Prod.fst nestedEquality).symm

/-- Hence the multiplication of this writer account monad is not
an isomorphism when a value and a nontrivial account exist. -/
theorem multiplication_not_isIso [Nontrivial M]
    {X : Type u} (value : X) :
    ¬ IsIso ((writerMonad M).μ.app X) := by
  intro invertible
  exact multiplication_not_injective M value
    ((isIso_iff_bijective _).mp invertible).1

/-- A nontrivial monoid supplies an inhabited carrier at which multiplication
fails to be invertible, so the whole natural transformation is not invertible. -/
theorem multiplication_not_isIso_natural [Nontrivial M] :
    ¬ IsIso (writerMonad M).μ := by
  intro invertible
  have : IsIso (writerMonad M).μ := invertible
  have : IsIso ((writerMonad M).μ.app M) := inferInstance
  exact multiplication_not_isIso M (1 : M) inferInstance

/-- The free-forget composite retains accounts.  Its genuine adjunction
therefore cannot have the natural identity round trip satisfied by literal
installation followed by syntactic stripping. -/
theorem freeForget_not_identity [Nontrivial M] :
    ¬ Nonempty (freeFunctor M ⋙ Action.forget (Type u) M ≅ 𝟭 (Type u)) := by
  exact MonadResolutionObstruction.no_identity_round_trip_of_noninvertible_multiplication
    (freeForgetAdjunction M) (multiplication_not_isIso_natural M)

#print axioms extension_unique
#print axioms freeForgetAdjunction
#print axioms erase_after_unit
#print axioms multiplication_not_injective
#print axioms multiplication_not_isIso
#print axioms multiplication_not_isIso_natural
#print axioms freeForget_not_identity

end Mettapedia.CategoryTheory.WriterActionAdjunction
