import Mettapedia.CategoryTheory.WriterActionObservation
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Free accounts over a fixed observation

The source is the existing slice of types over `K`.  The target is the existing
slice of monoid actions over the trivial action on `K`.  Mathlib's slice
adjunction construction lifts the concrete free-action adjunction, so algebraic
forgetting retains both the account and the generator while retaining its
specified observation.

The resulting monad multiplies account coordinates and keeps the generator's
observation.  These fixed-fibre models do not construct the authored Cost
transformer, substitution actions, or retained-language iteration.
-/

open CategoryTheory CategoryTheory.Category

namespace Mettapedia.CategoryTheory.WriterActionSlice

open WriterActionAdjunction

set_option autoImplicit false

universe u

variable (M K : Type u) [Monoid M]

/-- Install a free account and map its observation to the trivial action. -/
def install : Over K ⥤ Over (Action.trivial M K) :=
  Over.post (freeFunctor M) ⋙
    Over.map ((WriterActionAdjunction.freeForgetAdjunction M).counit.app
      (Action.trivial M K))

/-- Forget the action, retaining its complete carrier and observation. -/
def forget : Over (Action.trivial M K) ⥤ Over K :=
  Over.post (Action.forget (Type u) M)

/-- The actual adjunction on the two independently specified slices. -/
def freeForgetAdjunction : install M K ⊣ forget M K :=
  Over.postAdjunctionRight (Y := Action.trivial M K)
    (WriterActionAdjunction.freeForgetAdjunction M)

/-- The slice universal property is natural in generators and account models. -/
def homEquiv (generator : Over K) (target : Over (Action.trivial M K)) :
    ((install M K).obj generator ⟶ target) ≃
      (generator ⟶ (forget M K).obj target) :=
  (freeForgetAdjunction M K).homEquiv generator target

/-- The universal property respects maps of observed generators. -/
theorem homEquiv_naturality_left {first second : Over K}
    {target : Over (Action.trivial M K)} (before : first ⟶ second)
    (mapping : (install M K).obj second ⟶ target) :
    homEquiv M K first target ((install M K).map before ≫ mapping) =
      before ≫ homEquiv M K second target mapping :=
  (freeForgetAdjunction M K).homEquiv_naturality_left before mapping

/-- The universal property respects equivariant maps over the observation. -/
theorem homEquiv_naturality_right {generator : Over K}
    {first second : Over (Action.trivial M K)}
    (mapping : (install M K).obj generator ⟶ first) (after : first ⟶ second) :
    homEquiv M K generator second (mapping ≫ after) =
      homEquiv M K generator first mapping ≫ (forget M K).map after :=
  (freeForgetAdjunction M K).homEquiv_naturality_right mapping after

/-- Forgetting the observation from installation gives the original free action. -/
theorem install_underlying :
    install M K ⋙ Over.forget (Action.trivial M K) =
      Over.forget K ⋙ freeFunctor M := rfl

/-- Algebraic forgetting retains the same underlying account carrier. -/
theorem forget_underlying :
    forget M K ⋙ Over.forget K =
      Over.forget (Action.trivial M K) ⋙ Action.forget (Type u) M := rfl

/-- Free installation preserves precisely the given generator observation. -/
theorem install_observation_apply (generator : Over K)
    (account : M) (value : generator.left) :
    ((install M K).obj generator).hom.hom (account, value) =
      generator.hom value := rfl

/-- Restriction reads the actual equivariant map at unit-account generators. -/
theorem homEquiv_apply (generator : Over K) (target : Over (Action.trivial M K))
    (mapping : (install M K).obj generator ⟶ target) (value : generator.left) :
    (homEquiv M K generator target mapping).left value =
      mapping.left.hom (1, value) := rfl

/-- Extension uses the independently specified target action. -/
theorem homEquiv_symm_apply (generator : Over K)
    (target : Over (Action.trivial M K))
    (mapping : generator ⟶ (forget M K).obj target)
    (account : M) (value : generator.left) :
    ((homEquiv M K generator target).symm mapping).left.hom (account, value) =
      (target.left.ρ account) (mapping.left value) := rfl

/-- The observation-respecting equivariant extension is uniquely fixed by its
values on the unit-account generators. -/
theorem extension_unique (generator : Over K) (target : Over (Action.trivial M K))
    (mapping : generator ⟶ (forget M K).obj target)
    (extension : (install M K).obj generator ⟶ target)
    (onGenerators : ∀ value, extension.left.hom (1, value) = mapping.left value) :
    extension = (homEquiv M K generator target).symm mapping := by
  apply (homEquiv M K generator target).injective
  rw [Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  apply ConcreteCategory.ext_apply
  intro value
  exact onGenerators value

/-- The monad induced by algebraic installation and forgetting in the slices. -/
def writerMonad : CategoryTheory.Monad (Over K) :=
  (freeForgetAdjunction M K).toMonad

/-- The derived monad has the original writer carrier after dropping only
the specified observation map from its slice object. -/
theorem writer_underlying :
    (writerMonad M K).toFunctor ⋙ Over.forget K =
      Over.forget K ⋙ (WriterActionAdjunction.writerMonad M).toFunctor := rfl

theorem writer_unit_underlying (generator : Over K) :
    ((writerMonad M K).η.app generator).left =
      (WriterActionAdjunction.writerMonad M).η.app generator.left := rfl

theorem writer_multiplication_underlying (generator : Over K) :
    ((writerMonad M K).μ.app generator).left =
      (WriterActionAdjunction.writerMonad M).μ.app generator.left := rfl

theorem writer_obj_left (generator : Over K) :
    ((writerMonad M K).obj generator).left = (M × generator.left) := rfl

theorem writer_unit_apply (generator : Over K) (value : generator.left) :
    ((writerMonad M K).η.app generator).left value = (1, value) := rfl

theorem writer_multiplication_apply (generator : Over K)
    (outer inner : M) (value : generator.left) :
    ((writerMonad M K).μ.app generator).left (outer, (inner, value)) =
      (outer * inner, value) := rfl

/-- The actual slice multiplication retains the selected generator observation. -/
theorem multiplication_preserves_observation (generator : Over K)
    (outer inner : M) (value : generator.left) :
    ((writerMonad M K).obj generator).hom
      (((writerMonad M K).μ.app generator).left (outer, (inner, value))) =
      generator.hom value := rfl

/-- Adding an observation to the domain does not recover multiplied factors. -/
theorem multiplication_not_injective [Nontrivial M]
    (generator : Over K) (value : generator.left) :
    ¬ Function.Injective (((writerMonad M K).μ.app generator).left) :=
  WriterActionAdjunction.multiplication_not_injective M value

/-- A selected observation does not turn genuine account multiplication into
an isomorphism when the observed generator carrier is inhabited. -/
theorem multiplication_not_isIso [Nontrivial M]
    (generator : Over K) (value : generator.left) :
    ¬ IsIso ((writerMonad M K).μ.app generator) := by
  intro invertible
  have : IsIso ((writerMonad M K).μ.app generator) := invertible
  have underlying : IsIso ((Over.forget K).map
    ((writerMonad M K).μ.app generator)) := inferInstance
  exact multiplication_not_injective M K generator value
    ((isIso_iff_bijective _).mp underlying).1

#print axioms freeForgetAdjunction
#print axioms extension_unique
#print axioms homEquiv_naturality_left
#print axioms homEquiv_naturality_right
#print axioms writer_underlying
#print axioms writer_unit_underlying
#print axioms writer_multiplication_underlying
#print axioms writer_unit_apply
#print axioms writer_multiplication_apply
#print axioms multiplication_preserves_observation
#print axioms multiplication_not_injective
#print axioms multiplication_not_isIso

end Mettapedia.CategoryTheory.WriterActionSlice
