import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange

/-!
# Identity and composition for indexed covered-power base change

The nested argument pullback has an explicit natural comparison with the
direct pullback. Flattening retains the original argument and final
parameter; its inverse reconstructs the intermediate parameter from the
declared map. Both inverse laws are proved, and their direct-image maps
give inverse comparisons of the parameter-supported power families.

Successive power base change agrees with direct base change after those
constructed comparisons. The identity case has independently constructed
argument maps and a commuting power square. No argument is chosen from
an image proof and no differently structured pullback is equated by fiat.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerCoherence

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond)
open IndexedCoveredPowerBaseChange

universe u v w t s
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t} {G : D ⥤ Type s}
variable (operation : NaturalHom A B) (earlier : NaturalHom F B) (later : NaturalHom G F)

abbrev nestedArguments := argumentFamily (parameterProjection operation earlier) later
abbrev directArguments := argumentFamily operation (later.comp earlier)
abbrev nestedParameter := parameterProjection (parameterProjection operation earlier) later
abbrev directParameter := parameterProjection operation (later.comp earlier)

def flatten : NaturalHom (nestedArguments operation earlier later) (directArguments operation earlier later) where
  app point pair := ⟨(pair.val.1.val.1, pair.val.2),
    pair.val.1.property.trans (congrArg (earlier.app point) pair.property)⟩
  naturality _ _ := rfl

def unflatten : NaturalHom (directArguments operation earlier later) (nestedArguments operation earlier later) where
  app point pair := ⟨(⟨(pair.val.1, later.app point pair.val.2), pair.property⟩, pair.val.2), rfl⟩
  naturality step pair := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl (later.naturality step pair.val.2)
    · rfl

theorem flatten_unflatten (point : D) (pair : (nestedArguments operation earlier later).obj point) :
    (unflatten operation earlier later).app point ((flatten operation earlier later).app point pair) = pair := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext rfl pair.property.symm
  · rfl

theorem unflatten_flatten (point : D) (pair : (directArguments operation earlier later).obj point) :
    (flatten operation earlier later).app point ((unflatten operation earlier later).app point pair) = pair := rfl

theorem flatten_unflatten_hom :
    (flatten operation earlier later).comp (unflatten operation earlier later) =
      identityHom (nestedArguments operation earlier later) := by
  apply NaturalHom.ext
  exact flatten_unflatten operation earlier later

theorem unflatten_flatten_hom :
    (unflatten operation earlier later).comp (flatten operation earlier later) =
      identityHom (directArguments operation earlier later) := by
  apply NaturalHom.ext
  exact unflatten_flatten operation earlier later

theorem flatten_parameter :
    (flatten operation earlier later).comp (directParameter operation earlier later) =
      nestedParameter operation earlier later := rfl

theorem unflatten_parameter :
    (unflatten operation earlier later).comp (nestedParameter operation earlier later) =
      directParameter operation earlier later := rfl

def powerFlatten := IndexedCoveredPower.image (nestedParameter operation earlier later)
  (directParameter operation earlier later) (flatten operation earlier later)
  (flatten_parameter operation earlier later)

def powerUnflatten := IndexedCoveredPower.image (directParameter operation earlier later)
  (nestedParameter operation earlier later) (unflatten operation earlier later)
  (unflatten_parameter operation earlier later)

theorem power_flatten_unflatten (point : D)
    (entry : (IndexedCoveredPower.family (nestedParameter operation earlier later)).obj point) :
    (powerUnflatten operation earlier later).app point
      ((powerFlatten operation earlier later).app point entry) = entry := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change imagePower (unflatten operation earlier later) point
        (imagePower (flatten operation earlier later) point entry.val.2) = entry.val.2
    rw [imagePower_comp, flatten_unflatten_hom, imagePower_identity]

theorem power_unflatten_flatten (point : D)
    (entry : (IndexedCoveredPower.family (directParameter operation earlier later)).obj point) :
    (powerFlatten operation earlier later).app point
      ((powerUnflatten operation earlier later).app point entry) = entry := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change imagePower (flatten operation earlier later) point
        (imagePower (unflatten operation earlier later) point entry.val.2) = entry.val.2
    rw [imagePower_comp, unflatten_flatten_hom, imagePower_identity]

def powerFibreEquiv (point : D) :
    (IndexedCoveredPower.family (nestedParameter operation earlier later)).obj point ≃
      (IndexedCoveredPower.family (directParameter operation earlier later)).obj point where
  toFun := (powerFlatten operation earlier later).app point
  invFun := (powerUnflatten operation earlier later).app point
  left_inv := power_flatten_unflatten operation earlier later point
  right_inv := power_unflatten_flatten operation earlier later point

def powerSectionEquiv :
    (IndexedCoveredPower.family (nestedParameter operation earlier later)).sections ≃
      (IndexedCoveredPower.family (directParameter operation earlier later)).sections where
  toFun := (powerFlatten operation earlier later).mapSection
  invFun := (powerUnflatten operation earlier later).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact power_flatten_unflatten operation earlier later point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact power_unflatten_flatten operation earlier later point (term.val point)

def successiveBase : NaturalHom (baseFamily (parameterProjection operation earlier) later)
    (baseFamily operation (later.comp earlier)) where
  app point entry :=
    let inner := (forward operation earlier).app point entry.val.1
    ⟨(inner.val.1, entry.val.2), congrArg (earlier.app point) entry.property⟩
  naturality step entry := by
    apply Subtype.ext
    apply Prod.ext
    · have inner := (forward operation earlier).naturality step entry.val.1
      exact congrArg
        (fun pair : (baseFamily operation earlier).obj _ => pair.val.1) inner
    · rfl

def successiveForward := (forward (parameterProjection operation earlier) later).comp
  (successiveBase operation earlier later)

def directForward := (powerFlatten operation earlier later).comp
  (forward operation (later.comp earlier))

theorem flatten_argument :
    (flatten operation earlier later).comp (argumentProjection operation (later.comp earlier)) =
      (argumentProjection (parameterProjection operation earlier) later).comp
        (argumentProjection operation earlier) := rfl

theorem base_change_comp : successiveForward operation earlier later = directForward operation earlier later := by
  apply NaturalHom.ext
  intro point entry
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · change imagePower (argumentProjection operation earlier) point
          (imagePower (argumentProjection (parameterProjection operation earlier) later) point entry.val.2) =
        imagePower (argumentProjection operation (later.comp earlier)) point
          (imagePower (flatten operation earlier later) point entry.val.2)
      rw [imagePower_comp, imagePower_comp, flatten_argument]
  · rfl

def identityInsert : NaturalHom A (argumentFamily operation (identityHom B)) where
  app point argument := ⟨(argument, operation.app point argument), rfl⟩
  naturality step argument := by
    apply Subtype.ext
    exact Prod.ext rfl (operation.naturality step argument)

def identityFlatten : NaturalHom (argumentFamily operation (identityHom B)) A :=
  argumentProjection operation (identityHom B)

theorem identity_flatten_insert (point : D) (pair : (argumentFamily operation (identityHom B)).obj point) :
    (identityInsert operation).app point ((identityFlatten operation).app point pair) = pair := by
  apply Subtype.ext
  exact Prod.ext rfl pair.property

theorem identity_insert_flatten (point : D) (argument : A.obj point) :
    (identityFlatten operation).app point ((identityInsert operation).app point argument) = argument := rfl

theorem identity_flatten_insert_hom :
    (identityFlatten operation).comp (identityInsert operation) =
      identityHom (argumentFamily operation (identityHom B)) := by
  apply NaturalHom.ext
  exact identity_flatten_insert operation

theorem identity_insert_flatten_hom :
    (identityInsert operation).comp (identityFlatten operation) = identityHom A := by
  apply NaturalHom.ext
  exact identity_insert_flatten operation

theorem identity_flatten_parameter :
    (identityFlatten operation).comp operation = parameterProjection operation (identityHom B) := by
  apply NaturalHom.ext
  intro _ pair
  exact pair.property

def identityPower := IndexedCoveredPower.image (parameterProjection operation (identityHom B)) operation
  (identityFlatten operation) (identity_flatten_parameter operation)

def identityPowerInsert := IndexedCoveredPower.image operation (parameterProjection operation (identityHom B))
  (identityInsert operation) rfl

theorem identity_power_flatten_insert (point : D)
    (entry : (IndexedCoveredPower.family (parameterProjection operation (identityHom B))).obj point) :
    (identityPowerInsert operation).app point ((identityPower operation).app point entry) = entry := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change imagePower (identityInsert operation) point
        (imagePower (identityFlatten operation) point entry.val.2) = entry.val.2
    rw [imagePower_comp, identity_flatten_insert_hom, imagePower_identity]

theorem identity_power_insert_flatten (point : D)
    (entry : (IndexedCoveredPower.family operation).obj point) :
    (identityPower operation).app point ((identityPowerInsert operation).app point entry) = entry := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change imagePower (identityFlatten operation) point
        (imagePower (identityInsert operation) point entry.val.2) = entry.val.2
    rw [imagePower_comp, identity_insert_flatten_hom, imagePower_identity]

def identityBase : NaturalHom (IndexedCoveredPower.family operation) (baseFamily operation (identityHom B)) where
  app _ entry := ⟨(entry, entry.val.1), rfl⟩
  naturality _ _ := rfl

theorem base_change_identity :
    (identityPower operation).comp (identityBase operation) = forward operation (identityHom B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerCoherence
