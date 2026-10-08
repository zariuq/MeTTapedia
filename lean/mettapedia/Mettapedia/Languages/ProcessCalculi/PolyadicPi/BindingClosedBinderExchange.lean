import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralLaws
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinaryValues

/-!
# Whole private-binder exchange from the independent target schema

The authored binary structural metavariable ranges over the complete
two-name function object. Its ordered reading earns private-binder exchange
for every supplied body arrow, with arbitrary ambient parameters. The
comparison exchanges precisely the two bound positions and preserves the
complete ambient projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinderExchange

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open BindingClosedPrimitiveOperations BindingClosedStructuralValues BindingClosedStructuralLaws
open BindingClosedBinaryValues
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (exchange)

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)

def binaryMetadata {Z : C} (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding)) :
    Z ⟶ binding.model.family AllArity.structuralMetas :=
  lift (inactiveMetadata binding Z ≫ fst _ _)
    (lift (function ≫ binaryBody binding) (toUnit Z))

theorem binaryMetadata_second {Z : C}
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding)) :
    binaryMetadata binding function ≫ snd _ _ ≫ fst _ _ = function ≫ binaryBody binding := by
  change lift _ (lift (function ≫ binaryBody binding) (toUnit Z)) ≫ snd _ _ ≫ fst _ _ = _
  rw [lift_snd_assoc, lift_fst]

theorem private_swap_function
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding)) :
    MonoidalClosed.curry
      (MonoidalClosed.curry ((α_ (names binding) (names binding) Z).inv ≫
        MonoidalClosed.uncurry function) ≫ (continuation binding).fresh) ≫ (continuation binding).fresh =
      MonoidalClosed.curry
        (MonoidalClosed.curry ((α_ (names binding) (names binding) Z).inv ≫
          exchange (names binding) (names binding) ▷ Z ≫ MonoidalClosed.uncurry function) ≫
            (continuation binding).fresh) ≫ (continuation binding).fresh := by
  let environment : binding.model.Env Z [] := fun _ position => nomatch position
  have same := satisfied ⟨5, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .nu) (.cons (.op (.inl .nu)
        (.cons (binaryMeta (.var .zero) (.var (.succ .zero))) .nil)) .nil)) =
    binding.model.interp AllArity.structuralMetas
      (.op (.inl .nu) (.cons (.op (.inl .nu)
        (.cons (binaryMeta (.var (.succ .zero)) (.var .zero)) .nil)) .nil)) at same
  have atStage := congrArg
    (fun reading => reading.value Z (binaryMetadata binding function) environment) same
  erw [private_complete_value, private_complete_value,
    private_complete_value, private_complete_value] at atStage
  have projected : snd (names binding) (names binding ⊗ Z) ≫
      (snd (names binding) Z ≫ binaryMetadata binding function) =
      ambientProjection binding ≫ binaryMetadata binding function := (Category.assoc _ _ _).symm
  rw [projected] at atStage
  rw [binary_bound_value binding _ environment function (binaryMetadata_second binding function),
    binary_bound_swapped_value binding _ environment function (binaryMetadata_second binding function)] at atStage
  exact atStage

def binderExchange (Z : C) : names binding ⊗ (names binding ⊗ Z) ⟶ names binding ⊗ (names binding ⊗ Z) :=
  (α_ (names binding) (names binding) Z).inv ≫
    exchange (names binding) (names binding) ▷ Z ≫ (α_ (names binding) (names binding) Z).hom

theorem binderExchange_newest (Z : C) :
    binderExchange binding Z ≫ fst (names binding) (names binding ⊗ Z) =
      snd (names binding) (names binding ⊗ Z) ≫ fst (names binding) Z := by
  simp [binderExchange, exchange]

theorem binderExchange_previous (Z : C) :
    binderExchange binding Z ≫ snd (names binding) (names binding ⊗ Z) ≫ fst (names binding) Z =
      fst (names binding) (names binding ⊗ Z) := by
  simp [binderExchange, exchange]

theorem binderExchange_ambient (Z : C) :
    binderExchange binding Z ≫ ambientProjection binding = ambientProjection (Z := Z) binding := by
  simp [binderExchange, ambientProjection]

theorem private_swap
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (body : names binding ⊗ (names binding ⊗ Z) ⟶ processes binding) :
    MonoidalClosed.curry (MonoidalClosed.curry body ≫ (continuation binding).fresh) ≫
        (continuation binding).fresh =
      MonoidalClosed.curry (MonoidalClosed.curry (binderExchange binding Z ≫ body) ≫
        (continuation binding).fresh) ≫ (continuation binding).fresh := by
  have same := private_swap_function binding satisfied
    (MonoidalClosed.curry ((α_ (names binding) (names binding) Z).hom ≫ body))
  simpa only [MonoidalClosed.uncurry_curry, Category.assoc, Iso.inv_hom_id_assoc,
    binderExchange] using same

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinderExchange
