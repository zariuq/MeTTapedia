import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralValues

/-!
# Complete two-name structural metadata

The second structural metavariable receives both supplied names in their
authored order. Its actual argument-tuple function is compared with the
canonical binary function object using the genuine associator and unit
comparison. Both binder positions remain distinct in these readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinaryValues

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open BindingClosedPrimitiveOperations BindingClosedStructuralValues

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)
variable {context : Ctx AllArity.sig} {Z : C}

def binaryMeta {scope : Ctx AllArity.sig}
    (first second : Term (withMetas AllArity.sig AllArity.structuralMetas) scope .nm) :
    Term (withMetas AllArity.sig AllArity.structuralMetas) scope .pr :=
  .op (.inr (MetaOp.mk (M := AllArity.structuralMetas) ⟨1, by decide⟩))
    (.cons first (.cons second .nil))

theorem binary_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (first second : Term (withMetas AllArity.sig AllArity.structuralMetas) context .nm) :
    (binding.model.interp AllArity.structuralMetas (binaryMeta first second)).value Z parameters environment =
      lift
        (lift ((binding.model.interp AllArity.structuralMetas first).value Z parameters environment)
          (lift ((binding.model.interp AllArity.structuralMetas second).value Z parameters environment)
            (toUnit Z)))
        (parameters ≫ snd _ _ ≫ fst _ _) ≫
          (ihom.ev (names binding ⊗ (names binding ⊗ 𝟙_ C))).app (processes binding) := rfl

theorem binary_tuple_value (first second : Z ⟶ names binding) :
    lift first (lift second (toUnit Z)) ≫ (binaryTuple binding).hom = lift first second := by
  unfold binaryTuple
  apply hom_ext <;> simp

theorem binary_function_evaluation (first second : Z ⟶ names binding)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding)) :
    lift (lift first (lift second (toUnit Z))) (function ≫ binaryBody binding) ≫
      (ihom.ev (tuple binding 2)).app (processes binding) =
      lift (lift first second) function ≫ (ihom.ev (names binding ⊗ names binding)).app (processes binding) := by
  have paired : lift (lift first (lift second (toUnit Z))) (function ≫ binaryBody binding) =
      lift (lift first (lift second (toUnit Z))) function ≫ (tuple binding 2 ◁ binaryBody binding) := by
    change lift (lift first (lift second (toUnit Z))) (function ≫ binaryBody binding) =
      lift (lift first (lift second (toUnit Z))) function ≫
        ((names binding ⊗ (names binding ⊗ 𝟙_ C)) ◁ binaryBody binding)
    apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, lift_snd_assoc,
      whiskerLeft_fst, whiskerLeft_snd]
  rw [paired, Category.assoc, binary_body_evaluation, ← Category.assoc]
  congr 1
  apply hom_ext
  · simp only [Category.assoc, whiskerRight_fst, lift_fst]
    change lift (lift first (lift second (toUnit Z))) function ≫
      fst (names binding ⊗ (names binding ⊗ 𝟙_ C)) ((names binding ⊗ names binding) ⟶[C] processes binding) ≫
        (binaryTuple binding).hom = lift first second
    rw [lift_fst_assoc]
    exact binary_tuple_value binding first second
  · simp

theorem binary_supplied_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (first second : Term (withMetas AllArity.sig AllArity.structuralMetas) context .nm)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding))
    (second_read : parameters ≫ snd _ _ ≫ fst _ _ = function ≫ binaryBody binding) :
    (binding.model.interp AllArity.structuralMetas (binaryMeta first second)).value Z parameters environment =
      lift
        (lift ((binding.model.interp AllArity.structuralMetas first).value Z parameters environment)
          ((binding.model.interp AllArity.structuralMetas second).value Z parameters environment))
        function ≫ (ihom.ev (names binding ⊗ names binding)).app (processes binding) := by
  rw [binary_value, second_read]
  exact binary_function_evaluation binding _ _ function

def ambientProjection : names binding ⊗ (names binding ⊗ Z) ⟶ Z :=
  snd _ _ ≫ snd _ _

theorem binary_bound_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding))
    (second_read : parameters ≫ snd _ _ ≫ fst _ _ = function ≫ binaryBody binding) :
    (binding.model.interp AllArity.structuralMetas
      (binaryMeta (.var .zero) (.var (.succ .zero)) :
        Term (withMetas AllArity.sig AllArity.structuralMetas) (.nm :: .nm :: context) .pr)).value
          (names binding ⊗ (names binding ⊗ Z)) (ambientProjection binding ≫ parameters)
          (nameEnvironment binding (nameEnvironment binding environment)) =
      (α_ (names binding) (names binding) Z).inv ≫ MonoidalClosed.uncurry function := by
  have supplied : (ambientProjection binding ≫ parameters) ≫ snd _ _ ≫ fst _ _ =
      (ambientProjection binding ≫ function) ≫ binaryBody binding := by
    simpa only [Category.assoc] using congrArg (ambientProjection binding ≫ ·) second_read
  erw [binary_supplied_value binding (ambientProjection binding ≫ parameters)
    (nameEnvironment binding (nameEnvironment binding environment)) _ _
    (ambientProjection binding ≫ function) supplied, Model.interp_var, Model.interp_var]
  change lift
      (lift (fst (names binding) (names binding ⊗ Z))
        (snd (names binding) (names binding ⊗ Z) ≫ fst (names binding) Z))
      (ambientProjection binding ≫ function) ≫
        (ihom.ev (names binding ⊗ names binding)).app (processes binding) = _
  rw [MonoidalClosed.uncurry_eq, ← Category.assoc]
  congr 1
  apply hom_ext
  · apply hom_ext <;> simp
  · simp [ambientProjection]

theorem binary_bound_swapped_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding))
    (second_read : parameters ≫ snd _ _ ≫ fst _ _ = function ≫ binaryBody binding) :
    (binding.model.interp AllArity.structuralMetas
      (binaryMeta (.var (.succ .zero)) (.var .zero) :
        Term (withMetas AllArity.sig AllArity.structuralMetas) (.nm :: .nm :: context) .pr)).value
          (names binding ⊗ (names binding ⊗ Z)) (ambientProjection binding ≫ parameters)
          (nameEnvironment binding (nameEnvironment binding environment)) =
      (α_ (names binding) (names binding) Z).inv ≫
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange
          (names binding) (names binding) ▷ Z ≫ MonoidalClosed.uncurry function := by
  have supplied : (ambientProjection binding ≫ parameters) ≫ snd _ _ ≫ fst _ _ =
      (ambientProjection binding ≫ function) ≫ binaryBody binding := by
    simpa only [Category.assoc] using congrArg (ambientProjection binding ≫ ·) second_read
  erw [binary_supplied_value binding (ambientProjection binding ≫ parameters)
    (nameEnvironment binding (nameEnvironment binding environment)) _ _
    (ambientProjection binding ≫ function) supplied, Model.interp_var, Model.interp_var]
  change lift
      (lift (snd (names binding) (names binding ⊗ Z) ≫ fst (names binding) Z)
        (fst (names binding) (names binding ⊗ Z)))
      (ambientProjection binding ≫ function) ≫
        (ihom.ev (names binding ⊗ names binding)).app (processes binding) = _
  rw [MonoidalClosed.uncurry_eq]
  simp only [← Category.assoc]
  congr 1
  apply hom_ext
  · apply hom_ext <;> simp [Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange]
  · simp [ambientProjection]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinaryValues
