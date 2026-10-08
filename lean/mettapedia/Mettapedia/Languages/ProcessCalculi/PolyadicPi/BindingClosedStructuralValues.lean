import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperations

/-!
# Complete structural readings of polyadic binding primitives

The independently generated structural schemas are read at arbitrary
categorical stages and complete function arguments. Empty binder arguments
are packed by their actual terminal-context curry; private bodies retain the
whole supplied name function. These calculations apply before choosing any
runtime interpretation of the binding algebra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralValues

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open BindingClosedPrimitiveOperations
open Bridges.NamePassingContinuationOperations

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)
variable {metavariables : List (MetaArity AllArity.sig)} {context : Ctx AllArity.sig}
variable {Z : C} (parameters : Z ⟶ binding.model.family metavariables)
variable (environment : binding.model.Env Z context)

theorem empty_argument {result : Srt}
    (term : Term (withMetas AllArity.sig metavariables) context result) :
    MonoidalClosed.curry
      ((binding.model.interp metavariables term).value (𝟙_ C ⊗ Z)
        (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)) =
      (binding.model.interp metavariables term).value Z parameters environment ≫ plain binding result := by
  have natural := (binding.model.interp metavariables term).natural
    (snd (𝟙_ C) Z) parameters environment
  change (binding.model.interp metavariables term).value (𝟙_ C ⊗ Z)
    (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment) =
      snd _ _ ≫ (binding.model.interp metavariables term).value Z parameters environment at natural
  rw [natural]
  change MonoidalClosed.curry
      (snd (𝟙_ C) Z ≫ (binding.model.interp metavariables term).value Z parameters environment) =
    (binding.model.interp metavariables term).value Z parameters environment ≫
      MonoidalClosed.curry (snd (𝟙_ C) (binding.model.sort result))
  rw [← MonoidalClosed.curry_natural_left]
  rw [whiskerLeft_snd]

theorem parallel_value
    (first second : Term (withMetas AllArity.sig metavariables) context .pr) :
    (binding.model.interp metavariables
      (.op (.inl .par) (.cons first (.cons second .nil)))).value Z parameters environment =
      lift ((binding.model.interp metavariables first).value Z parameters environment)
        ((binding.model.interp metavariables second).value Z parameters environment) ≫
          (continuation binding).parallel := by
  change lift
    (MonoidalClosed.curry ((binding.model.interp metavariables first).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
    (lift (MonoidalClosed.curry ((binding.model.interp metavariables second).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment))) (toUnit Z)) ≫
      binding.operation AllArity.Op.par = _
  rw [empty_argument, empty_argument]
  change lift
      ((binding.model.interp metavariables first).value Z parameters environment ≫ plain binding Srt.pr)
      (lift ((binding.model.interp metavariables second).value Z parameters environment ≫ plain binding Srt.pr)
        (toUnit Z)) ≫ binding.operation AllArity.Op.par =
    lift ((binding.model.interp metavariables first).value Z parameters environment)
      ((binding.model.interp metavariables second).value Z parameters environment) ≫
      (lift (fst _ _ ≫ plain binding Srt.pr)
        (lift (snd _ _ ≫ plain binding Srt.pr) (toUnit _)) ≫ binding.operation AllArity.Op.par)
  rw [← Category.assoc, comp_lift, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc, comp_toUnit]

theorem nil_value :
    (binding.model.interp metavariables
      (.op (.inl .nil) .nil : Term (withMetas AllArity.sig metavariables) context .pr)).value
        Z parameters environment = toUnit Z ≫ (continuation binding).empty := rfl

theorem private_value
    (body : Term (withMetas AllArity.sig metavariables) (.nm :: context) .pr) :
    (binding.model.interp metavariables (.op (.inl .nu) (.cons body .nil))).value
      Z parameters environment =
      MonoidalClosed.curry
        ((binding.model.interp metavariables body).value ((names binding ⊗ 𝟙_ C) ⊗ Z)
          (snd _ _ ≫ parameters) (binding.model.extendEnv [.nm] environment)) ≫
        lift (𝟙 _) (toUnit _) ≫ binding.operation AllArity.Op.nu := by
  change lift (MonoidalClosed.curry _) (toUnit Z) ≫ binding.operation AllArity.Op.nu = _
  simp only [comp_lift_assoc, Category.comp_id, comp_toUnit]
  rfl

def nameEnvironment : binding.model.Env (names binding ⊗ Z) (.nm :: context) :=
  fun sort position => match position with
    | .zero => fst _ _
    | .succ old => snd _ _ ≫ environment sort old

theorem name_environment_comparison :
    binding.model.restage ((ρ_ (names binding)).inv ▷ Z)
      (binding.model.extendEnv [.nm] environment) = nameEnvironment binding environment := by
  funext sort position
  cases position with
  | zero =>
      change (ρ_ (names binding)).inv ▷ Z ≫ fst (names binding ⊗ 𝟙_ C) Z ≫
        fst (names binding) (𝟙_ C) = fst (names binding) Z
      simp
  | succ old =>
      change (ρ_ (names binding)).inv ▷ Z ≫
        lift (fst (names binding ⊗ 𝟙_ C) Z ≫ snd (names binding) (𝟙_ C))
          (snd (names binding ⊗ 𝟙_ C) Z) ≫ snd (𝟙_ C) Z ≫ environment sort old =
        snd (names binding) Z ≫ environment sort old
      simp

theorem private_body_read
    (body : Term (withMetas AllArity.sig metavariables) (.nm :: context) .pr) :
    ((ρ_ (names binding)).inv ▷ Z) ≫
      (binding.model.interp metavariables body).value ((names binding ⊗ 𝟙_ C) ⊗ Z)
        (snd _ _ ≫ parameters) (binding.model.extendEnv [.nm] environment) =
      (binding.model.interp metavariables body).value (names binding ⊗ Z)
        (snd _ _ ≫ parameters) (nameEnvironment binding environment) := by
  have natural := (binding.model.interp metavariables body).natural
    ((ρ_ (names binding)).inv ▷ Z) (snd (names binding ⊗ 𝟙_ C) Z ≫ parameters)
    (binding.model.extendEnv [.nm] environment)
  rw [name_environment_comparison] at natural
  simpa only [whiskerRight_snd_assoc] using natural.symm

theorem private_complete_value
    (body : Term (withMetas AllArity.sig metavariables) (.nm :: context) .pr) :
    (binding.model.interp metavariables (.op (.inl .nu) (.cons body .nil))).value
      Z parameters environment =
      MonoidalClosed.curry
        ((binding.model.interp metavariables body).value (names binding ⊗ Z)
          (snd _ _ ≫ parameters) (nameEnvironment binding environment)) ≫
        (continuation binding).fresh := by
  rw [← private_body_read]
  rw [private_value]
  change MonoidalClosed.curry
      ((binding.model.interp metavariables body).value ((names binding ⊗ 𝟙_ C) ⊗ Z)
        (snd _ _ ≫ parameters) (binding.model.extendEnv [.nm] environment)) ≫
      (lift (𝟙 _) (toUnit _) ≫ binding.operation AllArity.Op.nu) =
    MonoidalClosed.curry
      ((ρ_ (names binding)).inv ▷ Z ≫
        (binding.model.interp metavariables body).value ((names binding ⊗ 𝟙_ C) ⊗ Z)
          (snd _ _ ≫ parameters) (binding.model.extendEnv [.nm] environment)) ≫
      (lift ((MonoidalClosed.pre (ρ_ (names binding)).hom).app (processes binding))
        (toUnit _) ≫ binding.operation AllArity.Op.nu)
  rw [← Category.assoc, ← Category.assoc, comp_lift, comp_lift]
  simp only [Category.comp_id, comp_toUnit]
  have transported := MonoidalClosed.curry_pre_app (ρ_ (names binding)).hom
    ((ρ_ (names binding)).inv ▷ Z ≫
      (binding.model.interp metavariables body).value ((names binding ⊗ 𝟙_ C) ⊗ Z)
        (snd _ _ ≫ parameters) (binding.model.extendEnv [.nm] environment))
  rw [← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
    Category.id_comp] at transported
  exact congrArg (fun function => lift function (toUnit Z) ≫ binding.operation AllArity.Op.nu)
    transported.symm

def unaryMeta {scope : Ctx AllArity.sig}
    (argument : Term (withMetas AllArity.sig AllArity.structuralMetas) scope .nm) :
    Term (withMetas AllArity.sig AllArity.structuralMetas) scope .pr :=
  .op (.inr (MetaOp.mk (M := AllArity.structuralMetas) ⟨0, by decide⟩)) (.cons argument .nil)

theorem unary_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (argument : Term (withMetas AllArity.sig AllArity.structuralMetas) context .nm) :
    (binding.model.interp AllArity.structuralMetas (unaryMeta argument)).value Z parameters environment =
      lift (lift ((binding.model.interp AllArity.structuralMetas argument).value Z parameters environment)
        (toUnit Z)) (parameters ≫ fst _ _) ≫
          (ihom.ev (names binding ⊗ 𝟙_ C)).app (processes binding) := rfl

theorem unary_function_evaluation (argument : Z ⟶ names binding)
    (function : Z ⟶ (names binding ⟶[C] processes binding)) :
    lift (lift argument (toUnit Z)) (function ≫ unaryBody binding) ≫
      (ihom.ev (tuple binding 1)).app (processes binding) =
      lift argument function ≫ (ihom.ev (names binding)).app (processes binding) := by
  have paired : lift (lift argument (toUnit Z)) (function ≫ unaryBody binding) =
      lift (lift argument (toUnit Z)) function ≫ (tuple binding 1 ◁ unaryBody binding) := by
    change lift (lift argument (toUnit Z)) (function ≫ unaryBody binding) =
      lift (lift argument (toUnit Z)) function ≫ ((names binding ⊗ 𝟙_ C) ◁ unaryBody binding)
    apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd,
      lift_snd_assoc, whiskerLeft_fst, whiskerLeft_snd]
  rw [paired, Category.assoc, unary_body_evaluation, ← Category.assoc]
  congr 1
  apply hom_ext <;> simp

theorem unary_supplied_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (argument : Term (withMetas AllArity.sig AllArity.structuralMetas) context .nm)
    (function : Z ⟶ (names binding ⟶[C] processes binding))
    (first_read : parameters ≫ fst _ _ = function ≫ unaryBody binding) :
    (binding.model.interp AllArity.structuralMetas (unaryMeta argument)).value Z parameters environment =
      lift ((binding.model.interp AllArity.structuralMetas argument).value Z parameters environment)
        function ≫ (ihom.ev (names binding)).app (processes binding) := by
  rw [unary_value, first_read]
  exact unary_function_evaluation binding _ function

theorem unary_bound_value
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (function : Z ⟶ (names binding ⟶[C] processes binding))
    (first_read : parameters ≫ fst _ _ = function ≫ unaryBody binding) :
    (binding.model.interp AllArity.structuralMetas
      (unaryMeta (.var .zero :
        Term (withMetas AllArity.sig AllArity.structuralMetas) (.nm :: context) .nm))).value
          (names binding ⊗ Z) (snd _ _ ≫ parameters) (nameEnvironment binding environment) =
      MonoidalClosed.uncurry function := by
  have supplied : (snd (names binding) Z ≫ parameters) ≫ fst _ _ =
      (snd (names binding) Z ≫ function) ≫ unaryBody binding := by
    rw [Category.assoc, first_read, ← Category.assoc]
  erw [unary_supplied_value binding (snd (names binding) Z ≫ parameters)
    (nameEnvironment binding environment) _ (snd (names binding) Z ≫ function) supplied,
    Model.interp_var]
  change lift (fst (names binding) Z) (snd (names binding) Z ≫ function) ≫
    (ihom.ev (names binding)).app (processes binding) = MonoidalClosed.uncurry function
  rw [MonoidalClosed.uncurry_eq]
  congr 1
  apply hom_ext <;> simp

theorem unary_bound_curry
    (parameters : Z ⟶ binding.model.family AllArity.structuralMetas)
    (environment : binding.model.Env Z context)
    (function : Z ⟶ (names binding ⟶[C] processes binding))
    (first_read : parameters ≫ fst _ _ = function ≫ unaryBody binding) :
    MonoidalClosed.curry
      ((binding.model.interp AllArity.structuralMetas
        (unaryMeta (.var .zero :
          Term (withMetas AllArity.sig AllArity.structuralMetas) (.nm :: context) .nm))).value
            (names binding ⊗ Z) (snd _ _ ≫ parameters) (nameEnvironment binding environment)) =
      function := by
  rw [unary_bound_value binding parameters environment function first_read,
    MonoidalClosed.curry_uncurry]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralValues
