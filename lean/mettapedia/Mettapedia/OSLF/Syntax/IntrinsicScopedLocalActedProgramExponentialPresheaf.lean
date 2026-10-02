import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponentialHom
import Mettapedia.OSLF.Syntax.CategoricalBindingClosedTargetChange

/-!
# Actual selected program exponentials in classifier presheaves

The standard presheaf function object is identified with the authored scoped
program object by a natural equivalence of its sections. Its sections are read
at the actual stage-and-parameter product, and reconstructed by its product
universal property and contextual abstraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open SecondOrderContext SecondOrderVariableAbstraction
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- The actual representable for the full ordinary parameter context. -/
abbrev parameterRepresentable (Γ : Ctx S) : Presheaf.{w} R equations :=
  (embedding R equations).obj ((programSection R equations).obj (parameterContext equations Γ))

/-- Read a standard internal-hom section at the actual stage-parameter product. -/
def parameterFunctionToArrow (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt)
    (function : ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op a)) :
    productWithProgram R equations a (parameterContext equations Γ) ⟶
      (programSection R equations).obj ⟨single S [] s⟩ :=
  (function.app (Opposite.op (productWithProgram R equations a (parameterContext equations Γ)))
    (programProductFst R equations a _).op (ULift.up (programProductSnd R equations a _))).down

/-- The product universal property reconstructs the standard function section
from an actual authored arrow. -/
def arrowToParameterFunction (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt)
    (body : productWithProgram R equations a (parameterContext equations Γ) ⟶
      (programSection R equations).obj ⟨single S [] s⟩) :
    ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op a) where
  app stage stageMap := TypeCat.ofHom fun argument =>
    ULift.up (programProductLift R equations stageMap.unop argument.down ≫ body)
  naturality := by
    intro c d f g
    apply ConcreteCategory.hom_ext
    intro argument
    change ULift.up (programProductLift R equations (f.unop ≫ g.unop)
        (f.unop ≫ argument.down) ≫ body) =
      ULift.up (f.unop ≫ (programProductLift R equations g.unop argument.down ≫ body))
    apply congrArg ULift.up
    have paired : programProductLift R equations (f.unop ≫ g.unop)
        (f.unop ≫ argument.down) = f.unop ≫ programProductLift R equations g.unop argument.down := by
      symm
      apply programProductLift_unique
      · rw [Category.assoc, programProductLift_fst]
      · rw [Category.assoc, programProductLift_snd]
    rw [paired, Category.assoc]

/-- Reading a reconstructed function returns precisely the authored arrow. -/
theorem parameterFunctionToArrow_arrowToParameterFunction
    (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt)
    (body : productWithProgram R equations a (parameterContext equations Γ) ⟶
      (programSection R equations).obj ⟨single S [] s⟩) :
    parameterFunctionToArrow R equations a Γ s
        (arrowToParameterFunction.{w} R equations a Γ s body) = body := by
  change programProductLift R equations (programProductFst R equations a _)
      (programProductSnd R equations a _) ≫ body = body
  have paired := programProductLift_unique R equations
    (programProductFst R equations a (parameterContext equations Γ))
    (programProductSnd R equations a (parameterContext equations Γ))
    (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  rw [← paired, Category.id_comp]

/-- Reconstructing a standard function section returns that entire section,
not merely its value at one closed program stage. -/
theorem arrowToParameterFunction_parameterFunctionToArrow
    (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt)
    (function : ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op a)) :
    arrowToParameterFunction R equations a Γ s
        (parameterFunctionToArrow R equations a Γ s function) = function := by
  apply _root_.CategoryTheory.Functor.functorHom_ext
  intro stage stageMap
  apply ConcreteCategory.hom_ext
  intro argument
  let paired := programProductLift R equations stageMap.unop argument.down
  have naturality : (parameterRepresentable.{w} R equations Γ).map paired.op ≫
      function.app stage (paired ≫ programProductFst R equations a _).op =
    function.app (Opposite.op (productWithProgram R equations a (parameterContext equations Γ)))
        (programProductFst R equations a _).op ≫
      (program.{w} R equations [] s).map paired.op :=
    function.naturality paired.op (programProductFst R equations a _).op
  have pointwise := congrArg (fun h :
      (parameterRepresentable.{w} R equations Γ).obj
        (Opposite.op (productWithProgram R equations a (parameterContext equations Γ))) ⟶
      (program.{w} R equations [] s).obj stage =>
    h (ULift.up (programProductSnd R equations a (parameterContext equations Γ)))) naturality
  change function.app stage
      (paired ≫ programProductFst R equations a _).op
      (ULift.up (paired ≫ programProductSnd R equations a _)) =
    ULift.up (paired ≫ parameterFunctionToArrow R equations a Γ s function) at pointwise
  rw [programProductLift_fst, programProductLift_snd] at pointwise
  exact pointwise.symm

/-- The standard function-section correspondence with actual product arrows. -/
def parameterFunctionArrowEquiv (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt) :
    ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op a) ≃
      (productWithProgram R equations a (parameterContext equations Γ) ⟶
        (programSection R equations).obj ⟨single S [] s⟩) where
  toFun := parameterFunctionToArrow R equations a Γ s
  invFun := arrowToParameterFunction R equations a Γ s
  left_inv := arrowToParameterFunction_parameterFunctionToArrow R equations a Γ s
  right_inv := parameterFunctionToArrow_arrowToParameterFunction R equations a Γ s

/-- Reading the function section commutes with an arbitrary operational
change of stage, retaining its ordered parameter variables. -/
theorem parameterFunctionToArrow_reindex {a b : Classifier R equations}
    (f : a ⟶ b) (Γ : Ctx S) (s : S.Srt)
    (function : ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op b)) :
    parameterFunctionToArrow R equations a Γ s
        (((parameterRepresentable R equations Γ).functorHom
          (program R equations [] s)).map f.op function) =
      programParameterMap equations R f Γ ≫ parameterFunctionToArrow R equations b Γ s function := by
  have naturality : (parameterRepresentable.{w} R equations Γ).map
        (programParameterMap equations R f Γ).op ≫
      function.app (Opposite.op (productWithProgram R equations a (parameterContext equations Γ)))
        (programParameterMap equations R f Γ ≫ programProductFst R equations b _).op =
    function.app (Opposite.op (productWithProgram R equations b (parameterContext equations Γ)))
        (programProductFst R equations b _).op ≫
      (program.{w} R equations [] s).map (programParameterMap equations R f Γ).op :=
    function.naturality (programParameterMap equations R f Γ).op
      (programProductFst R equations b _).op
  have pointwise := congrArg (fun h :
      (parameterRepresentable.{w} R equations Γ).obj
        (Opposite.op (productWithProgram R equations b (parameterContext equations Γ))) ⟶
      (program.{w} R equations [] s).obj
        (Opposite.op (productWithProgram R equations a (parameterContext equations Γ))) =>
    h (ULift.up (programProductSnd R equations b (parameterContext equations Γ)))) naturality
  change function.app (Opposite.op (productWithProgram R equations a _))
      (programParameterMap equations R f Γ ≫ programProductFst R equations b _).op
      (ULift.up (programParameterMap equations R f Γ ≫ programProductSnd R equations b _)) =
    ULift.up (programParameterMap equations R f Γ ≫
      parameterFunctionToArrow R equations b Γ s function) at pointwise
  rw [programParameterMap, programProductLift_fst, programProductLift_snd] at pointwise
  exact congrArg ULift.down pointwise

/-- Sections of the standard presheaf function object are precisely authored
programs with the specified ordinary binder context. -/
def parameterPowerSectionEquiv (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt) :
    ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op a) ≃
      (program.{w} R equations Γ s).obj (Opposite.op a) :=
  (parameterFunctionArrowEquiv R equations a Γ s).trans
    ((selectedBinderHomEquiv equations R a Γ s).trans Equiv.ulift.symm)

/-- The function-body section correspondence is natural on all classifier
maps, including maps between stages carrying firing variables. -/
theorem parameterPowerSectionEquiv_reindex {a b : Classifier R equations}
    (f : a ⟶ b) (Γ : Ctx S) (s : S.Srt)
    (function : ((parameterRepresentable.{w} R equations Γ).functorHom
      (program R equations [] s)).obj (Opposite.op b)) :
    parameterPowerSectionEquiv R equations a Γ s
        (((parameterRepresentable R equations Γ).functorHom
          (program R equations [] s)).map f.op function) =
      (program R equations Γ s).map f.op
        (parameterPowerSectionEquiv R equations b Γ s function) := by
  change ULift.up (selectedBinderHomEquiv equations R a Γ s
      (parameterFunctionToArrow R equations a Γ s (_))) =
    ULift.up (f ≫ selectedBinderHomEquiv equations R b Γ s
      (parameterFunctionToArrow R equations b Γ s function))
  rw [parameterFunctionToArrow_reindex, selectedBinderHomEquiv_precompose]

/-- The actual standard internal hom is naturally the authored scoped program
presheaf, as proved by its stage-wise section correspondence. -/
def parameterPowerIso (Γ : Ctx S) (s : S.Srt) :
    (parameterRepresentable.{w} R equations Γ).functorHom (program R equations [] s) ≅
      program R equations Γ s :=
  NatIso.ofComponents (fun a => (parameterPowerSectionEquiv R equations a.unop Γ s).toIso)
    (by
      intro a b f
      apply ConcreteCategory.hom_ext
      intro function
      exact parameterPowerSectionEquiv_reindex R equations f.unop Γ s function)

/-- The represented selected power satisfies the exponential universal property
for its actual parameter representable, at every presheaf stage. -/
def parameterExponential (Γ : Ctx S) (s : S.Srt) :
    CategoricalBindingModel.Exponential (parameterRepresentable.{w} R equations Γ)
      (program R equations [] s) (program R equations Γ s) :=
  (CategoricalBindingModel.Exponential.closed (parameterRepresentable R equations Γ)
    (program R equations [] s)).transport (Iso.refl _) (Iso.refl _)
      (parameterPowerIso R equations Γ s)

/-- Selected evaluation is actual composition with the restored scoped body,
with the parameter assignment paired with the unchanged operational stage. -/
theorem parameterExponential_eval_apply (a : Classifier R equations)
    (Γ : Ctx S) (s : S.Srt)
    (argument : (parameterRepresentable.{w} R equations Γ).obj (Opposite.op a))
    (body : (program.{w} R equations Γ s).obj (Opposite.op a)) :
    (parameterExponential R equations Γ s).eval.app (Opposite.op a) (argument, body) =
      ULift.up (programProductLift R equations (𝟙 a) argument.down ≫
        (selectedBinderHomEquiv equations R a Γ s).symm body.down) := by
  rfl

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
