import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralValues

/-!
# Structural arrow laws earned from authored schema satisfaction

The actual seven structural declarations imply the corresponding laws on
arbitrary generalized process values and private-name functions. Supplied
functions are not restricted to syntactically represented bodies. The
generated equation guest supplies this schema satisfaction independently.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralLaws

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open BindingClosedPrimitiveOperations BindingClosedStructuralValues

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)

/-- Values for the unused metadata in the process-only structural laws. -/
def inactiveMetadata (Z : C) : Z ⟶ binding.model.family AllArity.structuralMetas :=
  lift (MonoidalClosed.curry (snd (names binding ⊗ 𝟙_ C) Z ≫ toUnit Z ≫
      binding.operation AllArity.Op.nil))
    (lift (MonoidalClosed.curry (snd (names binding ⊗ (names binding ⊗ 𝟙_ C)) Z ≫
        toUnit Z ≫ binding.operation AllArity.Op.nil)) (toUnit Z))

theorem parallel_comm
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (first second : Z ⟶ processes binding) :
    lift first second ≫ (continuation binding).parallel =
      lift second first ≫ (continuation binding).parallel := by
  let environment : binding.model.Env Z [Srt.pr, Srt.pr] :=
    fun sort position => match sort, position with
      | .pr, .zero => first
      | .pr, .succ .zero => second
  have same := satisfied ⟨0, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .par) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))) =
    binding.model.interp AllArity.structuralMetas
      (.op (.inl .par) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))) at same
  have atStage := congrArg (fun reading => reading.value Z (inactiveMetadata binding Z) environment) same
  erw [parallel_value, parallel_value] at atStage
  simpa only [Model.interp_var, environment] using atStage

theorem parallel_assoc
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (first second third : Z ⟶ processes binding) :
    lift (lift first second ≫ (continuation binding).parallel) third ≫ (continuation binding).parallel =
      lift first (lift second third ≫ (continuation binding).parallel) ≫
        (continuation binding).parallel := by
  let environment : binding.model.Env Z [Srt.pr, Srt.pr, Srt.pr] :=
    fun sort position => match sort, position with
      | .pr, .zero => first
      | .pr, .succ .zero => second
      | .pr, .succ (.succ .zero) => third
  have same := satisfied ⟨1, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .par)
        (.cons (.op (.inl .par) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
          (.cons (.var (.succ (.succ .zero))) .nil))) =
    binding.model.interp AllArity.structuralMetas
      (.op (.inl .par) (.cons (.var .zero)
        (.cons (.op (.inl .par)
          (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))) .nil))) at same
  have atStage := congrArg (fun reading => reading.value Z (inactiveMetadata binding Z) environment) same
  erw [parallel_value, parallel_value, parallel_value, parallel_value] at atStage
  simpa only [Model.interp_var, environment] using atStage

theorem parallel_unit
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (process : Z ⟶ processes binding) :
    lift process (toUnit Z ≫ (continuation binding).empty) ≫ (continuation binding).parallel = process := by
  let environment : binding.model.Env Z [Srt.pr] :=
    fun sort position => match sort, position with | .pr, .zero => process
  have same := satisfied ⟨2, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .par) (.cons (.var .zero) (.cons (.op (.inl .nil) .nil) .nil))) =
    binding.model.interp AllArity.structuralMetas (.var .zero) at same
  have atStage := congrArg (fun reading => reading.value Z (inactiveMetadata binding Z) environment) same
  erw [parallel_value, nil_value] at atStage
  simpa only [Model.interp_var, environment] using atStage

theorem private_unused
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (process : Z ⟶ processes binding) :
    MonoidalClosed.curry (snd (names binding) Z ≫ process) ≫ (continuation binding).fresh = process := by
  let environment : binding.model.Env Z [Srt.pr] :=
    fun sort position => match sort, position with | .pr, .zero => process
  have same := satisfied ⟨3, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .nu) (.cons (.var (.succ .zero)) .nil)) =
    binding.model.interp AllArity.structuralMetas (.var .zero) at same
  have atStage := congrArg (fun reading => reading.value Z (inactiveMetadata binding Z) environment) same
  erw [private_complete_value, Model.interp_var, Model.interp_var] at atStage
  exact atStage

def unaryMetadata {Z : C} (function : Z ⟶ (names binding ⟶[C] processes binding)) :
    Z ⟶ binding.model.family AllArity.structuralMetas :=
  lift (function ≫ unaryBody binding) (inactiveMetadata binding Z ≫ snd _ _)

theorem unaryMetadata_first {Z : C} (function : Z ⟶ (names binding ⟶[C] processes binding)) :
    unaryMetadata binding function ≫ fst _ _ = function ≫ unaryBody binding := by
  change lift (function ≫ unaryBody binding) _ ≫ fst _ _ = _
  exact lift_fst _ _

theorem private_parallel
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (function : Z ⟶ (names binding ⟶[C] processes binding))
    (frame : Z ⟶ processes binding) :
    lift (function ≫ (continuation binding).fresh) frame ≫ (continuation binding).parallel =
      MonoidalClosed.curry
        (lift (MonoidalClosed.uncurry function) (snd (names binding) Z ≫ frame) ≫
          (continuation binding).parallel) ≫ (continuation binding).fresh := by
  let environment : binding.model.Env Z [Srt.pr] :=
    fun sort position => match sort, position with | .pr, .zero => frame
  have same := satisfied ⟨4, by decide⟩
  change binding.model.interp AllArity.structuralMetas
      (.op (.inl .par) (.cons (.op (.inl .nu) (.cons (unaryMeta (.var .zero)) .nil))
        (.cons (.var .zero) .nil))) =
    binding.model.interp AllArity.structuralMetas
      (.op (.inl .nu) (.cons (.op (.inl .par)
        (.cons (unaryMeta (.var .zero)) (.cons (.var (.succ .zero)) .nil))) .nil)) at same
  have atStage := congrArg
    (fun reading => reading.value Z (unaryMetadata binding function) environment) same
  erw [parallel_value, private_complete_value, private_complete_value, parallel_value] at atStage
  rw [unary_bound_curry binding _ environment function (unaryMetadata_first binding function),
    unary_bound_value binding _ environment function (unaryMetadata_first binding function)] at atStage
  simpa only [Model.interp_var, nameEnvironment, environment] using atStage

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralLaws
