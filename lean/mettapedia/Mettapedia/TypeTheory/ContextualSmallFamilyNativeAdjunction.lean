import Mettapedia.TypeTheory.WiderPresheafDependentFunctions
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension

/-!
# Native dependent sections and original-bound contextual products

The parameter presheaf may be wider than the context universe. Full native
dependent sections quantify over its actual category of elements. Their
constructed compression to the small context cone retains every arrow and
typed argument. Evaluation and both inverse laws identify the original
small carrier with the native function family.

The universal properties below accept consumers in arbitrary value
universes. This is a comparison of constructed coherent families, not a
selection of coherent presentations from merely pointwise small fibres.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

open CategoryTheory
open ContextualSmallFamilyTypeFormers

universe u v h k

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def smallCurryValue {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain parameters) body)
    (point : base.Elements) (parameter : parameters.obj point) : ProductAt domain body point :=
  ⟨fun argument => operation.app ((futureArguments domain point).obj argument)
      (parameters.map (futureRootArrow domain point argument) parameter), by
    intro source target arrow
    have natural := operation.naturality ((futureArguments domain point).map arrow)
      (parameters.map (futureRootArrow domain point source) parameter)
    exact natural.trans
      (congrArg (operation.app ((futureArguments domain point).obj target))
        ((parameters.map_comp_apply _ _ parameter).symm.trans
          (congrArg (fun step => parameters.map step parameter)
            (futureRootArrow_triangle domain point arrow))))⟩

theorem homApplication_heq {E : Type v} [Category.{u} E]
    {source : E ⥤ Type h} {target : E ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom source target)
    {first second : E} (same : first = second)
    (value : source.obj first) (other : source.obj second) (values : HEq value other) :
    HEq (operation.app first value) (operation.app second other) := by
  cases same
  cases eq_of_heq values
  rfl

def smallCurry {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain parameters) body) :
    WiderPresheafDependentFunctions.Hom parameters (pi domain body) where
  app point := smallCurryValue domain body operation point
  naturality {first second} step parameter := by
    apply Subtype.ext
    funext argument
    apply eq_of_heq
    have parameterEq := ContextualSmallFamilyUniverse.familyMap_heq parameters rfl
      (congrArg Sigma.fst (prefixArguments_embedding domain step argument))
      (futureRootArrow domain first ((prefixArguments domain step).obj argument))
      (step ≫ futureRootArrow domain second argument) (prefixRootArrow_heq domain step argument)
      parameter parameter HEq.rfl
    have resultEq := homApplication_heq operation
      (prefixArguments_embedding domain step argument)
      (parameters.map (futureRootArrow domain first ((prefixArguments domain step).obj argument)) parameter)
      (parameters.map (futureRootArrow domain second argument) (parameters.map step parameter))
      (parameterEq.trans (heq_of_eq (parameters.map_comp_apply _ _ parameter)))
    exact (productMap_value domain body step
      (smallCurryValue domain body operation first parameter) argument).trans resultEq

def smallEvaluation : WiderPresheafDependentFunctions.Hom
    (WiderPresheafDependentFunctions.over domain (pi domain body)) body where
  app point term := evaluateValue domain body point.1 term point.2
  naturality {first second} step term := by
    rcases first with ⟨first, argument⟩
    rcases second with ⟨second, nextArgument⟩
    rcases step with ⟨step, saved⟩
    change first ⟶ second at step
    change domain.map step argument = nextArgument at saved
    subst nextArgument
    exact evaluateValue_natural domain body step term argument

def nativeToSmall : WiderPresheafDependentFunctions.Hom
    (WiderPresheafDependentFunctions.dependentFunctions domain body) (pi domain body) :=
  smallCurry domain body (WiderPresheafDependentFunctions.evaluate domain body)

theorem nativeToSmall_value (point : base.Elements)
    (term : WiderPresheafDependentFunctions.DependentSection domain body point)
    (argument : (futureDomain domain point).Elements) :
    ((nativeToSmall domain body).app point term).val argument =
      term.app ((futureArguments domain point).obj argument).1
        (futureRootArrow domain point argument) argument.2 := by
  change term.app _ (futureRootArrow domain point argument ≫ 𝟙 _) argument.2 = _
  rw [Category.comp_id]

theorem evaluation_compression (point : base.Elements)
    (term : WiderPresheafDependentFunctions.DependentSection domain body point)
    (argument : domain.obj point) :
    evaluateValue domain body point ((nativeToSmall domain body).app point term) argument =
      term.app point (𝟙 point) argument := by
  apply eq_of_heq
  exact (evaluateValue_heq domain body point ((nativeToSmall domain body).app point term) argument).trans
    ((heq_of_eq (nativeToSmall_value domain body point term (currentArgument domain point argument))).trans
      (WiderPresheafDependentFunctions.DependentSection.app_heq domain body term
        (congrArg Sigma.fst (currentArgument_embedding domain point argument))
        (futureRootArrow domain point (currentArgument domain point argument)) (𝟙 point)
        (futureRootArrow_current domain point argument) _ argument
        (currentArgument_value domain point argument)))

theorem evaluation_square :
    (WiderPresheafDependentFunctions.overHom domain (nativeToSmall domain body)).comp
      (smallEvaluation domain body) = WiderPresheafDependentFunctions.evaluate domain body := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point term
  exact evaluation_compression domain body point.1 term point.2

def smallToNative : WiderPresheafDependentFunctions.Hom
    (pi domain body) (WiderPresheafDependentFunctions.dependentFunctions domain body) :=
  WiderPresheafDependentFunctions.curry (smallEvaluation domain body)

theorem native_small_left : (nativeToSmall domain body).comp (smallToNative domain body) =
    WiderPresheafDependentFunctions.Hom.identity
      (WiderPresheafDependentFunctions.dependentFunctions domain body) := by
  have natural := WiderPresheafDependentFunctions.curry_natural_left
    (nativeToSmall domain body) (smallEvaluation domain body)
  rw [evaluation_square] at natural
  exact natural.symm.trans
    (WiderPresheafDependentFunctions.curry_uncurry
      (WiderPresheafDependentFunctions.Hom.identity
        (WiderPresheafDependentFunctions.dependentFunctions domain body)))

theorem native_small_right : (smallToNative domain body).comp (nativeToSmall domain body) =
    WiderPresheafDependentFunctions.Hom.identity (pi domain body) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point term
  apply Subtype.ext
  funext argument
  exact (nativeToSmall_value domain body point ((smallToNative domain body).app point term) argument).trans
    (evaluate_future domain body point term argument)

def nativeSmallEquiv (point : base.Elements) :
    WiderPresheafDependentFunctions.DependentSection domain body point ≃ ProductAt domain body point where
  toFun := (nativeToSmall domain body).app point
  invFun := (smallToNative domain body).app point
  left_inv term := congrArg (fun operation => operation.app point term) (native_small_left domain body)
  right_inv term := congrArg (fun operation => operation.app point term) (native_small_right domain body)

def smallUncurry {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom parameters (pi domain body)) :
    WiderPresheafDependentFunctions.Hom (WiderPresheafDependentFunctions.over domain parameters) body :=
  (WiderPresheafDependentFunctions.overHom domain operation).comp (smallEvaluation domain body)

theorem smallCurry_native {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain parameters) body) :
    (WiderPresheafDependentFunctions.curry operation).comp (nativeToSmall domain body) =
      smallCurry domain body operation := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point parameter
  apply Subtype.ext
  funext argument
  exact nativeToSmall_value domain body point
    ((WiderPresheafDependentFunctions.curry operation).app point parameter) argument

theorem small_uncurry_curry {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain parameters) body) :
    smallUncurry domain body (smallCurry domain body operation) = operation := by
  rw [← smallCurry_native]
  change ((WiderPresheafDependentFunctions.overHom domain (WiderPresheafDependentFunctions.curry operation)).comp
      (WiderPresheafDependentFunctions.overHom domain (nativeToSmall domain body))).comp
    (smallEvaluation domain body) = operation
  rw [WiderPresheafDependentFunctions.Hom.assoc, evaluation_square]
  exact WiderPresheafDependentFunctions.beta operation

theorem small_curry_uncurry {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom parameters (pi domain body)) :
    smallCurry domain body (smallUncurry domain body operation) = operation := by
  rw [← smallCurry_native]
  have natural := WiderPresheafDependentFunctions.curry_natural_left operation (smallEvaluation domain body)
  change WiderPresheafDependentFunctions.curry (smallUncurry domain body operation) =
    operation.comp (smallToNative domain body) at natural
  rw [natural, WiderPresheafDependentFunctions.Hom.assoc, native_small_right]
  exact WiderPresheafDependentFunctions.Hom.comp_identity operation

def smallHomEquiv (parameters : base.Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom (WiderPresheafDependentFunctions.over domain parameters) body ≃
      WiderPresheafDependentFunctions.Hom parameters (pi domain body) where
  toFun := smallCurry domain body
  invFun := smallUncurry domain body
  left_inv := small_uncurry_curry domain body
  right_inv := small_curry_uncurry domain body

theorem small_transpose_unique {parameters : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain parameters) body)
    (candidate : WiderPresheafDependentFunctions.Hom parameters (pi domain body))
    (computes : smallUncurry domain body candidate = operation) :
    candidate = smallCurry domain body operation := by
  rw [← computes, small_curry_uncurry]

theorem small_curry_natural_parameters {first : base.Elements ⥤ Type h}
    {second : base.Elements ⥤ Type k}
    (earlier : WiderPresheafDependentFunctions.Hom first second)
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over domain second) body) :
    smallCurry domain body ((WiderPresheafDependentFunctions.overHom domain earlier).comp operation) =
      earlier.comp (smallCurry domain body operation) := by
  rw [← smallCurry_native, WiderPresheafDependentFunctions.curry_natural_left,
    WiderPresheafDependentFunctions.Hom.assoc, smallCurry_native]

def sigmaCurry {result : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom (sigma domain body) result) :
    WiderPresheafDependentFunctions.Hom body (WiderPresheafDependentFunctions.over domain result) where
  app point value := operation.app point.1 ⟨point.2, value⟩
  naturality {first second} step value := by
    rcases first with ⟨first, argument⟩
    rcases second with ⟨second, nextArgument⟩
    rcases step with ⟨step, saved⟩
    change first ⟶ second at step
    change domain.map step argument = nextArgument at saved
    subst nextArgument
    exact operation.naturality step ⟨argument, value⟩

def sigmaUncurry {result : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom body
      (WiderPresheafDependentFunctions.over domain result)) :
    WiderPresheafDependentFunctions.Hom (sigma domain body) result where
  app point value := operation.app ⟨point, value.1⟩ value.2
  naturality step value := operation.naturality (argumentStep domain step value.1) value.2

theorem sigma_uncurry_curry {result : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom (sigma domain body) result) :
    sigmaUncurry domain body (sigmaCurry domain body operation) = operation := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  cases value
  rfl

theorem sigma_curry_uncurry {result : base.Elements ⥤ Type h}
    (operation : WiderPresheafDependentFunctions.Hom body
      (WiderPresheafDependentFunctions.over domain result)) :
    sigmaCurry domain body (sigmaUncurry domain body operation) = operation := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point value
  cases point
  rfl

def sigmaHomEquiv (result : base.Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom (sigma domain body) result ≃
      WiderPresheafDependentFunctions.Hom body (WiderPresheafDependentFunctions.over domain result) where
  toFun := sigmaCurry domain body
  invFun := sigmaUncurry domain body
  left_inv := sigma_uncurry_curry domain body
  right_inv := sigma_curry_uncurry domain body

end Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction
