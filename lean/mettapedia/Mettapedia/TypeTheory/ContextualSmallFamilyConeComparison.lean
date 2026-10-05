import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence

/-!
# Compression of full dependent sections to small future cones

For a small parameter presheaf, the existing dependent-function adjoint
and the complete future-cone construction have explicitly equivalent
fibres. The two future categories retain the same context arrows and
typed arguments. Their comparison is constructed from the parameter
equation carried by each arrow; no future or representative is chosen.

The small-cone construction itself also applies to wider parameter
presheaves. The older dependent-section interface compared here is
restricted to a small category of parameters.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyConeComparison

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange
open ContextualSmallFamilyTypeFormers

universe u

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def compression (point : base.Elements) :
    Future.Objects point.1 ⥤ Future.Objects point where
  obj future := ⟨(ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future,
    CategoryOfElements.homMk _ _ future.2 rfl⟩
  map step := ⟨(ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step, by
    apply Subtype.ext
    exact step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def expansion (point : base.Elements) :
    Future.Objects point ⥤ Future.Objects point.1 where
  obj future := ⟨future.1.1, future.2.1⟩
  map step := ⟨step.1.1, congrArg Subtype.val step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem compression_expansion (point : base.Elements) :
    Cat.compose (compression point) (expansion point) = Cat.identity (Future.Objects point.1) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem expansion_compression_obj (point : base.Elements) (future : Future.Objects point) :
    (compression point).obj ((expansion point).obj future) = future := by
  have target : (ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj
      ((expansion point).obj future) = future.1 :=
    Sigma.ext rfl (heq_of_eq future.2.2)
  exact Future.objects_ext target
    (ContextualSmallFamilyTypeFormers.elementArrow_heq rfl target _ _ HEq.rfl)

theorem expansion_compression (point : base.Elements) :
    Cat.compose (expansion point) (compression point) = Cat.identity (Future.Objects point) := by
  refine Functor.hext (expansion_compression_obj point) ?_
  intro first second step
  exact ContextualSmallFamilyUniverse.futureArrow_heq
    (expansion_compression_obj point first) (expansion_compression_obj point second) _ _
    (ContextualSmallFamilyTypeFormers.elementArrow_heq
      (congrArg Future.Objects.fst (expansion_compression_obj point first))
      (congrArg Future.Objects.fst (expansion_compression_obj point second)) _ _ HEq.rfl)

theorem compressed_domain (point : base.Elements) :
    restrict (compression point) (Future.domain domain point) = futureDomain domain point := rfl

theorem compressed_body (point : base.Elements) :
    restrict (Cat.elementsMap (compression point) (Future.domain domain point))
      (Future.result domain body point) = futureBody domain body point := rfl

def coneSections (point : base.Elements) :
    (Future.result domain body point).sections ≃ ProductAt domain body point :=
  (Cat.elementSectionEquivOfInverse (compression point) (expansion point)
    (compression_expansion point) (expansion_compression point)
    (Future.domain domain point) (Future.result domain body point)).trans
      (ContextualSmallFamilyTypeFormerCoherence.sectionCastEquiv (compressed_body domain body point))

def dependentSectionEquiv (point : base.Elements) :
    DependentSection domain body point ≃ ProductAt domain body point :=
  (Future.sectionEquiv domain body point).trans (coneSections domain body point)

theorem dependentSectionEquiv_value (point : base.Elements)
    (function : DependentSection domain body point)
    (argument : (futureDomain domain point).Elements) :
    HEq ((dependentSectionEquiv domain body point function).val argument)
      (function.app (futureArguments domain point |>.obj argument).1
        (futureRootArrow domain point argument) argument.2) := by
  exact MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection_value (compressed_body domain body point)
    (MaterialSets.Hypersets.PowerClassPresheafProducts.CP.restrictSection (Cat.elementsMap (compression point) (Future.domain domain point))
      (Future.result domain body point) (Future.sectionEquiv domain body point function)) argument

def nativeToCone : NatTrans (dependentFunctions domain body) (pi domain body) :=
  piCurry domain body (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.evaluate domain body)

theorem nativeToCone_app (point : base.Elements) (function : DependentSection domain body point) :
    (nativeToCone domain body).app point function = dependentSectionEquiv domain body point function := by
  apply Subtype.ext
  funext argument
  apply eq_of_heq
  have value : ((nativeToCone domain body).app point function).val argument =
      function.app ((futureArguments domain point).obj argument).1
        (futureRootArrow domain point argument) argument.2 := by
    change function.app _ (futureRootArrow domain point argument ≫ 𝟙 _) argument.2 = _
    rw [Category.comp_id]
  exact (heq_of_eq value).trans (dependentSectionEquiv_value domain body point function argument).symm

def coneToNative : NatTrans (pi domain body) (dependentFunctions domain body) where
  app point := TypeCat.ofHom (dependentSectionEquiv domain body point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro term
    change ProductAt domain body first at term
    apply (dependentSectionEquiv domain body second).injective
    change (dependentSectionEquiv domain body second)
        ((dependentSectionEquiv domain body second).symm (productMap domain body step term)) =
      (dependentSectionEquiv domain body second)
        (DependentSection.restrict domain body step ((dependentSectionEquiv domain body first).symm term))
    have natural := congrArg (fun map => map ((dependentSectionEquiv domain body first).symm term))
      ((nativeToCone domain body).naturality step)
    change (nativeToCone domain body).app second
        (DependentSection.restrict domain body step ((dependentSectionEquiv domain body first).symm term)) =
      productMap domain body step ((nativeToCone domain body).app first
        ((dependentSectionEquiv domain body first).symm term)) at natural
    rw [nativeToCone_app, nativeToCone_app] at natural
    change (dependentSectionEquiv domain body second)
        (DependentSection.restrict domain body step ((dependentSectionEquiv domain body first).symm term)) =
      productMap domain body step ((dependentSectionEquiv domain body first)
        ((dependentSectionEquiv domain body first).symm term)) at natural
    rw [Equiv.apply_symm_apply] at natural
    rw [Equiv.apply_symm_apply]
    exact natural.symm

theorem native_cone_left : composeNat (nativeToCone domain body) (coneToNative domain body) =
    identityNat (dependentFunctions domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro function
  change DependentSection domain body point at function
  change (dependentSectionEquiv domain body point).symm ((nativeToCone domain body).app point function) = function
  exact (congrArg (dependentSectionEquiv domain body point).symm
    (nativeToCone_app domain body point function)).trans
      ((dependentSectionEquiv domain body point).symm_apply_apply function)

theorem native_cone_right : composeNat (coneToNative domain body) (nativeToCone domain body) =
    identityNat (pi domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  change ProductAt domain body point at term
  change (nativeToCone domain body).app point ((dependentSectionEquiv domain body point).symm term) = term
  exact (nativeToCone_app domain body point _).trans
    ((dependentSectionEquiv domain body point).apply_symm_apply term)

theorem curry_compression {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans (overArguments domain parameters) body) :
    composeNat (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.curry operation)
      (nativeToCone domain body) = piCurry domain body operation := by
  change NatTrans (overElements domain parameters) body at operation
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  change (nativeToCone domain body).app point
    ((Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.curry operation).app point parameter) = _
  have component := nativeToCone_app domain body point
    ((Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.curry operation).app point parameter)
  apply component.trans
  apply Subtype.ext
  funext argument
  exact eq_of_heq (dependentSectionEquiv_value domain body point _ argument)

theorem uncurry_compression {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans parameters (dependentFunctions domain body)) :
    piUncurry domain body (composeNat operation (nativeToCone domain body)) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.uncurry operation := by
  apply (piHomEquiv domain body parameters).injective
  change piCurry domain body (piUncurry domain body (composeNat operation (nativeToCone domain body))) =
    piCurry domain body (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.uncurry operation)
  rw [pi_curry_uncurry]
  exact ((curry_compression domain body
    (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.uncurry operation)).symm).trans
      (congrArg (fun source => composeNat source (nativeToCone domain body))
        (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.curry_uncurry operation)) |>.symm

end Mettapedia.TypeTheory.ContextualSmallFamilyConeComparison
