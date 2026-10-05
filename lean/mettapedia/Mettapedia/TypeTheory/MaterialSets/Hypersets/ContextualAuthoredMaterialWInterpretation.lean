import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality

/-!
# Natural material consumers and hereditary W elimination

The independently constructed graph dictionaries give a two-way comparison
between native natural maps and literal material-member maps. Hereditary W
folds therefore act on actual material members. Their constructor equation
is verified at material values, and every natural member consumer obeying
that equation is the constructed fold.

The parameter presheaf may be larger than the receipt universe. Neither
inverse chooses a quotient representative or a decoder from mere existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialWInterpretation

open CategoryTheory Mettapedia.TypeTheory
open ContextualAuthoredMaterialFamilies ContextualReceiptFamilyModels

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (source target : Family base)

def nativeHom (operation : WiderPresheafDependentFunctions.Hom source.members target.members) : source ⟶ target where
  app point term := (target.models point).decode (operation.app point ((source.models point).decode.symm term))
  naturality {first second} step term := by
    have input : source.members.map step ((source.models first).decode.symm term) =
        (source.models second).decode.symm (source.native.map step term) := by
      change (source.models second).decode.symm
        (source.native.map step ((source.models first).decode ((source.models first).decode.symm term))) = _
      rw [Equiv.apply_symm_apply]
    exact (target.memberRestriction_decode step
      (operation.app first ((source.models first).decode.symm term))).symm.trans
        ((congrArg (target.models second).decode
          (operation.naturality step ((source.models first).decode.symm term))).trans
            (congrArg (fun member => (target.models second).decode (operation.app second member)) input))

def homEquiv : (source ⟶ target) ≃ WiderPresheafDependentFunctions.Hom source.members target.members where
  toFun := source.memberHom
  invFun := nativeHom source target
  left_inv operation := by
    apply WiderPresheafDependentFunctions.Hom.ext
    intro point term
    change (target.models point).decode ((target.models point).decode.symm
      (operation.app point ((source.models point).decode ((source.models point).decode.symm term)))) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  right_inv operation := by
    apply WiderPresheafDependentFunctions.Hom.ext
    intro point member
    change (target.models point).decode.symm ((target.models point).decode
      (operation.app point ((source.models point).decode.symm ((source.models point).decode member)))) = _
    exact ((target.models point).decode.symm_apply_apply _).trans
      (congrArg (operation.app point) ((source.models point).decode.symm_apply_apply member))

variable (domain : Family base) (body : Family domain.extension)
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (algebra : ContextualSmallFamilyWiderAlgebra.Algebra domain.native (domain.bodyNative body)
  (target := target.native))

noncomputable def fold : domain.w body worlds arrows ⟶ target :=
  ContextualSmallFamilyWiderRecursion.foldMap domain.native (domain.bodyNative body) algebra

noncomputable def materialFold :
    WiderPresheafDependentFunctions.Hom (domain.w body worlds arrows).members target.members :=
  (domain.w body worlds arrows).memberHom (fold target domain body worlds arrows algebra)

theorem materialFold_decode (point : base.Elements)
    (member : (domain.w body worlds arrows).members.obj point) :
    (target.models point).decode ((materialFold target domain body worlds arrows algebra).app point member) =
      ContextualSmallFamilyWiderAlgebra.foldValue domain.native (domain.bodyNative body) algebra point
        (((domain.w body worlds arrows).models point).decode member) :=
  (domain.w body worlds arrows).memberHom_decode (fold target domain body worlds arrows algebra) point member

/-- Material beta exposes the entire natural constructor branch section,
including all later contexts and their actual arrows. -/
theorem materialFold_beta (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain.native (domain.bodyNative body)
      (domain.w body worlds arrows).native point) :
    ((materialFold target domain body worlds arrows algebra).app point
      (((domain.w body worlds arrows).models point).decode.symm
        (ContextualSmallFamilyWiderAlgebra.constructorValue domain.native (domain.bodyNative body) point node))).val =
    (target.models point).value
      (algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain.native (domain.bodyNative body)
        (fold target domain body worlds arrows algebra) point node)) := by
  change (target.models point).value
    ((fold target domain body worlds arrows algebra).app point
      (((domain.w body worlds arrows).models point).decode
        (((domain.w body worlds arrows).models point).decode.symm
          (ContextualSmallFamilyWiderAlgebra.constructorValue domain.native (domain.bodyNative body) point node)))) = _
  exact (congrArg (fun tree => (target.models point).value
    ((fold target domain body worlds arrows algebra).app point tree))
      (((domain.w body worlds arrows).models point).decode.apply_symm_apply _)).trans
    (congrArg (target.models point).value
      (ContextualSmallFamilyWiderInitiality.fold_beta domain.native (domain.bodyNative body) algebra point node))

/-- A natural literal-member consumer is uniquely fixed by its decoded
whole-constructor equation. This hypothesis constrains an arbitrary
consumer; it does not supply the desired fold. -/
theorem materialFold_unique
    (candidate : WiderPresheafDependentFunctions.Hom (domain.w body worlds arrows).members target.members)
    (law : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWiderPolynomial.At domain.native (domain.bodyNative body)
        (domain.w body worlds arrows).native point),
      (nativeHom (domain.w body worlds arrows) target candidate).app point
        (ContextualSmallFamilyWiderAlgebra.constructorValue domain.native (domain.bodyNative body) point node) =
      algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain.native (domain.bodyNative body)
        (nativeHom (domain.w body worlds arrows) target candidate) point node)) :
    candidate = materialFold target domain body worlds arrows algebra := by
  have native := ContextualSmallFamilyWiderInitiality.fold_unique domain.native (domain.bodyNative body)
    algebra (nativeHom (domain.w body worlds arrows) target candidate) law
  exact ((homEquiv (domain.w body worlds arrows) target).apply_symm_apply candidate).symm.trans
    (congrArg (domain.w body worlds arrows).memberHom native)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialWInterpretation
