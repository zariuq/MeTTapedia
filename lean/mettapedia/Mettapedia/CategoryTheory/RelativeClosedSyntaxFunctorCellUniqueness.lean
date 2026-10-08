import Mettapedia.CategoryTheory.CartesianClosedFunctorCellIdentity
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationRealization

/-!
# Local-to-complete uniqueness of cells on relative closed syntax

Identity readings at the embedded base and individual fresh object names
propagate through every raw object constructor. Products are determined by
their two projections; functions by actual evaluation and the target closed
adjunction; equalizers by the mapped monic inclusion of their genuine limit.
Raw object presentations are retained throughout.

Consequently, a given natural isomorphism and any natural cell with the same
local generator readings agree on the entire generated category. This result
does not assume identity components at all generated objects, or assert that
unrestricted cells preserve the chosen primitive readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorCellUniqueness

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (cell : mapping ⟶ mapping)

structure PrimitiveComponentsFixed : Prop where
  base (object : C) : cell.app (baseObject signature object) = 𝟙 (mapping.obj (baseObject signature object))
  object (origin : symbols.ObjectName) : cell.app (namedObject origin) = 𝟙 (mapping.obj (namedObject origin))

theorem object_fixed (admitted : PrimitiveComponentsFixed mapping cell) (object : Object signature) :
    cell.app object = 𝟙 (mapping.obj object) := by
  rcases object with ⟨code, formed⟩
  revert formed
  cases constructor : code with
  | base object => exact fun _ => admitted.base object
  | name origin => exact fun _ => admitted.object origin
  | terminal => exact fun _ => CartesianClosedFunctorCellIdentity.terminal_fixed mapping cell
  | product first second =>
      intro formed
      obtain ⟨firstFormed, secondFormed⟩ := product_formation formed
      exact CartesianClosedFunctorCellIdentity.product_fixed mapping cell
        (⟨first, firstFormed⟩ : Object signature) ⟨second, secondFormed⟩
        (object_fixed admitted ⟨first, firstFormed⟩) (object_fixed admitted ⟨second, secondFormed⟩)
  | exponential argument result =>
      intro formed
      obtain ⟨argumentFormed, resultFormed⟩ := exponential_formation formed
      exact CartesianClosedFunctorCellIdentity.exponential_fixed mapping cell
        (⟨argument, argumentFormed⟩ : Object signature) ⟨result, resultFormed⟩
        (object_fixed admitted ⟨argument, argumentFormed⟩) (object_fixed admitted ⟨result, resultFormed⟩)
  | equalizer source target first second =>
      intro formed
      obtain ⟨sourceFormed, targetFormed, firstTyped, secondTyped⟩ := equalizer_formation formed
      let before : RawHom (⟨source, sourceFormed⟩ : Object signature) ⟨target, targetFormed⟩ := ⟨first, firstTyped⟩
      let after : RawHom (⟨source, sourceFormed⟩ : Object signature) ⟨target, targetFormed⟩ := ⟨second, secondTyped⟩
      have : Mono (mapping.map (PresentedEqualizer.inclusion before after)) :=
        Fork.IsLimit.mono (mappedPresentedIsLimit mapping before after)
      apply (cancel_mono (mapping.map (PresentedEqualizer.inclusion before after))).mp
      rw [Category.id_comp]
      have natural := cell.naturality (PresentedEqualizer.inclusion before after)
      rw [object_fixed admitted (⟨source, sourceFormed⟩ : Object signature), Category.comp_id] at natural
      exact natural.symm
termination_by objectDepth object.code
decreasing_by
  all_goals simp_all only [objectDepth]
  all_goals omega

theorem cell_identity (admitted : PrimitiveComponentsFixed mapping cell) : cell = 𝟙 mapping :=
  NatTrans.ext (funext (fun object => object_fixed mapping cell admitted object))

variable {mapping}
variable {target : Object signature ⥤ D}

theorem cells_equal_of_generators (comparison : mapping ≅ target) (candidate : mapping ⟶ target)
    (base : ∀ object : C, candidate.app (baseObject signature object) =
      comparison.hom.app (baseObject signature object))
    (objects : ∀ origin : symbols.ObjectName, candidate.app (namedObject origin) =
      comparison.hom.app (namedObject origin)) : candidate = comparison.hom := by
  let endomorphism : mapping ⟶ mapping := candidate ≫ comparison.inv
  have admitted : PrimitiveComponentsFixed mapping endomorphism := {
    base := fun object => by
      change candidate.app (baseObject signature object) ≫ comparison.inv.app (baseObject signature object) = _
      rw [base, Iso.hom_inv_id_app]
    object := fun origin => by
      change candidate.app (namedObject origin) ≫ comparison.inv.app (namedObject origin) = _
      rw [objects, Iso.hom_inv_id_app]
  }
  apply (cancel_mono comparison.inv).mp
  exact (cell_identity mapping endomorphism admitted).trans comparison.hom_inv_id.symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorCellUniqueness
