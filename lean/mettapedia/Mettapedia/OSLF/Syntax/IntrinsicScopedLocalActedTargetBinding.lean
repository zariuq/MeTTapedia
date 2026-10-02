import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedBindingRestriction
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetPostcomposition

/-!
# Program restriction commutes with qualified change of target

Postcomposition of equation-context interpretations uses the same binding
preservation data as the operational classifier. Restricting before or after
target change is the canonical associator on the actual carrier functors.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {schema : List (MetaArity S)}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]

/-- The actual postcomposition of structured equation-context functors. -/
def postcomposeQuotientFunctors (P : EquationPresentation S schema) :
    QuotientStructuredFunctor (D := D) P ⥤ QuotientStructuredFunctor (D := D') P where
  obj F := { carrier := F.carrier ⋙ H, preserving := F.preserving.postcompose H }
  map α := Functor.whiskerRight α H
  map_id _ := by
    apply NatTrans.ext
    funext a
    exact H.map_id _
  map_comp _ _ := by
    apply NatTrans.ext
    funext a
    exact H.map_comp _ _

end Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]
variable [PreservesLimitsOfShape WalkingCospan H]

/-- Restriction of classifier interpretations to programs commutes
naturally with the actual postcomposition functors, including all maps. -/
def postcomposeRestrictionIso :
    postcomposeStructured (R := R) (equations := equations) H ⋙ restrictionToPrograms ≅
      restrictionToPrograms ⋙ postcomposeQuotientFunctors H (authoredEquationPresentation S equations) :=
  NatIso.ofComponents
    (fun F =>
      { hom := (Functor.associator (programSection R equations) F.carrier H).inv
        inv := (Functor.associator (programSection R equations) F.carrier H).hom
        hom_inv_id := (Functor.associator (programSection R equations) F.carrier H).inv_hom_id
        inv_hom_id := (Functor.associator (programSection R equations) F.carrier H).hom_inv_id })
    (fun {F G} α => by
      apply NatTrans.ext
      funext a
      change H.map (α.app ((programSection R equations).obj a)) ≫ 𝟙 _ =
        𝟙 _ ≫ H.map (α.app ((programSection R equations).obj a))
      rw [Category.comp_id, Category.id_comp])

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
