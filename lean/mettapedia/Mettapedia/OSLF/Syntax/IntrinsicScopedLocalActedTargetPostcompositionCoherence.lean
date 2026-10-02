import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetPostcomposition
import Mettapedia.OSLF.Syntax.CategoricalBindingTargetComposition

/-!
# Identity and successive target changes for structured interpretations

The comparisons are the canonical unitor and associator of actual
postcomposition. They are natural in every interpretation map.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v u' v' u'' v''

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {D'' : Type u''} [Category.{v''} D''] [CartesianMonoidalCategory D'']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace StructuredFunctor

/-- An isomorphism of carrier functors is an isomorphism of structured
interpretations; the structure is part of the objects. -/
def isoOfCarrier {F G : StructuredFunctor R equations (D := D)}
    (i : F.carrier ≅ G.carrier) : F ≅ G where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

end StructuredFunctor

/-- The identity target change is naturally the identity interpretation. -/
def postcomposeStructuredIdentityIso :
    postcomposeStructured (R := R) (equations := equations) (𝟭 D) ≅
      𝟭 (StructuredFunctor R equations (D := D)) :=
  NatIso.ofComponents
    (fun F => StructuredFunctor.isoOfCarrier (Functor.rightUnitor F.carrier))
    (fun {F G} α => by
      apply NatTrans.ext
      funext a
      change α.app a ≫ 𝟙 _ = 𝟙 _ ≫ α.app a
      rw [Category.comp_id, Category.id_comp])

variable (H : D ⥤ D') (K : D' ⥤ D'')
variable [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]
variable [PreservesFiniteProducts K] [PreservesLimitsOfShape WalkingCospan K]
variable [ExponentialPreservation K]

/-- Successive changes of target agree with the composite change. -/
def postcomposeStructuredCompositionIso :
    postcomposeStructured (R := R) (equations := equations) H ⋙ postcomposeStructured K ≅
      postcomposeStructured (H ⋙ K) :=
  NatIso.ofComponents
    (fun F => StructuredFunctor.isoOfCarrier (Functor.associator F.carrier H K))
    (fun {F G} α => by
      apply NatTrans.ext
      funext a
      change K.map (H.map (α.app a)) ≫ 𝟙 _ = 𝟙 _ ≫ K.map (H.map (α.app a))
      rw [Category.comp_id, Category.id_comp])

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
