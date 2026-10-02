import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionBindingIso
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassification

/-!
# Isomorphism transport of the classifier's chosen structure

Chosen binding structure and event-projection pullbacks transport along
natural isomorphisms of the actual classifier functors. No preservation
law is imposed as an extra hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {R : List (LocalRule S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace StructuredFunctor

/-- The actual program restriction of a classifier-functor isomorphism. -/
def transportProgramIso {F : StructuredFunctor R equations (D := D)}
    {G : Classifier R equations ⥤ D} (e : F.carrier ≅ G) :
    ((authoredEquationPresentation S equations).quotientFunctor ⋙
      programSection R equations ⋙ F.carrier) ≅
    ((authoredEquationPresentation S equations).quotientFunctor ⋙
      programSection R equations ⋙ G) :=
  Functor.isoWhiskerLeft (authoredEquationPresentation S equations).quotientFunctor
    (Functor.isoWhiskerLeft (programSection R equations) e)

/-- Transport structured data along a natural isomorphism of carriers. -/
def ofIso (F : StructuredFunctor R equations (D := D))
    {G : Classifier R equations ⥤ D} (e : F.carrier ≅ G) :
    StructuredFunctor R equations (D := D) where
  carrier := G
  program := F.program.ofIso (transportProgramIso e)
  pullback f j := (F.pullback f j).of_iso
    (e.app _) (e.app _) (e.app _) (e.app _)
    (e.hom.naturality _) (e.hom.naturality _)
    (e.hom.naturality _) (e.hom.naturality _)

/-- The structured isomorphism is the original isomorphism on every
object and arrow of the classifier. -/
def ofIsoComparison (F : StructuredFunctor R equations (D := D))
    {G : Classifier R equations ⥤ D} (e : F.carrier ≅ G) :
    F ≅ F.ofIso e where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

end StructuredFunctor
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
