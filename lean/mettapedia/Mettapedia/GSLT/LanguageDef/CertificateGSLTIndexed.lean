import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mettapedia.GSLT.LanguageDef.CertificateGSLTSemantics

/-!
# Indexed proof semantics over CertificateGSLTs

For each fixed judgment, closed derivations form a covariant family over the
category of semantic presentations: interpreting a presentation transports
every derivation.  The same holds for open derivations with a fixed ordered
premise context.  These functors are the precise indexed structure behind the
informal statement that derivations are the fibers of `CertificateGSLT`.

Covariance is intentional.  A proof interpretation pushes derivations from
the source presentation to the target.  Context substitution inside an open
derivation is a separate, contravariant-looking axis supplied by `bind`.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

/-- Closed derivations of one judgment, covariantly indexed by semantic
presentation interpretations. -/
def derivationFunctor (goal : Pattern) :
    CategoryTheory.Functor Object Type where
  obj object := Derivation object.presentation goal
  map interpretation :=
    TypeCat.ofHom (Interpretation.mapDerivation interpretation)
  map_id object := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro derivation
    exact Interpretation.id_mapDerivation derivation
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro derivation
    exact Interpretation.comp_mapDerivation earlier later derivation

/-- Open derivations of one judgment from one ordered premise context,
covariantly indexed by semantic-presentation interpretations. -/
def openDerivationFunctor (context : List Pattern) (goal : Pattern) :
    CategoryTheory.Functor Object Type where
  obj object := OpenDerivation object.presentation context goal
  map interpretation :=
    TypeCat.ofHom (Interpretation.mapOpen interpretation)
  map_id object := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro derivation
    exact Interpretation.id_mapOpen derivation
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro derivation
    exact Interpretation.comp_mapOpen earlier later derivation

/-- Set-valued models form the contravariant semantic family: a proof
interpretation pulls every target model back to a source model. -/
def modelFunctor :
    CategoryTheory.Functor (Opposite Object) (Type (u + 1)) where
  obj object := Model.{u} (Opposite.unop object)
  map interpretation :=
    TypeCat.ofHom
      (Model.pullback (Quiver.Hom.unop interpretation))
  map_id object := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro model
    change Model.pullback
        (Interpretation.id (Opposite.unop object)) model = model
    exact Model.pullback_id model
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro model
    change Model.pullback
        (Interpretation.comp (Quiver.Hom.unop later)
          (Quiver.Hom.unop earlier)) model = _
    exact Model.pullback_comp
      (Quiver.Hom.unop later) (Quiver.Hom.unop earlier) model

/-! ## Concrete Grothendieck/category-of-elements endpoints -/

/-- Total category of a presentation together with one closed derivation of
`goal`.  A morphism is a presentation interpretation whose derivation action
sends the source proof to the target proof exactly. -/
abbrev DerivationTotal (goal : Pattern) :=
  (derivationFunctor goal).Elements

/-- Projection from total proof objects to their semantic presentations. -/
def derivationProjection (goal : Pattern) :
    DerivationTotal goal ⥤ Object :=
  CategoryTheory.CategoryOfElements.π (derivationFunctor goal)

/-- Total category of a presentation together with one open derivation from
the fixed ordered premise context. -/
abbrev OpenDerivationTotal (context : List Pattern) (goal : Pattern) :=
  (openDerivationFunctor context goal).Elements

/-- Projection from total open proofs to their semantic presentations. -/
def openDerivationProjection (context : List Pattern) (goal : Pattern) :
    OpenDerivationTotal context goal ⥤ Object :=
  CategoryTheory.CategoryOfElements.π
    (openDerivationFunctor context goal)

/-- Total category of set-valued models, over the opposite presentation
category because model transport is pullback. -/
abbrev ModelTotal := (modelFunctor.{u}).Elements

/-- Projection from semantic models to the presentations they realize. -/
def modelProjection : ModelTotal.{u} ⥤ Opposite Object :=
  CategoryTheory.CategoryOfElements.π modelFunctor.{u}

/-- The indexed action on closed derivations is exactly the already-proved
translation operation. -/
@[simp] theorem derivationFunctor_map_apply
    {source target : Object} (interpretation : source ⟶ target)
    {goal : Pattern} (derivation : Derivation source.presentation goal) :
    (derivationFunctor goal).map interpretation derivation =
      interpretation.mapDerivation derivation := rfl

/-- The indexed action on open proofs retains their ordered premise context. -/
@[simp] theorem openDerivationFunctor_map_apply
    {source target : Object} (interpretation : source ⟶ target)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation source.presentation context goal) :
    (openDerivationFunctor context goal).map interpretation derivation =
      interpretation.mapOpen derivation := rfl

/-- Plugging is natural in the presentation index: translating after plugging
equals plugging the translated proof and translated environment. -/
theorem bind_natural
    {source target : Object} (interpretation : source ⟶ target)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation source.presentation sourceContext goal)
    (environment :
      OpenDerivationList source.presentation targetContext sourceContext) :
    interpretation.mapOpen (derivation.bind environment) =
      (interpretation.mapOpen derivation).bind
        (interpretation.mapOpenList environment) :=
  Interpretation.mapOpen_bind interpretation derivation environment

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
