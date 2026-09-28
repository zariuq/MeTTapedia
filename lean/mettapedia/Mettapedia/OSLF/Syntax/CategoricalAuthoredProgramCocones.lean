import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramCarrierMaps
import Mettapedia.OSLF.Syntax.CategoricalBindingEquationEquivalence
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The program carrier as a cocone on interpreted sorts

An authored many-sorted model may have a common program object receiving a
map from every sort. This is a cocone over the discrete diagram of interpreted
sorts, not a coproduct assumption on the semantic target. Packaging the
carrier as a comma object exposes the extension that must be classified when
the binding-equation equivalence is enlarged by operational evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCocones

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature}
variable {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The discrete diagram of sorts interpreted by an equation model. -/
def sortDiagram (equations : EquationPresentation S schema) :
    SatisfyingInterpretation (D := D) equations ⥤
      (Discrete S.Srt ⥤ D) where
  obj X := Discrete.functor X.interpretation.model.sort
  map f := Discrete.natTrans (fun sort => f.underlying.sort sort.as)
  map_id := by
    intro X
    apply NatTrans.ext
    funext sort
    rfl
  map_comp := by
    intro X Y Z f g
    apply NatTrans.ext
    funext sort
    rfl

/-- A constant diagram with one shared program object. -/
def constantProgram : D ⥤ (Discrete S.Srt ⥤ D) :=
  Functor.const (Discrete S.Srt)

/-- Adding a common program carrier to an equation interpretation is a
comma construction. No coproduct of sorts is required in `D`. -/
abbrev ProgramCocones (equations : EquationPresentation S schema) :=
  Comma (sortDiagram (D := D) equations) (constantProgram (S := S))

/-- The same data in the direct authored-model presentation. -/
structure SatisfyingProgramModel
    (equations : EquationPresentation S schema) where
  base : ModelWithPrograms S D
  satisfies : base.binding.Satisfies equations

instance (equations : EquationPresentation S schema) :
    Category (SatisfyingProgramModel (D := D) equations) where
  Hom X Y := ModelWithPrograms.Hom X.base Y.base
  id X := ModelWithPrograms.Hom.id X.base
  comp f g := f.comp g
  id_comp := by
    intro X Y f
    exact ModelWithPrograms.Hom.id_comp f
  comp_id := by
    intro X Y f
    exact ModelWithPrograms.Hom.comp_id f
  assoc := by
    intro W X Y Z f g h
    exact ModelWithPrograms.Hom.comp_assoc f g h

/-- Restricting an authored program interpretation to its discrete sort
diagram records precisely the family of sort-to-program embeddings. -/
def asCocone (equations : EquationPresentation S schema) :
    SatisfyingProgramModel (D := D) equations ⥤
      ProgramCocones (D := D) equations where
  obj X := {
    left := ⟨⟨X.base.binding⟩, X.satisfies⟩
    right := X.base.carrier.program
    hom := Discrete.natTrans (fun sort => X.base.carrier.embedSort sort.as) }
  map f := {
    left := f.binding
    right := f.program
    w := by
      apply NatTrans.ext
      funext sort
      exact f.sort_comm sort.as }
  map_id := by
    intro X
    apply CommaMorphism.ext
    · rfl
    · rfl
  map_comp := by
    intro X Y Z f g
    apply CommaMorphism.ext
    · rfl
    · rfl

/-- Read a program cocone as the direct binding model and its carrier. -/
def fromCocone (equations : EquationPresentation S schema) :
    ProgramCocones (D := D) equations ⥤
      SatisfyingProgramModel (D := D) equations where
  obj X := {
    base := {
      binding := X.left.interpretation.model
      carrier := {
        program := X.right
        embedSort := fun sort => X.hom.app (Discrete.mk sort) } }
    satisfies := X.left.satisfies }
  map f := {
    binding := f.left
    program := f.right
    sort_comm := by
      intro sort
      have square := congrArg
        (fun arrow => arrow.app (Discrete.mk sort)) f.w
      exact square }
  map_id := by
    intro X
    apply ModelWithPrograms.Hom.ext <;> rfl
  map_comp := by
    intro X Y Z f g
    apply ModelWithPrograms.Hom.ext <;> rfl

/-- The cocone presentation remembers every map of authored sorts and the
shared program object, including noninjective sort embeddings. -/
instance asCocone_faithful
    (equations : EquationPresentation S schema) :
    (asCocone (D := D) equations).Faithful where
  map_injective := by
    intro X Y f g same
    apply ModelWithPrograms.Hom.ext
    · exact congrArg CommaMorphism.left same
    · exact congrArg CommaMorphism.right same

instance asCocone_full
    (equations : EquationPresentation S schema) :
    (asCocone (D := D) equations).Full where
  map_surjective := by
    intro X Y f
    refine ⟨(fromCocone (D := D) equations).map f, ?_⟩
    apply CommaMorphism.ext <;> rfl

instance asCocone_essSurj
    (equations : EquationPresentation S schema) :
    (asCocone (D := D) equations).EssSurj where
  mem_essImage X := by
    let source := (fromCocone (D := D) equations).obj X
    have same : (asCocone (D := D) equations).obj source = X := by
      cases X with
      | mk left right hom =>
          dsimp [source, fromCocone, asCocone]
          congr 1
    exact ⟨source, ⟨eqToIso same⟩⟩

noncomputable instance asCocone_isEquivalence
    (equations : EquationPresentation S schema) :
    (asCocone (D := D) equations).IsEquivalence where

/-- Common program carriers form the cocone extension of authored equation
interpretations, on objects and all interpretation maps. -/
noncomputable def programCoconeEquivalence
    (equations : EquationPresentation S schema) :
    SatisfyingProgramModel (D := D) equations ≌
      ProgramCocones (D := D) equations :=
  (asCocone (D := D) equations).asEquivalence

end Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCocones
