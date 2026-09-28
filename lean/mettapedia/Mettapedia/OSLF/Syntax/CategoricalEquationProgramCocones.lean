import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramCocones
import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence

/-!
# Program carriers along the authored equation classifier

The program object is additional semantic data over a binding-equation
interpretation. At the raw structured-functor stage, its sort cocone is
transported by the actual sort isomorphisms of the classifying theorem.
This provides the compatibility needed before any operational rule algebra
is added.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalEquationProgramCocones

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCocones
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (equations : EquationPresentation S schema)

/-- The sort objects picked out of a structured interpretation of authored
contexts. The selected one-metavariable context represents the sort. -/
def respectingSortDiagram :
    RespectingStructuredFunctor (D := D) equations ⥤
      (Discrete S.Srt ⥤ D) where
  obj X := Discrete.functor fun sort =>
    X.structured.carrier.obj (oneObj [] sort)
  map f := Discrete.natTrans fun sort =>
    f.app (oneObj [] sort.as)
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

/-- The identity between a semantic sort and its representing contextual
object is natural even for noninvertible interpretation maps. -/
theorem sortIso_natural {M N : Model S D}
    (h : CategoricalBindingInterpretationMaps.Hom M N)
    (sort : S.Srt) :
    (classifyingMap h).app (oneObj [] sort) ≫
      (N.sortIso sort).hom =
    (M.sortIso sort).hom ≫ h.underlying.sort sort := by
  have sortComponent :
      Model.natSort (classifyingMap h) sort =
        h.underlying.sort sort := by
    exact congrArg
      (fun map : CategoricalBindingInterpretationMaps.Hom M N =>
        map.underlying.sort sort)
      (CategoricalBindingInterpretationMaps.Hom.ofNat_classifyingMap h)
  calc
    (classifyingMap h).app (oneObj [] sort) ≫
        (N.sortIso sort).hom =
      ((M.sortIso sort).hom ≫ (M.sortIso sort).inv) ≫
        (classifyingMap h).app (oneObj [] sort) ≫
        (N.sortIso sort).hom := by simp
    _ = (M.sortIso sort).hom ≫
        Model.natSort (classifyingMap h) sort := by
          simp only [Model.natSort, Category.assoc]
    _ = (M.sortIso sort).hom ≫ h.underlying.sort sort := by
          rw [sortComponent]

/-- The two independently defined sort diagrams agree by the canonical
sort-object isomorphism, compatibly with every model morphism. -/
noncomputable def equationSortComparison :
    equationClassifier (D := D) equations ⋙
        respectingSortDiagram (D := D) equations ≅
      sortDiagram (D := D) equations :=
  NatIso.ofComponents
    (fun X => Discrete.natIso fun sort =>
      X.interpretation.model.sortIso sort.as)
    (by
      intro X Y h
      apply NatTrans.ext
      funext sort
      exact sortIso_natural h sort.as)

/-- Structured interpretations of the authored equation category equipped
with a separate common program object and all sort embeddings. -/
abbrev RespectingProgramCocones :=
  Comma (respectingSortDiagram (D := D) equations)
    (constantProgram (S := S))

/-- The binding-equation classifier extends to the extra program object.
The first equivalence transports the canonical sort isomorphisms; the second
uses the already proved equivalence of binding-equation interpretations. -/
noncomputable def equationProgramCoconeEquivalence :
    ProgramCocones (D := D) equations ≌
      RespectingProgramCocones (D := D) equations :=
  (Comma.mapLeftIso (R := constantProgram (S := S))
      (equationSortComparison (D := D) equations).symm).trans
    ((Comma.preLeft (equationClassifier (D := D) equations)
      (respectingSortDiagram (D := D) equations)
      (constantProgram (S := S))).asEquivalence)

/-- The resulting relative classification is an equivalence on objects and
all noninvertible interpretation maps, with the program carrier retained. -/
noncomputable def satisfyingProgramEquivalence :
    SatisfyingProgramModel (D := D) equations ≌
      RespectingProgramCocones (D := D) equations :=
  (programCoconeEquivalence (D := D) equations).trans
    (equationProgramCoconeEquivalence (D := D) equations)

/-- Quotient-context semantics selects exactly the same represented sort
objects: restriction does not change the one-metavariable object. -/
def quotientSortDiagram :
    QuotientStructuredFunctor (D := D) equations ⥤
      (Discrete S.Srt ⥤ D) :=
  restrictStructured (D := D) equations ⋙
    respectingSortDiagram (D := D) equations

theorem quotientSortDiagram_obj
    (X : QuotientStructuredFunctor (D := D) equations)
    (sort : S.Srt) :
    ((quotientSortDiagram (D := D) equations).obj X).obj
        (Discrete.mk sort) =
      X.carrier.obj ⟨oneObj [] sort⟩ :=
  rfl

/-- The program carrier is a genuine cocone over the equation-class
contexts, not a coproduct of the source-language sorts. -/
abbrev QuotientProgramCocones :=
  Comma (quotientSortDiagram (D := D) equations)
    (constantProgram (S := S))

/-- The quotient-context equivalence transports the whole sort cocone,
including every noninvertible map of program objects. -/
noncomputable def quotientProgramCoconeEquivalence :
    QuotientProgramCocones (D := D) equations ≌
      RespectingProgramCocones (D := D) equations :=
  ((Comma.preLeft (restrictStructured (D := D) equations)
      (respectingSortDiagram (D := D) equations)
      (constantProgram (S := S))).asEquivalence)

/-- Relative classification of equations and the additional common program
object, with its sort embeddings and all lawful interpretation maps. The
operational event algebra remains the next extension. -/
noncomputable def satisfyingQuotientProgramEquivalence :
    SatisfyingProgramModel (D := D) equations ≌
      QuotientProgramCocones (D := D) equations :=
  (satisfyingProgramEquivalence (D := D) equations).trans
    (quotientProgramCoconeEquivalence (D := D) equations).symm

end Mettapedia.OSLF.Binding.CategoricalEquationProgramCocones
