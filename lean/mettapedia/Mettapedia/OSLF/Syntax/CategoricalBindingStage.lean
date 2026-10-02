import Mettapedia.OSLF.Syntax.CategoricalBindingStageCore
import Mettapedia.OSLF.Syntax.CategoricalBindingEquations
import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality

/-!
# The binding clone of generalized elements at a stage

For a binding model in a category and a stage object `C`, the natural families
of generalized elements over `C` form a binding clone. A generalized element
`x : Z ⟶ M.family X.arities` of a metavariable family interprets the
equation-class binding model at `X` in the clone at `Z`: an equation class is
interpreted by its representative, sound because the model satisfies the
equations, and restaged along `x`. Reindexing `x` along a class of contextual
assignments is instantiating the metavariables by that assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

/-- Equation classes over the metavariables of `X` are interpreted by their
representatives; the model's satisfaction of the equations makes this sound. -/
noncomputable def classMap (sat : M.Satisfies P) (X : Object S) :
    FreeBindingClone.Hom
      (restrictAlgebra X (BindingEquationQuotientModel.algebra (P.axioms X)))
      (restrictAlgebra X (M.kripke X.arities)) :=
  restrictHom X (FreeBindingEquationModel.quotientHom (M.kripke X.arities)
    (fun related => M.interp_eqClosure (sat X) related))

/-- A generalized element of the metavariable family interprets the
equation-class binding model in the clone at its stage. -/
noncomputable def pointProgram (sat : M.Satisfies P) (X : Object S) {Z : D}
    (x : Z ⟶ M.family X.arities) :
    FreeBindingClone.Hom
      (restrictAlgebra X (BindingEquationQuotientModel.algebra (P.axioms X))) (M.stage Z) :=
  FreeBindingClone.Hom.comp (M.classMap P sat X) (M.restageHom X x)

/-- Restaging a point is restaging its interpretation. -/
theorem pointProgram_restage (sat : M.Satisfies P) (X : Object S) {Z Z' : D} (h : Z' ⟶ Z)
    (x : Z ⟶ M.family X.arities) :
    M.pointProgram P sat X (h ≫ x) =
      FreeBindingClone.Hom.comp (M.pointProgram P sat X x) (M.stageRestage h) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s q
  apply ElemOver.ext
  funext W w ρ
  exact congrArg (fun m => (((M.classMap P sat X).raw.map q) : M.ElemOver _ Γ s).value W m ρ)
    (Category.assoc w h x).symm

/-- **Reindexing a point instantiates the metavariables.** Moving a
generalized element along a class of contextual assignments interprets the
target context's equation classes through the assignment's model map. -/
theorem pointProgram_move {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))
    (sat : M.Satisfies (authoredEquationPresentation S equations))
    {X Y : EquationContexts (authoredEquationPresentation S equations)} (assignment : X ⟶ Y)
    {Z : D} (x : Z ⟶ M.family X.as.arities) :
    M.pointProgram _ sat Y.as
        (x ≫ (M.equationClassifyingFunctor _ sat).map assignment) =
      FreeBindingClone.Hom.comp (authoredEquationModelMapQuot S equations assignment)
        (M.pointProgram _ sat X.as x) := by
  induction assignment using Quot.ind with
  | _ raw =>
    apply FreeBindingClone.Hom.ext
    apply FreeBindingTerms.Hom.ext
    intro Γ s q
    induction q using Quotient.inductionOn with
    | _ t =>
      change M.restageElem (x ≫ M.assignHom raw) (M.interp Y.as.arities t) =
        M.restageElem x (M.interp X.as.arities (instInto raw t))
      rw [M.interp_instInto raw t]
      apply ElemOver.ext
      funext W w ρ
      exact congrArg (fun m => (M.interp Y.as.arities t).value W m ρ) (Category.assoc w x _).symm

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
