import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFiniteContextChange
import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality
import Mathlib.CategoryTheory.Grothendieck

/-!
# Operational contexts varying with the program interpretation

A binding-clone model determines a finite category of contextual event
variables and free authored firing-tree substitutions. Binding-model maps
act on those fibers. Their Grothendieck construction keeps the program-model
map and the event substitution as separate, composable parts of an arrow.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalTotalContext

open CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.SecondOrderContext

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- The free operational context category varies functorially with the
binding-clone interpretation. -/
noncomputable def operationalFibers :
    BindingCloneAlgebra.Algebra.{0} S ⥤ Cat.{0, 0} where
  obj A := Cat.of (ListContext (rules R A))
  map h := (pushFunctor R h).toCatHom
  map_id A := by
    apply Cat.Hom.ext
    exact pushFunctor_id R A
  map_comp f g := by
    apply Cat.Hom.ext
    exact pushFunctor_comp R f g

/-- A total context carries a program interpretation together with a
finite list of contextual event variables over that interpretation. -/
abbrev TotalContext := Grothendieck (operationalFibers R)

/-- Forget equation satisfaction while retaining the complete binding clone
and every substitution-preserving model map. -/
def forgetEquations (equations : List (EqAxiom S M)) :
    FreeBindingEquationModel.Model equations ⥤
      BindingCloneAlgebra.Algebra.{0} S where
  obj model := model.algebra
  map interpretation := interpretation
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Over an authored equation context, event variables are contextual
judgments in its actual equation-class binding model. A contextual
assignment reindexes the complete free rule trees. -/
noncomputable def authoredOperationalFibers
    (equations : List (EqAxiom S M)) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤
      Cat.{0, 0} :=
  authoredEquationQuotientModelPresheaf S equations ⋙
    forgetEquations equations ⋙ operationalFibers R

/-- The contextual operational category has an authored equation context
and a finite list of individually typed event variables at each object.
Its arrows carry the contextual assignment and a free firing-tree
substitution in the reindexed fiber. -/
abbrev AuthoredTotalContext (equations : List (EqAxiom S M)) :=
  Grothendieck (authoredOperationalFibers R equations)

/-- A chosen equation-class program context with its finite ordered list
of contextual event variables. -/
def authoredObject (equations : List (EqAxiom S M))
    (X : EquationContexts (authoredEquationPresentation S equations))
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)) :
    AuthoredTotalContext R equations :=
  ⟨Opposite.op X, Γ⟩

/-- An authored contextual assignment followed by a simultaneous
substitution of retained event variables. The base assignment is written
from `Y` to `X` because the free equation models form a presheaf. -/
noncomputable def authoredArrow (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra))
    (assignment : Y ⟶ X)
    (events : pushContext R
      (authoredEquationModelMapQuot S equations assignment) Γ ⟶ Δ) :
    authoredObject R equations X Γ ⟶ authoredObject R equations Y Δ where
  base := assignment.op
  fiber := events

theorem authoredArrow_base (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra))
    (assignment : Y ⟶ X)
    (events : pushContext R
      (authoredEquationModelMapQuot S equations assignment) Γ ⟶ Δ) :
    (authoredArrow R equations Γ Δ assignment events).base =
      assignment.op := rfl

theorem authoredArrow_fiber (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra))
    (assignment : Y ⟶ X)
    (events : pushContext R
      (authoredEquationModelMapQuot S equations assignment) Γ ⟶ Δ) :
    (authoredArrow R equations Γ Δ assignment events).fiber =
      events := rfl

/-- At a fixed contextual assignment, separate simultaneous event
substitutions remain separate arrows of the total category. -/
theorem authoredArrow_injective_events
    (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra))
    (assignment : Y ⟶ X) :
    Function.Injective
      (authoredArrow R equations Γ Δ assignment) := by
  intro first second equal
  injection equal

/-- The authored equation-context category embeds by carrying no assumed
firing events. Event variables are added by the operational fiber, while
the original contextual substitutions remain visible in the base. -/
noncomputable def programSection (equations : List (EqAxiom S M)) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤
      AuthoredTotalContext R equations where
  obj X := authoredObject R equations X.unop
    (emptyList R (authoredEquationModelAt S equations X.unop.as).algebra)
  map {X Y} assignment :=
    authoredArrow R equations
      (emptyList R (authoredEquationModelAt S equations X.unop.as).algebra)
      (emptyList R (authoredEquationModelAt S equations Y.unop.as).algebra)
      assignment.unop
      (fun _ slot => Fin.elim0 slot.1)
  map_id X := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      funext judgment slot
      exact Fin.elim0 slot.1
  map_comp f g := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      funext judgment slot
      exact Fin.elim0 slot.1

/-- Forgetting event variables after embedding an authored program context
returns exactly that original equation context and its assignment arrows. -/
theorem programSection_forget (equations : List (EqAxiom S M)) :
    programSection R equations ⋙
      Grothendieck.forget (authoredOperationalFibers R equations) =
        𝟭 ((EquationContexts
          (authoredEquationPresentation S equations))ᵒᵖ) := by
  refine CategoryTheory.Functor.hext (fun X => rfl) ?_
  intro X Y assignment
  rfl

/-- Adding the event-variable layer creates no new arrows between program
contexts that assume no firing events. -/
instance programSection_full (equations : List (EqAxiom S M)) :
    (programSection R equations).Full where
  map_surjective := by
    intro X Y arrow
    refine ⟨arrow.base, ?_⟩
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber =>
      funext judgment slot
      exact Fin.elim0 slot.1

/-- Distinct contextual program assignments remain distinct after adding
the event-variable layer. -/
instance programSection_faithful (equations : List (EqAxiom S M)) :
    (programSection R equations).Faithful where
  map_injective := by
    intro X Y first second equal
    exact congrArg Grothendieck.Hom.base equal

/-- Every authored rule action occurs in the total contextual category as
the same free firing-tree constructor, with one separate variable at each
ordered binder-local premise. The fiber inclusion does not quotient these
occurrences by their endpoints. -/
noncomputable def authoredConstructor (equations : List (EqAxiom S M))
    (X : EquationContexts (authoredEquationPresentation S equations))
    {judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment
      (authoredEquationModelAt S equations X.as).algebra}
    (shape : (rules R (authoredEquationModelAt S equations X.as).algebra).Shape
      PUnit.unit judgment) :
    authoredObject R equations X
      (arityList R (authoredEquationModelAt S equations X.as).algebra shape) ⟶
    authoredObject R equations X
      (singletonList R (authoredEquationModelAt S equations X.as).algebra
        judgment) :=
  (Grothendieck.ι (authoredOperationalFibers R equations)
    (Opposite.op X)).map
      (constructorArrowList R
        (authoredEquationModelAt S equations X.as).algebra shape)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalTotalContext
