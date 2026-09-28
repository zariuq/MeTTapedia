import Mettapedia.OSLF.Syntax.CategoricalAuthoredOperationalModels
import Mettapedia.OSLF.Syntax.CategoricalEquationProgramCocones

/-!
# Restriction of operational interpretations to program cocones

An authored operational model has the same binding-equation and program
carrier data classified by the quotient-context cocone equivalence. This
restriction is functorial on the actual scoped-rule interpretation maps.
It does not erase events inside the operational model; it selects the base
to which the free event extension must be compared.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredProgramRestriction

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCocones
open Mettapedia.OSLF.Binding.CategoricalEquationProgramCocones
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]

/-- Forget the chosen event object and rule actions while keeping the
authored binding, equations and shared program object. -/
def forgetToPrograms (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      SatisfyingProgramModel (D := D) equations where
  obj X := ⟨X.base, X.satisfies⟩
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The quotient-context classification of the program part of every
authored operational interpretation. Firing evidence is the remaining
independent extension of this base. -/
noncomputable def classifiedProgramRestriction
    (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      QuotientProgramCocones (D := D) equations :=
  forgetToPrograms (D := D) equations rules ⋙
    (satisfyingQuotientProgramEquivalence (D := D) equations).functor

end Mettapedia.OSLF.Binding.CategoricalAuthoredProgramRestriction
