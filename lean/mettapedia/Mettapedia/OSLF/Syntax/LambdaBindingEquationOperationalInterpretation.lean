import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.LambdaRulePolynomialMorphism
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback

/-!
# Relative interpretation of lambda syntax, equations, and rule evidence

The presented binding-equation model supplies the unique interpretation of
authored operations and substitution. Over that interpretation, the relative
fold supplies the unique interpretation of every beta or congruence firing
history into an arbitrary target rule algebra. The construction retains the
individual premises and their contexts; it does not identify them with an
endpoint reduction predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaBindingEquationOperationalInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial
open Mettapedia.OSLF.Binding.LambdaRulePolynomialMorphism
open Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback
open Mettapedia.OSLF.Binding.FreeBindingEquationModel

universe u v

variable {M : List (MetaArity sig)} {E : List (EqAxiom sig M)}
variable (target : FreeBindingEquationModel.Model.{u} E)
variable {carrier : (b : Unit) → Judgment target.algebra → Type v}
variable (algebra : (rules target.algebra).Algebra carrier)

/-- A simultaneous interpretation of the equation model and every
proof-relevant lambda rule constructor. The rule action is interpreted
along the exact binding-clone morphism chosen in the first field. -/
structure Interpretation where
  clone : FreeBindingClone.Hom (presented E).algebra target.algebra
  fire : (j : Judgment (presented E).algebra) →
    (rules (presented E).algebra).Fix () j →
      carrier () (mapJudgment clone j)
  preserves : ∀ (j : Judgment (presented E).algebra)
      (shape : RuleShape (presented E).algebra j)
      (children : (p : premisePosition shape) →
        (rules (presented E).algebra).Fix () (premiseJudgment shape p)),
      fire j (.roll shape children) =
        (pullback (polynomialHom clone) algebra).act () j
          ⟨shape, fun p => fire (premiseJudgment shape p) (children p)⟩

/-- The unique equation interpretation and relative rule fold together
give a simultaneous interpretation into any target equation/rule model. -/
noncomputable def canonical : Interpretation target algebra where
  clone := interpretHom target
  fire := fun j tree =>
    relativeFold (polynomialHom (interpretHom target)) algebra () j tree
  preserves := by
    intro j shape children
    rfl

/-- Any simultaneous interpretation has the canonical clone map and the
canonical action on every complete firing history. -/
theorem unique (candidate : Interpretation target algebra) :
    candidate = canonical target algebra := by
  cases candidate with
  | mk clone fire preserves =>
      have cloneEq : clone = interpretHom target :=
        hom_unique target clone
      cases cloneEq
      have fireEq : fire =
          (fun j tree =>
            relativeFold (polynomialHom (interpretHom target)) algebra () j tree) := by
        funext j tree
        apply relativeFold_unique
          (polynomialHom (interpretHom target)) algebra
          (fun _ i value => fire i value)
        · intro b i shape children
          cases b
          exact preserves i shape children
      cases fireEq
      rfl

#print axioms canonical
#print axioms unique

end Mettapedia.OSLF.Binding.LambdaBindingEquationOperationalInterpretation
