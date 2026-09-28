import Mettapedia.OSLF.Syntax.IndexedRuleFiniteProductClassification
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFreeGenerators

/-!
# Finitary contextual semantics of authored conditional rules

The generic finite-context construction applies to the actual intrinsic
authored-rule polynomial. Its positions are the finite ordered premise list,
even when a premise runs under its own local binders. Thus every authored
constructor has a context of exactly its recursive event inputs, and every
rule algebra gives a finite-product-preserving Set-valued interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextSemantics

open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits

universe u v

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable (A : BindingCloneAlgebra.Algebra.{u} S)

/-- Every constructor's recursive inputs are indexed by a finite list of
authored premises. -/
instance authoredPositionsFinite {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment) :
    Finite ((rules R A).Position shape) := by
  change Finite (Fin (R.get shape.1.index).premises.length)
  infer_instance

/-- The contextual input variables of an authored constructor are in
bijection with its ordered premise positions, retaining each position's
binder-extended judgment. -/
def authoredAritySlots {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment) :
    (Σ child, (arityContext (rules R A) shape).slots child) ≃
      Fin (R.get shape.1.index).premises.length :=
  aritySlotsEquiv (rules R A) shape

/-- A rule action determines a contextual semantic interpretation that
preserves all finite products. -/
theorem authoredAlgebraPreservesFiniteProducts
    {carrier : Judgment A → Type v}
    (action : (rules R A).Algebra (fun _ judgment => carrier judgment)) :
    PreservesFiniteProducts (algebraSemantics (rules R A) action) :=
  algebraSemanticsPreservesFiniteProducts (rules R A) action

/-- The semantic interpretation of an actual authored constructor is its
declared action on the ordered, binder-local premise values. -/
theorem authoredConstructorAction
    {carrier : Judgment A → Type v}
    (action : (rules R A).Algebra (fun _ judgment => carrier judgment))
    {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment)
    (assignment : Valuation (rules R A) (carrier := carrier)
      (arityContext (rules R A) shape)) :
    (singletonValuation (rules R A) judgment)
      ((algebraSemantics (rules R A) action).map
        (constructorArrow (rules R A) shape) assignment) =
      action.act PUnit.unit judgment
        ⟨shape, (arityValuation (rules R A) shape) assignment⟩ :=
  algebraSemantics_constructor (rules R A) action shape assignment

/-- On every finite family of existing event generators, contextual
interpretation agrees exactly with the preexisting authored firing-tree
fold. Both retain the same rule occurrences and ordered premise children. -/
theorem authoredFoldComparison
    (Γ : Context (rules R A))
    {carrier : Judgment A → Type v}
    (action : (rules R A).Algebra (fun _ judgment => carrier judgment))
    (assignment : Valuation (rules R A) (carrier := carrier) Γ)
    {judgment : Judgment A}
    (tree : IndexedRuleFiniteContexts.Term (rules R A) Γ judgment) :
    IntrinsicScopedConditionalFreeGenerators.foldWithEvents R A
        (fun index seed => assignment index seed) action judgment tree =
      interpretTerm (rules R A) action assignment tree := rfl

/-- At a fixed binding-and-equation model, the actual authored conditional
rules satisfy the finitary classification theorem. Its rule positions are
the source declaration's ordered, binder-local premises. -/
noncomputable def authoredRuleClassification :
    RuleAlgebraModel (rules R A) ≌
      ProductInterpretation (rules R A) :=
  finiteProductClassification (rules R A)
    (fun _ shape => authoredPositionsFinite R A shape)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextSemantics
