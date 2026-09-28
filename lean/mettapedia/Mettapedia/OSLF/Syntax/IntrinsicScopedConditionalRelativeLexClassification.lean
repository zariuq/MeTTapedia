import Mettapedia.OSLF.Syntax.IndexedRuleRelativeLexClassification
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFiniteContextSemantics

/-!
# Relative finite-limit semantics of authored scoped conditional rules

For a small binding-and-equation model, every authored conditional rule has
an ordered finite family of recursive premise positions. The generic
finite-list and relative finite-limit equivalences therefore apply to its
actual rule polynomial. This is the fixed-binding-model operational layer of
the larger classifying theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalRelativeLexClassification

open CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextSemantics
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
open Mettapedia.OSLF.Binding.IndexedRuleRelativeLexClassification
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.CartesianContextModels

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable (A : BindingCloneAlgebra.Algebra.{0} S)

/-- The finite-list event contexts of actual authored rules form a small
cartesian category. Its variables retain the exact local premise judgments
and repeated premise positions. -/
noncomputable def authoredListContextEquivalence :
    ListContext (rules R A) ≌
      Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts.Context (rules R A) :=
  listEquivalence (rules R A)

/-- At a fixed small binding-and-equation model, actual authored scoped
conditional rules are classified by left-exact Set-valued interpretations
of their relative finite-limit presentation. The equivalence includes all
constructor-preserving model maps and all natural interpretation maps. -/
noncomputable def authoredRuleLexSetClassification :
    RuleAlgebraModel (rules R A) ≌
      LexSetSemantics (ListContext (rules R A)) :=
  ruleLexSetClassification (rules R A)
    (fun _ shape => authoredPositionsFinite R A shape)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalRelativeLexClassification
