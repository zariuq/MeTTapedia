import Mettapedia.TypeTheory.ContextualPredicateCapabilities
import Mettapedia.TypeTheory.ContextualPiEta
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Dependent models with an external predicate doctrine

The model combines local dependent type operations, a Heyting predicate
doctrine with display quantifiers, an ordinary proposition type, guarded
assumption contexts and witness-preserving refinements. Its predicates may
be definable predicates of a generated theory; they are not required to be
all subobjects. The qualification contains only local product equations and
their chosen substitution laws, never generated syntax soundness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateModel

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualTypeOperations ContextualSumComprehension

universe c s t m p

structure LocalModel (C : CwfWithTerminal.{c, s, t, m}) where
  products : PiOperations C.toCwf
  sums : StableSums C.toCwf
  doctrine : PredicateDoctrine.{c, s, t, m, p} C.toCwf
  propositions : PropositionOperations doctrine
  assumptions : AssumptionOperations doctrine
  refinements : RefinementOperations doctrine

/-- The product family and operations have the stated strict chosen
substitution action. Coherent but non-strict models require an adapter. -/
structure Qualification {C : CwfWithTerminal.{c, s, t, m}}
    (model : LocalModel.{c, s, t, m, p} C) : Prop where
  stableProducts : StrictPiSubstitution model.products
  productBeta : PiBeta model.products
  productEta : ContextualPiEta.PiEta model.products stableProducts.1

end Mettapedia.TypeTheory.ContextualPredicateModel
