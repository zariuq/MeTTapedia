import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualProducts
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSumElimination
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptionModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPropositionModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinementModel
import Mettapedia.TypeTheory.ContextualPredicateModel

/-!
# The local dependent model of generated judgments

The generated context category, type and term fibres, predicate doctrine,
ordinary propositions, guarded assumptions and retained refinements form
one local dependent model. Its chosen product equations and substitution
qualification come from the generated rules, independently of any semantic
interpreter or classifying assertion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open Mettapedia.TypeTheory.ContextualPredicateModel

universe u
variable {S : Symbols.{u}}

noncomputable def generatedModel (D : Signature S) :
    LocalModel (QuotientCwf.withTerminal D) where
  products := Products.operations D
  sums := SumElimination.stable D
  doctrine := predicateDoctrine D
  propositions := PropositionModel.operations D
  assumptions := AssumptionModel.operations D
  refinements := RefinementModel.operations D

theorem generatedModel_qualification (D : Signature S) :
    Qualification (generatedModel D) where
  stableProducts := Products.substitution
  productBeta := Products.beta
  productEta := Products.eta

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
