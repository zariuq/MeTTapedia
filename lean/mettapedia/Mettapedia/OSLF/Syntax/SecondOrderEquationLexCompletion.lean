import Mettapedia.OSLF.Syntax.SecondOrderEquationProducts
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations

/-!
# Relative finite-limit completion of authored equation contexts

The authored higher-order equations first form a substitution-stable
second-order quotient. Its context products survive the quotient. The
existing relative finite-limit construction can therefore classify
product-preserving interpretations of these actual equation contexts in
every small finitely complete target.

This is the equational and finite-limit part of the classifying theorem.
Chosen function structure and individual firing events remain additional
operational structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels

/-- The relative finite-limit classifier applies to every authored list of
higher-order binding equations. Its universal property includes maps and
the equivalence coherence, for each small finitely complete target. -/
noncomputable def authoredEquationLexEquivalence
    (S : Signature) {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (D : Type) [SmallCategory D] [HasFiniteLimits D] :
    LeftExactTargetInterpretations
        (EquationContexts (authoredEquationPresentation S equations)) D ≌
      CartesianTargetInterpretations
        (EquationContexts (authoredEquationPresentation S equations)) D :=
  cartesianTargetLexEquivalence
    (EquationContexts (authoredEquationPresentation S equations)) D

/-- The finite-limit comparison also retains an arbitrary object of firing
events and both endpoint maps at a selected authored program sort. This
does not yet impose the authored conditional rule actions on that object. -/
noncomputable def authoredEquationEventEquivalence
    (S : Signature) {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    (program : EquationContexts
      (authoredEquationPresentation S equations)) :
    LeftExactEventInterpretations
        (EquationContexts (authoredEquationPresentation S equations)) D
        program ≌
      AuthoredEventInterpretations
        (EquationContexts (authoredEquationPresentation S equations)) D
        program :=
  eventInterpretationEquivalence
    (EquationContexts (authoredEquationPresentation S equations)) D program

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationLexEquivalence
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationEventEquivalence
