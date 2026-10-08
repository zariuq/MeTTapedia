import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPolynomial

/-!
# Complete raw readouts of rule-local binding occurrences

The actual semantic conclusion and each binder-local premise in the term
clone agree with the independently defined contextual schema instantiator.
The premise comparison retains its ordered position and complete extension.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalRawReadout

open SemanticContextualMetavariables SemanticScopedPremiseInterpretation
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedLocalPolynomial (LocalRule Instance)

variable {S : Signature} (rules : List (LocalRule S))

theorem conclusion (occurrence : Instance rules (BindingCloneAlgebra.terms S)) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms S) occurrence =
      (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort,
        ContextualAssignment.instantiate occurrence.valuation (fun _ x => .var x)
          occurrence.close (rules.get occurrence.index).2.conclusion.lhs,
        ContextualAssignment.instantiate occurrence.valuation (fun _ x => .var x)
          occurrence.close (rules.get occurrence.index).2.conclusion.rhs⟩ :
          Judgment (BindingCloneAlgebra.terms S)) := by
  change (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort,
    interpretSchema (BindingCloneAlgebra.terms S) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.lhs,
    interpretSchema (BindingCloneAlgebra.terms S) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.rhs⟩ :
      Judgment (BindingCloneAlgebra.terms S)) = _
  exact congrArg₂ (fun source target =>
    (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort, source, target⟩ :
      Judgment (BindingCloneAlgebra.terms S)))
    (interpretSchema_terms occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.lhs)
    (interpretSchema_terms occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.rhs)

theorem child (occurrence : Instance rules (BindingCloneAlgebra.terms S))
    (position : Fin (rules.get occurrence.index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules (BindingCloneAlgebra.terms S) occurrence position =
      let premise := (rules.get occurrence.index).2.premises.get position
      (⟨premise.binders ++ occurrence.ambient, premise.sort,
        ContextualAssignment.instantiate occurrence.valuation
          (ContextualAssignment.weakenSub (S := S) premise.binders
            (fun _ x => .var x : Sub S occurrence.ambient occurrence.ambient))
          (liftSub (S := S) occurrence.close premise.binders) premise.source,
        ContextualAssignment.instantiate occurrence.valuation
          (ContextualAssignment.weakenSub (S := S) premise.binders
            (fun _ x => .var x : Sub S occurrence.ambient occurrence.ambient))
          (liftSub (S := S) occurrence.close premise.binders) premise.target⟩ :
          Judgment (BindingCloneAlgebra.terms S)) := by
  change interpretPremise (BindingCloneAlgebra.terms S) occurrence.valuation
    occurrence.close ((rules.get occurrence.index).2.premises.get position) = _
  exact interpretPremise_terms occurrence.valuation occurrence.close
    ((rules.get occurrence.index).2.premises.get position)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalRawReadout
