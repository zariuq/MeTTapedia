import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationWholeRepresentative

/-!
# The whole-rule language does not authorize parallel contexts

The generated asynchronous language contains exactly R1. A parallel
configuration representative cannot match its contact-headed left side at
any recursive depth. Concrete located rho steps nevertheless have their
existing multiset frame law. These are distinct operational interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem authored_collection_no_match (sources : List Pattern) (rest : Option String) :
    matchPatternForRuleUsing rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeRedexRewrite
      (.collection .hashBag sources rest) = [] := by
  rw [matchPatternForRuleUsing, baseRhoDeclaration_selected]
  change matchPatternWith (canonicalEquivalent baseRhoDeclaration)
    (.apply costContactConstructorName _) (.collection .hashBag sources rest) = []
  simp only [matchPatternWith]

/-- Increasing contextual fuel cannot invent a missing congruence rule. -/
theorem authored_collection_no_step
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (sources : List Pattern) (rest : Option String) (target : Pattern) :
    ¬ Step (.reflection rhoCIGSLT.costWholeReflectionProfile) base rhoCIGSLT.costWholeLanguage
      (.collection .hashBag sources rest) target := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule membership matched premises rhs =>
      simp only [rhoCIGSLT.costWholeLanguage_rewrites, List.mem_singleton] at membership
      subst_vars
      rw [RuleInterpretation.reflection_matchRule, authored_collection_no_match] at matched
      exact List.not_mem_nil matched

/-- An actual selected R1 step does not supply a grouped authored step. -/
theorem selected_R1_does_not_authorize_frame
    (reversed : Bool) (channel body payload signature tail frame : Pattern) :
    Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage (orderedReceiverSource reversed channel body payload signature tail)
      (receiverContractum body payload tail) ∧
    ∀ target, ¬ Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      rhoCIGSLT.costWholeLanguage
      (.collection .hashBag [orderedReceiverSource reversed channel body payload signature tail, frame] none) target :=
  ⟨ordered_receiver_step reversed channel body payload signature tail,
    authored_collection_no_step _ _ _⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
