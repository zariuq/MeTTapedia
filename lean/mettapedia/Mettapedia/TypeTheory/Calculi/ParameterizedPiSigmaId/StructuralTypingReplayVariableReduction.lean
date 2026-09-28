import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayNeutral
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayFormation

/-!
# Finite beta computations returning variables

`BetaToVariable` records root contractions of the actual retained certificate,
including computations of the arguments used by those contractions. It is
syntactic evidence, not an alternative typing authority: source acceptance is
a separate premise of preservation. The terminal certificate is retained,
including cumulative wrappers.

Every lambda's extracted domain formation must satisfy the existing
neutral-elimination qualification. There is no bound on nesting, but there
is also no assertion that every checked term has such a computation. In
particular this relation is not a normalization theorem for the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {n : Nat}

/-- A finite computation to a variable, with recursively supplied argument
computations and exact certificate-instantiation receipts. No constructor
contains a semantic membership or certificate-coherence premise. -/
inductive BetaToVariable : Tm Head n → Tm Head n → Code Head NoConversion n →
    Fin n → Code Head NoConversion n → Prop where
  | var (index : Fin n) (type : Tm Head n) (code : Code Head NoConversion n) :
      BetaToVariable (.var index) type code index code
  | cumulative {subject : Tm Head n} {lower upper : Head}
      {source terminal : Code Head NoConversion n} {index : Fin n}
      (prior : BetaToVariable subject (.head lower) source index terminal) :
      BetaToVariable subject (.head upper) (.cumul lower source) index (.cumul lower terminal)
  | beta {A argument : Tm Head n} {B body : Tm Head (n + 1)}
      {level domainLevel bodyLevel : Head}
      {formation domainCode argumentCode argumentTerminal terminal : Code Head NoConversion n}
      {codomainCode bodyCode : Code Head NoConversion (n + 1)}
      {argumentIndex index : Fin n}
      (parts : formation.piFormation = some (domainLevel, bodyLevel, domainCode, codomainCode))
      (qualified : domainCode.neutralEliminations A (.head domainLevel) = true)
      (argumentTrace : BetaToVariable argument A argumentCode argumentIndex argumentTerminal)
      (reductTrace : BetaToVariable (inst0 argument body) (inst0 argument B)
        (Code.instantiate noConversionRename noConversionSubstitute body B argument bodyCode argumentCode)
        index terminal) :
      BetaToVariable (.app (.lam body) argument) (inst0 argument B)
        (.appElim A B (.lamIntro level formation bodyCode) argumentCode) index terminal

/-- A bounded certificate-producing search for the recorded computation
fragment. Exhausting fuel or encountering an unsupported shape returns
`none`, not evidence that the source is ill typed or divergent. Success does
not authorize the source either: terminal checking still needs its original
acceptance. Argument computations are used for domain admission, not as a
specification of evaluator order or runtime cost. -/
def Code.betaToVariable? [DecidableEq Head] (fuel : Nat) (subject type : Tm Head n)
    (code : Code Head NoConversion n) :
    Option { result : Fin n × Code Head NoConversion n //
      BetaToVariable subject type code result.1 result.2 } :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match subject, type, code with
      | .var index, type, code => some ⟨(index, code), .var index type code⟩
      | subject, .head upper, .cumul lower source => do
          let result ← source.betaToVariable? fuel subject (.head lower)
          pure ⟨(result.val.1, .cumul lower result.val.2), .cumulative result.property⟩
      | .app (.lam body) argument, type, .appElim A B (.lamIntro level formation bodyCode) argumentCode =>
          if sameType : type = inst0 argument B then
            match parts : formation.piFormation with
            | none => none
            | some (domainLevel, _, domainCode, _) =>
                if qualified : domainCode.neutralEliminations A (.head domainLevel) = true then do
                  let arg ← argumentCode.betaToVariable? fuel argument A
                  let continueSearch (_ : Unit) :
                      Option { result : Fin n × Code Head NoConversion n //
                        BetaToVariable (.app (.lam body) argument) type
                          (.appElim A B (.lamIntro level formation bodyCode) argumentCode)
                          result.1 result.2 } := do
                    let result ← (Code.instantiate noConversionRename noConversionSubstitute
                      body B argument bodyCode argumentCode).betaToVariable?
                      fuel (inst0 argument body) (inst0 argument B)
                    pure ⟨result.val, by
                      subst type
                      exact .beta parts qualified arg.property result.property⟩
                  match bodyShape : bodyCode with
                  | .var =>
                      if identity : body = .var 0 ∧ inst0 argument B = A then
                        pure ⟨arg.val, by
                          obtain ⟨rfl, codomain⟩ := identity
                          subst type
                          rw [bodyShape]
                          apply BetaToVariable.beta parts qualified arg.property
                          change BetaToVariable argument (inst0 argument B) argumentCode _ _
                          rw [codomain]
                          exact arg.property⟩
                      else continueSearch ()
                  | _ => continueSearch ()
                else none
          else none
      | _, _, _ => none

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Every terminal certificate is checked by the existing checker at the
original displayed type. The trace alone does not authorize either endpoint. -/
theorem BetaToVariable.terminal_checked
    {subject type : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : BetaToVariable subject type source index terminal) {context : Ctx Head n}
    (accepted : check R noConversionCheck context subject type source = true) :
    check R noConversionCheck context (.var index) type terminal = true := by
  induction trace with
  | var => exact accepted
  | cumulative prior ih =>
      simp only [check, Bool.and_eq_true] at accepted ⊢
      exact ⟨ih accepted.1, accepted.2⟩
  | beta parts qualified argumentTrace reductTrace ihArgument ihReduct =>
      apply ihReduct
      exact Code.contractBeta_result_checked R _ _ accepted rfl

omit [DecidableEq Head] [∀ h v, Decidable (R.headTyping h v)]
  [∀ h, Decidable (R.isUniverse h)] [∀ v w z, Decidable (R.join v w z)]
  [∀ v w, Decidable (R.cumulative v w)] in
/-- The recorded result is also reached by the calculus's existing raw
operational relation. Cumulative wrappers contribute no operational step. -/
theorem BetaToVariable.reduces
    {subject type : Tm Head n} {source terminal : Code Head NoConversion n} {index : Fin n}
    (trace : BetaToVariable subject type source index terminal) :
    Relation.ReflTransGen (StepCore R.computation R.headEq) subject (.var index) := by
  induction trace with
  | var => exact .refl
  | cumulative prior ih => exact ih
  | beta parts qualified argumentTrace reductTrace ihArgument ihReduct =>
      exact Relation.ReflTransGen.head (.betaPi _ _) ihReduct

#print axioms BetaToVariable.terminal_checked
#print axioms BetaToVariable.reduces
#print axioms Code.betaToVariable?

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
