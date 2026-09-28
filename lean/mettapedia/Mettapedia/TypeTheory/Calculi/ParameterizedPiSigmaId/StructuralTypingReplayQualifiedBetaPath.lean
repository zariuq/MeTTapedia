import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayResultQualification

/-!
# Finite qualified root-beta paths with retained certificates

Each contraction is computed from the actual retained typing certificate.
Qualification concerns the source tree at that step; acceptance remains an
independent checker premise. The terminal tree has neutral eliminations.

The bounded search returns a path or `none`. Exhausting fuel, reaching an
unsupported shape, or failing qualification is not evidence of divergence or
ill typing. No normalization theorem is claimed for all accepted terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {n : Nat}

/-- A finite sequence of exact certificate contractions to a qualified
terminal replay tree. The displayed type and context certificate are fixed
throughout; the raw subject and retained typing tree change at each step. -/
inductive QualifiedBetaPath (R : Rules Head) (successor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (displayed : Tm Head n) :
    Tm Head n → Code Head NoConversion n → Tm Head n → Code Head NoConversion n → Prop where
  | terminal (subject : Tm Head n) (code : Code Head NoConversion n)
      (neutral : code.neutralEliminations subject displayed = true) :
      QualifiedBetaPath R successor contextCode displayed subject code subject code
  | contraction {body : Tm Head (n + 1)} {argument : Tm Head n}
      {source result terminalCode : Code Head NoConversion n} {terminal : Tm Head n}
      (qualified : source.resultFormationsNeutral R successor contextCode
        (.app (.lam body) argument) displayed = true)
      (computed : source.contractBeta body argument displayed = some result)
      (rest : QualifiedBetaPath R successor contextCode displayed
        (inst0 argument body) result terminal terminalCode) :
      QualifiedBetaPath R successor contextCode displayed
        (.app (.lam body) argument) source terminal terminalCode

/-- A total bounded search for the finite path fragment. Successful output
is syntactic evidence; `QualifiedBetaPath.terminal_checked` still needs an
accepted source judgment to confer typing authority. -/
def Code.qualifiedBetaPath? (R : Rules Head) (successor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (fuel : Nat)
    (subject displayed : Tm Head n) (code : Code Head NoConversion n) :
    Option { endpoint : Tm Head n × Code Head NoConversion n //
      QualifiedBetaPath R successor contextCode displayed subject code endpoint.1 endpoint.2 } :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if normal : code.neutralEliminations subject displayed = true then
        some ⟨(subject, code), .terminal subject code normal⟩
      else
        match shape : subject with
        | .app (.lam body) argument =>
            if qualified : code.resultFormationsNeutral R successor contextCode subject displayed = true then
              match computed : code.contractBeta body argument displayed with
              | none => none
              | some result => do
                  let rest ← result.qualifiedBetaPath? R successor contextCode fuel
                    (inst0 argument body) displayed
                  pure ⟨rest.val, .contraction (by simpa only [shape] using qualified)
                    computed rest.property⟩
            else none
        | _ => none

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Acceptance propagates through every exact contraction, so the retained
terminal certificate checks against the original displayed type. -/
theorem QualifiedBetaPath.terminal_checked
    {successor : Head → Head} {contextCode : ContextCode Head NoConversion n}
    {displayed sourceTerm terminalTerm : Tm Head n}
    {sourceCode terminalCode : Code Head NoConversion n}
    (path : QualifiedBetaPath R successor contextCode displayed
      sourceTerm sourceCode terminalTerm terminalCode)
    {context : Ctx Head n}
    (accepted : check R noConversionCheck context sourceTerm displayed sourceCode = true) :
    check R noConversionCheck context terminalTerm displayed terminalCode = true := by
  induction path with
  | terminal => exact accepted
  | contraction qualified computed rest ih =>
      exact ih (Code.contractBeta_result_checked R _ _ accepted computed)

omit [DecidableEq Head] [∀ h v, Decidable (R.headTyping h v)]
  [∀ h, Decidable (R.isUniverse h)] [∀ v w z, Decidable (R.join v w z)]
  [∀ v w, Decidable (R.cumulative v w)] in
/-- The endpoint retains the syntactic qualification needed for independent
certificate comparison; successful search does not merely return a term. -/
theorem QualifiedBetaPath.terminal_neutral
    {successor : Head → Head} {contextCode : ContextCode Head NoConversion n}
    {displayed sourceTerm terminalTerm : Tm Head n}
    {sourceCode terminalCode : Code Head NoConversion n}
    (path : QualifiedBetaPath R successor contextCode displayed
      sourceTerm sourceCode terminalTerm terminalCode) :
    terminalCode.neutralEliminations terminalTerm displayed = true := by
  induction path with
  | terminal _ _ neutral => exact neutral
  | contraction _ _ _ ih => exact ih

omit [DecidableEq Head] [∀ h v, Decidable (R.headTyping h v)]
  [∀ h, Decidable (R.isUniverse h)] [∀ v w z, Decidable (R.join v w z)]
  [∀ v w, Decidable (R.cumulative v w)] in
/-- Every successful recorded path is a finite computation of the original
calculus, independently of its typing acceptance. -/
theorem QualifiedBetaPath.reduces
    {successor : Head → Head} {contextCode : ContextCode Head NoConversion n}
    {displayed sourceTerm terminalTerm : Tm Head n}
    {sourceCode terminalCode : Code Head NoConversion n}
    (path : QualifiedBetaPath R successor contextCode displayed
      sourceTerm sourceCode terminalTerm terminalCode) :
    Relation.ReflTransGen (StepCore R.computation R.headEq) sourceTerm terminalTerm := by
  induction path with
  | terminal => exact .refl
  | contraction qualified computed rest ih => exact Relation.ReflTransGen.head (.betaPi _ _) ih

#print axioms Code.qualifiedBetaPath?
#print axioms QualifiedBetaPath.terminal_checked
#print axioms QualifiedBetaPath.terminal_neutral
#print axioms QualifiedBetaPath.reduces

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
