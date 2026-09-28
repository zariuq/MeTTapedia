import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayNeutral

/-!
# Neutral formation evidence throughout a replay tree

The qualification examines the actual extracted result formation at every
typing premise. Subjects need not be neutral: applications of lambdas,
computed function arguments, pairs and type values are permitted. Each
binder uses the context certificate assembled from its actual domain child.

This is finite syntactic evidence, separate from acceptance by `check`.
It neither asserts semantic membership nor establishes qualification of
every accepted certificate. In particular, a judgment whose extracted
identity result formation has beta-bearing endpoints need not pass the test.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {n : Nat}

/-- Inspect the particular formation certificate extracted from this tree.
Failure includes unsuccessful extraction; it does not reject the typing
judgment or assert that another formation cannot be supplied. -/
def Code.resultFormationNeutral (universeSuccessor : Head → Head)
    (code : Code Head NoConversion n) (contextCode : ContextCode Head NoConversion n)
    (subject type : Tm Head n) : Bool :=
  match code.resultFormation noConversionRename noConversionSubstitute
      universeSuccessor contextCode subject type with
  | none => false
  | some (level, formation) => formation.neutralEliminations type (.head level)

/-- Every actual typing premise has qualified extracted formation evidence.
The recursive calls follow the original finite tree, not its beta reducts.
Constant formation is read at its declared closed type. -/
def Code.resultFormationsNeutral (R : Rules Head) (universeSuccessor : Head → Head) :
    {n : Nat} → Code Head NoConversion n → ContextCode Head NoConversion n →
      Tm Head n → Tm Head n → Bool
  | _, code, contextCode, subject, type =>
      code.resultFormationNeutral universeSuccessor contextCode subject type &&
        match code with
        | .headType | .var => true
        | .const level formation =>
            match subject with
            | .const name =>
                match R.constantType name with
                | none => false
                | some declared =>
                    formation.resultFormationsNeutral R universeSuccessor .nil declared (.head level)
            | _ => false
        | .piForm domainLevel bodyLevel domain body =>
            match subject, type with
            | .pi A B, .head _ =>
                domain.resultFormationsNeutral R universeSuccessor contextCode A (.head domainLevel) &&
                  body.resultFormationsNeutral R universeSuccessor
                    (.snoc contextCode domainLevel domain) B (.head bodyLevel)
            | _, _ => false
        | .sigmaForm domainLevel bodyLevel domain body =>
            match subject, type with
            | .sigma A B, .head _ =>
                domain.resultFormationsNeutral R universeSuccessor contextCode A (.head domainLevel) &&
                  body.resultFormationsNeutral R universeSuccessor
                    (.snoc contextCode domainLevel domain) B (.head bodyLevel)
            | _, _ => false
        | .lamIntro level formation body =>
            match subject, type with
            | .lam term, .pi A B =>
                formation.resultFormationsNeutral R universeSuccessor contextCode (.pi A B) (.head level) &&
                  match formation.piFormation with
                  | none => false
                  | some (domainLevel, _, domain, _) =>
                      body.resultFormationsNeutral R universeSuccessor
                        (.snoc contextCode domainLevel domain) term B
            | _, _ => false
        | .appElim A B function argument =>
            match subject with
            | .app f a =>
                function.resultFormationsNeutral R universeSuccessor contextCode f (.pi A B) &&
                  argument.resultFormationsNeutral R universeSuccessor contextCode a A
            | _ => false
        | .pairIntro level formation first second =>
            match subject, type with
            | .pair a b, .sigma A B =>
                formation.resultFormationsNeutral R universeSuccessor contextCode (.sigma A B) (.head level) &&
                  first.resultFormationsNeutral R universeSuccessor contextCode a A &&
                    second.resultFormationsNeutral R universeSuccessor contextCode b (inst0 a B)
            | _, _ => false
        | .fstElim B pair =>
            match subject with
            | .fst p => pair.resultFormationsNeutral R universeSuccessor contextCode p (.sigma type B)
            | _ => false
        | .sndElim A B pair =>
            match subject with
            | .snd p => pair.resultFormationsNeutral R universeSuccessor contextCode p (.sigma A B)
            | _ => false
        | .idForm level formation left right =>
            match subject, type with
            | .id A a b, .head _ =>
                formation.resultFormationsNeutral R universeSuccessor contextCode A (.head level) &&
                  left.resultFormationsNeutral R universeSuccessor contextCode a A &&
                    right.resultFormationsNeutral R universeSuccessor contextCode b A
            | _, _ => false
        | .reflIntro A term =>
            match subject with
            | .refl a => term.resultFormationsNeutral R universeSuccessor contextCode a A
            | _ => false
        | .cumul lower source =>
            match type with
            | .head _ => source.resultFormationsNeutral R universeSuccessor contextCode subject (.head lower)
            | _ => false
        | .convert _ _ _ _ impossible => nomatch impossible

theorem Code.resultFormationNeutral_iff (universeSuccessor : Head → Head)
    (code : Code Head NoConversion n) (contextCode : ContextCode Head NoConversion n)
    (subject type : Tm Head n) :
    code.resultFormationNeutral universeSuccessor contextCode subject type = true ↔
      ∃ level formation,
        code.resultFormation noConversionRename noConversionSubstitute universeSuccessor
          contextCode subject type = some (level, formation) ∧
        formation.neutralEliminations type (.head level) = true := by
  unfold Code.resultFormationNeutral
  split
  · simp_all
  · rename_i level formation computed
    constructor
    · intro qualified
      exact ⟨level, formation, computed, qualified⟩
    · rintro ⟨otherLevel, otherFormation, otherComputed, qualified⟩
      rw [computed] at otherComputed
      cases Option.some.inj otherComputed
      exact qualified

/-- Recursive qualification includes qualification at the root judgment. -/
theorem Code.resultFormationsNeutral_root (R : Rules Head) (universeSuccessor : Head → Head)
    (code : Code Head NoConversion n) (contextCode : ContextCode Head NoConversion n)
    (subject type : Tm Head n)
    (qualified : code.resultFormationsNeutral R universeSuccessor contextCode subject type = true) :
    code.resultFormationNeutral universeSuccessor contextCode subject type = true := by
  cases code with
  | convert _ _ _ _ impossible => exact nomatch impossible
  | _ => exact (Bool.and_eq_true_iff.mp qualified).1

/-- Use the actual extraction receipt to obtain its neutral qualification. -/
theorem Code.resultFormationNeutral_of_eq (universeSuccessor : Head → Head)
    (code : Code Head NoConversion n) (contextCode : ContextCode Head NoConversion n)
    (subject type : Tm Head n) (level : Head) (formation : Code Head NoConversion n)
    (qualified : code.resultFormationNeutral universeSuccessor contextCode subject type = true)
    (computed : code.resultFormation noConversionRename noConversionSubstitute universeSuccessor
      contextCode subject type = some (level, formation)) :
    formation.neutralEliminations type (.head level) = true := by
  simpa only [Code.resultFormationNeutral, computed] using qualified

/-- The root extraction receipt and its qualification are available without
assuming that the source checker accepts. -/
theorem Code.resultFormationsNeutral_result (R : Rules Head) (universeSuccessor : Head → Head)
    (code : Code Head NoConversion n) (contextCode : ContextCode Head NoConversion n)
    (subject type : Tm Head n)
    (qualified : code.resultFormationsNeutral R universeSuccessor contextCode subject type = true) :
    ∃ level formation,
      code.resultFormation noConversionRename noConversionSubstitute universeSuccessor
        contextCode subject type = some (level, formation) ∧
      formation.neutralEliminations type (.head level) = true := by
  apply (Code.resultFormationNeutral_iff universeSuccessor code contextCode subject type).mp
  exact code.resultFormationsNeutral_root R universeSuccessor contextCode subject type qualified

/-- Lambda bodies are qualified under the context built from the extracted
domain child, not an independently chosen context certificate. -/
theorem Code.resultFormationsNeutral_lamIntro
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A : Tm Head n) (B term : Tm Head (n + 1))
    (level domainLevel bodyLevel : Head)
    (formation domain : Code Head NoConversion n)
    (body codomain : Code Head NoConversion (n + 1))
    (parts : formation.piFormation = some (domainLevel, bodyLevel, domain, codomain))
    (qualified : (Code.lamIntro level formation body).resultFormationsNeutral
      R universeSuccessor contextCode (.lam term) (.pi A B) = true) :
    formation.resultFormationsNeutral R universeSuccessor contextCode (.pi A B) (.head level) = true ∧
      body.resultFormationsNeutral R universeSuccessor
        (.snoc contextCode domainLevel domain) term B = true := by
  exact Bool.and_eq_true_iff.mp (by
    simpa only [parts] using (Bool.and_eq_true_iff.mp qualified).2)

theorem Code.resultFormationsNeutral_piForm
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A : Tm Head n) (B : Tm Head (n + 1)) (domainLevel bodyLevel level : Head)
    (domain : Code Head NoConversion n) (body : Code Head NoConversion (n + 1))
    (qualified : (Code.piForm domainLevel bodyLevel domain body).resultFormationsNeutral
      R universeSuccessor contextCode (.pi A B) (.head level) = true) :
    domain.resultFormationsNeutral R universeSuccessor contextCode A (.head domainLevel) = true ∧
      body.resultFormationsNeutral R universeSuccessor
        (.snoc contextCode domainLevel domain) B (.head bodyLevel) = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2

theorem Code.resultFormationsNeutral_sigmaForm
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A : Tm Head n) (B : Tm Head (n + 1)) (domainLevel bodyLevel level : Head)
    (domain : Code Head NoConversion n) (body : Code Head NoConversion (n + 1))
    (qualified : (Code.sigmaForm domainLevel bodyLevel domain body).resultFormationsNeutral
      R universeSuccessor contextCode (.sigma A B) (.head level) = true) :
    domain.resultFormationsNeutral R universeSuccessor contextCode A (.head domainLevel) = true ∧
      body.resultFormationsNeutral R universeSuccessor
        (.snoc contextCode domainLevel domain) B (.head bodyLevel) = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2

theorem Code.resultFormationsNeutral_appElim
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A f a type : Tm Head n) (B : Tm Head (n + 1))
    (function argument : Code Head NoConversion n)
    (qualified : (Code.appElim A B function argument).resultFormationsNeutral
      R universeSuccessor contextCode (.app f a) type = true) :
    function.resultFormationsNeutral R universeSuccessor contextCode f (.pi A B) = true ∧
      argument.resultFormationsNeutral R universeSuccessor contextCode a A = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2

theorem Code.resultFormationsNeutral_pairIntro
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A a b : Tm Head n) (B : Tm Head (n + 1)) (level : Head)
    (formation first second : Code Head NoConversion n)
    (qualified : (Code.pairIntro level formation first second).resultFormationsNeutral
      R universeSuccessor contextCode (.pair a b) (.sigma A B) = true) :
    formation.resultFormationsNeutral R universeSuccessor contextCode (.sigma A B) (.head level) = true ∧
      first.resultFormationsNeutral R universeSuccessor contextCode a A = true ∧
        second.resultFormationsNeutral R universeSuccessor contextCode b (inst0 a B) = true := by
  have premises := (Bool.and_eq_true_iff.mp qualified).2
  obtain ⟨prior, second⟩ := Bool.and_eq_true_iff.mp premises
  obtain ⟨formation, first⟩ := Bool.and_eq_true_iff.mp prior
  exact ⟨formation, first, second⟩

theorem Code.resultFormationsNeutral_idForm
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n)
    (A a b : Tm Head n) (level resultLevel : Head)
    (formation left right : Code Head NoConversion n)
    (qualified : (Code.idForm level formation left right).resultFormationsNeutral
      R universeSuccessor contextCode (.id A a b) (.head resultLevel) = true) :
    formation.resultFormationsNeutral R universeSuccessor contextCode A (.head level) = true ∧
      left.resultFormationsNeutral R universeSuccessor contextCode a A = true ∧
        right.resultFormationsNeutral R universeSuccessor contextCode b A = true := by
  have premises := (Bool.and_eq_true_iff.mp qualified).2
  obtain ⟨prior, right⟩ := Bool.and_eq_true_iff.mp premises
  obtain ⟨formation, left⟩ := Bool.and_eq_true_iff.mp prior
  exact ⟨formation, left, right⟩

theorem Code.resultFormationsNeutral_reflIntro
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (A a type : Tm Head n)
    (term : Code Head NoConversion n)
    (qualified : (Code.reflIntro A term).resultFormationsNeutral
      R universeSuccessor contextCode (.refl a) type = true) :
    term.resultFormationsNeutral R universeSuccessor contextCode a A = true :=
  (Bool.and_eq_true_iff.mp qualified).2

theorem Code.resultFormationsNeutral_cumul
    (R : Rules Head) (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (subject : Tm Head n)
    (lower upper : Head) (source : Code Head NoConversion n)
    (qualified : (Code.cumul lower source).resultFormationsNeutral
      R universeSuccessor contextCode subject (.head upper) = true) :
    source.resultFormationsNeutral R universeSuccessor contextCode subject (.head lower) = true :=
  (Bool.and_eq_true_iff.mp qualified).2

namespace ResultQualificationControls

private def identityType (head : Head) {n : Nat} : Tm Head n := .pi (.head head) (.head head)

private def identityFormation (level : Head) {n : Nat} : Code Head NoConversion n :=
  .piForm level level .headType .headType

private def returnedFunction : Tm Head 0 :=
  .app (.lam (.var 0)) (.lam (.var 0))

private def returnedFunctionCode (head level joined : Head) : Code Head NoConversion 0 :=
  .appElim (identityType head) (identityType head)
    (.lamIntro joined
      (.piForm joined joined (identityFormation level) (identityFormation level)) .var)
    (.lamIntro joined (identityFormation level) .var)

/-- Computation returning an actual function is included; the source does
not satisfy the earlier neutral-elimination qualifier. This statement is
about qualification, not acceptance under arbitrary head rules. -/
theorem computed_function_qualified (R : Rules Head) (universeSuccessor : Head → Head)
    (head level joined : Head) :
    (returnedFunctionCode head level joined).resultFormationsNeutral R universeSuccessor .nil
      returnedFunction (identityType head) = true ∧
      (returnedFunctionCode head level joined).neutralEliminations
        returnedFunction (identityType head) = false := by
  exact ⟨rfl, rfl⟩

/-- The computed endpoint in the extracted identity formation is not
silently declared coherent merely because reflexivity's value is empty. -/
theorem computed_reflexivity_not_qualified (R : Rules Head) (universeSuccessor : Head → Head)
    (head level joined : Head) :
    (Code.reflIntro (identityType head) (returnedFunctionCode head level joined)).resultFormationsNeutral
      R universeSuccessor .nil (.refl returnedFunction)
        (.id (identityType head) returnedFunction returnedFunction) = false := rfl

end ResultQualificationControls

#print axioms Code.resultFormationNeutral_iff
#print axioms Code.resultFormationsNeutral_root
#print axioms Code.resultFormationNeutral_of_eq
#print axioms Code.resultFormationsNeutral_result
#print axioms Code.resultFormationsNeutral_lamIntro
#print axioms Code.resultFormationsNeutral_appElim
#print axioms Code.resultFormationsNeutral_pairIntro
#print axioms Code.resultFormationsNeutral_idForm
#print axioms ResultQualificationControls.computed_function_qualified
#print axioms ResultQualificationControls.computed_reflexivity_not_qualified

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
