import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedHOLProofRules

/-!
# Predicate equality on arbitrary small native carriers

Convertible, independently typed operands admit the ordinary identity
function as predicate transport. The carrier may be an actual native List
type. This installs no equality decoder and does not infer an operand's
typing or its conversion from the desired equation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveMixedLeibnizRules

open Presentation FormationSensitiveHOLProofListIntegration
open FormationSensitiveHOLProofFamily (proof universalProposition)
open FormationSensitiveHOLUniformList (rawImp)
open FormationSensitiveMixedHOLProofRules

variable {n : Nat}

def predicateType (domain : Tower.Tm n) : Tower.Tm n :=
  .pi domain (.const `HOLUniformList.prop)

def atPredicate (value : Tower.Tm n) : Tower.Tm (n + 1) :=
  .app (.var 0) (rename wk value)

def eqFormula (domain left right : Tower.Tm n) : Tower.Tm n :=
  universalProposition (predicateType domain)
    (.lam (rawImp (atPredicate left) (atPredicate right)))

theorem predicateType_formed {context : Tower.Ctx n} {domain : Tower.Tm n}
    (formed : Typing context domain (sortTm Tower.zero)) :
    Typing context (predicateType domain) (sortTm Tower.zero) :=
  pi_zero formed (proposition_formed _)

theorem atPredicate_typed {context : Tower.Ctx n} {domain value : Tower.Tm n}
    (typed : Typing context value domain) :
    Typing (.snoc context (predicateType domain)) (atPredicate value)
      (.const `HOLUniformList.prop) := by
  have argument := typed.weaken (extension := predicateType domain)
  have predicate : Typing (.snoc context (predicateType domain)) (.var 0)
      (.pi (rename wk domain) (.const `HOLUniformList.prop)) := .var 0
  exact FormationSensitive.Typing.appElim predicate argument

theorem eqFormula_typed {context : Tower.Ctx n} {domain left right : Tower.Tm n}
    (formed : Typing context domain (sortTm Tower.zero))
    (leftTyped : Typing context left domain) (rightTyped : Typing context right domain) :
    Typing context (eqFormula domain left right) (.const `HOLUniformList.prop) :=
  universal_lambda_proposition (predicateType_formed formed)
    (implication_proposition (atPredicate_typed leftTyped) (atPredicate_typed rightTyped))

/-- Conversion is independently supplied; the resulting proof is two native
lambdas, and its body is the original input witness. -/
theorem equality_of_conversion {context : Tower.Ctx n} {domain left right : Tower.Tm n}
    (formed : Typing context domain (sortTm Tower.zero))
    (leftTyped : Typing context left domain) (rightTyped : Typing context right domain)
    (conversion : Conv rules.headEq left right rules.computation) :
    Typing context (.lam (.lam (.var 0))) (proof (eqFormula domain left right)) := by
  have lp := atPredicate_typed leftTyped
  have rp := atPredicate_typed rightTyped
  apply universal_intro (predicateType_formed formed) (implication_proposition lp rp)
  apply implication_intro lp rp
  have comparison : Conv rules.headEq (proof (atPredicate left))
      (proof (atPredicate right)) rules.computation :=
    Conv.congApp (.refl _) (Conv.congApp (.refl _) (conversion.renameTerms wk))
  exact .conv (.var 0) (proof_formed rp).weaken (.sort Tower.zero)
    (comparison.renameTerms wk)

theorem predicate_application {context : Tower.Ctx n} {domain predicate value : Tower.Tm n}
    (predicateTyped : Typing context predicate (predicateType domain))
    (valueTyped : Typing context value domain) :
    Typing context (.app predicate value) (.const `HOLUniformList.prop) :=
  FormationSensitive.Typing.appElim predicateTyped valueTyped

theorem specialize {context : Tower.Ctx n} {domain left right equality predicate : Tower.Tm n}
    (formed : Typing context domain (sortTm Tower.zero))
    (leftTyped : Typing context left domain) (rightTyped : Typing context right domain)
    (equalityTyped : Typing context equality (proof (eqFormula domain left right)))
    (predicateTyped : Typing context predicate (predicateType domain)) :
    Typing context (.app equality predicate)
      (proof (rawImp (.app predicate left) (.app predicate right))) := by
  have instantiated := universal_elim (predicateType_formed formed)
    (implication_proposition (atPredicate_typed leftTyped) (atPredicate_typed rightTyped))
    equalityTyped predicateTyped
  have instantiate (value : Tower.Tm n) :
      inst0 predicate (atPredicate value) = .app predicate value := by
    change Tm.app predicate (inst0 predicate (rename wk value)) = _
    rw [inst0_rename_wk]
  have body : inst0 predicate (rawImp (atPredicate left) (atPredicate right)) =
      rawImp (.app predicate left) (.app predicate right) := by
    change rawImp (inst0 predicate (atPredicate left))
      (inst0 predicate (atPredicate right)) = _
    rw [instantiate, instantiate]
  simpa only [body] using instantiated

theorem elimination {context : Tower.Ctx n}
    {domain left right equality predicate input : Tower.Tm n}
    (formed : Typing context domain (sortTm Tower.zero))
    (leftTyped : Typing context left domain) (rightTyped : Typing context right domain)
    (equalityTyped : Typing context equality (proof (eqFormula domain left right)))
    (predicateTyped : Typing context predicate (predicateType domain))
    (inputTyped : Typing context input (proof (.app predicate left))) :
    Typing context (.app (.app equality predicate) input) (proof (.app predicate right)) :=
  implication_elim (predicate_application predicateTyped leftTyped)
    (predicate_application predicateTyped rightTyped)
    (specialize formed leftTyped rightTyped equalityTyped predicateTyped) inputTyped

theorem conversion_transport_returns_input (predicate input : Tower.Tm n) :
    Conv rules.headEq (.app (.app (.lam (.lam (.var 0))) predicate) input)
      input rules.computation := by
  have first : Conv rules.headEq (.app (.lam (.lam (.var 0))) predicate)
      (.lam (.var 0)) rules.computation := .rel _ _ (.betaPi (.lam (.var 0)) predicate)
  exact .trans _ _ _ (Conv.congApp first (.refl _))
    (.rel _ _ (.betaPi (.var 0) input))

#print axioms predicateType_formed
#print axioms eqFormula_typed
#print axioms equality_of_conversion
#print axioms specialize
#print axioms elimination
#print axioms conversion_transport_returns_input

end FormationSensitiveMixedLeibnizRules
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
