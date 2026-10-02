import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SignatureExtensions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayDependencies

/-!
# Actual cumulative decisions and dependent evidence packing

The primitive decisions below are earned from the actual tower head rules,
not supplied Boolean soundness assumptions. Declaration extension reuses the
existing signature layer. A checked lambda packs a value with its own native
identity proof, and application substitutes that exact value into the result
family. Wrong endpoints, missing declarations, unformed lambda evidence, and
self-universe certificates are rejected without refuting valid alternatives.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay
namespace TowerDecisions

def headTarget : Tower.Head → Tower.Head
  | .legacyGround => .sort Tower.zero
  | .sort level => .sort (.succ level)

theorem headTyping_iff (head target : Tower.Head) :
    Tower.HeadTyping head target ↔ target = headTarget head := by
  cases head with
  | legacyGround =>
      constructor
      · intro typing; cases typing; rfl
      · intro same; subst target; exact .legacyGround
  | sort level =>
      constructor
      · intro typing; cases typing; rfl
      · intro same; subst target; exact .sort level

instance (head target : Tower.Head) : Decidable (Tower.HeadTyping head target) :=
  decidable_of_iff (target = headTarget head) (headTyping_iff head target).symm

instance (head : Tower.Head) : Decidable (Tower.IsUniverse head) := by
  cases head with
  | legacyGround => exact .isFalse (by intro impossible; cases impossible)
  | sort level => exact .isTrue (.sort level)

instance (first second result : Tower.Head) : Decidable (Tower.Join first second result) := by
  cases first with
  | legacyGround => exact .isFalse (by intro impossible; cases impossible)
  | sort u =>
      cases second with
      | legacyGround => exact .isFalse (by intro impossible; cases impossible)
      | sort v =>
          cases result with
          | legacyGround => exact .isFalse (by intro impossible; cases impossible)
          | sort w =>
              apply decidable_of_iff (w = .max u v)
              constructor
              · intro same; subst w; exact .sorts u v
              · intro joined; cases joined; rfl

instance : ∀ h u, Decidable (Tower.rules.headTyping h u) :=
  fun h u => inferInstanceAs (Decidable (Tower.HeadTyping h u))

instance : ∀ h, Decidable (Tower.rules.isUniverse h) :=
  fun h => inferInstanceAs (Decidable (Tower.IsUniverse h))

instance : ∀ u v w, Decidable (Tower.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.Join u v w))

instance : ∀ u v, Decidable (Tower.rules.cumulative u v) :=
  fun u v => LevelTower.instDecidableCumulative u v

/-- Declaration extension inherits these same constructive primitive
decisions; it neither reinterprets universe rules nor admits conversions. -/
instance (signature : Declaration.Signature Tower.Head) :
    ∀ h u, Decidable ((Declaration.extendRules Tower.rules signature).headTyping h u) :=
  fun h u => inferInstanceAs (Decidable (Tower.HeadTyping h u))

instance (signature : Declaration.Signature Tower.Head) :
    ∀ h, Decidable ((Declaration.extendRules Tower.rules signature).isUniverse h) :=
  fun h => inferInstanceAs (Decidable (Tower.IsUniverse h))

instance (signature : Declaration.Signature Tower.Head) :
    ∀ u v w, Decidable ((Declaration.extendRules Tower.rules signature).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.Join u v w))

instance (signature : Declaration.Signature Tower.Head) :
    ∀ u v, Decidable ((Declaration.extendRules Tower.rules signature).cumulative u v) :=
  fun u v => LevelTower.instDecidableCumulative u v

end TowerDecisions

namespace DependentPack

private def zero : LevelExpr Nat := .const 0
private def one : LevelExpr Nat := .succ zero
private def pairLevel : LevelExpr Nat := .max zero zero
private def functionLevel : LevelExpr Nat := .max zero pairLevel

def signature : Declaration.Signature Tower.Head :=
  Declaration.Signature.ofList
    [(`A, ⟨sortTm zero, none⟩),
     (`a, ⟨.const `A, none⟩),
     (`b, ⟨.const `A, none⟩)]

abbrev rules := Declaration.extendRules Tower.rules signature

def carrier {n : Nat} : Tower.Tm n := .const `A

def carrierCode {n : Nat} : Code Tower.Head NoConversion n := .const (.sort one) .headType

def valueCode {n : Nat} : Code Tower.Head NoConversion n := .const (.sort zero) carrierCode

/-- The second component records the actual input, not a constant endpoint. -/
def resultFamily : Tower.Tm 1 :=
  .sigma carrier (.id carrier (.var 1) (.var 0))

def functionType : Tower.Tm 0 := .pi carrier resultFamily

def function : Tower.Tm 0 := .lam (.pair (.var 0) (.refl (.var 0)))

def familyCode : Code Tower.Head NoConversion 1 :=
  .sigmaForm (.sort zero) (.sort zero) carrierCode
    (.idForm (.sort zero) carrierCode .var .var)

def functionTypeCode : Code Tower.Head NoConversion 0 :=
  .piForm (.sort zero) (.sort pairLevel) carrierCode familyCode

def bodyCode : Code Tower.Head NoConversion 1 :=
  .pairIntro (.sort pairLevel) familyCode .var (.reflIntro carrier .var)

def functionCode : Code Tower.Head NoConversion 0 :=
  .lamIntro (.sort functionLevel) functionTypeCode bodyCode

def resultType (value : Tower.Tm 0) : Tower.Tm 0 :=
  .sigma carrier (.id carrier (rename wk value) (.var 0))

def applicationCode : Code Tower.Head NoConversion 0 :=
  .appElim carrier resultFamily functionCode valueCode

theorem carrier_formed : check rules noConversionCheck .nil carrier (sortTm zero) carrierCode = true := by
  decide +kernel

theorem function_checked : check rules noConversionCheck .nil function functionType functionCode = true := by
  decide +kernel

theorem actual_application_checked :
    check rules noConversionCheck .nil (.app function (.const `a)) (resultType (.const `a)) applicationCode = true := by
  decide +kernel

theorem other_application_checked :
    check rules noConversionCheck .nil (.app function (.const `b)) (resultType (.const `b)) applicationCode = true := by
  decide +kernel

/-- A valid value at another index does not have the old dependent result type. -/
theorem changed_index_rejected :
    check rules noConversionCheck .nil (.app function (.const `b)) (resultType (.const `a)) applicationCode = false := by
  decide +kernel

theorem actual_application_typed : FormationSensitive.Typing rules .nil
    (.app function (.const `a)) (resultType (.const `a)) :=
  check_sound rules noConversionCheck (noConversionSound rules) applicationCode actual_application_checked

theorem wrong_certificate_rejected :
    check rules noConversionCheck .nil function functionType
      (.lamIntro (.sort functionLevel) .var bodyCode) = false := by
  decide +kernel

theorem rejected_tree_does_not_refute_typing :
    FormationSensitive.Typing rules .nil function functionType :=
  check_sound rules noConversionCheck (noConversionSound rules) functionCode function_checked

theorem missing_declaration_rejected (type : Tower.Tm 0) (code : Code Tower.Head NoConversion 0) :
    check rules noConversionCheck .nil (.const `absent) type code = false := by
  apply missing_constant_rejected rules noConversionCheck (noConversionSound rules)
  decide +kernel

theorem self_universe_certificate_rejected :
    check rules noConversionCheck .nil (sortTm zero) (sortTm zero) .headType = false := by
  decide +kernel

theorem successor_universe_certificate_accepted :
    check rules noConversionCheck .nil (sortTm zero) (sortTm one) .headType = true := by
  decide +kernel

/-- The same actual input returns in both components through directed beta;
the proof component is a native reflexivity term, not a truth-only witness. -/
theorem actual_execution (value : Tower.Tm 0) :
    TelescopeAbstraction.BetaSteps (.app function value) (.pair value (.refl value)) := by
  exact Relation.ReflTransGen.single
    (StepCore.betaPi (root := RootComputation.empty) (headEq := fun _ _ => False)
      (.pair (.var 0) (.refl (.var 0))) value)

#print axioms function_checked
#print axioms actual_application_typed
#print axioms changed_index_rejected
#print axioms missing_declaration_rejected
#print axioms actual_execution

namespace Revision

/-- A new defined program, absent from the older dependent packing proof. -/
def extendedSignature : Declaration.Signature Tower.Head :=
  signature.insert `laterIdentity ⟨.pi carrier carrier, some (.lam (.var 0))⟩

abbrev extendedRules := Declaration.extendRules Tower.rules extendedSignature

theorem same_policy : PolicyAgreement rules extendedRules := ⟨rfl, rfl, rfl, rfl⟩

def applicationNames : List DeclName :=
  applicationCode.declarationRequests rules (.app function (.const `a)) (resultType (.const `a))

theorem application_dependencies_unchanged :
    declarationAgreementCheck rules extendedRules applicationNames = true := by decide +kernel

/-- The same finite certificate, not a newly chosen derivation, is reusable. -/
theorem application_replay_unchanged :
    checkJudgment rules noConversionCheck .nil (.app function (.const `a))
        (resultType (.const `a)) .nil applicationCode =
      checkJudgment extendedRules noConversionCheck .nil (.app function (.const `a))
        (resultType (.const `a)) .nil applicationCode := by
  apply checkJudgment_eq_of_agreement rules extendedRules noConversionCheck noConversionCheck
    same_policy
  · exact (declarationAgreementCheck_iff _ _ _).mp application_dependencies_unchanged
  · intro request _
    exact request.2.elim

theorem application_admitted_after_extension :
    FormationSensitive.Judgment extendedRules .nil (.app function (.const `a))
      (resultType (.const `a)) := by
  apply checkJudgment_sound extendedRules noConversionCheck (noConversionSound extendedRules)
  rw [← application_replay_unchanged]
  exact actual_application_checked

/-- Local reuse also preserves a failed certificate with a wrong dependent
index. It does not turn rejection of that tree into rejection of all trees. -/
theorem changed_index_rejection_reused :
    declarationAgreementCheck rules extendedRules
        (applicationCode.declarationRequests rules (.app function (.const `b))
          (resultType (.const `a))) = true ∧
      checkJudgment rules noConversionCheck .nil (.app function (.const `b))
        (resultType (.const `a)) .nil applicationCode = false ∧
      checkJudgment extendedRules noConversionCheck .nil (.app function (.const `b))
        (resultType (.const `a)) .nil applicationCode = false := by
  decide +kernel

/-- The result's evidence refers to the very value returned in its first field. -/
def outputCode : Code Tower.Head NoConversion 0 :=
  .pairIntro (.sort pairLevel)
    (.sigmaForm (.sort zero) (.sort zero) carrierCode
      (.idForm (.sort zero) carrierCode valueCode .var))
    valueCode (.reflIntro carrier valueCode)

theorem output_checked_after_extension :
    checkJudgment extendedRules noConversionCheck .nil
      (.pair (.const `a) (.refl (.const `a))) (resultType (.const `a)) .nil outputCode = true := by
  decide +kernel

/-- The existing directed computation and both formed endpoints hold in the
extended declaration theory. No operational event is replaced by equality. -/
theorem dependent_execution_after_extension :
    FormationSensitive.Judgment extendedRules .nil (.app function (.const `a))
        (resultType (.const `a)) ∧
      TelescopeAbstraction.BetaSteps (.app function (.const `a))
        (.pair (.const `a) (.refl (.const `a))) ∧
      FormationSensitive.Judgment extendedRules .nil
        (.pair (.const `a) (.refl (.const `a))) (resultType (.const `a)) :=
  ⟨application_admitted_after_extension, actual_execution _,
    checkJudgment_sound extendedRules noConversionCheck (noConversionSound extendedRules)
      output_checked_after_extension⟩

def damagedSignature : Declaration.Signature Tower.Head :=
  signature.insert `A ⟨.const `unformedCarrier, none⟩

abbrev damagedRules := Declaration.extendRules Tower.rules damagedSignature

/-- The displayed constant and its declared type are unchanged. Its formation
dependency has changed, so comparing that first lookup alone would be unsound. -/
theorem hidden_formation_change_rejected :
    rules.constantType `a = damagedRules.constantType `a ∧
      declarationAgreementCheck rules damagedRules
        ((valueCode (n := 0)).declarationRequests rules (.const `a) carrier) = false ∧
      check damagedRules noConversionCheck .nil (.const `a) carrier valueCode = false := by
  decide +kernel

def carrierContext : Tower.Ctx 1 := .snoc .nil carrier
def carrierContextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil (.sort zero) carrierCode

/-- Variable replay reads no declaration, but its ambient context must still
be formed. The whole judgment rejects a hidden context dependency change. -/
theorem ambient_formation_change_rejected :
    (Code.var : Code Tower.Head NoConversion 1).declarationRequests rules (.var 0) carrier = [] ∧
      check rules noConversionCheck carrierContext (.var 0) carrier .var = true ∧
      check damagedRules noConversionCheck carrierContext (.var 0) carrier .var = true ∧
      checkJudgment rules noConversionCheck carrierContext (.var 0) carrier carrierContextCode .var = true ∧
      checkJudgment damagedRules noConversionCheck carrierContext (.var 0) carrier carrierContextCode .var = false ∧
      declarationAgreementCheck rules damagedRules
        (carrierContextCode.declarationRequests rules carrierContext) = false := by
  decide +kernel

def suppliedMissingSignature : Declaration.Signature Tower.Head :=
  signature.insert `absent ⟨carrier, none⟩

abbrev suppliedMissingRules := Declaration.extendRules Tower.rules suppliedMissingSignature

/-- Rejection reuse records absent lookups. Adding a formerly missing name
can change the verdict and must fail the dependency comparison. -/
theorem newly_present_dependency_detected :
    check rules noConversionCheck .nil (.const `absent) carrier valueCode = false ∧
      check suppliedMissingRules noConversionCheck .nil (.const `absent) carrier valueCode = true ∧
      declarationAgreementCheck rules suppliedMissingRules
        ((valueCode (n := 0)).declarationRequests rules (.const `absent) carrier) = false := by
  decide +kernel

#print axioms application_replay_unchanged
#print axioms changed_index_rejection_reused
#print axioms dependent_execution_after_extension
#print axioms hidden_formation_change_rejected
#print axioms ambient_formation_change_rejected
#print axioms newly_present_dependency_detected

end Revision
end DependentPack
end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
