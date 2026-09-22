import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativePrincipalComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedBinderAlignment
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponentsControls

/-!
# Executing converted function and dependent pair introductions

Both parts of the introduction type change. The conversion certificates pass
through a List eliminator rather than preserving the outer constructor at
every intermediate term. The complete entry point admits the source, computes
the reduction, and returns a certificate checked at the original result type.
The second projection's type genuinely depends on the first projection.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ConvertedIntroductionControls

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate
open ContextConversionControls (oldType newType oldFormation newFormation)
open NativeRelatorConversionChecking.Examples (ground)
open NativeJudgmentReplay.Controls (context contextCode proofCode)
open PrincipalComputation

private def zero : Tower.Head := .sort Tower.zero
private def pairLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)

def oldFunctionType : Tower.Tm 1 := .pi oldType (Presentation.rename wk oldType)
def newFunctionType : Tower.Tm 1 := .pi newType (Presentation.rename wk newType)

def oldFunctionFormation : Code 1 :=
  .piForm zero zero oldFormation (NativeJudgmentReplay.rename wk oldFormation)

def newFunctionFormation : Code 1 :=
  .piForm zero zero newFormation (NativeJudgmentReplay.rename wk newFormation)

def functionConversion : Certificate oldFunctionType newFunctionType :=
  NativeParallelReceipt.ComponentControls.listDetour (.var 0)
    BinderAlignment.Controls.functionConversion

def functionCode : Code 1 :=
  .convert oldFunctionType pairLevel
    (.lamIntro pairLevel oldFunctionFormation .var)
    newFunctionFormation functionConversion.code

def argument : Tower.Tm 1 := .refl (.var 0)
def application : Tower.Tm 1 := .app (.lam (.var 0)) argument
def applicationCode : Code 1 :=
  .appElim newType (Presentation.rename wk newType) functionCode proofCode

theorem application_source_checked :
    check context application newType contextCode applicationCode = true := by decide +kernel

/-- Inspect the returned term, independently replay its certificate, and
check the returned directed step. Failure to return a result is a failure. -/
def executionChecks (subject type expected : Tower.Tm 1) (code : Code 1) : Bool :=
  match checkedExecute context contextCode subject type code with
  | none => false
  | some result => decide (result.term = expected) &&
      check context result.term type contextCode result.code &&
      NativeRelatorConversionChecking.checkStep result.step subject result.term

theorem converted_function_computes :
    executionChecks application newType argument applicationCode = true := by decide +kernel

def oldFamily : Tower.Tm 2 := .id (Presentation.rename wk oldType) (.var 0) (.var 0)
def newFamily : Tower.Tm 2 := .id (Presentation.rename wk newType) (.var 0) (.var 0)
def oldPairType : Tower.Tm 1 := .sigma oldType oldFamily
def newPairType : Tower.Tm 1 := .sigma newType newFamily

def oldPairFormation : Code 1 :=
  .sigmaForm zero zero oldFormation
    (.idForm zero (NativeJudgmentReplay.rename wk oldFormation) .var .var)

def newPairFormation : Code 1 :=
  .sigmaForm zero zero newFormation
    (.idForm zero (NativeJudgmentReplay.rename wk newFormation) .var .var)

def familyConversion : Certificate oldFamily newFamily :=
  BinderAlignment.Controls.bodyConversion.id (.refl _) (.refl _)

def pairConversion : Certificate oldPairType newPairType :=
  NativeParallelReceipt.ComponentControls.listDetour (.var 0)
    (BinderAlignment.Controls.binderConversion.sigma familyConversion)

def second : Tower.Tm 1 := .refl argument
def pair : Tower.Tm 1 := .pair argument second
def firstCode : Code 1 := .reflIntro ground .var
def secondCode : Code 1 := .reflIntro oldType firstCode

def pairCode : Code 1 :=
  .convert oldPairType pairLevel
    (.pairIntro pairLevel oldPairFormation firstCode secondCode)
    newPairFormation pairConversion.code

def firstProjectionCode : Code 1 := .fstElim newFamily pairCode
def secondProjectionCode : Code 1 := .sndElim newType newFamily pairCode
def secondProjectionType : Tower.Tm 1 := inst0 (.fst pair) newFamily

theorem converted_pair_source_checked :
    check context pair newPairType contextCode pairCode = true := by decide +kernel

theorem first_projection_source_checked :
    check context (.fst pair) newType contextCode firstProjectionCode = true := by decide +kernel

theorem second_projection_source_checked :
    check context (.snd pair) secondProjectionType contextCode secondProjectionCode = true := by
  decide +kernel

theorem converted_first_projection_computes :
    executionChecks (.fst pair) newType argument firstProjectionCode = true := by decide +kernel

theorem converted_dependent_second_projection_computes :
    executionChecks (.snd pair) secondProjectionType second secondProjectionCode = true := by
  decide +kernel

theorem dependent_projection_type_is_not_reduced :
    secondProjectionType ≠ inst0 argument newFamily := by decide +kernel

/-- The old second-component certificate does not prove the requested type.
The executor must construct the domain and dependent-index conversions. -/
theorem unchanged_second_certificate_rejected :
    check context second secondProjectionType contextCode secondCode = false := by decide +kernel

def alteredOutputRejected : Bool :=
  match checkedExecute context contextCode (.snd pair) secondProjectionType secondProjectionCode with
  | none => false
  | some result => !(check context (.var 0) secondProjectionType contextCode result.code)

theorem altered_output_rejected : alteredOutputRejected = true := by decide +kernel

theorem mismatched_inner_conversion_rejected :
    (checkedExecute context contextCode application newType
      (.appElim newType (Presentation.rename wk newType)
        (.convert oldFunctionType pairLevel
          (.lamIntro pairLevel oldFunctionFormation .var)
          newFunctionFormation (.refl oldFunctionType)) proofCode)).isNone = true := by
  decide +kernel

theorem unformed_inner_destination_rejected :
    (checkedExecute context contextCode (.snd pair) secondProjectionType
      (.sndElim newType newFamily
        (.convert oldPairType pairLevel
          (.pairIntro pairLevel oldPairFormation firstCode secondCode)
          .var pairConversion.code))).isNone = true := by decide +kernel

#print axioms application_source_checked
#print axioms converted_function_computes
#print axioms converted_pair_source_checked
#print axioms first_projection_source_checked
#print axioms second_projection_source_checked
#print axioms converted_first_projection_computes
#print axioms converted_dependent_second_projection_computes
#print axioms dependent_projection_type_is_not_reduced
#print axioms unchanged_second_certificate_rejected
#print axioms altered_output_rejected
#print axioms mismatched_inner_conversion_rejected
#print axioms unformed_inner_destination_rejected

#eval (executionChecks application newType argument applicationCode,
  executionChecks (.fst pair) newType argument firstProjectionCode,
  executionChecks (.snd pair) secondProjectionType second secondProjectionCode,
  alteredOutputRejected)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ConvertedIntroductionControls
