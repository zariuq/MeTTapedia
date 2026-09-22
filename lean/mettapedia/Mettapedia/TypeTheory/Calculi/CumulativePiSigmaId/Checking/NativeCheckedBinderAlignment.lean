import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponents
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayContextConversion

/-!
# Checked dependent bodies across computed component conversions

Function and pair conversion certificates supply both the binder conversion
and the body-type conversion. Existing checked context transport applies the
first; an explicit result cast applies the second. Both target formations are
checked independently. No inference from raw convertibility to formation is
used, and the body syntax is unchanged.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BinderAlignment

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate StructuralTypingReplay

def body {n : Nat} {old new : Tower.Tm n} {oldType newType : Tower.Tm (n + 1)}
    (components : Certificate old new × Certificate oldType newType)
    (oldLevel targetLevel : Tower.Head) (oldFormation : Code n)
    (newTypeFormation : Code (n + 1)) (subject : Tower.Tm (n + 1))
    (source : Code (n + 1)) : Code (n + 1) :=
  .convert oldType targetLevel
    (convertNewest new oldLevel oldFormation components.1.code subject oldType source)
    newTypeFormation components.2.code

theorem body_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old new : Tower.Tm n} {oldType newType subject : Tower.Tm (n + 1)}
    (components : Certificate old new × Certificate oldType newType)
    {oldLevel newLevel targetLevel : Tower.Head} {oldFormation newFormation : Code n}
    {source newTypeFormation : Code (n + 1)}
    (accepted : check (.snoc context old) subject oldType
      (.snoc contextCode oldLevel oldFormation) source = true)
    (newFormed : check context new (.head newLevel) contextCode newFormation = true)
    (newUniverse : IntrinsicRelator.rules.isUniverse newLevel)
    (newTypeFormed : check (.snoc context new) newType (.head targetLevel)
      (.snoc contextCode newLevel newFormation) newTypeFormation = true)
    (targetUniverse : IntrinsicRelator.rules.isUniverse targetLevel) :
    check (.snoc context new) subject newType (.snoc contextCode newLevel newFormation)
      (body components oldLevel targetLevel oldFormation newTypeFormation subject source) = true := by
  have transported := check_convertNewest accepted newFormed newUniverse components.1.checked
  simp only [check, checkJudgment, Bool.and_eq_true] at transported newTypeFormed
  simp only [body, check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨transported.1, ⟨⟨⟨targetUniverse, transported.2⟩, newTypeFormed.2⟩,
    components.2.checked⟩⟩

def piBody {n : Nat} {old new : Tower.Tm n} {oldType newType : Tower.Tm (n + 1)}
    (conversion : Certificate (.pi old oldType) (.pi new newType))
    (oldLevel targetLevel : Tower.Head) (oldFormation : Code n)
    (newTypeFormation : Code (n + 1)) (subject : Tower.Tm (n + 1))
    (source : Code (n + 1)) : Code (n + 1) :=
  body (NativeParallelReceipt.piComponents conversion) oldLevel targetLevel
    oldFormation newTypeFormation subject source

def sigmaBody {n : Nat} {old new : Tower.Tm n} {oldType newType : Tower.Tm (n + 1)}
    (conversion : Certificate (.sigma old oldType) (.sigma new newType))
    (oldLevel targetLevel : Tower.Head) (oldFormation : Code n)
    (newTypeFormation : Code (n + 1)) (subject : Tower.Tm (n + 1))
    (source : Code (n + 1)) : Code (n + 1) :=
  body (NativeParallelReceipt.sigmaComponents conversion) oldLevel targetLevel
    oldFormation newTypeFormation subject source

namespace Controls

open ContextConversionControls

def binderConversion : Certificate oldType newType :=
  ⟨NativeRelatorConversionChecking.Examples.identityExpansionCode (.var 0),
    NativeRelatorConversionChecking.Examples.identity_expansion_checked _⟩

def bodyConversion : Certificate (Presentation.rename wk oldType) (Presentation.rename wk newType) :=
  ⟨NativeRelatorConversionChecking.rename wk binderConversion.code,
    NativeRelatorConversionChecking.check_rename wk binderConversion.code binderConversion.checked⟩

def functionConversion : Certificate
    (.pi oldType (Presentation.rename wk oldType))
    (.pi newType (Presentation.rename wk newType)) :=
  binderConversion.pi bodyConversion

def pairConversion : Certificate
    (.sigma oldType (Presentation.rename wk oldType))
    (.sigma newType (Presentation.rename wk newType)) :=
  binderConversion.sigma bodyConversion

def resultFormation : Code 2 := NativeJudgmentReplay.rename wk newFormation

def alignedFunctionBody : Code 2 :=
  piBody functionConversion (.sort Tower.zero) (.sort Tower.zero)
    oldFormation resultFormation (.var 0) .var

def alignedPairBody : Code 2 :=
  sigmaBody pairConversion (.sort Tower.zero) (.sort Tower.zero)
    oldFormation resultFormation (.var 0) .var

theorem function_body_checked :
    check newContext (.var 0) (Presentation.rename wk newType)
      newContextCode alignedFunctionBody = true := by decide +kernel

theorem pair_body_checked :
    check newContext (.var 0) (Presentation.rename wk newType)
      newContextCode alignedPairBody = true := by decide +kernel

theorem altered_body_rejected :
    check newContext (.var 1) (Presentation.rename wk newType)
      newContextCode alignedFunctionBody = false := by decide +kernel

theorem unformed_destination_rejected :
    check newContext (.var 0) (Presentation.rename wk newType)
      (.snoc NativeJudgmentReplay.Controls.contextCode (.sort Tower.zero) .var)
      alignedFunctionBody = false := by decide +kernel

end Controls

#print axioms body_checked
#print axioms piBody
#print axioms sigmaBody
#print axioms Controls.function_body_checked
#print axioms Controls.pair_body_checked
#print axioms Controls.altered_body_rejected
#print axioms Controls.unformed_destination_rejected

#eval (check ContextConversionControls.newContext (.var 0)
    (Presentation.rename wk ContextConversionControls.newType)
    ContextConversionControls.newContextCode Controls.alignedFunctionBody,
  check ContextConversionControls.newContext (.var 0)
    (Presentation.rename wk ContextConversionControls.newType)
    ContextConversionControls.newContextCode Controls.alignedPairBody)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.BinderAlignment
