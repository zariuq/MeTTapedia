import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# OSLF and native-type gates for the derivation-check machine

These diagnostics consume the authored target presentation itself.  The
interface-independent missing-finish path supplies a closed positive witness:
it requires no formula, rule, evidence, provenance, or obligation instance.
Thus the open specialization seams cannot make the operational test vacuous.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationCheckMachineNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef

theorem index_instruction_crossing :
    ("dcm:drop", "Index", "Instruction") ∈ unaryCrossings language := by
  decide

theorem formula_decision_crossing :
    ("dcm:decision-root", "Formula", "Decision") ∈
      unaryCrossings language := by
  decide

theorem no_formula_outcome_crossing :
    ("dcm:invented-formula-outcome", "Formula", "Outcome") ∉
      unaryCrossings language := by
  decide

def configNativeType : langNativeType language "Config" where
  sort := "Config"
  pred := fun term =>
    checkHasType language WellSorted.FreeTypeContext.empty [] term
      (.base "Config") = true

theorem missing_start_inhabits_config :
    configNativeType.pred missingFinishStart := by
  change checkHasType language WellSorted.FreeTypeContext.empty []
    missingFinishStart (.base "Config") = true
  exact missingFinishStart_has_type

def machineOSLF := langOSLFUsing RelationEnv.empty language "Config"

theorem machine_galois :
    GaloisConnection
      (langDiamondUsing RelationEnv.empty language)
      (langBoxUsing RelationEnv.empty language) :=
  langGaloisUsing RelationEnv.empty language

theorem missing_finish_step_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishStart = [missingFinishDone] := by
  decide +kernel

theorem halted_has_no_reducts :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishDone = [] := by
  decide +kernel

#print axioms index_instruction_crossing
#print axioms formula_decision_crossing
#print axioms no_formula_outcome_crossing
#print axioms missing_start_inhabits_config
#print axioms machine_galois
#print axioms missing_finish_step_exact
#print axioms halted_has_no_reducts

end Mettapedia.GSLT.LanguageDef.DerivationCheckMachineNTT
