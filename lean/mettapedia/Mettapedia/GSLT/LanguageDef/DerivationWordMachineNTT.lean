import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# OSLF and native-type gates for the derivation-word machine

These diagnostics are derived from the mechanically lifted compact target
presentation.  The closed missing-finish transition gives a non-vacuous
operational witness without assuming any particular calculus service or
record decoder implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef

theorem integer_word_crossing :
    ("dwm:word", "Integer", "Word") ∈ unaryCrossings language := by
  decide

theorem instruction_decode_decision_crossing :
    ("dwm:decoded", "Instruction", "DecodeDecision") ∈
      unaryCrossings language := by
  decide

theorem no_formula_outcome_crossing :
    ("dwm:invented-formula-outcome", "Formula", "Outcome") ∉
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

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem missing_finish_step_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishStart = [missingFinishDone] := by
  exact missingFinishStep_exact

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem halted_has_no_reducts :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishDone = [] := by
  exact missingFinishDone_irreducible

#print axioms integer_word_crossing
#print axioms instruction_decode_decision_crossing
#print axioms no_formula_outcome_crossing
#print axioms missing_start_inhabits_config
#print axioms machine_galois
#print axioms missing_finish_step_exact
#print axioms halted_has_no_reducts

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineNTT
