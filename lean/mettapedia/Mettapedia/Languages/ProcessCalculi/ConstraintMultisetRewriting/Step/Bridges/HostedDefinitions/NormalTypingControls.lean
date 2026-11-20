import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Acceptance

/-!
# Structural development acceptance is distinct from typing qualification

The existing definition returning the first vector is structurally valid
when installed at a fresh name, but its row is refused by the existing typing
qualification. The actual source compiler still accepts that development.
The nearby addition definition passes both checks. These controls compare
the real gates; a checker's refusal is not used to infer failure of every
semantic root-preservation property of an extended package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.Definitions

def badDev : Development := [(addName, Vectors.Checker.keepDef)]
def goodDev : Development := [(addName, addDef)]

theorem bad_structurally_checked : devCheck badDev = true := by decide +kernel

theorem bad_name_fresh : devFresh badDev = true := by decide +kernel

theorem bad_rules : devRules badDev = some
    [⟨5, (spine (.const addName) (telescopeVars 5), .var 1)⟩] := by decide +kernel

theorem bad_compiles : ∃ built : Compiled badDev, compile badDev = some built :=
  checked_compiles badDev bad_structurally_checked

theorem bad_typing_refused : qualify 16 Vectors.Checker.keepDef = .refused 0 := keep_verdict

theorem good_structurally_checked : devCheck goodDev = true := by decide +kernel

theorem good_name_fresh : devFresh goodDev = true := by decide +kernel

theorem good_typing_qualified : qualify 16 addDef = .function true := add_verdict

theorem good_has_checked_term : ∃ term, Checked addDef 0 term := qualify_closed good_typing_qualified

theorem good_compiles : ∃ built : Compiled goodDev, compile goodDev = some built :=
  checked_compiles goodDev good_structurally_checked

theorem structural_acceptance_and_typing_refusal :
    devCheck badDev = true ∧ devFresh badDev = true ∧
      (∃ built : Compiled badDev, compile badDev = some built) ∧
      qualify 16 Vectors.Checker.keepDef = .refused 0 :=
  ⟨bad_structurally_checked, bad_name_fresh, bad_compiles, bad_typing_refused⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypingControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypingControls.structural_acceptance_and_typing_refusal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalTypingControls.good_has_checked_term
