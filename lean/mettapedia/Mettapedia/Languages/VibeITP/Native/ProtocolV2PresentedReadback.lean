import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofs

/-! Structural readback of the admitted crossing theory. Closed comparisons
inspect the allocated data fields; signature equality follows by applying
`sigOf` to equality of the fresh-symbol tables. No symbolic unfolding of the
complete execution state is needed to transport a supplied article. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Native.ProtocolV2PresentedReadback

open Spec Presentation Presentation.SimultaneousPresentation ProtocolV2LogicalControls
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private theorem definition_eq (first second : Definition) :
    first = second ↔ first.symbol = second.symbol ∧ first.fvars = second.fvars ∧ first.value = second.value := by
  cases first
  cases second
  simp only [Definition.mk.injEq]

local instance : DecidableEq Definition := fun first second =>
  decidable_of_iff (first.symbol = second.symbol ∧ first.fvars = second.fvars ∧ first.value = second.value)
    (definition_eq first second).symm

theorem allocated_readback : finalState.nextFresh = Controls.allocated := by decide +kernel

theorem fresh_readback (index : Nat) : Controls.freshInfo index = finalState.fresh index := by
  by_cases zero : index = 0
  · subst index; decide +kernel
  by_cases one : index = 1
  · subst index; decide +kernel
  by_cases two : index = 2
  · subst index; decide +kernel
  have unavailable : finalState.fresh index = none := by
    cases found : finalState.fresh index with
    | none => rfl
    | some info =>
        have small := (final_invariant.theory.fresh index).mp
          (by simpa only [State.theory, State.sig, sigOf, found] using
            (show (some info).isSome = true from rfl))
        rw [allocated_readback] at small
        change index < 3 at small
        omega
  rw [unavailable]
  simp [Controls.freshInfo, two, show ¬index < 2 by omega]

theorem theory_readback : Controls.theory = finalState.theory := by
  have signature : Controls.theory.sig = finalState.sig := congrArg sigOf (funext fresh_readback)
  have axioms : Controls.theory.axioms = finalState.axioms := by decide +kernel
  have definitions : Controls.theory.definitions = finalState.definitions := by decide +kernel
  change Theory.mk Controls.theory.sig Controls.theory.axioms Controls.theory.definitions =
    Theory.mk finalState.sig finalState.axioms finalState.definitions
  rw [signature, axioms, definitions]

theorem statement_readback : Controls.crossing = Spec.ProtocolV2.Controls.crossingResult := rfl

/-- A particular supplied article transports to the actual admitted byte-run
theory. Its identity is preserved; no existential replacement is selected. -/
theorem supplied_article_transports (article : RawProof)
    (accepted : checkRaw (validatedV2 Controls.theory Controls.allocated)
      (jThm (encTerm Controls.theory.sig Controls.crossing)) article = true) :
    checkRaw (validatedV2 finalState.theory finalState.nextFresh)
      (jThm (encTerm finalState.theory.sig Spec.ProtocolV2.Controls.crossingResult)) article = true := by
  rw [allocated_readback, ← theory_readback, ← statement_readback]
  exact accepted

theorem supplied_witness_transports (witness : SimultaneousProofs.Witness)
    (accepted : SimultaneousProofs.Witness.check Controls.theory witness Controls.crossing = true) :
    SimultaneousProofs.Witness.check finalState.theory witness Spec.ProtocolV2.Controls.crossingResult = true := by
  rw [← theory_readback, ← statement_readback]
  exact accepted

#print axioms theory_readback
#print axioms supplied_article_transports

end Mettapedia.Languages.VibeITP.Native.ProtocolV2PresentedReadback
