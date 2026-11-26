import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Scoped
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution

/-!
# Facts of the rule sources in the complete machine's runtime

The shared runtime retains the scoped source's rows and declarations on their
actual heads. Additional source families are outside that metadata contract.
Rule-job readout transports on its independently proved closed support.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Effects (State)
open Eval
open BridgeKit

/-- The scoped operation families and inert constructor heads. -/
def scopedSourceHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || head.startsWith "gslt:rule:" ||
    head.startsWith "gslt:premise:" || head.startsWith "gslt:automata:"

private def scopedLaterEquations :=
  RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations)
private def scopedLaterDeclarations :=
  RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations)

private theorem scopedLater_equations_absent :
    scopedLaterEquations.filter (fun row => scopedSourceHeads row.head) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have checked : scopedLaterEquations.all (fun row => !scopedSourceHeads row.head) = true := by decide +kernel
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem scopedLater_declarations_absent :
    scopedLaterDeclarations.filter (retainedCallDeclaration scopedSourceHeads) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have checked : scopedLaterDeclarations.all (fun row => !(retainedCallDeclaration scopedSourceHeads row)) = true := by decide +kernel
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem scoped_physical_agreement : ProgramAgreementOn scopedSourceHeads
    RuleExecutionProgram.scopedProgram
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) := by
  apply programAgreementOn_of_retained_rows
  · rw [PhysicalSourceAgreement.fold_equations, List.filter_append]
    change _ = _ ++ scopedLaterEquations.filter _
    rw [scopedLater_equations_absent, List.append_nil]
  · rw [PhysicalSourceAgreement.fold_declarations, List.filter_append]
    change _ = _ ++ scopedLaterDeclarations.filter _
    rw [scopedLater_declarations_absent, List.append_nil]

/-- Scoped metadata transports only on actual source and constructor heads. -/
theorem scoped_runtime_agreement (allowed : String → Bool)
    (supported : ∀ head, allowed head = true → scopedSourceHeads head = true) :
    ProgramAgreementOn allowed RuleExecutionProgram.scopedProgram scopedLibrary.runtime :=
  agreement_mono supported (agreement_trans scoped_physical_agreement
    (agreement_mono (fun _ _ => rfl) PhysicalSourceAgreement.physical_interpreted_agreement))

theorem readout_scoped_agreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
    ScopedRuleJobReadoutExecution.runtime scopedLibrary.runtime := by
  refine agreement_trans PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
    (scoped_runtime_agreement _ ?_)
  intro head supported
  have checked : ScopedRuleJobReadoutExecution.executionHeadNames.all scopedSourceHeads = true := by decide +kernel
  exact List.all_eq_true.mp checked head (List.contains_iff_mem.mp supported)

private def fillProofLibrary : Library :=
  ⟨{equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel)],
      declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel)]},
    {equations := [RuleExecutionProgram.scopedProgram.equations[118]'(by decide +kernel)],
      declarations := [RuleExecutionProgram.scopedProgram.declarations[118]'(by decide +kernel)]},
    ["gslt:rule:scope-fill"]⟩
private def fillProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || ["gslt:automata:append", "gslt:rule:scope-fill"].contains head
private theorem fillProof_checked : fillProofLibrary.check = true := by decide +kernel

private local instance scopedEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

private theorem fillProof_agreement :
    ProgramAgreementOn fillProofHeads fillProofLibrary.runtime scopedLibrary.runtime := by
  have sourceAgreement : ProgramAgreementOn fillProofHeads fillProofLibrary.runtime RuleExecutionProgram.scopedProgram := by
    apply programAgreementOn_of_retained_rows
    · decide +kernel
    · decide +kernel
  refine agreement_trans sourceAgreement (scoped_runtime_agreement _ ?_)
  intro head supported
  simp only [fillProofHeads, Bool.or_eq_true] at supported
  rcases supported with outside | named
  · simp only [scopedSourceHeads, outside, Bool.true_or]
  · simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at named
    rcases named with rfl | rfl <;> decide +kernel

/-- A scoped-library fact about a call at values holds in the complete machine's runtime. -/
syntax "metta_raise " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_raise [$_names,*] $fact) => `(tactic| exact $fact)

/-- Raise a fact about a call at values from the rule-job readout. -/
syntax "metta_from_readout " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_from_readout [$names,*] $fact) => `(tactic|
      metta_raise [$names,*]
        (transport_call ScopedRuleJobReadoutExecution.runtime_closed readout_scoped_agreement (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide) rfl (by decide +kernel) $fact))

open Mettapedia.GSLT.LanguageDef InferenceCettaWire in
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts in
/-- `gslt:rule:scope-fill` fills a context. -/
theorem scoped_fill_returns (state : State) (pattern : Pattern) : ∀ context : OneHoleContext,
    PureReturns scopedLibrary.runtime [] state
      (WireKit.apply "gslt:rule:scope-fill" [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern))
  | .hole => by
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill]
  | .apply head before inner after => by
    have joined := automata_append_returns encodePattern state before (inner.fill pattern :: after)
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner, joined] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern,
        encodePatterns_eq_encodeList, CettaWire.encodeList]
  | .lambda binder inner => by
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .multiLambda arity binders inner => by
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .substBody inner replacement => by
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .substReplacement body inner => by
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .collection kind before inner after rest => by
    have joined := automata_append_returns encodePattern state before (inner.fill pattern :: after)
    metta_call_in fillProof_checked using fillProof_agreement
    metta_eval [scoped_fill_returns state pattern inner, joined] with fillProof_checked in fillProof_agreement
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern,
        encodePatterns_eq_encodeList, CettaWire.encodeList]

open Mettapedia.GSLT.LanguageDef InferenceCettaWire in
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts in
/-- `gslt:rule:scope-fill`, in the complete machine's runtime. -/
theorem complete_fill_returns (state : State) (context : OneHoleContext) (pattern : Pattern) :
    PureReturns runtime [] state
      (WireKit.apply "gslt:rule:scope-fill" [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern)) := by
  metta_raise ["context", "pattern"] (scoped_fill_returns state pattern context)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.scoped_runtime_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.readout_scoped_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.scoped_fill_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.complete_fill_returns
