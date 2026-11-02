import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine
import Mettapedia.Languages.Datalog.ProgramGrounding

/-! Successful receipt readback retains actual source clause positions,
variable names and ground contextual captures. Premise rows are resolved
against the immutable snapshot used by the firing. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem grounding_fields (names : List String) (assignment : ScopedRuleMatching.Assignment)
    (values : List (String × Pattern)) (read : grounding? names assignment = some values) :
    values.map Prod.fst = names ∧ ∀ pair ∈ values, ∃ value,
      ScopedRuleMatching.lookup assignment (Join.logicalVariable pair.1) = some value ∧
      value.dependencies = [] ∧ value.ambient = 0 ∧ value.body = pair.2 := by
  induction names generalizing values with
  | nil =>
    have same : values = [] := by simpa [grounding?] using read.symm
    subst values
    exact ⟨rfl,by simp⟩
  | cons name names ih =>
    simp only [grounding?,List.mapM_cons] at read
    cases found : ScopedRuleMatching.lookup assignment (Join.logicalVariable name) with
    | none => simp [found] at read
    | some value =>
      simp only [found] at read
      change ((if value.dependencies.isEmpty && value.ambient == 0 then some (name,value.body) else none).bind
        (fun value => (grounding? names assignment).bind (fun rest => some (value :: rest)))) = some values at read
      by_cases ground : (value.dependencies.isEmpty && value.ambient == 0) = true
      · rw [if_pos ground,Option.bind_some] at read
        have parts := Bool.and_eq_true_iff.mp ground
        have dependencies : value.dependencies = [] := List.isEmpty_iff.mp parts.1
        have ambient : value.ambient = 0 := beq_iff_eq.mp parts.2
        cases tail : grounding? names assignment with
        | none => rw [tail] at read; cases read
        | some rest =>
          rw [tail] at read
          have same : (name,value.body) :: rest = values := Option.some.inj read
          subst values
          obtain ⟨identifiers,origins⟩ := ih rest tail
          constructor
          · simp only [List.map_cons,identifiers]
          · intro pair member
            rcases List.mem_cons.mp member with rfl | later
            · exact ⟨value,found,dependencies,ambient,rfl⟩
            · exact origins pair later
      · rw [if_neg ground] at read
        cases read

theorem key_source_fields (prepared : Executable.Prepared) (facts : List Pattern)
    (receipt : GeneralOccurrenceSemantics.Receipt) (key : Key)
    (read : key? prepared facts receipt = some key) :
    ∃ clause, ProgramGrounding.ClauseAt prepared.source key.statementIndex clause ∧
      grounding? (DerivationIdentity.clauseVariables clause) receipt.firing.completed = some key.grounding ∧
      premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts = some key.premises := by
  unfold key? at read
  cases selected : (LPBridge.numberedClauses prepared.source)[receipt.firing.job.declaration.declarationIndex]? with
  | none => simp [selected] at read
  | some entry =>
    rcases entry with ⟨ordinal,clause⟩
    simp only [selected] at read
    change ((grounding? (DerivationIdentity.clauseVariables clause) receipt.firing.completed).bind
      (fun bindings => (premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts).bind
        (fun premises => some (Key.mk ordinal bindings premises)))) = some key at read
    cases values : grounding? (DerivationIdentity.clauseVariables clause) receipt.firing.completed with
    | none => rw [values] at read; cases read
    | some bindings =>
      rw [values] at read
      change (premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts).bind
        (fun premises => some (Key.mk ordinal bindings premises)) = some key at read
      cases premises : premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts with
      | none => rw [premises] at read; cases read
      | some positive =>
        rw [premises] at read
        change some (Key.mk ordinal bindings positive) = some key at read
        cases read
        refine ⟨clause,?_,values,premises⟩
        apply (ProgramGrounding.clauseAt_iff_numbered _ _ _).mpr
        exact List.mem_of_getElem? selected

#print axioms grounding_fields
#print axioms key_source_fields

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
