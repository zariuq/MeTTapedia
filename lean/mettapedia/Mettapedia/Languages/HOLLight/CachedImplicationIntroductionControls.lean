import Mettapedia.Languages.HOLLight.CachedImplicationIntroduction

/-!
# Retained implication introduction and refusal controls

An assumption proves its own conditional discharge. Discharging a different
premise keeps the original assumption. Non-Boolean premises and auxiliary
binders captured by either hypotheses or the conclusion are refused.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.HOLLight.CachedImplicationIntroduction.Controls
open Mettapedia.Languages.OpenTheory GraphExpansion

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def p : CanonicalTerm := .free ⟨.global "__discharge_p",Ty.bool⟩
def q : CanonicalTerm := .free ⟨.global "__discharge_q",Ty.bool⟩
def auxiliary : Name := .global "__discharge_auxiliary"
def source : Theorem := HypothesisExpansion.assumption p
def origin : ProofExecution.Origin := ("cached-discharge-control",0)
def discharged : Theorem := Theorem.emptyResult ∅ (ImplicationExpansion.implication p p rfl rfl)
def retained : Theorem := Theorem.emptyResult {p} (ImplicationExpansion.implication q p rfl rfl)

private theorem noP : ¬ DBTerm.FreeOccurrence ⟨auxiliary,ExcludedMiddle.boolBinaryTy⟩ p.term := by
  intro occurrence
  have present := DBTerm.name_mem_freeNames occurrence
  have same : auxiliary = .global "__discharge_p" := by
    simpa [p,CanonicalTerm.free,DBTerm.freeNames] using present
  exact (by decide : "__discharge_auxiliary" ≠ "__discharge_p") (congrArg Name.component same)
private theorem noQ : ¬ DBTerm.FreeOccurrence ⟨auxiliary,ExcludedMiddle.boolBinaryTy⟩ q.term := by
  intro occurrence
  have present := DBTerm.name_mem_freeNames occurrence
  have same : auxiliary = .global "__discharge_q" := by
    simpa [q,CanonicalTerm.free,DBTerm.freeNames] using present
  exact (by decide : "__discharge_auxiliary" ≠ "__discharge_q") (congrArg Name.component same)
private theorem p_ne_q : p ≠ q := by
  intro equal
  have same := congrArg (fun term : CanonicalTerm => match term.term with
    | .free sourceVar => sourceVar.name.component
    | _ => "") equal
  exact (by decide : "__discharge_p" ≠ "__discharge_q") same

theorem self_discharge_produced : ∃ result, prepare? emptyAxiomPolicy p source auxiliary origin = some result := by
  apply prepare?_exists emptyAxiomPolicy p source auxiliary origin rfl rfl
  · rintro ⟨term,present,occurs⟩
    have same : term = p := by simpa [source,HypothesisExpansion.assumption,Theorem.emptyResult] using present
    subst term
    exact noP occurs
  · exact noP

theorem self_discharge_exact {result : Prepared}
    (accepted : prepare? emptyAxiomPolicy p source auxiliary origin = some result) : result.result = discharged := by
  have specification := prepare?_spec _ _ _ _ _ accepted
  apply Theorem.ext
  · exact specification.2.2.1
  · apply Sequent.ext
    · simpa [source,HypothesisExpansion.assumption,discharged,Theorem.emptyResult] using specification.2.1
    · exact CanonicalTerm.ext_term specification.2.2.2

theorem unrelated_discharge_produced : ∃ result, prepare? emptyAxiomPolicy q source auxiliary origin = some result := by
  apply prepare?_exists emptyAxiomPolicy q source auxiliary origin rfl rfl
  · rintro ⟨term,present,occurs⟩
    have options : term = q ∨ term = p := by simpa [source,HypothesisExpansion.assumption,Theorem.emptyResult] using present
    rcases options with rfl | rfl
    · exact noQ occurs
    · exact noP occurs
  · exact noP

theorem unrelated_hypothesis_retained {result : Prepared}
    (accepted : prepare? emptyAxiomPolicy q source auxiliary origin = some result) : result.result = retained := by
  have specification := prepare?_spec _ _ _ _ _ accepted
  apply Theorem.ext
  · exact specification.2.2.1
  · apply Sequent.ext
    · simpa [source,HypothesisExpansion.assumption,retained,Theorem.emptyResult,Ne.symm p_ne_q] using specification.2.1
    · exact CanonicalTerm.ext_term specification.2.2.2

theorem self_discharge_checked : ∃ result,
    prepare? emptyAxiomPolicy p source auxiliary origin = some result ∧
    BlockChecked emptyAxiomPolicy [source] result.result result.certificate := by
  obtain ⟨result,produced⟩ := self_discharge_produced
  exact ⟨result,produced,prepare?_checked _ _ _ _ _ produced⟩

def higher : CanonicalTerm := .free ⟨auxiliary,ExcludedMiddle.boolBinaryTy⟩
def equality : CanonicalTerm := .equalityOfSameType higher higher rfl
def capturedHypothesis : Theorem := HypothesisExpansion.assumption equality
def capturedConclusion : Theorem := EqualityExpansion.reflexivity higher

theorem captured_hypothesis_refused : prepare? emptyAxiomPolicy p capturedHypothesis auxiliary origin = none := by
  apply prepare?_refuses_capture
  exact ⟨equality,by simp [capturedHypothesis,HypothesisExpansion.assumption,Theorem.emptyResult],.appArgument .here⟩
theorem captured_conclusion_refused : prepare? emptyAxiomPolicy p capturedConclusion auxiliary origin = none :=
  prepare?_refuses_conclusion_capture _ _ _ _ _ (.appArgument .here)
theorem non_boolean_premise_refused : prepare? emptyAxiomPolicy higher source auxiliary origin = none := by decide

#print axioms self_discharge_checked
#print axioms unrelated_hypothesis_retained
#print axioms captured_hypothesis_refused
end Mettapedia.Languages.HOLLight.CachedImplicationIntroduction.Controls
