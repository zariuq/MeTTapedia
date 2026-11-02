import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationStage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeEquationInstances
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatchReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatchingTyping
import Mettapedia.Languages.Maude.PeanoTermination
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-! Authored equation instances fire through the actual normalization-stage
rule table. Sorted captures read back to forward source equation steps;
equation evidence remains separate from the source transition rules R. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem oriented_member (prepared : Prepared) {equation : Equation}
    (member : equation ∈ prepared.language.equations.take prepared.source.equations.length) :
    ScopedEquationExecution.orientedRule equation .forward ∈ (language prepared).rewrites := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨equation, member, rfl⟩)

theorem unconditional_root_step (base : BasePremiseEvaluator) (prepared : Prepared)
    (row : Maude.Row) (assignment : Maude.Valuation) {index : Nat} {equation : Equation}
    (produced : equation? prepared.source.signature index row = some equation)
    (member : equation ∈ prepared.language.equations.take prepared.source.equations.length)
    (empty : row.conditions = []) (inputs : row.inputsBound = true) :
    ContextualStep.Step base (language prepared)
      (encode (row.left.substitute assignment)) (encode (row.right.substitute assignment)) := by
  have bound : ∀ name ∈ row.right.variables, name ∈ row.left.variables := by
    simp only [Maude.Row.inputsBound, List.all_eq_true, List.contains_iff_mem] at inputs
    intro name occurs
    exact inputs name (List.mem_append_left _ occurs)
  obtain ⟨bindings, matched, applied, _, _, _⟩ := match_instance_readout assignment row.left row.right bound
  obtain ⟨left, right, premises, _⟩ := equation_unconditional empty produced
  let rule := ScopedEquationExecution.orientedRule equation .forward
  have shallow : ruleDepthAligned rule = true := by
    apply ruleDepthAligned_of_binderFree rule
    · change binderFree equation.left = true
      rw [left]
      exact (encode_firstOrder row.left).binderFree
    · change binderFree equation.right = true
      rw [right]
      exact (encode_firstOrder row.right).binderFree
  refine ⟨1, StepAt.rule (initialBindings := bindings) (finalBindings := bindings)
    (oriented_member prepared member) ?_ ?_ ?_⟩
  · simpa only [matchPatternForRule_eq_syntactic, ScopedEquationExecution.orientedRule, left] using matched
  · change PremisesAt base (language prepared) 0 bindings equation.premises bindings
    rw [premises]
    exact .nil bindings
  · rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings rule bindings shallow]
    simpa only [rule, ScopedEquationExecution.orientedRule, right] using applied

theorem source_of_sorted_root_match (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source target : Maude.Term) (sort : String) {bindings : Bindings}
    (declared : row ∈ prepared.source.equations) (empty : row.conditions = [])
    (checked : row.check prepared.source.signature = true)
    (leftTyped : Maude.HasSort prepared.source.signature row.usedContext row.left sort)
    (rightTyped : Maude.HasSort prepared.source.signature row.usedContext row.right sort)
    (matched : bindings ∈ matchPattern (encode row.left) (encode source))
    (applied : applyBindings bindings (encode row.right) = encode target)
    (sorted : SortedBindingsIn (language prepared) (freeContext ambient) (context row) bindings) :
    Maude.EquationReduction prepared.source ambient sort source target := by
  obtain ⟨assignment, typed, first, last⟩ := sorted_row_instance_readback prepared ambient row source target
    matched applied (sorted_bindings_original prepared ambient sorted)
  rw [← first, ← last]
  exact .root assignment declared checked leftTyped rightTyped typed (empty ▸ .nil assignment)

/-- Source typing and the actual match discharge the capture sorts. The
returned source target is decoded from those captures, not proposed by the
target executor. -/
theorem typed_root_readback (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source : Maude.Term) (sort : String) {bindings : Bindings} {target : Pattern}
    (valid : prepared.language.validate = [])
    (declared : row ∈ prepared.source.equations) (empty : row.conditions = [])
    (checked : row.check prepared.source.signature = true) (inputs : row.inputsBound = true)
    (leftTyped : Maude.HasSort prepared.source.signature row.usedContext row.left sort)
    (rightTyped : Maude.HasSort prepared.source.signature row.usedContext row.right sort)
    (sourceTyped : Maude.HasSort prepared.source.signature ambient source sort)
    (matched : bindings ∈ matchPattern (encode row.left) (encode source))
    (applied : applyBindings bindings (encode row.right) = target) :
    ∃ sourceTarget, target = encode sourceTarget ∧
      Maude.EquationReduction prepared.source ambient sort source sourceTarget := by
  have sorted := matched_row_sorted prepared ambient row source sort valid checked inputs leftTyped sourceTyped matched
  have values := matched_values_decode matched
  have typed := readAssignment_typed prepared ambient row.usedContext values sorted
  have sourceExact := matching_source_readback matched
  refine ⟨row.right.substitute (readAssignment bindings),
    applied.symm.trans (readAssignment_substitution values row.right), ?_⟩
  rw [← sourceExact]
  exact .root (readAssignment bindings) declared checked leftTyped rightTyped typed (empty ▸ .nil _)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage
