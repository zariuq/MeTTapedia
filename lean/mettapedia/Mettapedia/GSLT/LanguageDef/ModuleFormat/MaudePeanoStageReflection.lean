import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoStageSimulation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeContextReadback
import Mettapedia.GSLT.LanguageDef.ReactiveArgumentInversion

/-! Every normalization-stage step from a sorted encoded Peano term reads
back to a forward source equation step. This includes the context rules and
does not assume the target remains in the source image. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoReflection

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open PeanoSimulation

private theorem root_reflect (relEnv : Engine.RelationEnv) (context : Maude.VariableContext)
    (source : Maude.Term) {target : Pattern} {row : Maude.Row} {index fuel : Nat} {equation : Equation}
    {initial final : Bindings} (declared : row ∈ Maude.Examples.peano.equations)
    (produced : equation? peano.source.signature index row = some equation)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (matched : initial ∈ matchPatternForRule (language peano)
      (ScopedEquationExecution.orientedRule equation .forward) (encode source))
    (premises : PremisesAt (engineBasePremises relEnv) (language peano) fuel initial
      (ScopedEquationExecution.orientedRule equation .forward).premises final)
    (applied : applyBindingsForRule (language peano) (ScopedEquationExecution.orientedRule equation .forward) final = target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  have empty : row.conditions = [] := by
    simp only [Maude.Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨left, right, noPremises, _⟩ := equation_unconditional empty produced
  change PremisesAt (engineBasePremises relEnv) (language peano) fuel initial equation.premises final at premises
  rw [noPremises] at premises
  cases premises
  have shallow : ruleDepthAligned (ScopedEquationExecution.orientedRule equation .forward) = true := by
    apply ruleDepthAligned_of_binderFree
    · change binderFree equation.left = true
      rw [left]
      exact (encode_firstOrder row.left).binderFree
    · change binderFree equation.right = true
      rw [right]
      exact (encode_firstOrder row.right).binderFree
  have ordinary : initial ∈ matchPattern (encode row.left) (encode source) := by
    simpa only [matchPatternForRule_eq_syntactic, ScopedEquationExecution.orientedRule, left] using matched
  have plain : applyBindings initial (encode row.right) = target := by
    rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _ shallow] at applied
    simpa only [ScopedEquationExecution.orientedRule, right] using applied
  have checked : Maude.Examples.peano.equations.all (Maude.Row.check Maude.Examples.peano.signature) = true := by decide_cbv
  have bounded : Maude.Examples.peano.equations.all (fun row => row.inputsBound) = true := by decide_cbv
  have readback := typed_root_readback peano context row source "Nat" (prepare_valid preparation)
    (by simpa only [source_exact] using declared) empty
    (by simpa only [source_exact] using List.all_eq_true.mp checked row declared)
    (List.all_eq_true.mp bounded row declared)
    (by simpa only [source_exact] using (Maude.PeanoEquationRules.schemas_typed declared).1)
    (by simpa only [source_exact] using (Maude.PeanoEquationRules.schemas_typed declared).2)
    (by simpa only [source_exact] using typed) ordinary plain
  simpa only [source_exact] using readback

theorem reflect_at (relEnv : Engine.RelationEnv) (context : Maude.VariableContext) (fuel : Nat) :
    ∀ (source : Maude.Term) (target : Pattern),
      Maude.HasSort Maude.Examples.peano.signature context source "Nat" →
      StepAt (engineBasePremises relEnv) (language peano) fuel (encode source) target →
      ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  induction fuel with
  | zero => intro source target typed step; cases step
  | succ fuel ih =>
      intro source target typed step
      cases step with
      | @rule _ _ _ rule initial final member matched premises applied =>
          rcases rule_cases member with ⟨row, index, equation, declared, produced, rfl⟩ |
            ⟨label, beforeNames, afterNames, sourceName, targetName, congruence⟩
          · exact root_reflect relEnv context source declared produced typed matched premises applied
          · obtain ⟨before, after, redex, reduct, _, _, sourceShape, targetShape, inner⟩ :=
              congruence.invert matched premises applied
            obtain ⟨hole, frame, child, frameLabel, sourceEq, childEq, beforeEq, afterEq, childTyped⟩ :=
              argument_context_readback typed sourceShape
            have sameSort := hole_is_nat frame
            subst hole
            have childAt : StepAt (engineBasePremises relEnv) (language peano) fuel (encode child) reduct := by
              rw [childEq]
              exact inner
            obtain ⟨result, resultEq, sourceInner⟩ := ih child reduct childTyped childAt
            refine ⟨frame.plug result, ?_, ?_⟩
            · simpa only [Maude.ArgumentContext.plug, encode, List.map_append, List.map_cons,
                beforeEq, afterEq, frameLabel, ← resultEq] using targetShape
            · rw [sourceEq]
              exact .argument frame sourceInner

theorem contextual_reflect (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (step : ContextualStep.Step (engineBasePremises relEnv) (language peano) (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  obtain ⟨fuel, step⟩ := step
  exact reflect_at relEnv context fuel source target typed step

theorem reference_reflect (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (step : ReferenceStep.Step relEnv (language peano) (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result :=
  contextual_reflect relEnv typed
    ((ReferenceStep.contextualStep_iff_step relEnv (language peano) aligned).mpr step)

theorem reference_step_iff (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source target : Maude.Term} (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    ReferenceStep.Step relEnv (language peano) (encode source) (encode target) ↔
      Maude.EquationReduction Maude.Examples.peano context "Nat" source target := by
  constructor
  · intro step
    obtain ⟨result, same, reduced⟩ := reference_reflect relEnv typed step
    have sourceSame := encode_injective same
    subst result
    exact reduced
  · exact reference_step relEnv

theorem reference_path_reflect (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (path : Relation.ReflTransGen (ReferenceStep.Step relEnv (language peano)) (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  induction path with
  | refl => exact ⟨source, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨middle, middleEq, sourcePath⟩ := ih
      rw [middleEq] at step
      obtain ⟨result, resultEq, reduced⟩ := reference_reflect relEnv (sourcePath.equivalent typed).sorted.2 step
      exact ⟨result, resultEq, sourcePath.tail reduced⟩

theorem reference_path_iff (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source target : Maude.Term} (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    Relation.ReflTransGen (ReferenceStep.Step relEnv (language peano)) (encode source) (encode target) ↔
      Maude.EquationPath Maude.Examples.peano context "Nat" source target := by
  constructor
  · intro path
    obtain ⟨result, same, reduced⟩ := reference_path_reflect relEnv typed path
    have sourceSame := encode_injective same
    subst result
    exact reduced
  · exact reference_path relEnv

theorem normalizer_no_step (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source : Maude.Term} (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    ∀ target, ¬ ReferenceStep.Step relEnv (language peano) (encode (Maude.PeanoNormalization.reduce source)) target := by
  intro target step
  obtain ⟨result, _, reduced⟩ := reference_reflect relEnv (Maude.PeanoNormalization.reduce_typed typed) step
  exact Maude.PeanoNormalization.reduce_no_step typed reduced

theorem normal_result_exact (relEnv : Engine.RelationEnv) {context : Maude.VariableContext}
    {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (path : Relation.ReflTransGen (ReferenceStep.Step relEnv (language peano)) (encode source) target)
    (normal : ∀ next, ¬ ReferenceStep.Step relEnv (language peano) target next) :
    target = encode (Maude.PeanoNormalization.reduce source) := by
  obtain ⟨result, same, reduced⟩ := reference_path_reflect relEnv typed path
  have noSourceStep : ∀ next, ¬ Maude.EquationReduction Maude.Examples.peano context "Nat" result next := by
    intro next step
    apply normal (encode next)
    rw [same]
    exact reference_step relEnv step
  exact same.trans (congrArg encode (Maude.PeanoNormalization.normal_result_unique typed reduced noSourceStep))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoReflection
