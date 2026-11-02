import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationFiring
import Mettapedia.GSLT.LanguageDef.ReactiveContexts

/-! Source Peano equation steps are steps of the actual emitted-stage input.
Constructor descent uses the shared argument-congruence theorem. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoSimulation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open Mettapedia.GSLT.LanguageDef
open Maude.PeanoEquationRules

theorem preparation : prepare Maude.Examples.peano = .ok peano := by
  have accepted : (prepare Maude.Examples.peano).toOption.isSome = true := by decide_cbv
  cases result : prepare Maude.Examples.peano with
  | error message => simp [result, Except.toOption] at accepted
  | ok value =>
      have selected : peano = value := by simp [peano, result, Except.toOption]
      exact congrArg Except.ok selected.symm

theorem source_exact : peano.source = Maude.Examples.peano := prepare_source preparation

private theorem retained_row {row : Maude.Row} (member : row ∈ Maude.Examples.peano.equations) :
    ∃ index equation, equation? peano.source.signature index row = some equation ∧
      equation ∈ peano.language.equations.take peano.source.equations.length := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨equation, produced, present⟩ :=
    authored_equation_member preparation (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  have lengths : peano.language.equations.length = peano.source.equations.length := by decide_cbv
  refine ⟨index, equation, ?_, ?_⟩
  · rw [source_exact]
    exact produced
  · rw [← lengths, List.take_length]
    exact present

theorem root_step (relEnv : Engine.RelationEnv) {row : Maude.Row}
    (member : row ∈ Maude.Examples.peano.equations) (assignment : Maude.Valuation) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (encode (row.left.substitute assignment)) (encode (row.right.substitute assignment)) := by
  obtain ⟨index, equation, produced, retained⟩ := retained_row member
  have empty : row.conditions = [] := by
    simp only [Maude.Examples.peano, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  have bounded : Maude.Examples.peano.equations.all (fun row => row.inputsBound) = true := by decide_cbv
  exact unconditional_root_step (engineBasePremises relEnv) peano row assignment produced retained empty
    (List.all_eq_true.mp bounded row member)

private theorem context_member (declaration : Maude.Operator)
    (member : declaration ∈ Maude.Examples.peano.signature.operators) {rule : RewriteRule}
    (listed : rule ∈ congruences declaration) : rule ∈ (language peano).rewrites := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨declaration, by simpa only [source_exact] using member, listed⟩

private def successorRule : RewriteRule := (congruences successorOperator)[0]'(by decide_cbv)
private def addLeftRule : RewriteRule := (congruences additionOperator)[0]'(by decide_cbv)
private def addRightRule : RewriteRule := (congruences additionOperator)[1]'(by decide_cbv)
private def multiplyLeftRule : RewriteRule := (congruences multiplicationOperator)[0]'(by decide_cbv)
private def multiplyRightRule : RewriteRule := (congruences multiplicationOperator)[1]'(by decide_cbv)

private theorem successor_shape : ArgumentCongruence successorRule "peano.succ" [] []
    "maude:field:0" "maude:replacement" := ⟨rfl, rfl, rfl, by decide_cbv⟩
private theorem add_left_shape : ArgumentCongruence addLeftRule "peano.add" [] ["maude:field:1"]
    "maude:field:0" "maude:replacement" := ⟨rfl, rfl, rfl, by decide_cbv⟩
private theorem add_right_shape : ArgumentCongruence addRightRule "peano.add" ["maude:field:0"] []
    "maude:field:1" "maude:replacement" := ⟨rfl, rfl, rfl, by decide_cbv⟩
private theorem multiply_left_shape : ArgumentCongruence multiplyLeftRule "peano.mul" [] ["maude:field:1"]
    "maude:field:0" "maude:replacement" := ⟨rfl, rfl, rfl, by decide_cbv⟩
private theorem multiply_right_shape : ArgumentCongruence multiplyRightRule "peano.mul" ["maude:field:0"] []
    "maude:field:1" "maude:replacement" := ⟨rfl, rfl, rfl, by decide_cbv⟩

private theorem context_shape {declaration : Maude.Operator} {rule : RewriteRule}
    (declared : declaration ∈ Maude.Examples.peano.signature.operators)
    (listed : rule ∈ congruences declaration) :
    ∃ label before after source target, ArgumentCongruence rule label before after source target := by
  rcases operators declared with rfl | rfl | rfl | rfl
  · change rule ∈ [] at listed
    cases listed
  · change rule ∈ [successorRule] at listed
    obtain rfl := List.mem_singleton.mp listed
    exact ⟨_, _, _, _, _, successor_shape⟩
  · change rule ∈ [addLeftRule, addRightRule] at listed
    rcases List.mem_cons.mp listed with rfl | listed
    · exact ⟨_, _, _, _, _, add_left_shape⟩
    · obtain rfl := List.mem_singleton.mp listed
      exact ⟨_, _, _, _, _, add_right_shape⟩
  · change rule ∈ [multiplyLeftRule, multiplyRightRule] at listed
    rcases List.mem_cons.mp listed with rfl | listed
    · exact ⟨_, _, _, _, _, multiply_left_shape⟩
    · obtain rfl := List.mem_singleton.mp listed
      exact ⟨_, _, _, _, _, multiply_right_shape⟩

theorem rule_cases {rule : RewriteRule} (member : rule ∈ (language peano).rewrites) :
    (∃ row index equation, row ∈ Maude.Examples.peano.equations ∧
      equation? peano.source.signature index row = some equation ∧
      rule = ScopedEquationExecution.orientedRule equation .forward) ∨
    ∃ label before after source target, ArgumentCongruence rule label before after source target := by
  rcases List.mem_append.mp member with equationRule | contextRule
  · obtain ⟨equation, authoredMember, same⟩ := List.mem_map.mp equationRule
    obtain ⟨row, index, original, produced⟩ := authored_equation_source preparation authoredMember
    exact Or.inl ⟨row, index, equation, List.fst_mem_of_mem_zipIdx original,
      by simpa only [source_exact] using produced, same.symm⟩
  · obtain ⟨declaration, declared, listed⟩ := List.mem_flatMap.mp contextRule
    exact Or.inr (context_shape (by simpa only [source_exact] using declared) listed)

theorem hole_is_nat {context : Maude.VariableContext} {hole sort : String}
    (frame : Maude.ArgumentContext Maude.Examples.peano.signature context hole sort) : hole = "Nat" := by
  have member : hole ∈ frame.declaration.arguments := by
    rw [frame.argumentSorts]
    exact List.mem_append_right _ List.mem_cons_self
  rcases operators frame.declared with same | same | same | same
  · simp [same, zeroOperator] at member
  · simpa [same, successorOperator] using member
  · simpa [same, additionOperator] using member
  · simpa [same, multiplicationOperator] using member

theorem successor_step {relEnv : Engine.RelationEnv} {source target : Pattern}
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply "peano.succ" [source]) (.apply "peano.succ" [target]) := by
  exact successor_shape.step (context_member successorOperator successor_member (List.getElem_mem (by decide_cbv)))
    (beforeTerms := []) (afterTerms := []) rfl rfl inner

theorem addition_left_step {relEnv : Engine.RelationEnv} {source target : Pattern} (other : Pattern)
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply "peano.add" [source, other]) (.apply "peano.add" [target, other]) := by
  exact add_left_shape.step (context_member additionOperator addition_member (List.getElem_mem (by decide_cbv)))
    (beforeTerms := []) (afterTerms := [other]) rfl rfl inner

theorem addition_right_step {relEnv : Engine.RelationEnv} {source target : Pattern} (other : Pattern)
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply "peano.add" [other, source]) (.apply "peano.add" [other, target]) := by
  exact add_right_shape.step (context_member additionOperator addition_member (List.getElem_mem (by decide_cbv)))
    (beforeTerms := [other]) (afterTerms := []) rfl rfl inner

theorem multiplication_left_step {relEnv : Engine.RelationEnv} {source target : Pattern} (other : Pattern)
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply "peano.mul" [source, other]) (.apply "peano.mul" [target, other]) := by
  exact multiply_left_shape.step (context_member multiplicationOperator multiplication_member (List.getElem_mem (by decide_cbv)))
    (beforeTerms := []) (afterTerms := [other]) rfl rfl inner

theorem multiplication_right_step {relEnv : Engine.RelationEnv} {source target : Pattern} (other : Pattern)
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply "peano.mul" [other, source]) (.apply "peano.mul" [other, target]) := by
  exact multiply_right_shape.step (context_member multiplicationOperator multiplication_member (List.getElem_mem (by decide_cbv)))
    (beforeTerms := [other]) (afterTerms := []) rfl rfl inner

private theorem frame_lengths {context : Maude.VariableContext} {hole sort : String}
    (frame : Maude.ArgumentContext Maude.Examples.peano.signature context hole sort) :
    frame.before.length + 1 + frame.after.length = frame.declaration.arguments.length := by
  have sorts := congrArg List.length frame.argumentSorts
  have before := frame.beforeTyped.length_eq
  have after := frame.afterTyped.length_eq
  simp only [List.length_append, List.length_cons] at sorts
  omega

private theorem binary_argument_step {relEnv : Engine.RelationEnv} {context : Maude.VariableContext}
    {hole sort : String} (frame : Maude.ArgumentContext Maude.Examples.peano.signature context hole sort)
    (id : String) (label : frame.declaration.id = id) (arity : frame.declaration.arguments.length = 2)
    {source target : Maude.Term}
    (leftLift : ∀ other, ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply id [encode source, other]) (.apply id [encode target, other]))
    (rightLift : ∀ other, ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (.apply id [other, encode source]) (.apply id [other, encode target])) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (encode (frame.plug source)) (encode (frame.plug target)) := by
  have sizes := frame_lengths frame
  rw [arity] at sizes
  by_cases empty : frame.before = []
  · have length : frame.after.length = 1 := by simp only [empty, List.length_nil] at sizes; omega
    obtain ⟨other, after⟩ := List.length_eq_one_iff.mp length
    simpa only [Maude.ArgumentContext.plug, empty, after, List.nil_append, label,
      encode, List.map_cons, List.map_nil] using leftLift (encode other)
  · have positive : 0 < frame.before.length := List.length_pos_iff.mpr empty
    have length : frame.before.length = 1 := by omega
    obtain ⟨other, before⟩ := List.length_eq_one_iff.mp length
    have after : frame.after = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [Maude.ArgumentContext.plug, before, after, List.cons_append, List.nil_append, label,
      encode, List.map_cons, List.map_nil] using rightLift (encode other)

theorem argument_step {relEnv : Engine.RelationEnv} {context : Maude.VariableContext} {hole sort : String}
    (frame : Maude.ArgumentContext Maude.Examples.peano.signature context hole sort) {source target : Maude.Term}
    (inner : ContextualStep.Step (engineBasePremises relEnv) (language peano) (encode source) (encode target)) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano)
      (encode (frame.plug source)) (encode (frame.plug target)) := by
  rcases operators frame.declared with same | same | same | same
  · have sizes := frame_lengths frame
    rw [same] at sizes
    simp only [zeroOperator, List.length_nil] at sizes
    omega
  · have sizes := frame_lengths frame
    rw [same] at sizes
    simp only [successorOperator, List.length_cons, List.length_nil] at sizes
    have before : frame.before = [] := List.length_eq_zero_iff.mp (by omega)
    have after : frame.after = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [Maude.ArgumentContext.plug, before, after, List.nil_append, same, successorOperator,
      encode, List.map_cons, List.map_nil] using successor_step inner
  · apply binary_argument_step frame "peano.add" (by rw [same]; rfl) (by rw [same]; rfl)
    · exact fun other => addition_left_step other inner
    · exact fun other => addition_right_step other inner
  · apply binary_argument_step frame "peano.mul" (by rw [same]; rfl) (by rw [same]; rfl)
    · exact fun other => multiplication_left_step other inner
    · exact fun other => multiplication_right_step other inner

theorem source_step (relEnv : Engine.RelationEnv) {context : Maude.VariableContext} {sort : String}
    {source target : Maude.Term} (step : Maude.EquationReduction Maude.Examples.peano context sort source target) :
    ContextualStep.Step (engineBasePremises relEnv) (language peano) (encode source) (encode target) := by
  induction step with
  | root assignment declared _ _ _ _ _ => exact root_step relEnv declared assignment
  | argument frame _ ih => exact argument_step frame ih

theorem source_path (relEnv : Engine.RelationEnv) {context : Maude.VariableContext} {sort : String}
    {source target : Maude.Term} (path : Maude.EquationPath Maude.Examples.peano context sort source target) :
    Relation.ReflTransGen (ContextualStep.Step (engineBasePremises relEnv) (language peano))
      (encode source) (encode target) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (source_step relEnv step)

theorem aligned : ReferenceStep.ReferenceProfile (language peano) := by
  intro rule member
  have checked : (language peano).rewrites.all ReferenceStep.ruleAligned = true := by decide_cbv
  exact List.all_eq_true.mp checked rule member

theorem reference_step (relEnv : Engine.RelationEnv) {context : Maude.VariableContext} {sort : String}
    {source target : Maude.Term} (step : Maude.EquationReduction Maude.Examples.peano context sort source target) :
    ReferenceStep.Step relEnv (language peano) (encode source) (encode target) :=
  (ReferenceStep.contextualStep_iff_step relEnv (language peano) aligned).mp (source_step relEnv step)

theorem reference_path (relEnv : Engine.RelationEnv) {context : Maude.VariableContext} {sort : String}
    {source target : Maude.Term} (path : Maude.EquationPath Maude.Examples.peano context sort source target) :
    Relation.ReflTransGen (ReferenceStep.Step relEnv (language peano)) (encode source) (encode target) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (reference_step relEnv step)

theorem normalizer_reached (relEnv : Engine.RelationEnv) (context : Maude.VariableContext) (source : Maude.Term)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    Relation.ReflTransGen (ReferenceStep.Step relEnv (language peano))
      (encode source) (encode (Maude.PeanoNormalization.reduce source)) :=
  reference_path relEnv (Maude.PeanoNormalization.reduce_path context source typed)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoSimulation
