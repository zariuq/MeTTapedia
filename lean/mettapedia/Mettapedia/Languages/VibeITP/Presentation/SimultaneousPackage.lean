import Mettapedia.Languages.VibeITP.Presentation.SimultaneousRules
import Mettapedia.GSLT.LanguageDef.GroundFactExtension

/-! Concrete validated v2 packages for arbitrary finite theory tables.
The original constructor vocabulary and theory-fact identifier namespaces are
retained. Validation authenticates the package's structure; hosted-theory and
per-rule semantic proofs supply its separate logical interpretation. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.GroundFactExtension
open Spec

def definitionV2 (T : Theory) (allocated : Nat) : CalculusLanguageDef :=
  { fixedDefinitionV2 with rules := (rulesV2 ++ theoryRules T allocated).map FORule.toSchema }

theorem constructor_refines_v2 :
    ConstructorArityRefines kernelDefinition.toLanguageDef fixedDefinitionV2.toLanguageDef :=
  fun {_ _} accepted => accepted

theorem judgment_valid_v2 (head : String) (arguments : List Pattern)
    (known : (fixedDefinitionV2.lookupJudgment? head arguments.length).isSome = true)
    (valid : ∀ argument ∈ arguments, KernelDataValid argument) :
    fixedDefinitionV2.judgmentSchemaValid (.apply head arguments) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨known,
    fixedConstructorListsValid_of_refines constructor_refines_v2 arguments (kernelDataList_valid arguments valid)⟩

theorem closedRule_validIn_v2 (id : String) (nonempty : id ≠ "") {goal : Pattern}
    (data : IsData goal) (valid : fixedDefinitionV2.judgmentSchemaValid goal = true) :
    RuleSchema.isValidIn fixedDefinitionV2 (mkRule id [] [] goal).toSchema = true := by
  simp only [RuleSchema.isValidIn, closedRule_locallyValid id nonempty data, Bool.true_and]
  simpa [FORule.toSchema, FORule.formals, mkRule, RuleSchema.patterns] using valid

theorem theoryRule_validIn_v2 (T : Theory) (allocated : Nat) {rule : FORule}
    (member : rule ∈ theoryRules T allocated) : RuleSchema.isValidIn fixedDefinitionV2 rule.toSchema = true := by
  simp only [theoryRules, List.mem_append] at member
  rcases member with (symbol | admitted) | definition
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp symbol
    apply closedRule_validIn_v2 _ (by simp [symbolRuleId]) (IsData.app1 _ (isData_encSym T.sig _))
    exact judgment_valid_v2 "VSymDecl" [_]
      (by change (fixedDefinitionV2.lookupJudgment? "VSymDecl" 1).isSome = true; decide +kernel)
      (by simp [kernelData_encSym])
  · obtain ⟨index, statement, _, rfl⟩ := mem_axiomRules admitted
    apply closedRule_validIn_v2 _ (by simp [axiomRuleId]) (IsData.app1 _ (isData_encTerm T.sig _))
    exact judgment_valid_v2 "VThm" [_]
      (by change (fixedDefinitionV2.lookupJudgment? "VThm" 1).isSome = true; decide +kernel)
      (by simp [kernelData_encTerm])
  · obtain ⟨index, declaration, _, rfl⟩ := mem_theoryDefinitionRules definition
    apply closedRule_validIn_v2 _ (by simp [definitionRuleId]) (IsData.app1 _ (isData_encTerm T.sig _))
    exact judgment_valid_v2 "VThm" [_]
      (by change (fixedDefinitionV2.lookupJudgment? "VThm" 1).isSome = true; decide +kernel)
      (by simp [kernelData_encTerm])

set_option maxRecDepth 100000 in
theorem rulesV2_ids_nodup : (rulesV2.map FORule.id).Nodup := by decide +kernel

private theorem newRule_id_ne_prefixed (stem : String)
    (checked : simultaneousRules.all (fun rule =>
      decide (rule.id.toList.take stem.toList.length ≠ stem.toList)) = true)
    {rule : FORule} (member : rule ∈ simultaneousRules) (suffix : String) : rule.id ≠ stem ++ suffix := by
  intro same
  have front := congrArg (fun text : String => text.toList.take stem.toList.length) same
  simp only [String.toList_append, List.take_left] at front
  exact of_decide_eq_true (List.all_eq_true.mp checked rule member) front

theorem rule_id_ne_symbol {rule : FORule} (member : rule ∈ rulesV2) (index : Nat) :
    rule.id ≠ symbolRuleId index := by
  rcases List.mem_append.mp member with old | added
  · exact kernelRule_id_ne_symbolRuleId old index
  · exact newRule_id_ne_prefixed "vibe-symbol-" (by decide +kernel) added _

theorem rule_id_ne_axiom {rule : FORule} (member : rule ∈ rulesV2) (index : Nat) :
    rule.id ≠ axiomRuleId index := by
  rcases List.mem_append.mp member with old | added
  · exact kernelRule_id_ne_axiomRuleId old index
  · exact newRule_id_ne_prefixed "vibe-axiom-" (by decide +kernel) added _

theorem rule_id_ne_definition {rule : FORule} (member : rule ∈ rulesV2) (index : Nat) :
    rule.id ≠ definitionRuleId index := by
  rcases List.mem_append.mp member with old | added
  · exact kernelRule_id_ne_definitionRuleId old index
  · exact newRule_id_ne_prefixed "vibe-definition-" (by decide +kernel) added _

theorem rulesAndTheoryV2_ids_nodup (T : Theory) (allocated : Nat) :
    ((rulesV2 ++ theoryRules T allocated).map FORule.id).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨rulesV2_ids_nodup, theoryRules_ids_nodup T allocated, ?_⟩
  intro id left other right
  obtain ⟨rule, member, rfl⟩ := List.mem_map.mp left
  obtain ⟨fact, supplied, rfl⟩ := List.mem_map.mp right
  simp only [theoryRules, List.mem_append] at supplied
  rcases supplied with (symbol | admitted) | definition
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp symbol
    exact rule_id_ne_symbol member _
  · obtain ⟨index, statement, _, rfl⟩ := mem_axiomRules admitted
    exact rule_id_ne_axiom member _
  · obtain ⟨index, declaration, _, rfl⟩ := mem_theoryDefinitionRules definition
    exact rule_id_ne_definition member _

theorem definitionV2_valid (T : Theory) (allocated : Nat) : (definitionV2 T allocated).isValid = true := by
  have fixed := fixedDefinitionV2_valid
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules, Bool.and_eq_true] at fixed
  obtain ⟨⟨⟨⟨⟨language, localRules⟩, _⟩, signature⟩, rules⟩, conversion⟩ := fixed
  have distinct : (definitionV2 T allocated).ruleIds.Nodup := by
    change (((rulesV2 ++ theoryRules T allocated).map FORule.toSchema).map RuleSchema.id).Nodup
    simpa only [List.map_map, FORule.toSchema, Function.comp_def] using
      (rulesAndTheoryV2_ids_nodup T allocated).map (f := fun id => (⟨id⟩ : RuleId))
        (fun _ _ same => RuleId.mk.inj same)
  have localFacts : (theoryRules T allocated).all (fun rule => RuleSchema.isLocallyValid rule.toSchema) = true :=
    List.all_eq_true.mpr (fun rule member => theoryRule_locallyValid T allocated member)
  have validFacts : (theoryRules T allocated).all (fun rule => RuleSchema.isValidIn fixedDefinitionV2 rule.toSchema) = true :=
    List.all_eq_true.mpr (fun rule member => theoryRule_validIn_v2 T allocated member)
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨language, ?_⟩, ?_⟩, signature⟩, ?_⟩, conversion⟩
  · change ((rulesV2 ++ theoryRules T allocated).map FORule.toSchema).all RuleSchema.isLocallyValid = true
    rw [List.map_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr ⟨localRules, by simpa only [List.all_map, Function.comp_def] using localFacts⟩
  · exact (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr distinct
  · change ((rulesV2 ++ theoryRules T allocated).map FORule.toSchema).all (RuleSchema.isValidIn (definitionV2 T allocated)) = true
    have context (rule : RuleSchema) : RuleSchema.isValidIn (definitionV2 T allocated) rule =
        RuleSchema.isValidIn fixedDefinitionV2 rule := rfl
    rw [funext context, List.map_append, List.all_append]
    exact Bool.and_eq_true_iff.mpr ⟨rules, by simpa only [List.all_map, Function.comp_def] using validFacts⟩

def validatedV2 (T : Theory) (allocated : Nat) : ValidatedCalculusLanguageDef :=
  ⟨definitionV2 T allocated, definitionV2_valid T allocated⟩

theorem validatedV2_presents (T : Theory) (allocated : Nat) :
    Presents (validatedV2 T allocated) (rulesV2 ++ theoryRules T allocated) :=
  ⟨rulesV2_foPackage.append (theoryRules_foPackage T allocated), rfl⟩

#print axioms definitionV2_valid

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
