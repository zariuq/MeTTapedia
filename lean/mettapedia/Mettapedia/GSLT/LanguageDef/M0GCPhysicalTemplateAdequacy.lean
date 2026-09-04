import Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy
import Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay

/-!
# Physical-table adequacy for M0GC templates

The M0GC runtime stores rule templates as four-field nodes plus a flat child
table.  This module gives that carrier two independent executable readings:

* `decodeTemplate?` reconstructs the logical `SchemaTemplate`; and
* `instantiateFlatTemplate?` substitutes source arguments while walking the
  physical tables directly.

The main theorem proves that direct physical instantiation is exactly logical
decoding followed by ordinary template instantiation.  Hash-consing is not
part of the trusted statement: any shared or unshared table satisfying the
same decoder has the same logical behavior.

Maturity boundary: the four-field node array, flat child array, numeric rule
table, and present fuel discipline are a fully connected physical proof of
concept.  They are not claimed to be an endgame-optimal layout, compression,
cache strategy, or universal NIK wire format.  The decoder and commuting
theorems deliberately isolate the replaceable representation from meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy

/-! ## Decoded physical template carrier -/

/-- The four semantic fields of the generated C `M0TemplateNode`. -/
structure TemplateNode where
  kind : UInt8
  value : UInt16
  arity : UInt16
  childStart : UInt32
deriving DecidableEq, Repr

/-- Flat generated tables consumed by the current proof-of-concept template
walker.  This layout is a concrete correspondence witness, not an optimality
claim; alternative layouts qualify by decoding to the same logical carrier. -/
structure TemplateTables where
  nodes : Array TemplateNode
  children : List UInt32
deriving DecidableEq, Repr

def variableKind : UInt8 := 0

def applicationKind : UInt8 := 1

mutual

/-- Reconstruct one logical template from a physical root.  Fuel bounds
arbitrary or cyclic untrusted tables; generated tables need no trusted
acyclicity assumption. -/
def decodeTemplate? (profile : RuntimeProfile) (tables : TemplateTables) :
    Nat → UInt32 → Option SchemaTemplate
  | 0, _ => none
  | fuel + 1, root => do
      let node ← tables.nodes[root.toNat]?
      if node.kind = variableKind then
        some (.variable node.value.toNat)
      else if node.kind = applicationKind then
        let symbol ← profile.symbols[node.value.toNat]?
        if node.arity = symbol.arity then
          let childRoots ← checkedSlice? tables.children
            node.childStart.toNat node.arity.toNat
          let arguments ← decodeTemplates? profile tables fuel childRoots
          some (.application symbol.name arguments)
        else none
      else none

/-- Reconstruct an ordered physical child vector. -/
def decodeTemplates? (profile : RuntimeProfile) (tables : TemplateTables)
    (fuel : Nat) : List UInt32 → Option (List SchemaTemplate)
  | [] => some []
  | root :: roots => do
      let head ← decodeTemplate? profile tables fuel root
      let tail ← decodeTemplates? profile tables fuel roots
      some (head :: tail)

end

mutual

/-- Direct physical instantiation.  This is the allocating specification of
the generated C matcher's allocation-free comparison loop. -/
def instantiateFlatTemplate? (profile : RuntimeProfile)
    (tables : TemplateTables) (arguments : List Pattern) :
    Nat → UInt32 → Option Pattern
  | 0, _ => none
  | fuel + 1, root => do
      let node ← tables.nodes[root.toNat]?
      if node.kind = variableKind then
        arguments[node.value.toNat]?
      else if node.kind = applicationKind then
        let symbol ← profile.symbols[node.value.toNat]?
        if node.arity = symbol.arity then
          let childRoots ← checkedSlice? tables.children
            node.childStart.toNat node.arity.toNat
          let instantiated ←
            instantiateFlatTemplates? profile tables arguments fuel childRoots
          some (.apply symbol.name instantiated)
        else none
      else none

def instantiateFlatTemplates? (profile : RuntimeProfile)
    (tables : TemplateTables) (arguments : List Pattern) (fuel : Nat) :
    List UInt32 → Option (List Pattern)
  | [] => some []
  | root :: roots => do
      let head ← instantiateFlatTemplate? profile tables arguments fuel root
      let tail ←
        instantiateFlatTemplates? profile tables arguments fuel roots
      some (head :: tail)

end

/-! ## The physical/logical commuting theorem -/

/-- At every fuel bound, direct physical substitution equals reconstruction
of the logical template followed by its independently defined substitution.
The vector statement is retained alongside the root statement because child
order is semantic. -/
theorem instantiateFlat_eq_decode_bind
    (profile : RuntimeProfile) (tables : TemplateTables)
    (arguments : List Pattern) : ∀ fuel,
    (∀ root,
      instantiateFlatTemplate? profile tables arguments fuel root =
        (decodeTemplate? profile tables fuel root).bind
          (instantiateTemplate? arguments)) ∧
    (∀ roots,
      instantiateFlatTemplates? profile tables arguments fuel roots =
        (decodeTemplates? profile tables fuel roots).bind
          (instantiateTemplates? arguments)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro root
        simp [instantiateFlatTemplate?, decodeTemplate?]
      · intro roots
        induction roots with
        | nil => simp [instantiateFlatTemplates?, decodeTemplates?,
            instantiateTemplates?]
        | cons root roots inductionHypothesis =>
            simp [instantiateFlatTemplates?, decodeTemplates?,
              instantiateFlatTemplate?, decodeTemplate?]
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with ⟨rootHypothesis, rootsHypothesis⟩
      have rootStatement : ∀ root,
          instantiateFlatTemplate? profile tables arguments (fuel + 1) root =
            (decodeTemplate? profile tables (fuel + 1) root).bind
              (instantiateTemplate? arguments) := by
        intro root
        simp only [instantiateFlatTemplate?, decodeTemplate?]
        cases nodeEq : tables.nodes[root.toNat]? with
        | none => simp
        | some node =>
            by_cases isVariable : node.kind = variableKind
            · simp [isVariable, instantiateTemplate?]
            · by_cases isApplication : node.kind = applicationKind
              · cases symbolEq : profile.symbols[node.value.toNat]? with
                | none =>
                    simp [isApplication, symbolEq,
                      variableKind, applicationKind]
                | some symbol =>
                    by_cases arityEq : node.arity = symbol.arity
                    · cases childrenEq : checkedSlice? tables.children
                          node.childStart.toNat node.arity.toNat with
                      | none =>
                          have childrenEqSymbol : checkedSlice? tables.children
                              node.childStart.toNat symbol.arity.toNat = none := by
                            simpa [arityEq] using childrenEq
                          simp [isApplication, symbolEq,
                            arityEq, childrenEqSymbol, variableKind,
                            applicationKind]
                      | some childRoots =>
                          have childrenEqSymbol : checkedSlice? tables.children
                              node.childStart.toNat symbol.arity.toNat =
                                some childRoots := by
                            simpa [arityEq] using childrenEq
                          simp [isApplication, symbolEq,
                            arityEq, childrenEqSymbol,
                            rootsHypothesis childRoots, instantiateTemplate?,
                            Option.bind_assoc, variableKind, applicationKind]
                    · simp [isApplication, symbolEq,
                        arityEq, variableKind, applicationKind]
              · simp [isVariable, isApplication]
      have rootsStatement : ∀ roots,
          instantiateFlatTemplates? profile tables arguments (fuel + 1) roots =
            (decodeTemplates? profile tables (fuel + 1) roots).bind
              (instantiateTemplates? arguments) := by
        intro roots
        induction roots with
        | nil => simp [instantiateFlatTemplates?, decodeTemplates?,
            instantiateTemplates?]
        | cons root roots inductionHypothesis =>
            simp only [instantiateFlatTemplates?, decodeTemplates?]
            rw [rootStatement root, inductionHypothesis]
            cases headDecode :
                decodeTemplate? profile tables (fuel + 1) root with
            | none => simp
            | some head =>
                cases tailDecode :
                    decodeTemplates? profile tables (fuel + 1) roots with
                | none => simp
                | some tail =>
                    simp [instantiateTemplates?]
      exact ⟨rootStatement, rootsStatement⟩

theorem instantiateFlatTemplate?_eq_decode_bind
    (profile : RuntimeProfile) (tables : TemplateTables)
    (arguments : List Pattern) (fuel : Nat) (root : UInt32) :
    instantiateFlatTemplate? profile tables arguments fuel root =
      (decodeTemplate? profile tables fuel root).bind
        (instantiateTemplate? arguments) :=
  (instantiateFlat_eq_decode_bind profile tables arguments fuel).1 root

theorem instantiateFlatTemplates?_eq_decode_bind
    (profile : RuntimeProfile) (tables : TemplateTables)
    (arguments : List Pattern) (fuel : Nat) (roots : List UInt32) :
    instantiateFlatTemplates? profile tables arguments fuel roots =
      (decodeTemplates? profile tables fuel roots).bind
        (instantiateTemplates? arguments) :=
  (instantiateFlat_eq_decode_bind profile tables arguments fuel).2 roots

/-- Once a physical root is independently decoded as a logical template, its
direct table-walk result is exactly that template's source substitution. -/
theorem instantiateFlatTemplate?_of_decode
    {profile : RuntimeProfile} {tables : TemplateTables}
    {fuel : Nat} {root : UInt32} {template : SchemaTemplate}
    (decoded : decodeTemplate? profile tables fuel root = some template)
    (arguments : List Pattern) :
    instantiateFlatTemplate? profile tables arguments fuel root =
      instantiateTemplate? arguments template := by
  rw [instantiateFlatTemplate?_eq_decode_bind, decoded]
  rfl

theorem instantiateFlatTemplates?_of_decode
    {profile : RuntimeProfile} {tables : TemplateTables}
    {fuel : Nat} {roots : List UInt32} {templates : List SchemaTemplate}
    (decoded : decodeTemplates? profile tables fuel roots = some templates)
    (arguments : List Pattern) :
    instantiateFlatTemplates? profile tables arguments fuel roots =
      instantiateTemplates? arguments templates := by
  rw [instantiateFlatTemplates?_eq_decode_bind, decoded]
  rfl

/-! ## Generated rule-table adequacy -/

/-- The root-layout fields that complement one generated `RuleProfile`.
Counts, fingerprints, and stable source rule identity remain in the runtime
profile and cannot be selected by certificate bytes. -/
structure RuleLayout where
  premiseStart : UInt32
  conclusion : UInt32
deriving DecidableEq, Repr

/-- Current proof-of-concept rule-root indexing.  In particular, the separate
layout array and premise-root slice are not prescribed as the final runtime
organization. -/
structure RuleTables where
  templates : TemplateTables
  premiseRoots : List UInt32
  layouts : Array RuleLayout
deriving DecidableEq, Repr

/-- Independently reconstruct the logical rule template designated by one
generated physical rule index. -/
def decodeRuleTemplate? (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (ruleIndex : UInt16) : Option RuleTemplate := do
  let rule ← profile.rules[ruleIndex.toNat]?
  let layout ← tables.layouts[ruleIndex.toNat]?
  let premiseRoots ← checkedSlice? tables.premiseRoots
    layout.premiseStart.toNat rule.premiseCount.toNat
  let premises ← decodeTemplates? profile tables.templates fuel premiseRoots
  let conclusion ←
    decodeTemplate? profile tables.templates fuel layout.conclusion
  some
    { ruleId := rule.ruleId
      formalCount := rule.argumentCount.toNat
      premises
      conclusion }

/-- Direct physical rule instantiation.  This has the same ordered template
walk as the generated C replay loop, but returns the reconstructed source
premises and conclusion instead of comparing them in place. -/
def instantiateFlatRule? (profile : RuntimeProfile) (tables : RuleTables)
    (arguments : List Pattern) (fuel : Nat) (ruleIndex : UInt16) :
    Option (List Pattern × Pattern) := do
  let rule ← profile.rules[ruleIndex.toNat]?
  let layout ← tables.layouts[ruleIndex.toNat]?
  if arguments.length = rule.argumentCount.toNat then
    let premiseRoots ← checkedSlice? tables.premiseRoots
      layout.premiseStart.toNat rule.premiseCount.toNat
    let premises ← instantiateFlatTemplates? profile tables.templates
      arguments fuel premiseRoots
    let conclusion ← instantiateFlatTemplate? profile tables.templates
      arguments fuel layout.conclusion
    some (premises, conclusion)
  else none

/-- Successful physical rule decoding makes direct table replay exactly the
ordinary logical `RuleTemplate` instantiator. -/
theorem instantiateFlatRule?_of_decode
    {profile : RuntimeProfile} {tables : RuleTables}
    {fuel : Nat} {ruleIndex : UInt16} {template : RuleTemplate}
    (decoded : decodeRuleTemplate? profile tables fuel ruleIndex =
      some template)
    (arguments : List Pattern) :
    instantiateFlatRule? profile tables arguments fuel ruleIndex =
      template.instantiate? arguments := by
  unfold decodeRuleTemplate? at decoded
  cases ruleEq : profile.rules[ruleIndex.toNat]? with
  | none => simp [ruleEq] at decoded
  | some rule =>
      cases layoutEq : tables.layouts[ruleIndex.toNat]? with
      | none => simp [ruleEq, layoutEq] at decoded
      | some layout =>
          cases rootsEq : checkedSlice? tables.premiseRoots
              layout.premiseStart.toNat rule.premiseCount.toNat with
          | none => simp [ruleEq, layoutEq, rootsEq] at decoded
          | some premiseRoots =>
              cases premisesEq :
                  decodeTemplates? profile tables.templates fuel premiseRoots with
              | none =>
                  simp [ruleEq, layoutEq, rootsEq, premisesEq] at decoded
              | some premises =>
                  cases conclusionEq :
                      decodeTemplate? profile tables.templates fuel
                        layout.conclusion with
                  | none =>
                      simp [ruleEq, layoutEq, conclusionEq] at decoded
                  | some conclusion =>
                      simp [ruleEq, layoutEq, rootsEq, premisesEq,
                        conclusionEq] at decoded
                      subst template
                      unfold instantiateFlatRule? RuleTemplate.instantiate?
                      rw [ruleEq, layoutEq]
                      dsimp
                      by_cases arity :
                          arguments.length = rule.argumentCount.toNat
                      · rw [if_pos arity, rootsEq]
                        dsimp
                        rw [instantiateFlatTemplates?_of_decode premisesEq]
                        rw [instantiateFlatTemplate?_of_decode conclusionEq]
                        rw [if_pos arity]
                      · rw [if_neg arity, if_neg arity]

/-- The complete semantic seam: when the same logical template is obtained
from authored source compilation and from physical rule-table decoding,
direct physical replay equals the ordinary validated source-rule operation. -/
theorem instantiateFlatRule?_eq_source_rule
    {definition : ValidatedCalculusLanguageDef}
    {profile : RuntimeProfile} {tables : RuleTables}
    {fuel : Nat} {ruleIndex : UInt16}
    {rule : RuleSchema} {template : RuleTemplate}
    (sourceCompiled : compileRuleTemplate? rule = some template)
    (physicalDecoded : decodeRuleTemplate? profile tables fuel ruleIndex =
      some template)
    (arguments : List Pattern)
    (lookup : definition.1.lookupRule? rule.id = some rule)
    (argumentsValid :
      argumentsValidAt rule.metavariables arguments = true) :
    instantiateFlatRule? profile tables arguments fuel ruleIndex =
      instantiateRule? definition { ruleId := rule.id, arguments } := by
  rw [instantiateFlatRule?_of_decode physicalDecoded arguments]
  exact RuleTemplate.instantiate_eq_source_rule sourceCompiled arguments
    lookup argumentsValid

/-! ## Nontrivial positive and negative table canaries -/

def canaryProfile : RuntimeProfile :=
  { profileDigest := []
    sourceDigest := []
    symbols :=
      #[ { name := "left", arity := 0 }
       , { name := "right", arity := 0 }
       , { name := "pair", arity := 2 } ]
    rules :=
      #[ { ruleId := ⟨"pair"⟩
           argumentCount := 2
           premiseCount := 0
           fingerprint := 917431 } ] }

def pairTables : TemplateTables :=
  { nodes :=
      #[ { kind := variableKind, value := 0, arity := 0, childStart := 0 }
       , { kind := variableKind, value := 1, arity := 0, childStart := 0 }
       , { kind := applicationKind, value := 2, arity := 2, childStart := 0 } ]
    children := [0, 1] }

def left : Pattern := .apply "left" []

def right : Pattern := .apply "right" []

def pair : Pattern := .apply "pair" [left, right]

theorem pair_root_decodes :
    decodeTemplate? canaryProfile pairTables 2 2 =
      some (.application "pair" [.variable 0, .variable 1]) := by
  simp [decodeTemplate?, decodeTemplates?, canaryProfile, pairTables,
    checkedSlice?, variableKind, applicationKind]

theorem pair_root_instantiates :
    instantiateFlatTemplate? canaryProfile pairTables [left, right] 2 2 =
      some pair := by
  simp [instantiateFlatTemplate?, instantiateFlatTemplates?, canaryProfile,
    pairTables, checkedSlice?, variableKind, applicationKind, left, right,
    pair]

def wrongKindTables : TemplateTables :=
  { pairTables with
    nodes :=
      #[ { kind := variableKind, value := 0, arity := 0, childStart := 0 }
       , { kind := variableKind, value := 1, arity := 0, childStart := 0 }
       , { kind := 7, value := 2, arity := 2, childStart := 0 } ] }

theorem unknown_kind_rejected :
    instantiateFlatTemplate? canaryProfile wrongKindTables [left, right] 2 2 =
      none := by
  simp [instantiateFlatTemplate?, canaryProfile, wrongKindTables, pairTables,
    variableKind, applicationKind]

def truncatedChildrenTables : TemplateTables :=
  { pairTables with children := [0] }

theorem truncated_children_rejected :
    instantiateFlatTemplate? canaryProfile truncatedChildrenTables
      [left, right] 2 2 = none := by
  simp [instantiateFlatTemplate?, canaryProfile, truncatedChildrenTables,
    pairTables, checkedSlice?, variableKind, applicationKind]

theorem insufficient_fuel_rejected :
    instantiateFlatTemplate? canaryProfile pairTables [left, right] 1 2 =
      none := by
  simp [instantiateFlatTemplate?, instantiateFlatTemplates?, canaryProfile,
    pairTables, checkedSlice?, variableKind, applicationKind]

def pairRuleTables : RuleTables :=
  { templates := pairTables
    premiseRoots := []
    layouts := #[{ premiseStart := 0, conclusion := 2 }] }

theorem pair_rule_decodes :
    decodeRuleTemplate? canaryProfile pairRuleTables 2 0 =
      some binaryTemplate := by
  simp [decodeRuleTemplate?, canaryProfile, pairRuleTables, binaryTemplate,
    pairTables, decodeTemplate?, decodeTemplates?, checkedSlice?,
    variableKind, applicationKind]

theorem pair_rule_instantiates_source :
    instantiateFlatRule? canaryProfile pairRuleTables [left, right] 2 0 =
      instantiateRule?
        ⟨binaryDefinition, binaryDefinition_valid⟩
        { ruleId := ⟨"pair"⟩, arguments := [left, right] } := by
  apply instantiateFlatRule?_eq_source_rule compile_binaryRule pair_rule_decodes
  · rfl
  · rfl

theorem wrong_rule_index_rejected :
    instantiateFlatRule? canaryProfile pairRuleTables [left, right] 2 1 =
      none := by
  rfl

theorem wrong_argument_arity_rejected :
    instantiateFlatRule? canaryProfile pairRuleTables [left] 2 0 = none := by
  simp [instantiateFlatRule?, canaryProfile, pairRuleTables]

#print axioms instantiateFlat_eq_decode_bind
#print axioms instantiateFlatTemplate?_of_decode
#print axioms instantiateFlatRule?_of_decode
#print axioms instantiateFlatRule?_eq_source_rule
#print axioms pair_root_decodes
#print axioms pair_root_instantiates
#print axioms unknown_kind_rejected
#print axioms truncated_children_rejected
#print axioms insufficient_fuel_rejected
#print axioms pair_rule_decodes
#print axioms pair_rule_instantiates_source
#print axioms wrong_rule_index_rejected
#print axioms wrong_argument_arity_rejected

end Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
