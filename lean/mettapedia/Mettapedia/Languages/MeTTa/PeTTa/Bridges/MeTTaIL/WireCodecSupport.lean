import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodeSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RulePlanWire

/-! Uniform support laws for authored wire codecs. Constructor and variable
names are literal payloads. Their contents cannot introduce evaluation heads
into the encoded plan. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodecSupport

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open WireCodeSupport

def tags : List String :=
  ["Var","FVar","PApp","PLam","PMultiLam","PSubst","PCollection","BSome","RSome","LCons",
    "TBase","TArrow","TMultiBinder","TCollection","TermSimple","TermAbstraction","TermMultiAbstraction",
    "GrammarTypingV1","GrammarTypingWrappedV1","RulePremise","RuleOccurrence","RuleDependency","RuleBindingSpec","RuleBindingSome",
    "TypeBinding","Freshness","Congruence","ScopedStep","RelationQuery","ForAll","ScopedRewriteRuleV1",
    "BindingInferredGrammar","RuleBindingPlan","RuleJobDeclaration"]

def Supported (allowed : String → Bool) : Prop := ∀ tag ∈ tags, allowed tag = true

private theorem tag_static : ∀ tag ∈ tags, tag ≠ "eval" ∧ tag ≠ "unique" := by decide +kernel

theorem app (allowed : String → Bool) (supported : Supported allowed)
    (head : String) (member : head ∈ tags) (arguments : List Term)
    (children : checkMany allowed arguments = true) : check allowed (.application head arguments) = true :=
  check_application allowed head arguments (by
    have static := tag_static head member
    simp [Eval.expressionHeadWithin, supported head member, static.1, static.2]) children

theorem binder (allowed : String → Bool) (supported : Supported allowed) (value : Option String) :
    check allowed (encodeBinder value) = true := by
  cases value with
  | none => rfl
  | some name => exact app allowed supported "BSome" (by decide) _ rfl

theorem rest (allowed : String → Bool) (supported : Supported allowed) (value : Option String) :
    check allowed (encodeRest value) = true := by
  cases value with
  | none => rfl
  | some name => exact app allowed supported "RSome" (by decide) _ rfl

theorem collectionType (allowed : String → Bool) (kind : CollType) :
    check allowed (encodeCollectionType kind) = true := by cases kind <;> rfl

mutual
  theorem pattern (allowed : String → Bool) (supported : Supported allowed) (value : Pattern) :
      check allowed (encodePattern value) = true := by
    cases value with
    | bvar index =>
      rw [encodePattern]
      exact app allowed supported "Var" (by decide) [.natural index] rfl
    | fvar name =>
      rw [encodePattern]
      exact app allowed supported "FVar" (by decide) [.string name] rfl
    | apply head arguments =>
      rw [encodePattern]
      apply app allowed supported "PApp" (by decide)
      simp only [checkMany,check_string,Bool.and_true,patterns allowed supported arguments]
    | lambda name body =>
      rw [encodePattern]
      apply app allowed supported "PLam" (by decide)
      simp only [checkMany,binder allowed supported,pattern allowed supported body,Bool.true_and]
    | multiLambda arity names body =>
      rw [encodePattern]
      apply app allowed supported "PMultiLam" (by decide)
      have namesValid := check_encodeList allowed Term.string (supported "LCons" (by decide)) names
        (fun _ _ => rfl)
      simpa only [checkMany,check_natural,Bool.true_and,Bool.and_true,
        pattern allowed supported body,InferenceCettaWire.encodeList,CettaTerm.string] using namesValid
    | subst body replacement =>
      rw [encodePattern]
      apply app allowed supported "PSubst" (by decide)
      simp only [checkMany,pattern allowed supported body,pattern allowed supported replacement,Bool.true_and]
    | collection kind elements tail =>
      rw [encodePattern]
      apply app allowed supported "PCollection" (by decide)
      simp only [checkMany,collectionType,patterns allowed supported elements,rest allowed supported tail,Bool.true_and]
  termination_by sizeOf value
  decreasing_by all_goals simp_all <;> omega

  theorem patterns (allowed : String → Bool) (supported : Supported allowed) (values : List Pattern) :
      check allowed (encodePatterns values) = true := by
    cases values with
    | nil => rw [encodePatterns]; rfl
    | cons first tail =>
      rw [encodePatterns]
      apply app allowed supported "LCons" (by decide)
      simp only [checkMany,pattern allowed supported first,patterns allowed supported tail,Bool.true_and]
  termination_by sizeOf values
  decreasing_by all_goals simp_all <;> omega
end

theorem type (allowed : String → Bool) (supported : Supported allowed) (value : TypeExpr) :
    check allowed (AuthoredRule.typeTerm value) = true := by
  induction value with
  | base name => exact app allowed supported "TBase" (by decide) _ rfl
  | arrow domain codomain hd hc =>
    apply app allowed supported "TArrow" (by decide)
    simp only [checkMany,hd,hc,Bool.true_and]
  | multiBinder body ih =>
    apply app allowed supported "TMultiBinder" (by decide)
    simp only [checkMany,ih,Bool.true_and]
  | collection kind element ih =>
    apply app allowed supported "TCollection" (by decide)
    simp only [checkMany,collectionType,ih,Bool.true_and]

theorem parameter (allowed : String → Bool) (supported : Supported allowed) (value : TermParam) :
    check allowed (AuthoredRule.parameterTerm value) = true := by
  cases value with
  | simple name sort =>
    apply app allowed supported "TermSimple" (by decide)
    simp only [checkMany,check_string,type allowed supported sort,Bool.true_and]
  | abstractionNamed name body sort =>
    apply app allowed supported "TermAbstraction" (by decide)
    simp only [checkMany,binder allowed supported name,check_string,type allowed supported sort,Bool.true_and]
  | multiAbstractionNamed names body sort =>
    apply app allowed supported "TermMultiAbstraction" (by decide)
    have namesValid := check_encodeList allowed Term.string (supported "LCons" (by decide)) names (fun _ _ => rfl)
    simpa only [checkMany,check_string,type allowed supported sort,Bool.true_and,Bool.and_true,
      InferenceCettaWire.encodeList,CettaTerm.string] using namesValid

theorem site (allowed : String → Bool) (supported : Supported allowed) (value : RulePatternSite) :
    check allowed (AuthoredRule.siteTerm value) = true := by
  cases value with
  | left => rfl
  | right => rfl
  | premise index quantifiers argument =>
    exact app allowed supported "RulePremise" (by decide)
      [.natural index,.natural quantifiers,.natural argument] rfl

theorem occurrence (allowed : String → Bool) (supported : Supported allowed) (value : MetavariableOccurrence) :
    check allowed (AuthoredRule.occurrenceTerm value) = true := by
  apply app allowed supported "RuleOccurrence" (by decide)
  have pathValid := check_encodeList allowed Term.natural (supported "LCons" (by decide)) value.path (fun _ _ => rfl)
  simpa only [checkMany,check_string,site allowed supported value.site,patterns allowed supported value.arguments,
    Bool.true_and,Bool.and_true,InferenceCettaWire.encodeList,CettaTerm.natural] using pathValid

theorem dependency (allowed : String → Bool) (supported : Supported allowed) (value : String × List TypeExpr) :
    check allowed (AuthoredRule.dependencyTerm value) = true := by
  apply app allowed supported "RuleDependency" (by decide)
  have sortsValid := check_encodeList allowed AuthoredRule.typeTerm (supported "LCons" (by decide)) value.2
    (fun sort _ => type allowed supported sort)
  simpa only [checkMany,check_string,Bool.true_and,Bool.and_true,InferenceCettaWire.encodeList] using sortsValid

theorem bindingSpec (allowed : String → Bool) (supported : Supported allowed) (value : RuleBindingSpec) :
    check allowed (AuthoredRule.bindingSpecTerm value) = true := by
  apply app allowed supported "RuleBindingSpec" (by decide)
  have dependencies := check_encodeList allowed AuthoredRule.dependencyTerm (supported "LCons" (by decide))
    value.dependencies (fun item _ => dependency allowed supported item)
  have occurrences := check_encodeList allowed AuthoredRule.occurrenceTerm (supported "LCons" (by decide))
    value.occurrences (fun item _ => occurrence allowed supported item)
  simp only [checkMany,InferenceCettaWire.encodeList,dependencies,occurrences,Bool.true_and]

theorem optionalBinding (allowed : String → Bool) (supported : Supported allowed) (value : Option RuleBindingSpec) :
    check allowed (AuthoredRule.optionalBindingTerm value) = true := by
  cases value with
  | none => rfl
  | some specification =>
    apply app allowed supported "RuleBindingSome" (by decide)
    simp only [checkMany,bindingSpec allowed supported specification,Bool.true_and]

theorem typeBinding (allowed : String → Bool) (supported : Supported allowed) (value : String × TypeExpr) :
    check allowed (AuthoredRule.typeBindingTerm value) = true := by
  apply app allowed supported "TypeBinding" (by decide)
  simp only [checkMany,check_string,type allowed supported value.2,Bool.true_and]

theorem premise (allowed : String → Bool) (supported : Supported allowed) (value : Premise) :
    check allowed (AuthoredRule.premiseTerm value) = true := by
  induction value with
  | freshness condition =>
    apply app allowed supported "Freshness" (by decide)
    simp only [checkMany,check_string,pattern allowed supported condition.term,Bool.true_and]
  | congruence source target =>
    apply app allowed supported "Congruence" (by decide)
    simp only [checkMany,pattern allowed supported source,pattern allowed supported target,Bool.true_and]
  | scopedStep step =>
    apply app allowed supported "ScopedStep" (by decide)
    have bindersValid := check_encodeList allowed AuthoredRule.typeTerm (supported "LCons" (by decide)) step.binders
      (fun sort _ => type allowed supported sort)
    simpa only [checkMany,type allowed supported step.resultType,pattern allowed supported step.source,
      pattern allowed supported step.target,Bool.true_and,Bool.and_true,InferenceCettaWire.encodeList] using bindersValid
  | relationQuery name arguments =>
    apply app allowed supported "RelationQuery" (by decide)
    simp only [checkMany,check_string,patterns allowed supported arguments,Bool.true_and]
  | forAll collection parameter body ih =>
    apply app allowed supported "ForAll" (by decide)
    simp only [checkMany,check_string,ih,Bool.true_and]

theorem rewrite (allowed : String → Bool) (supported : Supported allowed) (value : RewriteRule) :
    check allowed (AuthoredRule.rewriteTerm value) = true := by
  apply app allowed supported "ScopedRewriteRuleV1" (by decide)
  have context := check_encodeList allowed AuthoredRule.typeBindingTerm (supported "LCons" (by decide)) value.typeContext
    (fun item _ => typeBinding allowed supported item)
  have premises := check_encodeList allowed AuthoredRule.premiseTerm (supported "LCons" (by decide)) value.premises
    (fun item _ => premise allowed supported item)
  simp only [checkMany,check_string,InferenceCettaWire.encodeList,context,premises,
    pattern allowed supported value.left,pattern allowed supported value.right,optionalBinding allowed supported value.bindings,
    Bool.true_and]

theorem typingDeclaration (allowed : String → Bool) (supported : Supported allowed) (value : GrammarRule) :
    check allowed (AuthoredRule.typingDeclarationTerm value) = true := by
  have parameters := check_encodeList allowed AuthoredRule.parameterTerm (supported "LCons" (by decide))
    value.params (fun item _ => parameter allowed supported item)
  cases representation : value.collectionRepresentation with
  | bare =>
    simp only [AuthoredRule.typingDeclarationTerm,representation]
    apply app allowed supported "GrammarTypingV1" (by decide)
    simpa only [checkMany,check_string,Bool.true_and,Bool.and_true,InferenceCettaWire.encodeList] using parameters
  | wrapped =>
    simp only [AuthoredRule.typingDeclarationTerm,representation]
    apply app allowed supported "GrammarTypingWrappedV1" (by decide)
    simpa only [checkMany,check_string,Bool.true_and,Bool.and_true,InferenceCettaWire.encodeList] using parameters

theorem origin (allowed : String → Bool) (supported : Supported allowed)
    (value : Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.Origin) :
    check allowed (ScopedRuleJobReadoutExecution.originTerm value) = true := by
  cases value with
  | authored => rfl
  | inferredRootInputs => rfl
  | inferredGrammar implicitTypes =>
    apply app allowed supported "BindingInferredGrammar" (by decide)
    have types := check_encodeList allowed AuthoredRule.typeBindingTerm (supported "LCons" (by decide)) implicitTypes
      (fun item _ => typeBinding allowed supported item)
    simpa only [checkMany,Bool.and_true] using types

theorem bindingPlan (allowed : String → Bool) (supported : Supported allowed)
    (value : Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.BindingPlan) :
    check allowed (ScopedRuleJobReadoutExecution.bindingPlanTerm value) = true := by
  apply app allowed supported "RuleBindingPlan" (by decide)
  simp only [checkMany,bindingSpec allowed supported value.spec,origin allowed supported value.origin,Bool.true_and]

theorem rulePlan (allowed : String → Bool) (supported : Supported allowed)
    (value : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.RulePlan) :
    check allowed (ScopedRuleJobReadoutExecution.rulePlanTerm value) = true := by
  apply app allowed supported "RuleJobDeclaration" (by decide)
  simp only [checkMany,check_natural,rewrite allowed supported value.authored,bindingPlan allowed supported value.binding,
    Bool.true_and]

#print axioms rulePlan

#print axioms rewrite

#print axioms pattern
#print axioms type

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodecSupport
