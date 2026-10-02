import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.SchemaVariables
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Validating premise-free binder-free rules by evaluation

`LanguageDef.validate` reads the metavariables and binder names of a rule
through functions defined by well-founded recursion, which the kernel does
not unfold on a literal rule.  For a rule that carries no premise and whose
two sides contain no binder, the same conditions can be stated with
structurally recursive functions alone.

This module states them as two tests, one for an equation and one for a
rewrite, and proves that a rule passing its test passes the corresponding row
of the declaration gate.  A third test covers the ordered binding-flow gate.
A language whose rules are generated from a table can then be validated by
evaluating the tests on the generated list, with no rule-by-rule argument.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.Match

namespace LanguageDef

/-- Every member of a list passing the list form of the binder-free test
passes the test. -/
theorem binderFree_of_mem_binderFreeList :
    ∀ {patterns : List Pattern}, binderFreeList patterns = true →
      ∀ pattern ∈ patterns, binderFree pattern = true
  | [], _, _, membership => by cases membership
  | head :: tail, free, pattern, membership => by
      simp only [binderFreeList, Bool.and_eq_true] at free
      rcases List.mem_cons.mp membership with rfl | inTail
      · exact free.1
      · exact binderFree_of_mem_binderFreeList free.2 pattern inTail

/-- A pattern with no binding former introduces no binder name. -/
theorem patternBinderNames_eq_nil_of_binderFree (pattern : Pattern)
    (free : binderFree pattern = true) : patternBinderNames pattern = [] := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [patternBinderNames]
  | hfvar name => simp [patternBinderNames]
  | happly constructor arguments recurse =>
      simp only [binderFree] at free
      simp only [patternBinderNames, List.flatMap_eq_nil_iff]
      rintro ⟨argument, membership⟩ -
      exact recurse argument membership
        (binderFree_of_mem_binderFreeList free argument membership)
  | hlambda binderName body _ => simp [binderFree] at free
  | hmultiLambda arity binderNames body _ => simp [binderFree] at free
  | hsubst body replacement _ _ => simp [binderFree] at free
  | hcollection collectionType elements rest recurse =>
      simp only [binderFree] at free
      simp only [patternBinderNames, List.flatMap_eq_nil_iff]
      rintro ⟨element, membership⟩ -
      exact recurse element membership
        (binderFree_of_mem_binderFreeList free element membership)

/-- With no bound name to exclude, the metavariables of a rule side are its
schema variables. -/
theorem patternFvarNames_nil (pattern : Pattern) :
    patternFvarNames [] pattern = pattern.schemaVariables := by
  simp [patternFvarNames, Pattern.schemaVariables_eq_freeFvarNames]

/-- The scope and naming conditions of a premise-free rule between
binder-free sides, as a test the kernel evaluates. -/
def plainRulePatternsOk (labels : List String)
    (typeContext : List (String × TypeExpr)) (left right : Pattern) : Bool :=
  left.isWellScoped && right.isWellScoped && binderFree left && binderFree right &&
    (left.schemaVariables ++ right.schemaVariables).all (fun name => !labels.contains name) &&
    typeContext.all (fun entry => !labels.contains entry.1) &&
    right.schemaVariables.all (fun name => left.schemaVariables.contains name)

/-- A rule passing the test has no scope, naming or dangling-variable error. -/
theorem validateRulePatterns_eq_nil_of_plainRulePatternsOk
    {labels : List String} {typeContext : List (String × TypeExpr)}
    {left right : Pattern}
    (ok : plainRulePatternsOk labels typeContext left right = true) (context : String) :
    validateRulePatterns context labels typeContext [] left right = [] := by
  simp only [plainRulePatternsOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.mem_append] at ok
  obtain ⟨⟨⟨⟨⟨⟨leftScoped, rightScoped⟩, leftFree⟩, rightFree⟩, noCollision⟩, contextClean⟩,
    bound⟩ := ok
  unfold validateRulePatterns
  simp only [List.flatMap_nil, List.append_nil, List.all_nil,
    patternFvarNames_nil, patternBinderNames_eq_nil_of_binderFree left leftFree,
    patternBinderNames_eq_nil_of_binderFree right rightFree, leftScoped, rightScoped,
    Bool.and_self, if_true, List.nil_append, List.append_eq_nil_iff,
    List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro name membership
    have listed := List.mem_eraseDups.mp membership
    rw [noCollision name (List.mem_append.mp listed)]
    rfl
  · intro name membership
    simp at membership
  · rintro ⟨name, type⟩ membership
    have clean := contextClean (name, type) membership
    simp only [clean, Bool.false_eq_true, if_false]
  · intro name membership
    have listed := List.mem_eraseDups.mp membership
    have inLeft := bound name listed
    simp only [inLeft, Bool.true_or, if_true]

/-- The declaration-gate row of a premise-free equation between binder-free
sides, as a test the kernel evaluates. -/
def plainEquationOk (lang : LanguageDef) (equation : Equation) : Bool :=
  equation.premises.isEmpty &&
    equation.typeContext.all (fun entry =>
      entry.2.baseNames.all fun typeName => lang.typeNames.contains typeName) &&
    equation.left.constructorRefs.all (referenceDeclared lang.terms) &&
    equation.right.constructorRefs.all (referenceDeclared lang.terms) &&
    plainRulePatternsOk (lang.terms.map (·.label)) equation.typeContext
      equation.left equation.right

/-- An equation passing the test validates. -/
theorem validateEquation_eq_nil_of_plainEquationOk {lang : LanguageDef}
    {equation : Equation} (ok : plainEquationOk lang equation = true) :
    validateEquation lang equation = [] := by
  simp only [plainEquationOk, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff,
    List.contains_iff_mem] at ok
  obtain ⟨⟨⟨⟨premiseFree, types⟩, leftDeclared⟩, rightDeclared⟩, patterns⟩ := ok
  exact validateEquation_eq_nil_of_premiseFree lang equation premiseFree
    (fun entry membership typeName inType => types entry membership typeName inType)
    leftDeclared rightDeclared
    (validateRulePatterns_eq_nil_of_plainRulePatternsOk patterns)

/-- The declaration-gate row of a premise-free rewrite between binder-free
sides, as a test the kernel evaluates. -/
def plainRewriteOk (lang : LanguageDef) (rewrite : RewriteRule) : Bool :=
  rewrite.premises.isEmpty &&
    rewrite.typeContext.all (fun entry =>
      entry.2.baseNames.all fun typeName => lang.typeNames.contains typeName) &&
    rewrite.left.constructorRefs.all (referenceDeclared lang.terms) &&
    rewrite.right.constructorRefs.all (referenceDeclared lang.terms) &&
    plainRulePatternsOk (lang.terms.map (·.label)) rewrite.typeContext
      rewrite.left rewrite.right

/-- A rewrite passing the test validates. -/
theorem validateRewrite_eq_nil_of_plainRewriteOk {lang : LanguageDef}
    {rewrite : RewriteRule} (ok : plainRewriteOk lang rewrite = true) :
    validateRewrite lang rewrite = [] := by
  simp only [plainRewriteOk, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff,
    List.contains_iff_mem] at ok
  obtain ⟨⟨⟨⟨premiseFree, types⟩, leftDeclared⟩, rightDeclared⟩, patterns⟩ := ok
  exact validateRewrite_eq_nil_of_premiseFree lang rewrite premiseFree
    (fun entry membership typeName inType => types entry membership typeName inType)
    leftDeclared rightDeclared
    (validateRulePatterns_eq_nil_of_plainRulePatternsOk patterns)

/-- The binding-flow conditions of a language whose rules and equations
carry no premise: a rewrite binds every variable of its right side on its
left, and an equation has the same variables on both sides. -/
def plainFlowOk (lang : LanguageDef) : Bool :=
  lang.rewrites.all (fun rewrite =>
      rewrite.premises.isEmpty &&
        rewrite.right.schemaVariables.all fun name =>
          rewrite.left.schemaVariables.contains name) &&
    lang.equations.all (fun equation =>
      equation.premises.isEmpty &&
        (equation.right.schemaVariables.all fun name =>
          equation.left.schemaVariables.contains name) &&
        equation.left.schemaVariables.all fun name =>
          equation.right.schemaVariables.contains name)

/-- A language passing the flow test passes the ordered binding-flow gate
under every relation-mode table. -/
theorem executionFlowErrors_eq_nil_of_plainFlowOk {lang : LanguageDef}
    (ok : plainFlowOk lang = true) (modes : RelationModeTable) :
    lang.executionFlowErrors modes = [] := by
  simp only [plainFlowOk, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff,
    List.contains_iff_mem, Pattern.schemaVariables_eq_freeFvarNames] at ok
  obtain ⟨rewrites, equations⟩ := ok
  exact executionFlowErrors_eq_nil_of_premiseFree_withEquations lang modes
    (fun rule membership => (rewrites rule membership).1)
    (fun rule membership name inRight => (rewrites rule membership).2 name inRight)
    (fun equation membership => (equations equation membership).1.1)
    (fun equation membership name inRight => (equations equation membership).1.2 name inRight)
    (fun equation membership name inLeft => (equations equation membership).2 name inLeft)

end LanguageDef

end Mettapedia.OSLF.MeTTaIL.Syntax
