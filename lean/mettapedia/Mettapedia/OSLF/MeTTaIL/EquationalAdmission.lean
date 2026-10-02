import Mettapedia.OSLF.MeTTaIL.FlowAdmission

/-!
# Admission of a language with equations and concrete notation

Two gates stand between an authored definition and its use: the declaration
gate and the ordered binding-flow gate.  For a language with concrete
notation, authored equations and contextual rules, this module reduces each
gate to conditions on the rows of the definition.

* The declaration gate passes when the four name families are free of
  duplicates, every constructor returns and mentions declared sorts, the
  notation of every constructor uses only literals and its own parameters,
  and every equation and rewrite row validates.
* The binding-flow gate passes when every rewrite has one of the two shapes
  of a calculus with contextual reduction and every equation, read in either
  direction, binds what it reads: it carries no premise and its two sides
  have the same variables.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

namespace LanguageDef

/-- The declaration gate, row by row, for a language with concrete notation
and authored equations. -/
theorem validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
    (lang : LanguageDef)
    (htypes : lang.typeNames.Nodup)
    (hconstructors : (lang.terms.map (·.label)).Nodup)
    (hequations : (lang.equations.map (·.name)).Nodup)
    (hrewrites : (lang.rewrites.map (·.name)).Nodup)
    (hcategory : ∀ term ∈ lang.terms, term.category ∈ lang.typeNames)
    (hparams : ∀ term ∈ lang.terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ lang.typeNames)
    (hsyntax : concreteSyntaxRowsValid lang = true)
    (hequationValid : ∀ equation ∈ lang.equations,
      validateEquation lang equation = [])
    (hrewriteValid : ∀ rewrite ∈ lang.rewrites,
      validateRewrite lang rewrite = []) :
    lang.validate = [] := by
  apply validate_eq_nil_of_rows lang htypes hconstructors hequations hrewrites _
    hequationValid hrewriteValid
  intro term hterm
  simp only [validateTerm, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
  refine ⟨⟨by simp [hcategory term hterm], ?_⟩, ?_⟩
  · intro param hparam
    apply validateTypeExpr_eq_nil_of_baseNames
    exact hparams term hterm param hparam
  · apply validateSyntaxPattern_terminalsAndBoundNonTerminals
    intro item hitem
    unfold concreteSyntaxRowsValid at hsyntax
    simp only [List.all_eq_true] at hsyntax
    have itemSyntax := hsyntax term hterm item hitem
    cases item with
    | terminal _ => trivial
    | nonTerminal _ =>
        simp [concreteSyntaxItemAllowed] at itemSyntax
        simpa only [List.mem_flatMap, List.mem_cons] using itemSyntax
    | separator _ => trivial
    | delimiter _ _ => trivial
    | op _ => simp [concreteSyntaxItemAllowed] at itemSyntax

/-- An equation passes the binding-flow gate in both directions: it carries
no premise and its two sides have the same variables. -/
structure EquationFlows (equation : Equation) : Prop where
  premiseFree : equation.premises = []
  rightBound : ∀ name ∈ equation.right.freeFvarNames, name ∈ equation.left.freeFvarNames
  leftBound : ∀ name ∈ equation.left.freeFvarNames, name ∈ equation.right.freeFvarNames

/-- **Flow admission by shape, with equations.**  A language whose every
rewrite has one of the two rule shapes and whose every equation binds what it
reads in both directions passes the binding-flow gate. -/
theorem executionFlowErrors_eq_nil_of_ruleAndEquationFlows (lang : LanguageDef)
    (modes : RelationModeTable)
    (rules : ∀ rule ∈ lang.rewrites, RuleFlows rule)
    (equations : ∀ equation ∈ lang.equations, EquationFlows equation) :
    lang.executionFlowErrors modes = [] := by
  unfold executionFlowErrors
  rw [List.append_eq_nil_iff]
  constructor
  · apply List.flatMap_eq_nil_iff.mpr
    intro rule membership
    exact directedRuleFlowErrors_eq_nil_of_ruleFlows modes _ (rules rule membership)
  · apply List.flatMap_eq_nil_iff.mpr
    intro equation membership
    have flows := equations equation membership
    rw [List.append_eq_nil_iff]
    constructor
    · exact directedRuleFlowErrors_eq_nil_of_ruleFlows modes _
        (rule := { name := equation.name, typeContext := equation.typeContext,
                   premises := equation.premises, left := equation.left,
                   right := equation.right })
        (.plain flows.premiseFree flows.rightBound)
    · exact directedRuleFlowErrors_eq_nil_of_ruleFlows modes _
        (rule := { name := equation.name, typeContext := equation.typeContext,
                   premises := equation.premises, left := equation.right,
                   right := equation.left })
        (.plain flows.premiseFree flows.leftBound)

end LanguageDef

end Mettapedia.OSLF.MeTTaIL.Syntax
