import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Separating controls for finite equation and alpha admission

A growing unit equation has infinitely many raw representatives and selected
syntactic contexts. Normalizing alpha metadata repairs repeated captures only
when that policy is actually applied. Neither control turns administrative
equation paths into new primitive physical events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationSeparators

open Syntax Match DerivedContexts ContextualStep
open GeneralEquationCanonical GeneralEquationAdmission GeneralEquationMeasures PatternTreeSize
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- A unit insertion schema, deliberately outside balanced finite admission. -/
def unitEquation : Equation where
  name := "unit-insertion"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .fvar "P"
  right := .apply "Parallel" [.fvar "P", .apply "Zero" []]
  bindings := some {dependencies := [("P", [])]}

def unitLanguage : LanguageDef where
  name := "UnitExpansion"
  types := [TypeDecl.plain "Proc"]
  terms := [
    {label := "Atom", category := "Proc", params := [], syntaxPattern := []},
    {label := "Zero", category := "Proc", params := [], syntaxPattern := []},
    {label := "Parallel", category := "Proc", params := [
      .simple "P" (.base "Proc"), .simple "Q" (.base "Proc")], syntaxPattern := []}]
  equations := [unitEquation]
  rewrites := []

def expand (pattern : Pattern) : Pattern := .apply "Parallel" [pattern, .apply "Zero" []]

def repeated (count : Nat) (pattern : Pattern) : Pattern :=
  match count with
  | 0 => pattern
  | count + 1 => expand (repeated count pattern)

theorem unit_generator (base : BasePremiseEvaluator) (pattern : Pattern) :
    EquationContextStep base unitLanguage pattern (expand pattern) := by
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := unitEquation)
    (initialBindings := [("P", pattern)]) (finalBindings := [("P", pattern)]) ?_ ?_ ?_ (.nil _) ?_⟩
  · exact List.Mem.head _
  · decide
  · simp [unitEquation, matchPattern]
  · simp [unitEquation, applyBindings]

theorem repeated_equivalent (base : BasePremiseEvaluator) (pattern : Pattern) (count : Nat) :
    EquationEquiv base unitLanguage pattern (repeated count pattern) := by
  induction count with
  | zero => exact .refl pattern
  | succ count ih => exact .trans _ _ _ ih (.rel _ _ (unit_generator base (repeated count pattern)))

theorem repeated_nodes (pattern : Pattern) (count : Nat) :
    nodes (repeated count pattern) = nodes pattern + 2 * count := by
  induction count with
  | zero => simp [repeated]
  | succ count ih => simp only [repeated, expand, nodes, listNodes, ih]; omega

theorem repeated_injective (pattern : Pattern) : Function.Injective (fun count => repeated count pattern) := by
  intro left right equal
  have counts := congrArg nodes equal
  simp only [repeated_nodes] at counts
  omega

def largest (patterns : List Pattern) : Nat := (patterns.map nodes).foldr max 0

theorem nodes_le_largest (patterns : List Pattern) (pattern : Pattern) (member : pattern ∈ patterns) :
    nodes pattern ≤ largest patterns := by
  induction patterns with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

/-- No finite raw representative list covers even this single equation class. -/
theorem unit_raw_representatives_unbounded (base : BasePremiseEvaluator) (pattern : Pattern)
    (candidates : List Pattern) :
    ∃ representative, EquationEquiv base unitLanguage pattern representative ∧ representative ∉ candidates := by
  refine ⟨repeated (largest candidates + 1) pattern,
    repeated_equivalent base pattern (largest candidates + 1), ?_⟩
  intro member
  have bounded := nodes_le_largest candidates _ member
  rw [repeated_nodes] at bounded
  omega

def unitContext : Nat → OneHoleContext
  | 0 => .hole
  | count + 1 => .apply "Parallel" [] (unitContext count) [.apply "Zero" []]

theorem unitContext_fill (count : Nat) (pattern : Pattern) :
    (unitContext count).fill pattern = repeated count pattern := by
  induction count with
  | zero => rfl
  | succ count ih => simp [unitContext, OneHoleContext.fill, repeated, expand, ih]

theorem unitContext_injective : Function.Injective unitContext := by
  intro left right equal
  apply repeated_injective (.apply "Atom" [])
  simpa only [unitContext_fill] using congrArg (fun context => context.fill (.apply "Atom" [])) equal

theorem unitContext_selects (count : Nat) (pattern : Pattern) :
    Selects pattern (unitContext count) (repeated count pattern) := by
  rw [← unitContext_fill]
  exact Selects.of_fill _ _

/-- Arbitrarily deep, distinct raw context occurrences exist in one source
class. Their equation detours do not by themselves identify physical events. -/
theorem unit_context_occurrences_unbounded (base : BasePremiseEvaluator) (pattern : Pattern)
    (candidates : List OneHoleContext) :
    ∃ context representative, context ∉ candidates ∧
      EquationEquiv base unitLanguage pattern representative ∧ Selects pattern context representative := by
  let count := largest (candidates.map (fun context => context.fill pattern)) + 1
  refine ⟨unitContext count, repeated count pattern, ?_, repeated_equivalent base pattern count,
    unitContext_selects count pattern⟩
  intro member
  have bounded := nodes_le_largest (candidates.map (fun context => context.fill pattern))
    ((unitContext count).fill pattern) (List.mem_map.mpr ⟨unitContext count, member, rfl⟩)
  rw [unitContext_fill, repeated_nodes] at bounded
  dsimp only [count] at bounded
  omega

theorem unit_equation_not_finite_admitted : checkEquation unitEquation = false := by
  simp [checkEquation, unitEquation, ScopedEquationExecution.orientedRule, checkRule,
    balancedSides, balanced, constantContribution, evaluate, evaluateList]

/-- Literal repeated captures distinguish raw display names. -/
def repeatRule : RewriteRule where
  name := "repeated-capture"
  typeContext := [("P", .arrow (.base "Name") (.base "Name"))]
  premises := []
  left := .apply "Pair" [.fvar "P", .fvar "P"]
  right := .fvar "P"
  bindings := some {dependencies := [("P", [])]}

def repeatedDisplaySource : Pattern :=
  .apply "Pair" [.lambda (some "x") (.bvar 0), .lambda (some "y") (.bvar 0)]

theorem raw_repeated_capture_fails :
    ScopedRuleMatching.matchRuleAt repeatRule {dependencies := [("P", [])]} 0 repeatedDisplaySource = [] := by
  simp [repeatRule, repeatedDisplaySource, ScopedRuleMatching.matchRuleAt, ScopedRuleMatching.matchRuleWithAt,
    ScopedRuleMatching.matchAtWith, ScopedRuleMatching.matchArgsAtWith, ScopedRuleMatching.capture?,
    RuleBinding.dependencies?, RuleBinding.arguments?, RuleBinding.occurrenceDeclared,
    RuleBinding.sitePattern?, RuleBinding.occurrenceAt?, RuleBinding.recoverValue?, RuleBinding.variableSpine?,
    RuleBinding.instantiateValue?,
    ContextSubstitution.substitute, ContextSubstitution.lift, Pattern.isWellScopedAt,
    ScopedRuleMatching.assign, ScopedRuleMatching.lookup]

theorem canonical_repeated_capture_succeeds :
    canonicalMatchRule repeatRule {dependencies := [("P", [])]} 0 repeatedDisplaySource ≠ [] := by
  simp [canonicalMatchRule, repeatRule, repeatedDisplaySource, Pattern.eraseBinderMetadata,
    ScopedRuleMatching.matchRuleAt, ScopedRuleMatching.matchRuleWithAt,
    ScopedRuleMatching.matchAtWith, ScopedRuleMatching.matchArgsAtWith, ScopedRuleMatching.capture?,
    RuleBinding.dependencies?, RuleBinding.arguments?, RuleBinding.occurrenceDeclared,
    RuleBinding.sitePattern?, RuleBinding.occurrenceAt?, RuleBinding.recoverValue?, RuleBinding.variableSpine?,
    RuleBinding.instantiateValue?,
    ContextSubstitution.substitute, ContextSubstitution.lift, Pattern.isWellScopedAt,
    ScopedRuleMatching.assign, ScopedRuleMatching.lookup]

theorem repeated_display_alpha :
    Pattern.AlphaEquiv repeatedDisplaySource
      (.apply "Pair" [.lambda none (.bvar 0), .lambda none (.bvar 0)]) := by
  simp [Pattern.AlphaEquiv, repeatedDisplaySource, Pattern.eraseBinderMetadata]

end Mettapedia.OSLF.MeTTaIL.GeneralEquationSeparators
