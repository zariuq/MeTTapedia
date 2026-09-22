import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Variable survival and first-occurrence depth in the current applier

The scoped binding applier uses the first capture depth found in the left-hand
side. The condition `depthAligned` identifies agreement with the earlier
applier on its stated domain; that agreement is not a safety certificate.
The following examples compute unresolved variables and first-occurrence
depths on concrete rules, without claiming a whole-corpus reachability audit.

**A right-hand side variable the left-hand side never binds.**  The language
validator already rejects such a rule: `unboundRule_has_pattern_error` below
proves it, and since `Pattern.freeFvarNames` counts a collection's rest, the
rest-variable case is rejected too.  The finding is elsewhere.  Called directly,
`applyBindingsScoped` fires anyway and emits the variable as itself, because
**the applier does not consult validation** -- so the reduct is open though the
redex was closed, and `depthAligned` reports `true`, a variable with no capture
depth being vacuously aligned.  The gap is between the validator and the
applier, not a rule shape nothing can see.

**A metavariable captured at two depths.**  Capture depth is read off the
left-hand side by a traversal that stops at the first occurrence.  A variable
bound once outside a binder and once inside it therefore reports the outer
depth, and every use is shifted as though that were the only occurrence.

These examples distinguish executor behavior from the meaning of a rule.
A declared metavariable can occur at different ambient depths when its
arguments identify its dependencies. A declared variable absent from the left
may be instantiated by a premise or by an explicitly generative rule semantics.
Neither shape is intrinsically meaningless. The defect is using an incomplete
assignment or a first-occurrence depth as if it supplied those declarations.
-/

namespace Mettapedia.OSLF.Binding.RuleVariableSurvival

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

set_option autoImplicit false

/-! ## A variable the left-hand side never binds -/

/-- Binds one variable. -/
def unboundLhs : Pattern := .apply "f" [.fvar "X"]

/-- Uses two: the bound one, and one the rule never introduced. -/
def unboundRhs : Pattern := .apply "g" [.fvar "X", .fvar "Y"]

/-- A closed redex. -/
def unboundSource : Pattern := .apply "f" [.apply "A" []]

/-- The match binds exactly what the left-hand side names. -/
theorem unbound_match :
    matchPattern unboundLhs unboundSource = [[("X", .apply "A" [])]] := by
  decide +kernel

/-- **And the rule fires anyway, with its own variable in the result.**  No
failure is reported and no solution is dropped: the reduct simply mentions `Y`. -/
theorem unbound_rule_variable_survives :
    (matchPattern unboundLhs unboundSource).map
        (fun bindings => applyBindingsScoped unboundLhs bindings 0 unboundRhs)
      = [.apply "g" [.apply "A" [], .fvar "Y"]] := by
  decide +kernel

/-- The reduct is not closed, though the redex was. -/
theorem unbound_reduct_is_open :
    (Pattern.apply "g" [.apply "A" [], .fvar "Y"]).isWellScopedAt 0 = true
      ∧ ¬ (Pattern.apply "g" [.apply "A" [], .fvar "Y"]).isGround = true := by
  refine ⟨by decide, by decide⟩

/-- **The conservativity condition does not see it.**  A variable with no
capture depth is vacuously aligned, so the rule is certified as one the scope
correction leaves alone -- which is true, and beside the point. -/
theorem unbound_passes_the_gate :
    captureDepth "Y" 0 unboundLhs = none
      ∧ depthAligned unboundLhs 0 unboundRhs = true := by
  refine ⟨rfl, by decide +kernel⟩

/-! ## A metavariable captured at two depths -/

/-- `Z` is bound once outside the binder and once inside it. -/
def twoDepthLhs : Pattern :=
  .apply "h" [.fvar "Z", .lambda (some "w") (.fvar "Z")]

/-- **Capture depth reports the first occurrence.**  The traversal stops there,
so the inner occurrence -- one binder deeper -- is not consulted, and every use
of `Z` is shifted as though the outer occurrence were the only one. -/
theorem twoDepth_reports_the_first :
    captureDepth "Z" 0 twoDepthLhs = some 0 := rfl

/-- The inner occurrence really is at a different depth: read on its own, the
body of the binder reports one. -/
theorem twoDepth_inner_is_deeper :
    captureDepth "Z" 0 (.lambda (some "w") (.fvar "Z")) = some 1 := rfl

/-- So the two occurrences disagree, and the traversal picks one without
recording that it chose. -/
theorem twoDepth_disagree :
    captureDepth "Z" 0 twoDepthLhs
      ≠ captureDepth "Z" 0 (.lambda (some "w") (.fvar "Z")) := by decide

/-! ## Existing syntax validation and a consistent repeated binding

The syntax validator already reports variables unavailable from the left and
from output-capable premises. This is a check for the current syntax, not a
universal restriction on rule theories. Multiple depths alone do not make a
rule unusable: the closed repeated-value example below matches consistently.
-/

/-- The unbound-variable pattern pair, as a rule. -/
def unboundRule : RewriteRule :=
  { «name» := "unbound", typeContext := [], premises := []
    left := unboundLhs, right := unboundRhs }

/-- The existing syntax validator reports the unresolved output name. -/
theorem unboundRule_has_pattern_error :
    (LanguageDef.validateRulePatterns "test" [] unboundRule.typeContext
      unboundRule.premises unboundRule.left unboundRule.right).isEmpty = false := by
  simp [unboundRule, unboundLhs, unboundRhs, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

/-- The two-depth pattern, as a rule. -/
def twoDepthRule : RewriteRule :=
  { «name» := "two-depth", typeContext := [], premises := []
    left := twoDepthLhs, right := .fvar "Z" }

/-- A closed value can consistently instantiate both ambient depths. -/
theorem twoDepthRule_matches_closed_repetition :
    (matchPattern twoDepthRule.left
      (.apply "h" [.apply "A" [], .lambda (some "w") (.apply "A" [])])).isEmpty
      = false := by decide +kernel

/-! ### A rest variable the left-hand side never binds

The rest variable of a collection is a metavariable, and a rule can leave one
unbound exactly as it can leave a named variable unbound.  The reading that
drops rest variables -- which is what the substitution layer's free-variable
function computes -- reports this rule closed. -/

/-- Binds the element variable and no rest. -/
def unboundRestLhs : Pattern := .collection .hashBag [.fvar "S"] none

/-- Uses a rest the left-hand side never introduced. -/
def unboundRestRhs : Pattern := .collection .hashBag [.fvar "S"] (some "rest")

/-- The rule built from them. -/
def unboundRestRule : RewriteRule :=
  { «name» := "unbound-rest", typeContext := [], premises := []
    left := unboundRestLhs, right := unboundRestRhs }

/-- The established validator counts rests and reports this unresolved name. -/
theorem unboundRestRule_has_pattern_error :
    (LanguageDef.validateRulePatterns "test" [] unboundRestRule.typeContext
      unboundRestRule.premises unboundRestRule.left unboundRestRule.right).isEmpty
      = false := by
  simp [unboundRestRule, unboundRestLhs, unboundRestRhs,
    LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- **And the blind reading misses it.**  `freeVars` gathers a collection's
elements and drops its rest, so a condition stated with it sees nothing to
report on a right-hand side whose only unbound variable is a rest. -/
theorem freeVars_cannot_see_the_rest :
    Mettapedia.OSLF.MeTTaIL.Substitution.freeVars unboundRestRhs = ["S"]
      ∧ unboundRestRhs.freeFvarNames = ["S", "rest"] := by
  refine ⟨by simp [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars, unboundRestRhs],
    by simp [unboundRestRhs, Pattern.freeFvarNames]⟩

end Mettapedia.OSLF.Binding.RuleVariableSurvival
