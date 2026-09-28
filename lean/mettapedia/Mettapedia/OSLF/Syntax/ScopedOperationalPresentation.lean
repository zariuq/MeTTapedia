import Mettapedia.OSLF.Syntax.ScopedPremiseSkeleton
import Mettapedia.OSLF.Syntax.ScopedRuleConstructorFrame
import Mettapedia.OSLF.Syntax.FiniteRulePremiseLists

/-!
# A fixed finite presentation of authored scoped operational shapes

The shape of a complete conditional rule consists of its selected authored
declaration, a contextual capture, an ordered oracle-independent premise
skeleton, and a checked reduct. Its finite list of children contains exactly
the recursive premise judgments under their local binder contexts. Runtime
firings project to these shapes. A reverse tree/execution correspondence is
not asserted here: selected oracle ordinals are additional event data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedOperationalPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

/-- Bounded reduction keeps the ambient context alongside both endpoints.
A recursive premise moves to its declared local extension and smaller fuel. -/
structure Judgment where
  fuel : Nat
  ambient : Nat
  source : Pattern
  target : Pattern

/-- An oracle-independent whole-rule constructor. The evidence parameter
fixes only the carrier of nonrecursive base events; recursive results are
absent from the shape and enter through child positions. -/
structure RuleSkeleton (Evidence : Type) (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : Nat)
    (source target : Pattern) where
  rule : RewriteRule
  ruleIndex : Nat
  listed : (rule, ruleIndex) ∈ lang.rewrites.zipIdx
  spec : RuleBindingSpec
  declared : rule.bindings = some spec
  admitted : admittedFor rule spec = true
  captured : Assignment
  selected : captured ∈ matchRuleAt rule spec ambient source
  completed : Assignment
  premises : RunSkeleton Evidence relEnv lang rule spec ambient 0
    rule.premises captured completed
  reduct : reduct? rule spec ambient completed = some target
  resultScoped : target.isWellScopedAt ambient = true

/-- Each listed child is one actual recursive premise of the rule shape,
with its own context and endpoints. -/
def RuleSkeleton.children {Evidence : Type} {relEnv : RelationEnv}
    {lang : LanguageDef} {ambient : Nat}
    {source target : Pattern}
    (shape : RuleSkeleton Evidence relEnv lang ambient source target) :
    List (Nat × Pattern × Pattern) :=
  shape.premises.children

theorem RuleSkeleton.children_length_le {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {ambient : Nat} {source target : Pattern}
    (shape : RuleSkeleton Evidence relEnv lang ambient source target) :
    shape.children.length ≤ shape.rule.premises.length :=
  shape.premises.children_length_le

/-- A rule with one authored scoped premise requests precisely one child in
that premise's binder extension, independent of its selected occurrence. -/
theorem RuleSkeleton.single_scoped_child {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {ambient : Nat} {source target : Pattern}
    (shape : RuleSkeleton Evidence relEnv lang ambient source target)
    {step : ScopedStepPremise}
    (single : shape.rule.premises = [.scopedStep step]) :
    ∃ childSource childTarget,
      shape.children =
        [(step.binders.length + ambient, childSource, childTarget)] := by
  exact RunSkeleton.single_scoped_child_of_eq shape.premises single

/-- Finishing a firing establishes the actual reduct, independently of
which premise histories were selected. -/
theorem finish?_reduct {Evidence : Type}
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (captured completed : Assignment)
    (history : List (PremiseEvent Evidence)) (firing : RuleFiring Evidence)
    (finished : finish? rule spec ambient captured completed history =
      some firing) :
    reduct? rule spec ambient completed = some firing.target := by
  unfold finish? at finished
  cases result : reduct? rule spec ambient completed with
  | none => simp [result] at finished
  | some target =>
      by_cases targetScoped : target.isWellScopedAt ambient = true
      · simp [result, targetScoped] at finished
        cases finished
        rfl
      · simp [result, targetScoped] at finished

/-- Forget selected recursive oracle results, while keeping the author's
rule position, all intermediate assignments, and the checked reduct. -/
noncomputable def RuleConstructorFrame.toSkeleton {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {ambient : Nat}
    {rule : RewriteRule} {source : Pattern}
    {firing : RuleFiring Evidence}
    (ruleIndex : Nat)
    (listed : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (frame : RuleConstructorFrame oracle relEnv lang ambient
      rule source firing) :
    RuleSkeleton Evidence relEnv lang ambient source firing.target where
  rule := rule
  ruleIndex := ruleIndex
  listed := listed
  spec := frame.spec
  declared := frame.declared
  admitted := frame.admitted
  captured := frame.captured
  selected := frame.selected
  completed := frame.completed
  premises := ScopedPremiseSkeleton.RunFrame.toSkeleton frame.premises
  reduct := finish?_reduct rule frame.spec ambient frame.captured
    frame.completed frame.history firing frame.finished
  resultScoped := finish?_scoped rule frame.spec ambient frame.captured
    frame.completed frame.history firing frame.finished

/-- Every child of a whole-rule skeleton projected from an actual firing
has a selected result in the same oracle, at its own binder-local context. -/
theorem RuleConstructorFrame.toSkeleton_children_selected
    {Evidence : Type} {oracle : StepOracle Evidence}
    {relEnv : RelationEnv} {lang : LanguageDef} {ambient : Nat}
    {rule : RewriteRule} {source : Pattern}
    {firing : RuleFiring Evidence}
    (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (frame : RuleConstructorFrame oracle relEnv lang ambient
      rule source firing)
    (requested : Nat × Pattern × Pattern)
    (listedChild : requested ∈
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame).children) :
    ∃ evidence,
      (evidence, requested.2.2) ∈
        oracle requested.1 requested.2.1 := by
  apply RunFrame.toSkeleton_children_selected frame.premises requested
  simpa [RuleSkeleton.children, RuleConstructorFrame.toSkeleton]
    using listedChild

/-- The complete rule frame retains its selected recursive requests in
premise order, including each child history and oracle result ordinal. -/
def RuleConstructorFrame.childRequests {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {ambient : Nat}
    {rule : RewriteRule} {source : Pattern}
    {firing : RuleFiring Evidence}
    (frame : RuleConstructorFrame oracle relEnv lang ambient
      rule source firing) : List (ChildRequest Evidence) :=
  RunFrame.childRequests frame.premises

/-- The indexed free constructor positions agree exactly, in order, with
the selected recursive requests of the executable rule frame. -/
theorem RuleConstructorFrame.toSkeleton_children_eq_requests
    {Evidence : Type} {oracle : StepOracle Evidence}
    {relEnv : RelationEnv} {lang : LanguageDef} {ambient : Nat}
    {rule : RewriteRule} {source : Pattern}
    {firing : RuleFiring Evidence}
    (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (frame : RuleConstructorFrame oracle relEnv lang ambient
      rule source firing) :
    (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame).children =
      (RuleConstructorFrame.childRequests frame).map fun child =>
        (child.ambient, child.source, child.target) := by
  simpa [RuleSkeleton.children, RuleConstructorFrame.toSkeleton,
    RuleConstructorFrame.childRequests] using
      RunFrame.toSkeleton_children_eq_requests frame.premises

/-- Substituting the selected recursive child histories back into the fixed
rule skeleton recovers the exact ordered event list of the firing. -/
theorem RuleConstructorFrame.materializeEvents_selected
    {oracle : StepOracle RuleHistory} {relEnv : RelationEnv}
    {lang : LanguageDef} {ambient : Nat}
    {rule : RewriteRule} {source : Pattern}
    {firing : RuleFiring RuleHistory}
    (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (frame : RuleConstructorFrame oracle relEnv lang ambient
      rule source firing) :
    RunSkeleton.materializeEvents?
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame).premises
      ((RuleConstructorFrame.childRequests frame).map
        ChildRequest.evidence) = some frame.history := by
  simpa [RuleConstructorFrame.toSkeleton,
    RuleConstructorFrame.childRequests] using
      RunFrame.materializeEvents_selected frame.premises

/-- A fixed finite-premise presentation. Shapes do not depend on the
recursive evidence family; each child position is a premise-list position. -/
def presentation (relEnv : RelationEnv) (lang : LanguageDef) :
    FinitePresentation Unit (fun _ => Judgment) where
  Shape := fun _ judgment =>
    match judgment.fuel with
    | 0 => Empty
    | _ + 1 => RuleSkeleton RuleHistory relEnv lang
        judgment.ambient judgment.source judgment.target
  premises := fun _ judgment shape =>
    match judgment with
    | ⟨0, _, _, _⟩ => nomatch shape
    | ⟨previous + 1, _, _, _⟩ =>
        shape.children.map fun child =>
          ⟨previous, child.1, child.2.1, child.2.2⟩

/-- Every actual bounded firing determines a shape of the fixed
presentation, including the authored rule position in its retained history.
This is the sound direction of the source/execution bridge. -/
theorem runtime_has_shape_with_history
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory)
    (executed : (history, target) ∈
      rewriteAt relEnv lang (fuel + 1) ambient source) :
    ∃ shape : RuleSkeleton RuleHistory relEnv lang ambient source target,
      ∃ premiseHistory : List (PremiseEvent RuleHistory),
        history = .fire shape.ruleIndex premiseHistory ∧
        shape.children.length ≤ shape.rule.premises.length := by
  obtain ⟨rule, ruleIndex, listed, firing, ⟨frame⟩,
      historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff_frames relEnv lang fuel ambient
      source target history).mp executed
  subst target
  let shape := RuleConstructorFrame.toSkeleton ruleIndex listed frame
  exact ⟨shape, firing.history, historyEq, shape.children_length_le⟩

/-- Forgetting the retained history yields an inhabited constructor shape
at the exact bounded judgment. -/
theorem runtime_has_shape (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory)
    (executed : (history, target) ∈
      rewriteAt relEnv lang (fuel + 1) ambient source) :
    ∃ shape : RuleSkeleton RuleHistory relEnv lang ambient source target,
      shape.children.length ≤ shape.rule.premises.length := by
  obtain ⟨shape, _, _, lengthBound⟩ :=
    runtime_has_shape_with_history relEnv lang fuel ambient source target
      history executed
  exact ⟨shape, lengthBound⟩

end Mettapedia.OSLF.Binding.ScopedOperationalPresentation
