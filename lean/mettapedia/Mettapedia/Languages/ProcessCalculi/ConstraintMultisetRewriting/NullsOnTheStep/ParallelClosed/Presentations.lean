import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Every presentation with a parallel context rule is closed beside

A presentation is the tree's five-field `LanguageDef`; its reduction is the least relation generated
by its authored rewrite rules (`ContextualStep.Step`, and under an explicit rule interpretation
`InterpretedContextualStep.Step`), and OSLF reads it modulo the presentation's equations
(`EquationSemantics.StepModuloEquations`). Contextual authority comes only from authored rules
with a congruence premise (`DerivedContexts.RuleAuthorizesContext`).

## The hypothesis, read off the declared rules

`IsParallelContextRule kind rule`: the rule's only premise reduces a metavariable `source` to
`target`, and its two sides are the **parallel frame** of the collection kind
(`parallelFrame kind rest`: one element in the hole, the rest of the collection named `rest`) filled
with them, the three names distinct. It is the tree's authored context frame at the parallel frame
(`IsParallelContextRule.authorizes`), with the premise list and the names pinned down.
`HasParallelContextRule kind language`: one of the declared rewrites is such a rule. Rho's
`ParCong` is one (`rhoCalc_hasParallelContextRule`).

## The theorems

* `step_besideAll`, for every rule interpretation that reads the context rule syntactically
  (`ReadsSyntactically`; the syntactic interpretation always does, a reflection profile does when it
  selects no presentation for the rule): a step of `p` is a step of `p` beside any list of
  components. `closedBeside_contextual`, `closedBeside_moduloEquations`: the core reduction and
  the reduction modulo equations are closed beside (`beside kind p r`), whatever the other rules.
* `contextual_not_switchedOff`, `moduloEquations_not_switchedOff`: **no relation that a parallel
  component switches off is the reduction of a presentation with a parallel context rule.**
  `contextual_not_patternNoneStep`: the none step on patterns (`PatternNoneStep`: add `a` where `c` is
  not a parallel component) is such a relation.
* Success: `Component kind ω t` (`ω` is a parallel component of `t`, through nested collections of
  the kind) persists beside; modulo equations (`ShowsModulo`) too. `presentationCalculus` is the
  presentation read as a calculus with a parallel composition, and `presentationCalculus_persistent`
  proves it persistent.

## Controls

* `Controls.withoutContext`: a parallel bag and one root rule `a ~> b`, no context rule. It steps
  `a ~> b` and never steps `{a | z} ~> {b | z}`: its reduction is not closed beside
  (`Controls.withoutContext_not_closed`). With rho's `ParCong` added (`Controls.withContext`) it is
  (`Controls.withContext_closed`).
* `Controls.patternNoneStep_example`: the none step fires at the empty bag and is switched off by a
  parallel `c`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (RuleInterpretation)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations
  equationEquiv_fill equationSetoid)

/-! ## The hypothesis -/

/-- **The parallel frame** of a collection kind: one element in the hole, the rest of the collection
named `rest`. -/
def parallelFrame (kind : CollType) (rest : String) : OneHoleContext :=
  .collection kind [] .hole [] (some rest)

@[simp] theorem parallelFrame_fill (kind : CollType) (rest : String) (pattern : Pattern) :
    (parallelFrame kind rest).fill pattern = .collection kind [pattern] (some rest) := rfl

/-- **A parallel context rule** of a collection kind, read off the rule: its only premise reduces the
metavariable `source` to `target`, and its two sides are the parallel frame filled with them; the
three names are distinct. -/
def IsParallelContextRule (kind : CollType) (rule : RewriteRule) : Prop :=
  ∃ source target rest : String, source ≠ target ∧ source ≠ rest ∧ target ≠ rest ∧
    rule.premises = [.congruence (.fvar source) (.fvar target)] ∧
    rule.left = (parallelFrame kind rest).fill (.fvar source) ∧
    rule.right = (parallelFrame kind rest).fill (.fvar target)

/-- **A presentation has a parallel context rule** of a kind: one of its declared rewrites is one. -/
def HasParallelContextRule (kind : CollType) (language : LanguageDef) : Prop :=
  ∃ rule ∈ language.rewrites, IsParallelContextRule kind rule

/-- A parallel context rule authorizes the parallel frame in the tree's sense. -/
theorem IsParallelContextRule.authorizes {kind : CollType} {rule : RewriteRule}
    (parallel : IsParallelContextRule kind rule) :
    ∃ rest, RuleAuthorizesContext rule (parallelFrame kind rest) := by
  obtain ⟨source, target, rest, _, _, _, premises, left, right⟩ := parallel
  exact ⟨rest, source, target, by rw [premises]; exact List.mem_singleton_self _, left, right⟩

/-- **Rho's `ParCong` is a parallel context rule**, so the rho presentation has one. -/
theorem rhoCalc_hasParallelContextRule : HasParallelContextRule .hashBag rhoCalc :=
  ⟨rhoParCongRewrite, by simp [rhoCalc],
    "S", "T", "rest", by decide, by decide, by decide, rfl, rfl, rfl⟩

/-- An interpretation **reads a rule syntactically**: it matches the rule's left side structurally
and instantiates its right side by binding application. -/
def ReadsSyntactically (interpretation : RuleInterpretation) (language : LanguageDef)
    (rule : RewriteRule) : Prop :=
  (∀ term, interpretation.matchRule language rule term = matchPattern rule.left term) ∧
    ∀ bindings, interpretation.instantiateRule language rule bindings =
      applyRuleBindings rule bindings

/-- The syntactic interpretation reads every rule syntactically. -/
theorem syntactic_reads (language : LanguageDef) (rule : RewriteRule) :
    ReadsSyntactically .syntactic language rule :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- A reflection profile reads syntactically every rule for which it selects no presentation. -/
theorem reflection_reads {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    (language : LanguageDef) {rule : RewriteRule}
    (noMatching : Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.matchingPresentationForRule?
      profile rule = none)
    (noSubstitution :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.substitutionPresentationForRule?
        profile rule = none) :
    ReadsSyntactically (.reflection profile) language rule :=
  ⟨fun term => Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic_of_no_presentation
      noMatching term,
    fun bindings =>
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic_of_no_presentation
        noSubstitution bindings⟩

/-! ## Closure beside -/

/-- `p` beside `r`: the two-element collection of the kind. -/
def beside (kind : CollType) (p r : Pattern) : Pattern := .collection kind [p, r] none

/-- **The parallel frame matches a component in front of the others**, for every kind. -/
theorem parallel_match (kind : CollType) {source rest : String} (apart : source ≠ rest)
    (p : Pattern) (others : List Pattern) :
    [(rest, .collection kind others none), (source, p)] ∈
      matchPattern ((parallelFrame kind rest).fill (.fvar source))
        (.collection kind (p :: others) none) := by
  have merged : mergeBindings [(source, p)] [(rest, .collection kind others none)] =
      some [(rest, .collection kind others none), (source, p)] := by
    simp [mergeBindings, apart]
  apply matchPattern_iff_matchRel.mpr
  rw [parallelFrame_fill]
  by_cases vector : kind = .vec
  · subst vector
    exact MatchRel.vectorRest (.cons .fvar .nil (by simp [mergeBindings])) merged
  · exact MatchRel.collection vector (.cons 0 (by simp) .fvar .nilRest merged)

/-- **A step of `p` is a step of `p` in front of any other components**, under every interpretation
that reads a parallel context rule of the presentation syntactically. -/
theorem step_besideAll {interpretation : RuleInterpretation} {base : BasePremiseEvaluator}
    {language : LanguageDef} {kind : CollType} {rule : RewriteRule}
    (member : rule ∈ language.rewrites) (parallel : IsParallelContextRule kind rule)
    (reads : ReadsSyntactically interpretation language rule) {p q : Pattern}
    (step : Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base language p q)
    (others : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base language
      (.collection kind (p :: others) none) (.collection kind (q :: others) none) := by
  obtain ⟨source, target, rest, sourceTarget, sourceRest, targetRest, premises, left, right⟩ :=
    parallel
  have restSource : rest ≠ source := fun same => sourceRest same.symm
  have restTarget : rest ≠ target := fun same => targetRest same.symm
  refine Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_of_single_congruence_rule
    (rule := rule) (initialBindings := [(rest, .collection kind others none), (source, p)])
    (finalBindings := [(target, q), (rest, .collection kind others none), (source, p)])
    (premiseBindings := [(target, q)]) (premiseSource := .fvar source)
    (premiseTarget := .fvar target) (candidate := q) member ?_ premises ?_ ?_ ?_ ?_
  · rw [reads.1, left]
    exact parallel_match kind sourceRest p others
  · have lookup : applyBindings [(rest, .collection kind others none), (source, p)] (.fvar source) =
        p := by
      simp [applyBindings, restSource]
    rw [lookup]
    exact step
  · simp [matchPattern]
  · have restTargetFalse : (rest == target) = false := by simpa using restTarget
    have sourceTargetFalse : (source == target) = false := by simpa using sourceTarget
    simp [mergeBindings, List.find?, restTargetFalse, sourceTargetFalse]
  · rw [reads.2, applyRuleBindings, right,
      applyBindingsScoped_zero_of_binderFree _ _ _ (by simp [binderFree, binderFreeList])]
    simp [applyBindings, targetRest]

/-- An interpretation **has a parallel context rule** of a presentation: a declared parallel context
rule that it reads syntactically. -/
def HasParallelContextRuleUnder (interpretation : RuleInterpretation) (kind : CollType)
    (language : LanguageDef) : Prop :=
  ∃ rule ∈ language.rewrites, IsParallelContextRule kind rule ∧
    ReadsSyntactically interpretation language rule

theorem HasParallelContextRule.syntactic {kind : CollType} {language : LanguageDef}
    (has : HasParallelContextRule kind language) :
    HasParallelContextRuleUnder .syntactic kind language := by
  obtain ⟨rule, member, parallel⟩ := has
  exact ⟨rule, member, parallel, syntactic_reads language rule⟩

/-- **Closed beside, under every interpretation that reads a parallel context rule syntactically.** -/
theorem closedBeside_interpreted {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {language : LanguageDef} {kind : CollType}
    (has : HasParallelContextRuleUnder interpretation kind language) :
    ClosedBeside (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.Step interpretation base language)
      (beside kind) := by
  obtain ⟨rule, member, parallel, reads⟩ := has
  intro p q r step
  exact step_besideAll member parallel reads step [r]

/-- **The reduction of every presentation with a parallel context rule is closed beside**, whatever
its other rules are. -/
theorem closedBeside_contextual {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) :
    ClosedBeside (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base language) (beside kind) := by
  intro p q r step
  have interpreted := closedBeside_interpreted (base := base) has.syntactic p q r
    ((Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_syntactic_iff_contextual
      base language p q).mpr step)
  exact (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.step_syntactic_iff_contextual
    base language _ _).mp interpreted

/-- Equation equivalence is a congruence for putting a term beside another. -/
theorem equationEquiv_beside {base : BasePremiseEvaluator} {language : LanguageDef}
    (kind : CollType) {p p' : Pattern} (equivalent : EquationEquiv base language p p')
    (r : Pattern) : EquationEquiv base language (beside kind p r) (beside kind p' r) :=
  equationEquiv_fill (.collection kind [] .hole [r] none) equivalent

/-- **The reduction modulo equations is closed beside** too: the reduction OSLF reads. -/
theorem closedBeside_moduloEquations {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) :
    ClosedBeside (StepModuloEquations base language) (beside kind) := by
  rintro p q r ⟨redex, contractum, before, step, after⟩
  exact ⟨beside kind redex r, beside kind contractum r, equationEquiv_beside kind before r,
    closedBeside_contextual has redex contractum r step, equationEquiv_beside kind after r⟩

/-! ## No relation a parallel component switches off -/

/-- **No relation that a parallel component switches off is the reduction of a presentation with a
parallel context rule.** -/
theorem contextual_not_switchedOff {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) {R : Pattern → Pattern → Prop}
    (switched : SwitchedOffBeside R (beside kind)) :
    ¬ ∀ x y, Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base language x y ↔ R x y :=
  not_iff_of_switchedOff (closedBeside_contextual has) switched

/-- The same for the reduction modulo equations. -/
theorem moduloEquations_not_switchedOff {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) {R : Pattern → Pattern → Prop}
    (switched : SwitchedOffBeside R (beside kind)) :
    ¬ ∀ x y, StepModuloEquations base language x y ↔ R x y :=
  not_iff_of_switchedOff (closedBeside_moduloEquations has) switched

/-! ## Components and the none step on patterns -/

/-- `c` is **a parallel component** of a pattern: the pattern itself, or a component of an element
of a collection of the kind. -/
inductive Component (kind : CollType) (c : Pattern) : Pattern → Prop
  | here : Component kind c c
  | inside {elements : List Pattern} {rest : Option String} {p : Pattern} :
      p ∈ elements → Component kind c p → Component kind c (.collection kind elements rest)

/-- A component of `p` is a component of `p` beside anything. -/
theorem Component.beside {kind : CollType} {c p : Pattern} (component : Component kind c p)
    (r : Pattern) : Component kind c (ParallelClosed.beside kind p r) :=
  .inside (List.mem_cons_self) component

/-- `c` is a component of anything beside `c`. -/
theorem component_beside_self (kind : CollType) (c p : Pattern) :
    Component kind c (beside kind p c) :=
  .inside (by simp) .here

/-- The empty collection has no component other than itself. -/
theorem not_component_empty {kind : CollType} {c : Pattern}
    (other : c ≠ .collection kind [] none) : ¬ Component kind c (.collection kind [] none) := by
  intro component
  cases component with
  | here => exact other rfl
  | inside member _ => simp at member

/-- **The none step on patterns**: add `a` beside `P` where `c` is not a parallel component of
`P`. -/
def PatternNoneStep (kind : CollType) (c a P Q : Pattern) : Prop :=
  ¬ Component kind c P ∧ Q = beside kind P a

/-- **A parallel `c` switches the none step off.** -/
theorem patternNoneStep_switchedOff {kind : CollType} {c P : Pattern} (a : Pattern)
    (missing : ¬ Component kind c P) : SwitchedOffBeside (PatternNoneStep kind c a) (beside kind) :=
  ⟨P, beside kind P a, c, ⟨missing, rfl⟩, fun step => step.1 (component_beside_self kind c P)⟩

/-- **The none step is not the reduction of any presentation with a parallel context rule**, for
every `c` that some pattern lacks as a component. -/
theorem contextual_not_patternNoneStep {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) {c P : Pattern} (a : Pattern)
    (missing : ¬ Component kind c P) :
    ¬ ∀ x y, Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base language x y ↔
      PatternNoneStep kind c a x y :=
  contextual_not_switchedOff has (patternNoneStep_switchedOff a missing)

/-- **Instance: rho.** The none step of every `c` other than the empty bag is not the reduction of
the rho presentation, nor of any presentation with `ParCong` among its rules. -/
theorem rhoCalc_not_patternNoneStep (base : BasePremiseEvaluator) {c : Pattern} (a : Pattern)
    (other : c ≠ .collection .hashBag [] none) :
    ¬ ∀ x y, Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base rhoCalc x y ↔
      PatternNoneStep .hashBag c a x y :=
  contextual_not_patternNoneStep rhoCalc_hasParallelContextRule a (not_component_empty other)

/-! ## The presentation as a calculus with a parallel composition -/

/-- Success modulo equations: an equation-equivalent pattern has `ω` as a parallel component. -/
def ShowsModulo (base : BasePremiseEvaluator) (language : LanguageDef) (kind : CollType)
    (ω t : Pattern) : Prop :=
  ∃ t', EquationEquiv base language t t' ∧ Component kind ω t'

/-- **A presentation as a calculus with a parallel composition**: patterns, reduction modulo
equations, the composition `beside`, success "`ω` is a component modulo equations", and the
equations as static equivalence. -/
def presentationCalculus (base : BasePremiseEvaluator) (language : LanguageDef) (kind : CollType)
    (ω : Pattern) : ParallelCalculus where
  Term := Pattern
  step := StepModuloEquations base language
  par := beside kind
  composable _ _ := True
  success := ShowsModulo base language kind ω
  same := EquationEquiv base language

/-- **Every presentation with a parallel context rule is persistent**: its reduction modulo equations
is closed beside, success persists beside, and reachable success is read modulo equations. -/
theorem presentationCalculus_persistent {base : BasePremiseEvaluator} {language : LanguageDef}
    {kind : CollType} (has : HasParallelContextRule kind language) (ω : Pattern) :
    (presentationCalculus base language kind ω).Persistent where
  closed := closedBeside_moduloEquations has
  persists := by
    rintro t u ⟨t', equivalent, component⟩
    exact ⟨beside kind t' u, equationEquiv_beside kind equivalent u, component.beside u⟩
  respects := by
    rintro t t' same ⟨t'', run, shows⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨middle, first, rest⟩
    · obtain ⟨t''', equivalent, component⟩ := shows
      exact ⟨t, .refl, t''', (equationSetoid base language).iseqv.trans same equivalent, component⟩
    · exact ⟨t'', Relation.ReflTransGen.head
        (Mettapedia.GSLT.LanguageDef.EquationSemantics.stepModuloEquations_change_source
          ((equationSetoid base language).iseqv.symm same) first) rest, shows⟩

/-! ## Controls -/

namespace Controls

/-- The atom `a`. -/
def atomA : Pattern := .apply "a" []
/-- The atom `b`. -/
def atomB : Pattern := .apply "b" []
/-- The atom `z`. -/
def atomZ : Pattern := .apply "z" []

/-- The root rule `a ~> b`, with no premise. -/
def aToB : RewriteRule where
  name := "AtoB"
  typeContext := []
  premises := []
  left := atomA
  right := atomB

/-- The parallel bag, as rho declares it, without its algebra. -/
def parallelBag : GrammarRule where
  label := "PPar"
  category := "Proc"
  params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
  syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"]

/-- **A presentation with a parallel composition and no context rule for it.** -/
def withoutContext : LanguageDef where
  name := "AtomsBeside"
  types := ["Proc"]
  terms := [parallelBag]
  equations := []
  rewrites := [aToB]

/-- The same presentation with rho's `ParCong` added. -/
def withContext : LanguageDef := { withoutContext with rewrites := [aToB, rhoParCongRewrite] }

/-- `a ~> b` at the root, in both presentations. -/
theorem step_aToB {base : BasePremiseEvaluator} {language : LanguageDef}
    (member : aToB ∈ language.rewrites) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base language atomA atomB := by
  refine ⟨1, .rule (initialBindings := []) (finalBindings := []) member ?_ (.nil []) ?_⟩
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (.apply .nil rfl)
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic]
    simp [applyRuleBindings, aToB, atomB]

/-- **Without a context rule the reduction is not closed beside**: `a ~> b`, and `{a | z}` has no
step at all. -/
theorem withoutContext_not_closed (base : BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withoutContext atomA atomB ∧
      ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withoutContext
        (beside .hashBag atomA atomZ) (beside .hashBag atomB atomZ) ∧
      ¬ ClosedBeside (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withoutContext)
        (beside .hashBag) := by
  have stuck : ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withoutContext
      (beside .hashBag atomA atomZ) (beside .hashBag atomB atomZ) := by
    apply Mettapedia.OSLF.MeTTaIL.ContextualStep.not_step_of_matchPatternForRule_eq_nil
    intro rule member
    simp only [withoutContext, List.mem_singleton] at member
    subst member
    rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro bindings matched
    have relation := matchPattern_iff_matchRel.mp matched
    cases relation
  refine ⟨step_aToB (by simp [withoutContext]), stuck, fun closed => stuck ?_⟩
  exact closed _ _ atomZ (step_aToB (by simp [withoutContext]))

/-- **With `ParCong` it is closed beside**, an instance of `closedBeside_contextual`. -/
theorem withContext_closed (base : BasePremiseEvaluator) :
    ClosedBeside (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withContext) (beside .hashBag) ∧
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withContext
        (beside .hashBag atomA atomZ) (beside .hashBag atomB atomZ) := by
  have has : HasParallelContextRule .hashBag withContext :=
    ⟨rhoParCongRewrite, by simp [withContext],
      "S", "T", "rest", by decide, by decide, by decide, rfl, rfl, rfl⟩
  exact ⟨closedBeside_contextual has,
    closedBeside_contextual has _ _ atomZ (step_aToB (by simp [withContext]))⟩

/-- **The none step fires and is switched off.** With `c = z`: it adds `a` beside the empty bag,
and never fires beside a parallel `z`. -/
theorem patternNoneStep_example :
    PatternNoneStep .hashBag atomZ atomA (.collection .hashBag [] none)
        (beside .hashBag (.collection .hashBag [] none) atomA) ∧
      ∀ P Q, ¬ PatternNoneStep .hashBag atomZ atomA (beside .hashBag P atomZ) Q :=
  ⟨⟨not_component_empty (by simp [atomZ]), rfl⟩,
    fun P _ step => step.1 (component_beside_self .hashBag atomZ P)⟩

end Controls

#print axioms IsParallelContextRule.authorizes
#print axioms rhoCalc_hasParallelContextRule
#print axioms reflection_reads
#print axioms parallel_match
#print axioms step_besideAll
#print axioms closedBeside_interpreted
#print axioms closedBeside_contextual
#print axioms closedBeside_moduloEquations
#print axioms contextual_not_switchedOff
#print axioms moduloEquations_not_switchedOff
#print axioms contextual_not_patternNoneStep
#print axioms rhoCalc_not_patternNoneStep
#print axioms presentationCalculus_persistent
#print axioms Controls.withoutContext_not_closed
#print axioms Controls.withContext_closed
#print axioms Controls.patternNoneStep_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
