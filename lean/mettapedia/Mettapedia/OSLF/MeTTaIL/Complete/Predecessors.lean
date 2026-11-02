import Mettapedia.OSLF.MeTTaIL.Complete.Inversion
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalCaptures
import Mettapedia.OSLF.MeTTaIL.GeneralEquationMatcherWork

/-!
# The terms that step into a term by an equation

An equation rebuilt rewrites a source `v` at a licensed site into a target `u`. To explore
equality classes without enumerating terms, the sources of instances into `u` must be found from
`u` itself. `predecessors` does this for every compiled equation and every position of `u`: it
matches the equation's right side at the position, instantiates the left side with the captures,
and returns the filled terms with every bag pattern's elements in each order, display metadata
erased.

`mem_predecessors`: when every equation of the plan passes the balance admission
(`equationsChecked`, which every accepted compiled plan satisfies), the source of every completed
equation rebuilt is among the predecessors of its target. The list is a complete candidate set, not an exact one: a
caller keeps a candidate only after its own forward equation search reaches the target.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Predecessors

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Inversion DerivedContexts

/-! ## Contexts -/

/-- The binders a hole sits under. -/
def binderDepth : OneHoleContext → Nat
  | .hole => 0
  | .apply _ _ inner _ => binderDepth inner
  | .lambda _ inner => 1 + binderDepth inner
  | .multiLambda arity _ inner => arity + binderDepth inner
  | .substBody inner _ => 1 + binderDepth inner
  | .substReplacement _ inner => binderDepth inner
  | .collection _ _ inner _ _ => binderDepth inner

/-- A context with its display metadata erased. -/
def eraseContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor (before.map Pattern.eraseBinderMetadata) (eraseContext inner)
        (after.map Pattern.eraseBinderMetadata)
  | .lambda _ inner => .lambda none (eraseContext inner)
  | .multiLambda arity _ inner => .multiLambda arity [] (eraseContext inner)
  | .substBody inner replacement => .substBody (eraseContext inner) replacement.eraseBinderMetadata
  | .substReplacement body inner => .substReplacement body.eraseBinderMetadata (eraseContext inner)
  | .collection kind before inner after rest =>
      .collection kind (before.map Pattern.eraseBinderMetadata) (eraseContext inner)
        (after.map Pattern.eraseBinderMetadata) rest

theorem binderDepth_erase (context : OneHoleContext) : binderDepth (eraseContext context) = binderDepth context := by
  induction context <;> simp_all [eraseContext, binderDepth]

theorem fill_erase (context : OneHoleContext) (focus : Pattern) :
    (context.fill focus).eraseBinderMetadata = (eraseContext context).fill focus.eraseBinderMetadata := by
  induction context <;> simp_all [eraseContext, OneHoleContext.fill, Pattern.eraseBinderMetadata, List.map_append]

/-- Every position of a term: the context and the focus. -/
def decompositions : Pattern → List (OneHoleContext × Pattern)
  | .bvar index => [(.hole, .bvar index)]
  | .fvar name => [(.hole, .fvar name)]
  | .apply constructor arguments =>
      (.hole, .apply constructor arguments) ::
        arguments.attach.zipIdx.flatMap fun (argument, index) =>
          (decompositions argument.1).map fun (inner, focus) =>
            (.apply constructor (arguments.take index) inner (arguments.drop (index + 1)), focus)
  | .lambda binder body =>
      (.hole, .lambda binder body) :: (decompositions body).map fun (inner, focus) => (.lambda binder inner, focus)
  | .multiLambda arity binders body =>
      (.hole, .multiLambda arity binders body) ::
        (decompositions body).map fun (inner, focus) => (.multiLambda arity binders inner, focus)
  | .subst body replacement =>
      (.hole, .subst body replacement) ::
        ((decompositions body).map fun (inner, focus) => (.substBody inner replacement, focus)) ++
        (decompositions replacement).map fun (inner, focus) => (.substReplacement body inner, focus)
  | .collection kind elements rest =>
      (.hole, .collection kind elements rest) ::
        elements.attach.zipIdx.flatMap fun (element, index) =>
          (decompositions element.1).map fun (inner, focus) =>
            (.collection kind (elements.take index) inner (elements.drop (index + 1)) rest, focus)
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals try (have := List.sizeOf_lt_of_mem argument.2; simp_wf; omega)
  all_goals try (have := List.sizeOf_lt_of_mem element.2; simp_wf; omega)
  all_goals try sizeOf_pattern_dec

theorem hole_mem_decompositions (pattern : Pattern) : (.hole, pattern) ∈ decompositions pattern := by
  cases pattern <;> simp [decompositions]

theorem mem_zipIdx_attach {α : Type} {items : List α} {index : Nat} (bounded : index < items.length) :
    ((⟨items[index], List.getElem_mem bounded⟩ : {item // item ∈ items}), index) ∈ items.attach.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  simp [bounded]

theorem mem_decompositions (context : OneHoleContext) (focus : Pattern) :
    (context, focus) ∈ decompositions (context.fill focus) := by
  induction context with
  | hole => exact hole_mem_decompositions focus
  | apply constructor before inner after ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    have bounded : before.length < (before ++ inner.fill focus :: after).length := by simp
    refine ⟨(⟨(before ++ inner.fill focus :: after)[before.length], List.getElem_mem bounded⟩, before.length),
      mem_zipIdx_attach bounded, ?_⟩
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, List.mem_map]
    exact ⟨(inner, focus), ih, by simp⟩
  | lambda binder inner ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(inner, focus), ih, rfl⟩)
  | multiLambda arity binders inner ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(inner, focus), ih, rfl⟩)
  | substBody inner replacement ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨(inner, focus), ih, rfl⟩))
  | substReplacement body inner ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨(inner, focus), ih, rfl⟩))
  | collection kind before inner after rest ih =>
    simp only [OneHoleContext.fill]
    rw [decompositions]
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    have bounded : before.length < (before ++ inner.fill focus :: after).length := by simp
    refine ⟨(⟨(before ++ inner.fill focus :: after)[before.length], List.getElem_mem bounded⟩, before.length),
      mem_zipIdx_attach bounded, ?_⟩
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, List.mem_map]
    exact ⟨(inner, focus), ih, by simp⟩

/-- A licensed site's binder context is the caller's, extended by the binders above its hole. -/
theorem focusBound_length {language : LanguageDef} {free : FreeTypeContext}
    {permissions : GeneralTypedSites.OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed language free permissions bound expected
      source site) :
    site.focusBound.length = bound.length + binderDepth site.context := by
  induction licensed with
  | here => simp [GeneralTypedSites.SiteData.here, binderDepth]
  | application _ _ _ _ _ _ _ _ _ ih => simpa [GeneralTypedSites.SiteData.wrapApplication, binderDepth] using ih
  | lambda _ _ ih =>
    simp only [GeneralTypedSites.SiteData.wrapLambda, binderDepth, List.length_cons] at ih ⊢
    omega
  | multiLambda _ _ ih =>
    simp only [GeneralTypedSites.SiteData.wrapMultiLambda, binderDepth, List.length_append,
      List.length_replicate] at ih ⊢
    omega
  | directCollection _ _ _ _ _ ih => simpa [GeneralTypedSites.SiteData.wrapCollection, binderDepth] using ih
  | authoredCollection _ _ _ _ _ _ _ ih => simpa [GeneralTypedSites.SiteData.wrapCollection, binderDepth] using ih

/-! ## Declared dependency contexts of matched values -/

/-- Every stored value has its metavariable's declared dependency context. -/
def Declared (spec : RuleBindingSpec) (assignment : Assignment) : Prop :=
  ∀ name value, lookup assignment name = some value → dependencies? spec name = some value.dependencies

theorem assign_declared {spec : RuleBindingSpec} {initial final : Assignment} {name : String}
    {value : ContextualValue} (before : Declared spec initial)
    (declared : dependencies? spec name = some value.dependencies) (assigned : assign initial name value = some final) :
    Declared spec final := by
  unfold assign at assigned
  cases prior : lookup initial name with
  | none =>
    simp only [prior, Option.some.injEq] at assigned
    subst final
    intro other otherValue found
    by_cases same : other = name
    · subst same
      rw [lookup_cons_self] at found
      cases found
      exact declared
    · rw [lookup_cons_other _ _ same] at found
      exact before other otherValue found
  | some earlier =>
    simp only [prior] at assigned
    split at assigned
    · cases assigned
      exact before
    · cases assigned

theorem capture_declared {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {name : String} {target : Pattern}
    (before : Declared spec initial)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    Declared spec final := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, _, _, value, recovered, assigned⟩ := captured
  have context := recoverValue?_context _ _ _ _ _ _ recovered
  exact assign_declared before (by rw [declared, context.1]) assigned

mutual
  theorem matches_declared {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
      {pattern target : Pattern} (before : Declared spec initial)
      (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial pattern target final) :
      Declared spec final := by
    cases matching with
    | capture captured => exact capture_declared before captured
    | bound => exact before
    | constructor arguments => exact arguments_declared before arguments
    | binder body => exact matches_declared before body
    | binders body => exact matches_declared before body
    | substitution body replacement => exact matches_declared (matches_declared before body) replacement
    | bag _ bag => exact bag_declared before bag
    | vector arguments => exact arguments_declared before arguments
    | vectorRest arguments captured =>
      unfold captureRest? at captured
      exact capture_declared (arguments_declared before arguments) captured

  theorem arguments_declared {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment} {index : Nat}
      {patterns targets : List Pattern} (before : Declared spec initial)
      (matching : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index patterns targets final) :
      Declared spec final := by
    cases matching with
    | nil => exact before
    | cons head tail => exact arguments_declared (matches_declared before head) tail

  theorem bag_declared {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment} {index : Nat}
      {patterns : List Pattern} {rest : Option String} {kind : CollType} {targets : List Pattern}
      (before : Declared spec initial)
      (matching : GeneralScopedMatch.Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
      Declared spec final := by
    cases matching with
    | nil => exact before
    | rest captured =>
      unfold captureRest? at captured
      exact capture_declared before captured
    | cons _ _ head tail => exact bag_declared (matches_declared before head) tail
end

/-! ## Predecessors -/

/-- The matcher of an equation's right side at a focus. -/
abbrev rightRequest (equation : EquationPlan) (ambient : Nat) (focus : Pattern) : GeneralScopedMatchMachine.Request :=
  ⟨equation.rule, equation.binding.spec, ambient, .right, [], 0, [], equation.rule.right, focus⟩

/-- Every match of an equation's right side at a focus, by the completed scoped matcher. -/
def rightMatches (equation : EquationPlan) (ambient : Nat) (focus : Pattern) : List Assignment :=
  (GeneralEquationJobExecution.finishMatcher (rightRequest equation ambient focus)
    (GeneralScopedMatchMachine.start (rightRequest equation ambient focus))).answers.map (·.assignment)

/-- The candidate sources of equation instances into a term. -/
def predecessors (plan : Plan) (bound : List TypeExpr) (target : Pattern) : List Pattern :=
  (decompositions target).flatMap fun (context, focus) =>
    plan.equations.flatMap fun equation =>
      let ambient := bound.length + binderDepth context
      (rightMatches equation ambient focus).flatMap
        fun captures =>
          match instantiateAt? equation.rule equation.binding.spec ambient .left [] 0 captures equation.rule.left with
          | none => []
          | some rebuilt => (variants equation.rule.left rebuilt).map fun source =>
              (context.fill source).eraseBinderMetadata

theorem predecessors_eq_nil_of_no_equations (plan : Plan) (bound : List TypeExpr) (target : Pattern)
    (empty : plan.equations = []) : predecessors plan bound target = [] := by
  simp [predecessors, empty]

/-- Every equation of the plan passes the balance admission. -/
def equationsChecked (plan : Plan) : Bool :=
  plan.equations.all fun equation => GeneralEquationAdmission.checkRule equation.rule equation.binding.spec

/-- Every accepted compiled plan has balanced equations. -/
theorem equationsChecked_of_complete {snapshot : Snapshot} {permissions : Permissions}
    (accepted : (compile snapshot permissions).complete = true) : equationsChecked (compile snapshot permissions) = true :=
  List.all_eq_true.mpr fun _ member => GeneralEquationJobs.compiled_equation_checked accepted member

/-- **Every source of a completed equation rebuilt is a predecessor of its target**, when the
plan's equations are balanced. -/
theorem mem_predecessors {plan : Plan} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (checked : equationsChecked plan = true)
    (completion : GeneralEquationJobs.Completion plan bound type source receipt) :
    source ∈ predecessors plan bound receipt.target := by
  obtain ⟨licensed, sourceTyped, matched, _, premises, _, reduct, _, endpoint⟩ := completion
  have member : receipt.job.equation ∈ plan.equations :=
    List.fst_mem_of_mem_zipIdx licensed.1
  have checked := GeneralEquationAdmission.checkRule_sides _ _ (List.all_eq_true.mp checked _ member)
  have filled := licensed.2.source_eq
  have depthEq := focusBound_length licensed.2
  have sameNames : receipt.job.equation.rule.left.freeFvarNames.Perm receipt.job.equation.rule.right.freeFvarNames := by
    have balanced := GeneralEquationAdmission.balancedSides_balanced checked.2.2.2
    simp only [GeneralEquationMeasures.balanced, Bool.and_eq_true, decide_eq_true_eq] at balanced
    exact balanced.2
  have declared : Declared receipt.job.equation.binding.spec receipt.captured :=
    matches_declared (fun _ _ found => by simp [lookup] at found) matched.matching
  have canonicalCaptured : GeneralPremise.CanonicalValues receipt.captured :=
    GeneralPremise.matching_canonicalValues (fun _ _ found => by simp [lookup] at found)
      (Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _) matched.matching
  have capturedNames := GeneralEquationCaptureDomain.matched_captures matched.matching
  have extension := premises.extension
  have sameValue : ∀ name ∈ receipt.job.equation.rule.left.freeFvarNames,
      lookup receipt.completed name = lookup receipt.captured name := by
    intro name inLeft
    obtain ⟨value, found⟩ := capturedNames name inLeft
    rw [extension name value found, found]
  have fits : Fits receipt.job.equation.binding.spec receipt.completed receipt.job.equation.rule.right.freeFvarNames := by
    intro name inRight value found
    have inLeft := sameNames.symm.subset inRight
    rw [sameValue name inLeft] at found
    exact ⟨declared name value found, canonicalCaptured name value found⟩
  obtain ⟨rightTrace, captures, tracedRight, _, agreeRight⟩ := traced_of_instantiate _ _ _ .right [] 0 receipt.completed []
    _ _ checked.2.2.1 reduct fits (fun _ _ found => by simp [lookup] at found)
  obtain ⟨rebuilt, interpreted, variant⟩ := instantiate_of_traced matched checked.2.1 captures
    (fun name inLeft => by rw [agreeRight name (sameNames.subset inLeft), sameValue name inLeft])
  unfold predecessors
  apply List.mem_flatMap.mpr
  refine ⟨(eraseContext receipt.job.site.context, receipt.rawReduct.eraseBinderMetadata), ?_, ?_⟩
  · rw [endpoint, fill_erase, Pattern.eraseBinderMetadata_idempotent]
    exact mem_decompositions _ _
  · apply List.mem_flatMap.mpr
    refine ⟨receipt.job.equation, member, ?_⟩
    simp only [binderDepth_erase, ← depthEq]
    apply List.mem_flatMap.mpr
    refine ⟨captures, List.mem_map.mpr ⟨⟨captures, rightTrace⟩,
      (GeneralEquationJobExecution.finishMatcher_answers_iff .start _).mpr tracedRight, rfl⟩, ?_⟩
    rw [interpreted]
    apply List.mem_map.mpr
    refine ⟨receipt.job.site.focus.eraseBinderMetadata, by simpa [Pattern.eraseBinderMetadata_idempotent] using variant, ?_⟩
    rw [← fill_erase, filled, Pattern.eraseBinderMetadata_idempotent]
    exact Pattern.eraseBinderMetadata_eq_self_of_canonical sourceTyped.2.1

end Mettapedia.OSLF.MeTTaIL.Complete.Predecessors
