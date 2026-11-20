import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.CollectionMatchingNormalization
import Mettapedia.OSLF.MeTTaIL.CanonicalFiring
import Mettapedia.OSLF.Framework.GeneralFiniteWorkUniqueness

/-!
# Source coverage across collection presentations

Canonicalization can merge set elements. The semantic collection judgment,
rather than injective occurrence matching, transports those firings to the
finite matcher. Typing and constructor computation retain the established
scoped judgments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionRootSearch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags CollectionMatcherBackend RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem raw_receipt_of_collection
    (request : ScopedCollectionMachine.Request) (ready : RootReady request)
    (unordered : request.kind ≠ .vec)
    (fixed : arrange request.kind request.targets = request.targets)
    (captured : ScopedRuleMatching.Assignment)
    (matched : ScopedCollectionMatching.Matches request.rule request.spec 0 .left [] 0 0 []
      request.schemas request.rest request.kind request.targets captured) :
    ∃ receipt : ScopedCollectionMachine.Receipt,
      ScopedCollectionMachine.Valid request receipt ∧ receipt.matching.assignment = captured := by
  have member := (ScopedCollectionMatching.run_exact request.rule request.spec 0 .left [] 0 0
    [] captured request.schemas request.rest unordered (by
      intro setKind
      have distinct := CollectionSelection.canonical_set_distinct request.targets
      rw [setKind] at fixed
      rwa [fixed] at distinct)).mpr matched
  obtain ⟨work, complete⟩ := ScopedCollectionMachine.eventually_complete request
    (ScopedCollectionMachine.start request)
  have values := ScopedCollectionMachine.completed_assignments request work complete
  have found : captured ∈ (ScopedCollectionMachine.publication
      (ScopedCollectionMachine.resume request work (ScopedCollectionMachine.start request))).map
        (fun receipt => receipt.matching.assignment) := by
    rw [values]
    simpa only [ready.ambient, ready.site, ready.path, ready.depth, ready.index, ready.initial] using member
  obtain ⟨receipt, published, same⟩ := List.mem_map.mp found
  exact ⟨receipt, ScopedCollectionMachine.publication_sound request work published, same⟩

def canonicalRequest (declaration : GeneralExecutionAdmission.RulePlan)
    (kind : CollType) (schemas : List Pattern) (rest : Option String) (targets : List Pattern) :
    ScopedCollectionMachine.Request :=
  ⟨declaration.rule, declaration.binding.spec, 0, .left, [], 0, 0, [],
    schemas, rest, kind, arrange kind (targets.map canon)⟩

theorem canonicalRequest_origin
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan)
    {ordinal : Nat} {declaration : GeneralExecutionAdmission.RulePlan}
    (selected : plan.rules[ordinal]? = some declaration)
    {kind : CollType} {schemas targets : List Pattern} {rest : Option String}
    (unordered : kind ≠ .vec) (left : declaration.rule.left = .collection kind schemas rest) :
    (ordinal, canonicalRequest declaration kind schemas rest targets) ∈
      requests plan profile (canon (.collection kind targets none)) := by
  have within : ordinal < plan.rules.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at selected
    contradiction
  apply List.mem_filterMap.mpr
  refine ⟨ordinal, List.mem_range.mpr within, ?_⟩
  cases kind with
  | vec => exact False.elim (unordered rfl)
  | hashBag | hashSet =>
    simp [CollectionExecutionAdmission.requestForSource?, CollectionExecutionAdmission.request?,
      selected, left, canon, canonicalRequest, CollectionExecutionAdmission.arrange_fixed]

/-- Every unconditional source root firing has a packet at the canonical
source, with canonical captures and a collection-equal result. This theorem
quantifies over source presentations and does not count proof witnesses as
additional answer occurrences. -/
theorem canonical_root_source_packet
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    {ordinal : Nat} {declaration : GeneralExecutionAdmission.RulePlan}
    (selected : plan.rules[ordinal]? = some declaration)
    {kind : CollType} {schemas targets : List Pattern} {rest : Option String}
    (unordered : kind ≠ .vec) (left : declaration.rule.left = .collection kind schemas rest)
    (free : ∀ schema ∈ schemas, setFree schema = true)
    (increasing : IncreasingSpines declaration.rule declaration.binding.spec)
    (unconditional : declaration.rule.premises = [])
    (binderOk : BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule)
    {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    {target : Pattern}
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected
      (.collection kind targets none) ordinal trace captured completed history target) :
    ∃ receipt : Receipt,
      receipt.Valid (profile := profile) expected (canon (.collection kind targets none)) ∧
      receipt.matched.ordinal = ordinal ∧
      receipt.matched.receipt.matching.assignment = canonAssignment captured ∧
      receipt.completed = canonAssignment completed ∧ receipt.history = history ∧
      Same target receipt.target := by
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sorted matched typed premises reduced targetTyped =>
    have ruleSame := Option.some.inj (declared.symm.trans (GeneralPlanEnvironment.selected_rule plan selected))
    have specSame := Option.some.inj (specified.symm.trans (GeneralPlanEnvironment.selected_specification plan selected))
    subst rule
    subst spec
    rw [unconditional] at premises
    cases premises
    let request := canonicalRequest declaration kind schemas rest targets
    have ready : RootReady request := ⟨rfl, rfl, rfl, rfl, rfl, rfl, left⟩
    have meaning := CollectionMatchingNormalization.matches_canonical increasing unordered free
      (show GeneralScopedMatch.Matches declaration.rule declaration.binding.spec 0 .left [] 0 []
        (.collection kind schemas rest) (.collection kind targets none) captured from
        left ▸ matched.matching)
    obtain ⟨raw, validRaw, sameRaw⟩ := raw_receipt_of_collection request ready unordered
      (CollectionExecutionAdmission.arrange_fixed _ _) (canonAssignment captured) meaning
    have origin := canonicalRequest_origin profile selected unordered left (targets := targets)
    let authority := match_authority_of_origin plan profile.collection _ origin validRaw
    obtain ⟨answer, _, same⟩ := CollectionMatcherCompatibility.ordinaryAnswers_complete
      ready.index unordered validRaw
    let rootAnswer := CollectionMatcherBackend.ordinaryRootAnswer request raw ready answer
    have sameAnswer : rootAnswer.val.assignment = canonAssignment captured := same.trans sameRaw
    have rematched : GeneralScopedMatchMachine.TracedMatches declaration.rule declaration.binding.spec 0 .left [] 0 []
        declaration.rule.left (CollectionMatcherCompatibility.ordinaryTarget request raw)
        rootAnswer.val.trace (canonAssignment captured) := by
      rw [← sameAnswer]
      exact rootAnswer.property
    obtain ⟨target', reduced', sameTarget⟩ := instantiateWith?_same declaration.rule declaration.binding.spec 0
      (ScopedReflectiveExecution.binderOperation (GeneralPlanEnvironment.environment plan).reflection declaration.rule)
      (binderOperation_same _ declaration.rule binderOk) declaration.rule.right .right [] 0
      captured (canonAssignment captured) target (assignSame_canon captured) reduced
    have transported : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected
        (CollectionMatcherCompatibility.ordinaryTarget request raw) ordinal rootAnswer.val.trace
        (canonAssignment captured) (canonAssignment captured) [] target' :=
      .fire authority.declared authority.specified admitted
        (authority.source_typed (openPatternWellSorted_canon sorted)) rematched
        (typedAssignment_canon typed) (by
          dsimp only [canonicalRequest]
          rw [unconditional]
          exact .nil) reduced'
        (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp sameTarget) targetTyped)
    let receipt : Receipt := ⟨⟨ordinal, request, raw⟩, canonAssignment captured, [], target'⟩
    refine ⟨receipt, ⟨authority, rootAnswer.val.trace, ?_⟩, rfl, sameRaw, rfl, rfl, sameTarget⟩
    simpa only [receipt, sameRaw] using transported

theorem canonical_root_covered
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    {ordinal : Nat} {declaration : GeneralExecutionAdmission.RulePlan}
    (selected : plan.rules[ordinal]? = some declaration)
    {kind : CollType} {schemas targets : List Pattern} {rest : Option String}
    (unordered : kind ≠ .vec) (left : declaration.rule.left = .collection kind schemas rest)
    (free : ∀ schema ∈ schemas, setFree schema = true)
    (increasing : IncreasingSpines declaration.rule declaration.binding.spec)
    (unconditional : declaration.rule.premises = [])
    (binderOk : BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule)
    {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    {target : Pattern}
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected
      (.collection kind targets none) ordinal trace captured completed history target) :
    ∃ work receipt, receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run (canon (.collection kind targets none)) work) ∧
      receipt.matched.ordinal = ordinal ∧
      receipt.matched.receipt.matching.assignment = canonAssignment captured ∧
      receipt.completed = canonAssignment completed ∧ receipt.history = history ∧
      canon receipt.target = canon target := by
  obtain ⟨receipt, valid, ordinalEq, capturesEq, completedEq, historyEq, same⟩ :=
    canonical_root_source_packet profile expected selected unordered left free increasing unconditional binderOk held
  obtain ⟨work, published⟩ := source_coverage expected valid
  exact ⟨work, receipt, published, ordinalEq, capturesEq, completedEq, historyEq, same.symm⟩

private theorem licensed_root_eq
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed language free
      .rootOnly bound expected source site) :
    site = GeneralTypedSites.SiteData.here bound expected source := by
  cases licensed <;> simp_all [GeneralTypedSites.OperationalPermissions.rootOnly]

/-- The local syntactic conditions used by canonical root coverage. These
conditions describe the rule, not a supplied execution-correctness result. -/
def CanonicalRootRule (reflection : Reflection.ReflectionProfile)
    (declaration : GeneralExecutionAdmission.RulePlan) : Prop :=
  ∃ kind schemas rest, kind ≠ CollType.vec ∧
    declaration.rule.left = .collection kind schemas rest ∧
    (∀ schema ∈ schemas, setFree schema = true) ∧
    IncreasingSpines declaration.rule declaration.binding.spec ∧ declaration.rule.premises = [] ∧
    BinderLawsFor [] reflection declaration.rule

/-- Read the variable indices of an authored substitution, independently of
the binder depth at which it will be used. -/
def spineIndices? (arguments : List Pattern) : Option (List Nat) :=
  arguments.mapM fun argument => match argument with
    | .bvar index => some index
    | _ => none

private theorem spineIndices_bvars (indices : List Nat) :
    spineIndices? (indices.map Pattern.bvar) = some indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp [spineIndices?, List.mapM_cons] at ih ⊢
    rw [ih]
    rfl

/-- Nonvariable and noninjective substitutions cannot be variable-spine
captures. Genuine variable spines must list their indices increasingly. -/
def checkSpineOrder (arguments : List Pattern) : Bool :=
  match spineIndices? arguments with
  | none => true
  | some indices => !decide indices.Nodup || decide (indices.Pairwise (· < ·))

private theorem checkSpineOrder_sound {arguments : List Pattern} {depth : Nat} {indices : List Nat}
    (checked : checkSpineOrder arguments = true)
    (spine : variableSpine? depth arguments = some indices) : indices.Pairwise (· < ·) := by
  have distinct : indices.Nodup := by
    unfold variableSpine? at spine
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
    obtain ⟨found, _, rest⟩ := spine
    split at rest
    · cases rest; assumption
    · cases rest
  rw [variableSpine?_arguments spine] at checked
  simpa only [checkSpineOrder, spineIndices_bvars, distinct, decide_true, Bool.not_true,
    Bool.false_or, decide_eq_true_eq] using checked

/-- A finite declaration check supplies the existing universally quantified
spine condition, without restricting the number of dependencies. -/
def checkBindingSpines (spec : RuleBindingSpec) : Bool :=
  spec.occurrences.all fun occurrence => checkSpineOrder occurrence.arguments

theorem checkBindingSpines_sound {rule : RewriteRule} {spec : RuleBindingSpec}
    (checked : checkBindingSpines spec = true) : IncreasingSpines rule spec := by
  intro name site path arguments found depth indices spine
  unfold RuleBinding.arguments? at found
  simp only [bind, Option.bind_eq_some_iff, guard, pure] at found
  obtain ⟨dependencies, _, _, _, rest⟩ := found
  cases rowsEq : spec.occurrences.filter
      (fun row => row.name == name && row.site == site && row.path == path) with
  | nil =>
    rw [rowsEq] at rest
    change (if dependencies.isEmpty then some [] else none) = some arguments at rest
    split at rest
    · cases rest
      exact checkSpineOrder_sound (by rfl) spine
    · cases rest
  | cons row rows =>
    cases rows with
    | nil =>
      rw [rowsEq] at rest
      change (if occurrenceDeclared rule row && row.arguments.length == dependencies.length
        then some row.arguments else none) = some arguments at rest
      split at rest
      · cases rest
        have member : row ∈ spec.occurrences := List.mem_of_mem_filter
          (by rw [rowsEq]; exact List.mem_cons_self)
        exact checkSpineOrder_sound (List.all_eq_true.mp checked row member) spine
      · cases rest
    | cons other rows => simp [rowsEq] at rest

/-- Executable local root-rule admission. -/
def canonicalRuleCheck (reflection : Reflection.ReflectionProfile)
    (declaration : GeneralExecutionAdmission.RulePlan) : Bool :=
  match declaration.rule.left with
  | .collection .vec _ _ => false
  | .collection _ schemas _ => setFreeList schemas && declaration.rule.premises.isEmpty &&
      checkBindingSpines declaration.binding.spec && checkBinderLawsFor [] reflection declaration.rule
  | _ => false

theorem canonicalRuleCheck_sound {reflection : Reflection.ReflectionProfile}
    {declaration : GeneralExecutionAdmission.RulePlan}
    (checked : canonicalRuleCheck reflection declaration = true) : CanonicalRootRule reflection declaration := by
  cases left : declaration.rule.left <;> simp [canonicalRuleCheck, left] at checked
  rename_i kind schemas rest
  cases kind with
  | vec => contradiction
  | hashBag | hashSet =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at checked
    obtain ⟨⟨⟨free, unconditional⟩, ordered⟩, compatible⟩ := checked
    exact ⟨_, schemas, rest, by decide, left, setFreeList_iff.mp free,
      checkBindingSpines_sound ordered, unconditional, (checkBinderLawsFor_iff _ _ _).mp compatible⟩

/-- A recognized backend profile records local declaration and algebra
conditions. Its source-coverage theorem is derived below, never supplied. -/
structure CoverageProfile (plan : GeneralExecutionAdmission.Plan) where
  profile : Profile plan
  rules : ∀ declaration ∈ plan.rules,
    CanonicalRootRule (GeneralPlanEnvironment.environment plan).reflection declaration
  noLaws : Complete.Normalized.laws plan = []
  noExtrusions : Complete.Normalized.extrusions plan = []

def coverageProfile? (plan : GeneralExecutionAdmission.Plan) : Option (CoverageProfile plan) := do
  let profile ← profile? plan
  if rules : plan.rules.all (canonicalRuleCheck (GeneralPlanEnvironment.environment plan).reflection) = true then
    if laws : Complete.Normalized.laws plan = [] then
      if extrusions : Complete.Normalized.extrusions plan = [] then
        some ⟨profile, fun declaration member => canonicalRuleCheck_sound
          (List.all_eq_true.mp rules declaration member), laws, extrusions⟩
      else none
    else none
  else none

/-- Every primitive source occurrence, at any presentation, is covered at
the canonical source. Declaration position and captures remain identified. -/
theorem canonical_primitive_covered
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    (rules : ∀ declaration ∈ plan.rules,
      CanonicalRootRule (GeneralPlanEnvironment.environment plan).reflection declaration)
    {source : Pattern} {original : GeneralRuleJobs.Receipt}
    (valid : original.Valid plan [] expected source) :
    ∃ work receipt, receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run (canon source) work) ∧
      receipt.matched.ordinal = original.job.ordinal ∧
      receipt.matched.receipt.matching.assignment = canonAssignment original.captured ∧
      receipt.completed = canonAssignment original.completed ∧ receipt.history = original.premiseHistory ∧
      canon receipt.target = canon original.target := by
  obtain ⟨licensed, held, _, endpoint, _⟩ := valid
  have root := licensed.2
  rw [profile.rootOnly] at root
  have siteEq := licensed_root_eq root
  have position := List.mk_mem_zipIdx_iff_getElem?.mp licensed.1
  obtain ⟨kind, schemas, rest, unordered, left, free, increasing, unconditional, binderOk⟩ :=
    rules original.job.declaration (List.fst_mem_of_mem_zipIdx licensed.1)
  have firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected source
      original.job.ordinal original.matcherTrace original.captured original.completed
      original.premiseHistory original.localTarget := by
    simpa only [siteEq, GeneralTypedSites.SiteData.here, GeneralPlanEnvironment.environmentWith_empty] using held
  have matching : GeneralScopedMatch.Matches original.job.declaration.rule
      original.job.declaration.binding.spec 0 .left [] 0 []
      (.collection kind schemas rest) source original.captured := by
    cases firing with
    | fire declared specified _ _ matched _ _ _ _ =>
      have ruleSame := Option.some.inj (declared.symm.trans (GeneralPlanEnvironment.selected_rule plan position))
      have specSame := Option.some.inj (specified.symm.trans (GeneralPlanEnvironment.selected_specification plan position))
      simpa only [ruleSame, specSame, left, List.length_nil] using matched.matching
  have shape : ∃ targets, source = .collection kind targets none := by
    cases matching with
    | bag _ _ => exact ⟨_, rfl⟩
    | vector _ => exact False.elim (unordered rfl)
    | vectorRest _ _ => exact False.elim (unordered rfl)
  obtain ⟨targets, sourceEq⟩ := shape
  have targetEq : original.target = original.localTarget := by
    simpa only [siteEq, GeneralTypedSites.SiteData.here,
      DerivedContexts.OneHoleContext.fill] using endpoint
  rw [sourceEq] at firing ⊢
  rw [targetEq]
  exact canonical_root_covered profile expected position unordered left free increasing unconditional binderOk firing

private theorem standardStep_bagStep_nil {left right : Pattern}
    (step : StandardStep [] [] left right) : BagStep left right := by
  induction step with
  | law step => exact step.bagStep_nil
  | extrude absent => cases absent
  | apply _ ih => exact .apply ih
  | lambda _ ih => exact .lambda ih
  | multiLambda _ ih => exact .multiLambda ih
  | substBody _ ih => exact .substBody ih
  | substReplacement _ ih => exact .substReplacement ih
  | element _ ih => exact .element ih

theorem modelEquiv_canon
    {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} (expected : TypeExpr)
    (noEquations : plan.equations = [])
    (laws : Complete.Normalized.laws plan = []) (extrusions : Complete.Normalized.extrusions plan = [])
    {left right : Pattern} (related : Complete.Presented.ModelEquiv plan bound expected left right) :
    canon left = canon right := by
  induction related with
  | rel left right step =>
    rcases step with equation | standard
    · obtain ⟨receipt, complete, _⟩ := equation
      have member := complete.job.1
      rw [noEquations] at member
      cases member
    · rw [laws, extrusions] at standard
      exact ((same_iff _ _).mpr (.rel _ _ (standardStep_bagStep_nil standard)))
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Completeness for the independently defined presented GSLT when its only
model equalities are the built-in bag/set equalities. The result is an actual
published source packet; arbitrary equation proofs do not become occurrences. -/
theorem presented_covered
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    (rules : ∀ declaration ∈ plan.rules,
      CanonicalRootRule (GeneralPlanEnvironment.environment plan).reflection declaration)
    (laws : Complete.Normalized.laws plan = []) (extrusions : Complete.Normalized.extrusions plan = [])
    {source target : Pattern} (stepped : (Complete.Presented.gslt plan [] expected).Step source target) :
    ∃ work receipt, receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run (canon source) work) ∧
      canon receipt.target = canon target := by
  obtain ⟨representative, original, before, valid, after⟩ := stepped
  have beforeEq := modelEquiv_canon expected profile.noEquations laws extrusions before
  have afterEq := modelEquiv_canon expected profile.noEquations laws extrusions after
  obtain ⟨work, receipt, published, _, _, _, _, targetEq⟩ :=
    canonical_primitive_covered profile expected rules valid
  rw [← beforeEq] at published
  exact ⟨work, receipt, published, targetEq.trans afterEq⟩

/-- The source relation and the one shared search agree on canonical
successors. Occurrence conservation is separately provided by the retained
per-allocation publication theorem, rather than by counting equality proofs. -/
theorem presented_iff_published
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    (rules : ∀ declaration ∈ plan.rules,
      CanonicalRootRule (GeneralPlanEnvironment.environment plan).reflection declaration)
    (laws : Complete.Normalized.laws plan = []) (extrusions : Complete.Normalized.extrusions plan = [])
    (source target : Pattern) :
    (Complete.Presented.gslt plan [] expected).Step source (canon target) ↔
      ∃ work receipt, receipt ∈ (search (profile := profile) expected).publication
        ((search (profile := profile) expected).run (canon source) work) ∧
        canon receipt.target = canon target := by
  constructor
  · intro stepped
    simpa only [canon_idempotent] using presented_covered profile expected rules laws extrusions stepped
  · rintro ⟨work, receipt, published, same⟩
    have stepped := (search_lawful (profile := profile) expected).sound _ _ _ published
    have actual := Receipt.presented_step expected stepped
    rw [same] at actual
    obtain ⟨target', actual', equal⟩ := Complete.Presented.presentation_invariant plan [] expected
      (Relation.EqvGen.symm _ _ (Complete.Presented.canon_equiv plan [] expected source)) actual
    exact Complete.Presented.step_resp_right plan [] expected actual' (.symm _ _ equal)

/-- A reported complete frontier contains every valid source packet.
The proof combines eventual coverage with prefix growth and stability;
completion is not inferred from a bounded observation alone. -/
theorem packet_exact_of_complete
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    (source : Pattern) (work : Nat)
    (complete : (search (profile := profile) expected).status
      ((search (profile := profile) expected).run source work) = .complete)
    (receipt : Receipt) :
    receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run source work) ↔
      receipt.Valid (profile := profile) expected source := by
  constructor
  · exact (search_lawful expected).sound source work receipt
  · intro valid
    obtain ⟨eventual, published⟩ := source_coverage expected valid
    have growing := (search_lawful (profile := profile) expected).publication_prefix source eventual work
    have stable := (search_stable (profile := profile) expected)
      ((search (profile := profile) expected).run source work) eventual complete
    rw [(search_lawful expected).resume_run] at stable
    have member := growing.subset published
    rw [Nat.add_comm eventual work, stable.1] at member
    exact member

theorem presented_iff_complete_publication
    {plan : GeneralExecutionAdmission.Plan} (certificate : CoverageProfile plan) (expected : TypeExpr)
    (source target : Pattern) (work : Nat)
    (complete : (search (profile := certificate.profile) expected).status
      ((search (profile := certificate.profile) expected).run (canon source) work) = .complete) :
    (Complete.Presented.gslt plan [] expected).Step source (canon target) ↔
      ∃ receipt, receipt ∈ (search (profile := certificate.profile) expected).publication
        ((search (profile := certificate.profile) expected).run (canon source) work) ∧
        canon receipt.target = canon target := by
  rw [presented_iff_published certificate.profile expected certificate.rules
    certificate.noLaws certificate.noExtrusions]
  constructor
  · rintro ⟨eventual, receipt, published, targetEq⟩
    have valid := (search_lawful (profile := certificate.profile) expected).sound _ _ _ published
    exact ⟨receipt, (packet_exact_of_complete certificate.profile expected _ work complete receipt).mpr valid,
      targetEq⟩
  · rintro ⟨receipt, published, targetEq⟩
    exact ⟨work, receipt, published, targetEq⟩

/-- Every successor of an explored canonical node appears as an edge when
the shared explorer is settled. State sharing does not remove receipt edges. -/
theorem explorer_canonical
    {plan : GeneralExecutionAdmission.Plan} (profile : Profile plan) (expected : TypeExpr)
    (source : Pattern) (work : Nat)
    {node : Complete.Explore.Node Pattern (Run (profile := profile) expected) Receipt}
    (present : node ∈ (Complete.Explore.explore
      (search (profile := profile) expected) (canon source) work).nodes) :
    canon node.state = node.state := by
  obtain ⟨current, receipts, states, born, run, consumed⟩ := node
  obtain ⟨history, head, last⟩ := Complete.Explore.node_chain (search_lawful expected) (canon source) work _ present
  change canon current = current
  change states.head? = some current at head
  change states.getLast? = some (canon source) at last
  cases history with
  | start state =>
    have headEq : state = current := Option.some.inj head
    have lastEq : state = canon source := Option.some.inj last
    rw [← headEq, lastEq]
    exact canon_idempotent source
  | @commit state states receipts receipt previous valid =>
    have headEq : canon receipt.target = current := Option.some.inj head
    rw [← headEq]
    exact canon_idempotent receipt.target

theorem explores_presented_multistep
    {plan : GeneralExecutionAdmission.Plan} (certificate : CoverageProfile plan) (expected : TypeExpr)
    (source : Pattern) {target : Pattern}
    (reaches : (Complete.Presented.gslt plan [] expected).MultiStep source target) :
    Complete.Explore.Explored (S := search (profile := certificate.profile) expected) (canon source) (canon target) := by
  have along : ∀ first last,
      (Complete.Presented.gslt plan [] expected).MultiStep first last →
      Complete.Explore.Explored (S := search (profile := certificate.profile) expected) (canon source) (canon first) →
      Complete.Explore.Explored (S := search (profile := certificate.profile) expected) (canon source) (canon last) := by
    intro first last reaches
    induction reaches with
    | refl => exact id
    | @step first middle last stepped _ ih =>
      intro explored
      obtain ⟨work, receipt, published, same⟩ := presented_covered certificate.profile expected
        certificate.rules certificate.noLaws certificate.noExtrusions stepped
      have next := Complete.Explore.explored_target (search_lawful expected) explored published
      change Complete.Explore.Explored (S := search (profile := certificate.profile) expected)
        (canon source) (canon receipt.target) at next
      rw [same] at next
      exact ih next
  exact along source target reaches (Complete.Explore.explored_source _)

theorem edges_cover_presented_steps
    {plan : GeneralExecutionAdmission.Plan} (certificate : CoverageProfile plan) (expected : TypeExpr)
    (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (search (profile := certificate.profile) expected)
      (Complete.Explore.explore (search (profile := certificate.profile) expected) source work) = true)
    {node : Complete.Explore.Node Pattern (Run (profile := certificate.profile) expected) Receipt}
    (present : node ∈ (Complete.Explore.explore
      (search (profile := certificate.profile) expected) source work).nodes)
    (canonical : canon node.state = node.state) {target : Pattern}
    (stepped : (Complete.Presented.gslt plan [] expected).Step node.state target) :
    ∃ receipt, (node.state, receipt, canon receipt.target) ∈
      Complete.Graph.edges (search (profile := certificate.profile) expected)
        (Complete.Explore.explore (search (profile := certificate.profile) expected) source work) ∧
      canon receipt.target = canon target := by
  obtain ⟨rounds, receipt, published, same⟩ := presented_covered certificate.profile expected
    certificate.rules certificate.noLaws certificate.noExtrusions stepped
  rw [canonical] at published
  exact ⟨receipt, Complete.Graph.edges_complete (search_lawful expected) (search_stable expected)
    source work done node present rounds receipt published, same⟩

/-- At a settled explored graph, the recorded edges agree exactly with
source successors at every explored node. Several receipts may have the
same target; this relation comparison leaves those entries intact. -/
theorem settled_graph_source_exact
    {plan : GeneralExecutionAdmission.Plan} (certificate : CoverageProfile plan) (expected : TypeExpr)
    (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (search (profile := certificate.profile) expected)
      (Complete.Explore.explore (search (profile := certificate.profile) expected) (canon source) work) = true) :
    (∀ edge ∈ Complete.Graph.edges (search (profile := certificate.profile) expected)
      (Complete.Explore.explore (search (profile := certificate.profile) expected) (canon source) work),
      (Complete.Presented.gslt plan [] expected).Step edge.1 edge.2.2) ∧
    ∀ node ∈ (Complete.Explore.explore (search (profile := certificate.profile) expected) (canon source) work).nodes,
      ∀ target, (Complete.Presented.gslt plan [] expected).Step node.state (canon target) ↔
        ∃ receipt, (node.state, receipt, canon target) ∈ Complete.Graph.edges
          (search (profile := certificate.profile) expected)
          (Complete.Explore.explore (search (profile := certificate.profile) expected) (canon source) work) := by
  have sound : ∀ edge ∈ Complete.Graph.edges (search (profile := certificate.profile) expected)
      (Complete.Explore.explore (search (profile := certificate.profile) expected) (canon source) work),
      (Complete.Presented.gslt plan [] expected).Step edge.1 edge.2.2 := by
    intro edge member
    obtain ⟨valid, targetEq⟩ := Complete.Graph.edge_valid (search_lawful expected) (canon source) work edge member
    rw [targetEq]
    exact Receipt.presented_step expected valid
  refine ⟨sound, ?_⟩
  intro node present target
  constructor
  · intro stepped
    obtain ⟨receipt, member, targetEq⟩ := edges_cover_presented_steps certificate expected (canon source) work done
      present (explorer_canonical certificate.profile expected source work present) stepped
    rw [canon_idempotent] at targetEq
    exact ⟨receipt, targetEq ▸ member⟩
  · rintro ⟨receipt, member⟩
    exact sound _ member

/-! ## Exact receipt multisets from finite work accounts -/

variable {plan : GeneralExecutionAdmission.Plan} {certificate : CollectionExecutionAdmission.Certificate plan}
    {source : Pattern} {expected : TypeExpr}
    (matched : Retained.Match)
    (authority : MatchAuthority plan certificate source matched.ordinal matched.request matched.receipt)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source) (depth : Nat)

abbrev initialContinuation := Retained.Frame.initial matched authority typed depth

/-- The existing finite work tree for one source-derived raw origin. It
contains the actual typed continuation, not a supplied answer list. -/
def continuationForest : GeneralPremise.Scheduler.TaskForest
    (StructuralDescent.Scheduled.expand (GeneralPlanEnvironment.environment plan)
      (.root (depth + 1) [] expected
        (CollectionMatcherCompatibility.ordinaryTarget matched.request matched.receipt) matched.ordinal))
    (initialContinuation matched authority typed depth).state.agenda :=
  StructuralDescent.Scheduled.continueRootAnswers_forest
    (GeneralPlanEnvironment.environment plan)
    (.root (depth + 1) [] expected
      (CollectionMatcherCompatibility.ordinaryTarget matched.request matched.receipt) matched.ordinal)
    depth [] expected (CollectionMatcherCompatibility.ordinaryTarget matched.request matched.receipt)
    matched.ordinal matched.request.rule matched.request.spec authority.declared authority.specified authority.admitted
    (authority.source_typed typed) (.done _)
    (StructuralDescent.Scheduled.doneTrees _ _) [] .nil
    ((rawRootAnswers matched.request matched.receipt authority.ready).take 1)

/-- A drained continuation publishes exactly its finite work-tree readout.
This equality retains all answer occurrences and premise origins. -/
theorem continuation_readouts_exact (work : Nat)
    (idle : (Retained.Frame.run work (initialContinuation matched authority typed depth)).state.agenda = []) :
    (Retained.Frame.run work (initialContinuation matched authority typed depth)).publication =
      (continuationForest matched authority typed depth).answers.filterMap
        (initialContinuation matched authority typed depth).read := by
  let frame := initialContinuation matched authority typed depth
  let forest := continuationForest matched authority typed depth
  let expand := StructuralDescent.Scheduled.expand (matcher := GeneralPremise.MatchingExecution.ordinary)
    (GeneralPlanEnvironment.environment plan)
    (.root (depth + 1) [] expected
      (CollectionMatcherCompatibility.ordinaryTarget matched.request matched.receipt) matched.ordinal)
  have empty : frame.state.answers = [] := by
    simp only [frame, initialContinuation, Retained.Frame.initial, startMatch, startRequest,
      StructuralDescent.Scheduled.continueRootAnswers_answers]
  have referenceIdle := GeneralPremise.Scheduler.finiteWork_drains expand forest.cost frame.state forest (Nat.le_refl _)
  have readout := GeneralPremise.Scheduler.finiteWork_readouts expand forest.cost frame.state forest (Nat.le_refl _)
  have same := GeneralPremise.Scheduler.settled_run_unique expand frame.state work forest.cost idle referenceIdle
  have answers : (Retained.Frame.run work frame).state.answers = forest.answers := by
    change (GeneralPremise.Scheduler.run expand work frame.state).answers = _
    rw [same, readout.1, empty]
    rfl
  change ((Retained.Frame.run work frame).state.answers.filterMap (Retained.Frame.run work frame).read) = _
  rw [answers]
  rfl


/-- Observable source packets of the finite continuation account. -/
def continuationPackets : List Retained.Publication :=
  (continuationForest matched authority typed depth).answers.filterMap
    (initialContinuation matched authority typed depth).read

omit matched authority typed depth in
/-- Chronological batch publication is a permutation of the independently
accounted continuation packets, preserving multiplicity across raw origins. -/
theorem retained_readout_multiset_exact
    (origins : List (Retained.CheckedMatch plan certificate source))
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source)
    (depth : Retained.Match → Nat) (work : Nat)
    (done : (Retained.State.run work (Retained.State.initial origins typed depth)).complete = true) :
    (Retained.State.run work (Retained.State.initial origins typed depth)).log.Perm
      (origins.flatMap fun matched => continuationPackets matched.val matched.property typed (depth matched.val)) := by
  have balanced : (Retained.State.run work (Retained.State.initial origins typed depth)).Balanced :=
    Retained.State.run_balanced work (Retained.State.begin_balanced _)
  apply balanced.trans
  apply List.Perm.of_eq
  rw [Retained.State.run_frames]
  change ((origins.map fun matched => Retained.Frame.initial matched.val matched.property typed (depth matched.val)).map
    (Retained.Frame.run work)).flatMap Retained.Frame.publication = _
  simp only [List.flatMap_map, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro matched member
  apply continuation_readouts_exact
  have initial : Retained.Frame.initial matched.val matched.property typed (depth matched.val) ∈
      (Retained.State.initial origins typed depth).frames := List.mem_map_of_mem member
  have retained : Retained.Frame.run work (Retained.Frame.initial matched.val matched.property typed (depth matched.val)) ∈
      (Retained.State.run work (Retained.State.initial origins typed depth)).frames := by
    rw [Retained.State.run_frames]
    exact List.mem_map_of_mem initial
  exact List.isEmpty_iff.mp (List.all_eq_true.mp done _ retained)


omit matched authority typed depth in
/-- Matching completion and typed continuation accounting compose: one
complete root frontier has exactly the source-derived packet multiset.
Ordinary validation witnesses are selected once per retained raw origin. -/
theorem root_publication_multiset_exact
    {profile : Profile plan}
    (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source) :
    ∃ matching : Matching plan profile source,
      CollectionPlanMachine.complete matching.state = true ∧
      ∃ work, (search (profile := profile) expected).status
        ((search (profile := profile) expected).run source work) = .complete ∧
        ((search (profile := profile) expected).publication
          ((search (profile := profile) expected).run source work)).Perm
          ((matching.matches.flatMap fun origin =>
            continuationPackets origin.val origin.property typed (CollectionRootSearch.depth origin.val)).map observe) := by
  obtain ⟨enteredAt, matching, matched, entered⟩ :=
    matching_enters_continuing expected typed (Matching.begin source)
  obtain ⟨work, finished⟩ := Retained.State.eventually_settled matching.matches typed CollectionRootSearch.depth
  have reached : (search (profile := profile) expected).run source (enteredAt + work) =
      ⟨source, .continuing typed
        (Retained.State.run work (Retained.State.initial matching.matches typed CollectionRootSearch.depth))
        (Retained.State.run_balanced work (Retained.State.begin_balanced _))⟩ := by
    change rounds expected (enteredAt + work) (begin expected source) = _
    rw [begin_typed expected source typed, rounds_add, entered]
    erw [rounds_continuing]
  refine ⟨matching, matched, enteredAt + work, ?_, ?_⟩
  · rw [reached]
    simp only [search, status, finished, ↓reduceIte]
  · rw [reached]
    exact (retained_readout_multiset_exact matching.matches typed CollectionRootSearch.depth work finished).map observe



omit matched authority typed depth in
/-- Completing at different work bounds yields the same chronological
publication, not merely the same set of targets. -/
theorem complete_publications_unique {profile : Profile plan} (source : Pattern)
    (first second : Nat)
    (firstDone : (search (profile := profile) expected).status
      ((search (profile := profile) expected).run source first) = .complete)
    (secondDone : (search (profile := profile) expected).status
      ((search (profile := profile) expected).run source second) = .complete) :
    (search (profile := profile) expected).publication ((search (profile := profile) expected).run source first) =
      (search (profile := profile) expected).publication ((search (profile := profile) expected).run source second) := by
  have front := (search_stable (profile := profile) expected) ((search expected).run source first) second firstDone
  have back := (search_stable (profile := profile) expected) ((search expected).run source second) first secondDone
  rw [(search_lawful expected).resume_run] at front back
  calc
    _ = (search (profile := profile) expected).publication
        ((search expected).run source (first + second)) := front.1.symm
    _ = (search (profile := profile) expected).publication
        ((search expected).run source (second + first)) := by rw [Nat.add_comm first second]
    _ = _ := back.1

omit matched authority typed depth in
/-- Every completed frontier has the exact source-derived packet multiset.
The completion bound is not an input to the occurrence-counting policy. -/
theorem complete_publication_multiset_exact {profile : Profile plan} (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source) (work : Nat)
    (done : (search (profile := profile) expected).status
      ((search (profile := profile) expected).run source work) = .complete) :
    ∃ matching : Matching plan profile source,
      CollectionPlanMachine.complete matching.state = true ∧
      ((search (profile := profile) expected).publication ((search expected).run source work)).Perm
        ((matching.matches.flatMap fun origin => continuationPackets origin.val origin.property typed
          (CollectionRootSearch.depth origin.val)).map observe) := by
  obtain ⟨matching, matched, actual, complete, accounted⟩ := root_publication_multiset_exact source typed
  exact ⟨matching, matched, (complete_publications_unique source work actual done complete) ▸ accounted⟩

end Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
