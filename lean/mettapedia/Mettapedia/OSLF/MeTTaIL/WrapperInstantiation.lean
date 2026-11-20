import Mettapedia.OSLF.MeTTaIL.WrapperReflective
import Mettapedia.OSLF.MeTTaIL.QuoteDropInstantiation

/-!
# Instantiating right sides with wrapper normal captures

A right side instantiated with the captures mapped by their roles (`wrapperAssignment`) gives a result
reached from the original result by a forward chain of quote-drop and wrapper steps
(`instantiateWith?_wrapper`), when its collection rests are rests, no explicit substitution lies under a
binder, and each explicit substitution has an ordinary captured body occurring with a variable spine and
an explicit quotation as replacement (`RightShaped`), and the binder operation respects wrapper normal
bodies (`BinderRespectsWrapper`): the ordinary one always, the reflective one of a closed quote scope
when its result is closed.
Below binders, where no substitution occurs, the result moves by a forward chain without any scope
condition (`instantiateWith?_plain`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch ReflectiveSubstitution CanonicalBags CollectionLaws
open QuoteDrop (spineBody allIndices allIndices_bvars isQuotation lookup_normal_of_mem instantiateArgsWith?_single)

variable {laws : List Laws} {declaration : ReflectivePresentationDecl}

/-! ## Instantiating values -/

/-- **Instantiating a value and its mapped value** gives results joined by a forward chain. -/
theorem instantiateValue?_mapForward {f : Pattern → Pattern} (keepsScope : ∀ pattern depth,
    (f pattern).isWellScopedAt depth = pattern.isWellScopedAt depth)
    (forward : ∀ pattern, QWForward laws declaration pattern (f pattern))
    {value : ContextualValue} {ambient depth : Nat} {arguments : List Pattern} {result : Pattern}
    (found : instantiateValue? value ambient depth arguments = some result) :
    ∃ result', instantiateValue? (mapValue f value) ambient depth arguments = some result' ∧
      QWForward laws declaration result result' ∧
      result' = ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
        (f value.body) ∧
      result = ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body := by
  obtain ⟨ambientOk, lengthOk, bodyScoped, argumentsScoped, substituted, resultScoped⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp found
  have moved : QWForward laws declaration result
      (ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments) (f value.body)) := by
    rw [← substituted]
    exact QWForward.substitute (forward value.body) _
  refine ⟨_, (instantiateValue?_eq_some_iff _ _ _ _ _).mpr ⟨ambientOk, lengthOk, ?_, argumentsScoped, rfl, ?_⟩, moved,
    rfl, substituted.symm⟩
  · simp only [mapValue]; rw [keepsScope]; exact bodyScoped
  · simp only [mapValue]; rw [← QWForward.wellScoped moved]; exact resultScoped

theorem captureMap_keepsScope (rests : List String) (name : String) (pattern : Pattern) (depth : Nat) :
    (captureMap laws rests name pattern).isWellScopedAt depth = pattern.isWellScopedAt depth :=
  (bodyMap_captureMap rests name).keepsScope pattern depth

theorem captureMap_qwForward (rests : List String) (name : String) (pattern : Pattern) :
    QWForward laws declaration pattern (captureMap laws rests name pattern) :=
  QWForward.ofWrapper (captureMap_forward rests name pattern)

/-- A collection instantiated from a rest value is a collection of the same kind when instantiated from
the mapped rest value, with elements joined pointwise by forward chains. -/
theorem substitute_collection_inner {assignment : ContextSubstitution.Assignment} {body : Pattern}
    {kind : CollType} {elements : List Pattern}
    (shape : ContextSubstitution.substitute assignment body = .collection kind elements none) :
    ∃ elements', ContextSubstitution.substitute assignment (wrapperInner laws body) = .collection kind elements' none ∧
      List.Forall₂ (QWForward laws declaration) elements elements' := by
  cases body with
  | bvar index =>
    simp only [wrapperInner, wrapperNormal_bvar]
    exact ⟨elements, shape, List.forall₂_same.mpr fun _ _ => .refl⟩
  | collection kind' items rest =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, Pattern.collection.injEq]
      at shape
    obtain ⟨rfl, rfl, rfl⟩ := shape
    rw [wrapperInner_collection]
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map]
    refine ⟨_, rfl, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun item _ => QWForward.substitute (QWForward.ofWrapper (to_wrapperNormal item)) _
  | _ => simp [ContextSubstitution.substitute] at shape

/-! ## Right sides -/

/-- A collection rest that is a rest. -/
def restShaped (rests : List String) : Option String → Bool
  | some name => rests.contains name
  | none => true

mutual
  /-- A pattern without explicit substitutions whose collection rests are rests. -/
  def PlainRight (rests : List String) : Pattern → Bool
    | .fvar _ => true
    | .bvar _ => true
    | .apply _ arguments => PlainRightList rests arguments
    | .lambda _ body => PlainRight rests body
    | .multiLambda _ _ body => PlainRight rests body
    | .subst _ _ => false
    | .collection _ elements rest => restShaped rests rest && PlainRightList rests elements

  /-- Every pattern of a list is plain. -/
  def PlainRightList (rests : List String) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => PlainRight rests pattern && PlainRightList rests patterns
end

theorem plainRightList_iff {rests : List String} :
    ∀ items : List Pattern, PlainRightList rests items = true ↔ ∀ item ∈ items, PlainRight rests item = true
  | [] => by simp [PlainRightList]
  | item :: rest => by simp [PlainRightList, plainRightList_iff rest]

variable (declaration) in
mutual
  /-- A right side instantiated at wrapper normal captures: collection rests are rests, binders hold
  plain patterns, and each explicit substitution has an ordinary captured body occurring with a variable
  spine and an explicit quotation of a plain pattern as replacement. -/
  def RightShaped (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite) (rests : List String) :
      List Nat → Pattern → Bool
    | _, .fvar _ => true
    | _, .bvar _ => true
    | path, .apply _ arguments => ArgumentsShaped rule spec site rests path 0 arguments
    | _, .lambda _ body => PlainRight rests body
    | _, .multiLambda _ _ body => PlainRight rests body
    | path, .subst (.fvar name) (.apply label [payload]) =>
        !(rests.contains name) && spineBody rule spec site (path ++ [0]) (.fvar name) &&
          label == declaration.quoteConstructor && PlainRight rests payload
    | _, .subst _ _ => false
    | path, .collection _ elements rest => restShaped rests rest && ArgumentsShaped rule spec site rests path 0 elements

  def ArgumentsShaped (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite) (rests : List String) :
      List Nat → Nat → List Pattern → Bool
    | _, _, [] => true
    | path, index, pattern :: patterns =>
        RightShaped rule spec site rests (path ++ [index]) pattern &&
          ArgumentsShaped rule spec site rests path (index + 1) patterns
end

/-! ## Binder operations -/

variable (laws declaration) in
/-- A binder operation that maps the wrapper normal form of its body and a forward chain of its quoted
replacement to a forward chain, when its result is closed. -/
def BinderRespectsWrapper (operation : Pattern → Pattern → Pattern) : Prop :=
  ∀ {payload payload' body : Pattern}, QWForward laws declaration payload payload' →
    (operation (.apply declaration.quoteConstructor [payload]) body).isWellScopedAt 0 = true →
    QWForward laws declaration (operation (.apply declaration.quoteConstructor [payload]) body)
      (operation (.apply declaration.quoteConstructor [payload']) (wrapperNormal laws body))

theorem binderRespectsWrapper_ordinary : BinderRespectsWrapper laws declaration Substitution.instantiateBVar :=
  fun forwardPayload _ => instantiateBVar_qwForward (qwForward_apply _ (.cons forwardPayload .nil))
    (QWForward.ofWrapper (to_wrapperNormal _))

theorem binderRespectsWrapper_reflective (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (closedScope : declaration.quoteScope = .closed)
    (compatible : BinderWrapperCompatible laws declaration) :
    BinderRespectsWrapper laws declaration (ScopedRuleInstantiation.reflectiveOperation declaration) :=
  fun forwardPayload inScope =>
    reflectiveOperation_wrapper distinct closedScope compatible forwardPayload _ inScope

theorem binderRespectsWrapper_binderOperation (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {profile : Reflection.ReflectionProfile} {rule : RewriteRule}
    (selection : substitutionPresentationForRule? profile rule = none ∨
      (substitutionPresentationForRule? profile rule = some declaration ∧
        declaration.quoteScope = .closed ∧ BinderWrapperCompatible laws declaration)) :
    BinderRespectsWrapper laws declaration (ScopedReflectiveExecution.binderOperation profile rule) := by
  rcases selection with ordinary | ⟨reflective, closedScope, compatible⟩
  · simp only [ScopedReflectiveExecution.binderOperation, ordinary]
    exact binderRespectsWrapper_ordinary
  · simp only [ScopedReflectiveExecution.binderOperation, reflective]
    exact binderRespectsWrapper_reflective distinct closedScope compatible

/-! ## Instantiation -/

theorem plainRight_apply {rests : List String} {label : String} {arguments : List Pattern}
    (plain : PlainRight rests (.apply label arguments) = true) : ∀ argument ∈ arguments, PlainRight rests argument = true := by
  rw [PlainRight] at plain
  exact (plainRightList_iff arguments).mp plain

theorem plainRight_collection {rests : List String} {kind : CollType} {elements : List Pattern}
    {rest : Option String} (plain : PlainRight rests (.collection kind elements rest) = true) :
    restShaped rests rest = true ∧ ∀ element ∈ elements, PlainRight rests element = true := by
  rw [PlainRight, Bool.and_eq_true] at plain
  exact ⟨plain.1, (plainRightList_iff elements).mp plain.2⟩

theorem restShaped_some {rests : List String} {name : String} (shaped : restShaped rests (some name) = true) :
    name ∈ rests := by
  simpa [restShaped] using shaped

theorem lookup_mapped {rests : List String} {assignment : ScopedRuleMatching.Assignment} {name : String}
    {value : ContextualValue} (found : lookup assignment name = some value) :
    lookup (wrapperAssignment laws rests assignment) name = some (mapValue (captureMap laws rests name) value) := by
  rw [lookup_wrapperAssignment, found]; rfl

/-- The rest of an instantiated collection, from a rest value and from its mapped value. -/
theorem collectionRest_wrapper {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {assignment : ScopedRuleMatching.Assignment}
    {kind : CollType} {name : String} {explicit explicit' : List Pattern} {result : Pattern}
    (isRest : name ∈ rests) (pointwise : List.Forall₂ (QWForward laws declaration) explicit explicit')
    (finish : (do
      let value ← lookup assignment name
      let arguments ← arguments? rule spec name site path
      match ← instantiateValue? value ambient depth arguments with
      | .collection actualKind residual none =>
          if actualKind == kind then some (Pattern.collection kind (explicit ++ residual) none) else none
      | _ => none) = some result) :
    ∃ result', (do
      let value ← lookup (wrapperAssignment laws rests assignment) name
      let arguments ← arguments? rule spec name site path
      match ← instantiateValue? value ambient depth arguments with
      | .collection actualKind residual none =>
          if actualKind == kind then some (Pattern.collection kind (explicit' ++ residual) none) else none
      | _ => none) = some result' ∧ QWForward laws declaration result result' := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at finish ⊢
  obtain ⟨value, valueFound, arguments, argumentsFound, produced, instantiated, finish⟩ := finish
  obtain ⟨produced', found', _, producedEq', producedEq⟩ := instantiateValue?_mapForward (laws := laws)
    (declaration := declaration) (captureMap_keepsScope rests name) (captureMap_qwForward rests name) instantiated
  cases produced with
  | collection actualKind residual residualRest =>
    cases residualRest with
    | some _ => simp at finish
    | none =>
      have inner : captureMap laws rests name = wrapperInner laws := by rw [captureMap, if_pos isRest]
      rw [inner] at producedEq'
      obtain ⟨residual', shape', residualForward⟩ := substitute_collection_inner (laws := laws)
        (declaration := declaration) producedEq.symm
      rw [← producedEq'] at shape'
      simp only at finish
      split at finish
      · rename_i sameKind
        simp only [Option.some.injEq] at finish
        subst finish
        refine ⟨_, ⟨mapValue (captureMap laws rests name) value, lookup_mapped valueFound, arguments, argumentsFound,
          produced', found', by simp [shape', sameKind]⟩, qwForward_collection _ _ (List.rel_append pointwise residualForward)⟩
      · cases finish
  | _ => simp at finish

mutual
  /-- **Instantiating a plain pattern with mapped captures** gives a result reached by a forward chain. -/
  theorem instantiateWith?_plain (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (operation : Pattern → Pattern → Pattern) (rests : List String) :
      ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
        (assignment : ScopedRuleMatching.Assignment) (result : Pattern),
        PlainRight rests pattern = true →
        ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth assignment pattern = some result →
        ∃ result', ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth
            (wrapperAssignment laws rests assignment) pattern = some result' ∧ QWForward laws declaration result result'
    | .fvar name, site, path, depth, assignment, result, _, found => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
      obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := found
      obtain ⟨result', found', forward, _, _⟩ := instantiateValue?_mapForward (laws := laws) (declaration := declaration)
        (captureMap_keepsScope rests name) (captureMap_qwForward rests name) instantiated
      exact ⟨result', ⟨_, lookup_mapped valueFound, arguments, argumentsFound, found'⟩, forward⟩
    | .bvar index, site, path, depth, assignment, result, _, found => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      exact ⟨result, found, .refl⟩
    | .apply constructor arguments, site, path, depth, assignment, result, plain, found => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨results, resultsFound, rfl⟩ := found
      obtain ⟨otherResults, otherFound, pointwise⟩ := instantiateArgsWith?_plain rule spec ambient operation rests
        arguments site path depth assignment 0 results (plainRight_apply plain) resultsFound
      exact ⟨_, ⟨otherResults, otherFound, rfl⟩, qwForward_apply _ pointwise⟩
    | .lambda binder body, site, path, depth, assignment, result, plain, found => by
      rw [PlainRight] at plain
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨otherInner, otherFound, forward⟩ := instantiateWith?_plain rule spec ambient operation rests body site
        (path ++ [0]) (depth + 1) assignment inner plain innerFound
      exact ⟨_, ⟨otherInner, otherFound, rfl⟩, qwForward_lambda _ forward⟩
    | .multiLambda arity binders body, site, path, depth, assignment, result, plain, found => by
      rw [PlainRight] at plain
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨otherInner, otherFound, forward⟩ := instantiateWith?_plain rule spec ambient operation rests body site
        (path ++ [0]) (depth + arity) assignment inner plain innerFound
      exact ⟨_, ⟨otherInner, otherFound, rfl⟩, qwForward_multiLambda _ _ forward⟩
    | .subst _ _, _, _, _, _, _, plain, _ => by rw [PlainRight] at plain; cases plain
    | .collection kind elements rest, site, path, depth, assignment, result, plain, found => by
      obtain ⟨restOk, each⟩ := plainRight_collection plain
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
      obtain ⟨explicit, explicitFound, finish⟩ := found
      obtain ⟨otherExplicit, otherExplicitFound, pointwise⟩ := instantiateArgsWith?_plain rule spec ambient operation
        rests elements site path depth assignment 0 explicit each explicitFound
      cases rest with
      | none =>
        simp only [Option.some.injEq] at finish
        subst finish
        exact ⟨_, ⟨otherExplicit, otherExplicitFound, rfl⟩, qwForward_collection _ _ pointwise⟩
      | some name =>
        obtain ⟨result', found', forward⟩ := collectionRest_wrapper (restShaped_some restOk) pointwise finish
        exact ⟨result', ⟨otherExplicit, otherExplicitFound, found'⟩, forward⟩
  termination_by pattern => sizeOf pattern

  theorem instantiateArgsWith?_plain (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (operation : Pattern → Pattern → Pattern) (rests : List String) :
      ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
        (assignment : ScopedRuleMatching.Assignment) (index : Nat) (results : List Pattern),
        (∀ pattern ∈ patterns, PlainRight rests pattern = true) →
        ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth assignment index patterns =
          some results →
        ∃ otherResults, ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth
            (wrapperAssignment laws rests assignment) index patterns = some otherResults ∧
          List.Forall₂ (QWForward laws declaration) results otherResults
    | [], site, path, depth, assignment, index, results, _, found => by
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, .nil⟩
    | pattern :: patterns, site, path, depth, assignment, index, results, plain, found => by
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨head, headFound, tail, tailFound, rfl⟩ := found
      obtain ⟨otherHead, otherHeadFound, headForward⟩ := instantiateWith?_plain rule spec ambient operation rests
        pattern site (path ++ [index]) depth assignment head (plain _ (by simp)) headFound
      obtain ⟨otherTail, otherTailFound, tailForward⟩ := instantiateArgsWith?_plain rule spec ambient operation rests
        patterns site path depth assignment (index + 1) tail (fun other member => plain other (by simp [member]))
        tailFound
      exact ⟨_, ⟨otherHead, otherHeadFound, otherTail, otherTailFound, rfl⟩, .cons headForward tailForward⟩
  termination_by patterns => sizeOf patterns
end

theorem rightShaped_apply {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {rests : List String}
    {path : List Nat} {label : String} {arguments : List Pattern}
    (shaped : RightShaped declaration rule spec site rests path (.apply label arguments) = true) :
    ArgumentsShaped declaration rule spec site rests path 0 arguments = true := by
  rw [RightShaped] at shaped
  exact shaped

theorem rightShaped_collection {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    {rests : List String} {path : List Nat} {kind : CollType} {elements : List Pattern} {rest : Option String}
    (shaped : RightShaped declaration rule spec site rests path (.collection kind elements rest) = true) :
    restShaped rests rest = true ∧ ArgumentsShaped declaration rule spec site rests path 0 elements = true := by
  rw [RightShaped] at shaped
  simpa only [Bool.and_eq_true] using shaped

theorem rightShaped_plain {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {rests : List String}
    {path : List Nat} {pattern : Pattern}
    (binder : (∃ name body, pattern = .lambda name body) ∨ ∃ arity names body, pattern = .multiLambda arity names body)
    (shaped : RightShaped declaration rule spec site rests path pattern = true) : PlainRight rests pattern = true := by
  rcases binder with ⟨name, body, rfl⟩ | ⟨arity, names, body, rfl⟩
  · rw [RightShaped] at shaped
    rw [PlainRight]
    exact shaped
  · rw [RightShaped] at shaped
    rw [PlainRight]
    exact shaped

mutual
  /-- **Instantiating a shaped right side with mapped captures** gives a result reached by a forward
  chain, when the binder operation respects wrapper normal bodies and the original result is closed. -/
  theorem instantiateWith?_wrapper (rule : RewriteRule) (spec : RuleBindingSpec)
      (operation : Pattern → Pattern → Pattern) (respects : BinderRespectsWrapper laws declaration operation)
      (rests : List String) :
      ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat)
        (assignment : ScopedRuleMatching.Assignment) (result : Pattern),
        RightShaped declaration rule spec site rests path pattern = true →
        ScopedRuleMatching.instantiateWith? operation rule spec 0 site path 0 assignment pattern = some result →
        result.isWellScopedAt 0 = true →
        ∃ result', ScopedRuleMatching.instantiateWith? operation rule spec 0 site path 0
            (wrapperAssignment laws rests assignment) pattern = some result' ∧ QWForward laws declaration result result'
    | .fvar name, site, path, assignment, result, _, found, _ =>
      instantiateWith?_plain rule spec 0 operation rests (.fvar name) site path 0 assignment result
        (by rw [PlainRight]) found
    | .bvar index, site, path, assignment, result, _, found, _ =>
      instantiateWith?_plain rule spec 0 operation rests (.bvar index) site path 0 assignment result
        (by rw [PlainRight]) found
    | .apply constructor arguments, site, path, assignment, result, shaped, found, inScope => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨results, resultsFound, rfl⟩ := found
      have each : ∀ item ∈ results, item.isWellScopedAt 0 = true := by
        simp only [Pattern.isWellScopedAt] at inScope
        exact (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope
      obtain ⟨otherResults, otherFound, pointwise⟩ := instantiateArgsWith?_wrapper rule spec operation respects rests
        arguments site path assignment 0 results (rightShaped_apply shaped) resultsFound each
      exact ⟨_, ⟨otherResults, otherFound, rfl⟩, qwForward_apply _ pointwise⟩
    | .lambda binder body, site, path, assignment, result, shaped, found, _ =>
      instantiateWith?_plain rule spec 0 operation rests (.lambda binder body) site path 0 assignment result
        (rightShaped_plain (.inl ⟨_, _, rfl⟩) shaped) found
    | .multiLambda arity binders body, site, path, assignment, result, shaped, found, _ =>
      instantiateWith?_plain rule spec 0 operation rests (.multiLambda arity binders body) site path 0 assignment result
        (rightShaped_plain (.inr ⟨_, _, _, rfl⟩) shaped) found
    | .subst (.fvar name) (.apply label [payload]), site, path, assignment, result, shaped, found, inScope => by
      rw [RightShaped] at shaped
      simp only [Bool.and_eq_true, beq_iff_eq] at shaped
      obtain ⟨⟨⟨ordinary, bodyShape⟩, quoteLabel⟩, payloadPlain⟩ := shaped
      subst quoteLabel
      have notRest : name ∉ rests := by simpa using ordinary
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨body', bodyFound, replacement', replacementFound, rfl⟩ := found
      -- the body: an ordinary capture with a variable spine, instantiated in wrapper normal form
      rw [ScopedRuleMatching.instantiateWith?] at bodyFound
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at bodyFound
      obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := bodyFound
      rw [spineBody, argumentsFound] at bodyShape
      have bvars := allIndices_bvars bodyShape
      have normalBody : ScopedRuleMatching.instantiateWith? operation rule spec 0 site (path ++ [0]) (0 + 1)
          (wrapperAssignment laws rests assignment) (.fvar name) = some (wrapperNormal laws body') := by
        rw [ScopedRuleMatching.instantiateWith?]
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
        refine ⟨mapValue (captureMap laws rests name) value, lookup_mapped valueFound, arguments, argumentsFound, ?_⟩
        rw [captureMap, if_neg notRest, instantiateValue?_map bodyMap_wrapperNormal bvars, instantiated]
        rfl
      -- the replacement: an explicit quotation of a plain pattern
      rw [ScopedRuleMatching.instantiateWith?] at replacementFound
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at replacementFound
      obtain ⟨results, resultsFound, rfl⟩ := replacementFound
      obtain ⟨payloadResult, rfl⟩ := instantiateArgsWith?_single resultsFound
      obtain ⟨otherResults, otherFound, pointwise⟩ := instantiateArgsWith?_plain rule spec 0 operation rests [payload]
        site (path ++ [1]) 0 assignment 0 [payloadResult] (by simpa using payloadPlain) resultsFound
      obtain ⟨other, rfl, forwardPayload⟩ : ∃ other, otherResults = [other] ∧
          QWForward laws declaration payloadResult other := by
        cases pointwise with
        | cons same rest => cases rest; exact ⟨_, rfl, same⟩
      have otherReplacement : ScopedRuleMatching.instantiateWith? operation rule spec 0 site (path ++ [1]) 0
          (wrapperAssignment laws rests assignment) (.apply declaration.quoteConstructor [payload]) =
          some (.apply declaration.quoteConstructor [other]) := by
        rw [ScopedRuleMatching.instantiateWith?]
        simp [otherFound]
      exact ⟨_, ⟨wrapperNormal laws body', normalBody, _, otherReplacement, rfl⟩, respects forwardPayload inScope⟩
    | .subst (.fvar _) (.apply _ []), _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.fvar _) (.apply _ (_ :: _ :: _)), _, _, _, _, shaped, _, _ => by
      simp [RightShaped] at shaped
    | .subst (.fvar _) (.bvar _), _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.fvar _) (.fvar _), _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.fvar _) (.lambda _ _), _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.fvar _) (.multiLambda _ _ _), _, _, _, _, shaped, _, _ => by
      simp [RightShaped] at shaped
    | .subst (.fvar _) (.subst _ _), _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.fvar _) (.collection _ _ _), _, _, _, _, shaped, _, _ => by
      simp [RightShaped] at shaped
    | .subst (.bvar _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.apply _ _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.lambda _ _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.multiLambda _ _ _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.subst _ _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .subst (.collection _ _ _) _, _, _, _, _, shaped, _, _ => by simp [RightShaped] at shaped
    | .collection kind elements rest, site, path, assignment, result, shaped, found, inScope => by
      obtain ⟨restOk, argumentsOk⟩ := rightShaped_collection shaped
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
      obtain ⟨explicit, explicitFound, finish⟩ := found
      have explicitScoped : ∀ item ∈ explicit, item.isWellScopedAt 0 = true := by
        cases rest with
        | none =>
          simp only [Option.some.injEq] at finish
          subst finish
          simp only [Pattern.isWellScopedAt] at inScope
          exact (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope
        | some name =>
          simp only [Option.bind_eq_some_iff] at finish
          obtain ⟨_, _, _, _, produced, _, finish⟩ := finish
          cases produced with
          | collection actualKind residual residualRest =>
            cases residualRest with
            | some _ => simp at finish
            | none =>
              simp only at finish
              split at finish
              · simp only [Option.some.injEq] at finish
                subst finish
                simp only [Pattern.isWellScopedAt] at inScope
                intro item member
                exact (ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope item
                  (List.mem_append_left _ member)
              · cases finish
          | _ => simp at finish
      obtain ⟨otherExplicit, otherExplicitFound, pointwise⟩ := instantiateArgsWith?_wrapper rule spec operation respects
        rests elements site path assignment 0 explicit argumentsOk explicitFound explicitScoped
      cases rest with
      | none =>
        simp only [Option.some.injEq] at finish
        subst finish
        exact ⟨_, ⟨otherExplicit, otherExplicitFound, rfl⟩, qwForward_collection _ _ pointwise⟩
      | some name =>
        obtain ⟨result', found', forward⟩ := collectionRest_wrapper (restShaped_some restOk) pointwise finish
        exact ⟨result', ⟨otherExplicit, otherExplicitFound, found'⟩, forward⟩
  termination_by pattern => sizeOf pattern

  theorem instantiateArgsWith?_wrapper (rule : RewriteRule) (spec : RuleBindingSpec)
      (operation : Pattern → Pattern → Pattern) (respects : BinderRespectsWrapper laws declaration operation)
      (rests : List String) :
      ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat)
        (assignment : ScopedRuleMatching.Assignment) (index : Nat) (results : List Pattern),
        ArgumentsShaped declaration rule spec site rests path index patterns = true →
        ScopedRuleMatching.instantiateArgsWith? operation rule spec 0 site path 0 assignment index patterns =
          some results →
        (∀ item ∈ results, item.isWellScopedAt 0 = true) →
        ∃ otherResults, ScopedRuleMatching.instantiateArgsWith? operation rule spec 0 site path 0
            (wrapperAssignment laws rests assignment) index patterns = some otherResults ∧
          List.Forall₂ (QWForward laws declaration) results otherResults
    | [], site, path, assignment, index, results, _, found, _ => by
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, .nil⟩
    | pattern :: patterns, site, path, assignment, index, results, shaped, found, inScope => by
      rw [ArgumentsShaped, Bool.and_eq_true] at shaped
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨head, headFound, tail, tailFound, rfl⟩ := found
      obtain ⟨otherHead, otherHeadFound, headForward⟩ := instantiateWith?_wrapper rule spec operation respects rests
        pattern site (path ++ [index]) assignment head shaped.1 headFound (inScope head (by simp))
      obtain ⟨otherTail, otherTailFound, tailForward⟩ := instantiateArgsWith?_wrapper rule spec operation respects
        rests patterns site path assignment (index + 1) tail shaped.2 tailFound
        (fun item member => inScope item (by simp [member]))
      exact ⟨_, ⟨otherHead, otherHeadFound, otherTail, otherTailFound, rfl⟩, .cons headForward tailForward⟩
  termination_by patterns => sizeOf patterns
end

end Mettapedia.OSLF.MeTTaIL.Wrappers
