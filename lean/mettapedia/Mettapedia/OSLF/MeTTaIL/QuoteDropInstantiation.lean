import Mettapedia.OSLF.MeTTaIL.QuoteDropReflective

/-!
# Instantiating right sides with quote-drop normal captures

A right side whose explicit substitutions put an explicit quotation into a captured body that
occurs with a variable spine (`substQuoted`, as rho's `p[@q]`) gives quote-drop equal results when
instantiated with the captures or with their normal forms (`instantiateWith?_normal`), for every
binder operation that commutes with the normal form of its body (`BinderRespects`): the ordinary
one and the reflective one (`binderRespects_ordinary`, `binderRespects_reflective`).

Captures recovered from a term whose drops are applied to names keep that property
(`matches_dropsNamed`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch ReflectiveSubstitution CanonicalBags

variable {declaration : ReflectivePresentationDecl}

/-! ## Scope and renamings -/

theorem QuoteDropStep.wellScoped {left right : Pattern} (step : QuoteDropStep declaration left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  intro depth
  have leftNormal := normal_wellScoped (declaration := declaration) left depth
  have rightNormal := normal_wellScoped (declaration := declaration) right depth
  -- both sides have the scope of the common normal form, computed without the distinctness of
  -- quote and drop: a step only removes a quote-drop pair around a subterm
  induction step generalizing depth with
  | collapse name => simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  | @apply label before after argument changed _ ih =>
    simp only [Pattern.isWellScopedAt]
    induction before with
    | nil => simp [Pattern.isWellScopedListAt, ih depth (normal_wellScoped _ _) (normal_wellScoped _ _)]
    | cons first rest restIH => simp [Pattern.isWellScopedListAt, restIH (normal_wellScoped _ _) (normal_wellScoped _ _)]
  | lambda _ ih => simp only [Pattern.isWellScopedAt]; exact ih _ (normal_wellScoped _ _) (normal_wellScoped _ _)
  | multiLambda _ ih => simp only [Pattern.isWellScopedAt]; exact ih _ (normal_wellScoped _ _) (normal_wellScoped _ _)
  | substBody _ ih =>
    simp only [Pattern.isWellScopedAt, ih _ (normal_wellScoped _ _) (normal_wellScoped _ _)]
  | substReplacement _ ih =>
    simp only [Pattern.isWellScopedAt, ih _ (normal_wellScoped _ _) (normal_wellScoped _ _)]
  | @element kind before after element changed rest _ ih =>
    simp only [Pattern.isWellScopedAt]
    induction before with
    | nil => simp [Pattern.isWellScopedListAt, ih depth (normal_wellScoped _ _) (normal_wellScoped _ _)]
    | cons first others restIH =>
      simp [Pattern.isWellScopedListAt, restIH (normal_wellScoped _ _) (normal_wellScoped _ _)]

theorem QuoteDropSame.wellScoped {left right : Pattern} (same : QuoteDropSame declaration left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction same with
  | rel _ _ step => exact step.wellScoped depth
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem isName_substitute {assignment : ContextSubstitution.Assignment} (renames : Renaming assignment) {pattern : Pattern}
    (nameShaped : isName declaration pattern = true) :
    isName declaration (ContextSubstitution.substitute assignment pattern) = true := by
  match pattern, nameShaped with
  | .bvar index, _ =>
    obtain ⟨other, found⟩ := renames index
    simp [ContextSubstitution.substitute, found, isName]
  | .fvar _, _ => simp [ContextSubstitution.substitute, isName]
  | .apply label [payload], nameShaped =>
    simpa [ContextSubstitution.substitute, isName] using nameShaped

/-- A renaming keeps drops applied to names. -/
theorem dropsNamed_substitute (pattern : Pattern) :
    ∀ {assignment : ContextSubstitution.Assignment}, Renaming assignment → dropsNamed declaration pattern = true →
      dropsNamed declaration (ContextSubstitution.substitute assignment pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro assignment renames _
    obtain ⟨other, found⟩ := renames index
    simp [ContextSubstitution.substitute, found, dropsNamed]
  | hfvar name => intro _ _ _; simp [ContextSubstitution.substitute, dropsNamed]
  | happly label arguments ih =>
    intro assignment renames named
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply dropsNamed_of_apply
    · intro argument member
      obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
      exact ih original originalIn renames (dropsNamed_args named original originalIn)
    · intro dropped argument single
      subst dropped
      match arguments, single with
      | [original], single =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at single
        subst single
        exact isName_substitute renames (dropsNamed_drop named)
  | hlambda binder body ih =>
    intro assignment renames named
    simp only [ContextSubstitution.substitute, dropsNamed] at named ⊢
    exact ih (renames.lift 1) named
  | hmultiLambda arity binders body ih =>
    intro assignment renames named
    simp only [ContextSubstitution.substitute, dropsNamed] at named ⊢
    exact ih (renames.lift arity) named
  | hsubst body replacement bodyIH replacementIH =>
    intro assignment renames named
    rw [dropsNamed, Bool.and_eq_true] at named
    simp only [ContextSubstitution.substitute, dropsNamed, Bool.and_eq_true]
    exact ⟨bodyIH (renames.lift 1) named.1, replacementIH renames named.2⟩
  | hcollection kind elements rest ih =>
    intro assignment renames named
    have each := dropsNamed_collection named
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, dropsNamed,
      List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map]
    rintro _ ⟨original, originalIn, rfl⟩
    exact ih original originalIn renames (each original originalIn)

/-! ## Instantiating values -/

/-- **Instantiating a value and its normal form** gives results joined by a forward chain. -/
theorem instantiateValue?_normalValue {value : ContextualValue} {ambient depth : Nat} {arguments : List Pattern}
    {result : Pattern} (found : instantiateValue? value ambient depth arguments = some result) :
    ∃ result', instantiateValue? (normalValue declaration value) ambient depth arguments = some result' ∧
      QuoteDropForward declaration result result' ∧
      result' = ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
        (normal declaration value.body) ∧
      result = ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body := by
  obtain ⟨ambientOk, lengthOk, bodyScoped, argumentsScoped, substituted, resultScoped⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp found
  have same : QuoteDropForward declaration result
      (ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
        (normal declaration value.body)) := by
    rw [← substituted]
    exact (quoteDrop_forward value.body).substitute _
  refine ⟨_, (instantiateValue?_eq_some_iff _ _ _ _ _).mpr ⟨ambientOk, lengthOk, ?_, argumentsScoped, rfl, ?_⟩, same,
    rfl, substituted.symm⟩
  · simp only [normalValue]; rw [normal_wellScoped]; exact bodyScoped
  · simp only [normalValue]; rw [← same.same.wellScoped]; exact resultScoped

/-- A collection instantiated from a value is a collection of the same kind when instantiated from
the value's normal form, with elements joined pointwise by forward chains. -/
theorem substitute_collection_normal {assignment : ContextSubstitution.Assignment} {body : Pattern}
    {kind : CollType} {elements : List Pattern}
    (shape : ContextSubstitution.substitute assignment body = .collection kind elements none) :
    ∃ elements', ContextSubstitution.substitute assignment (normal declaration body) = .collection kind elements' none ∧
      List.Forall₂ (QuoteDropForward declaration) elements elements' := by
  cases body with
  | bvar index =>
    rw [normal_bvar]
    exact ⟨elements, shape, List.forall₂_same.mpr fun _ _ => .refl⟩
  | collection kind' items rest =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, Pattern.collection.injEq]
      at shape
    obtain ⟨rfl, rfl, rfl⟩ := shape
    rw [normal_collection]
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map]
    refine ⟨_, rfl, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun item _ => (quoteDrop_forward item).substitute _
  | _ => simp [ContextSubstitution.substitute] at shape

/-! ## Admissible right sides -/

/-- Every argument is an index. -/
def allIndices : Option (List Pattern) → Bool
  | some arguments => arguments.all fun argument => match argument with
    | .bvar _ => true
    | _ => false
  | none => false

theorem allIndices_bvars {arguments : List Pattern} (indices : allIndices (some arguments) = true) :
    ∀ argument ∈ arguments, ∃ index, argument = .bvar index := by
  intro argument member
  simp only [allIndices, List.all_eq_true] at indices
  have := indices argument member
  split at this
  · exact ⟨_, rfl⟩
  · cases this

/-- A captured body occurring with a variable spine. -/
def spineBody (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite) (path : List Nat) :
    Pattern → Bool
  | .fvar name => allIndices (arguments? rule spec name site path)
  | _ => false

variable (declaration) in
/-- An explicit quotation. -/
def isQuotation : Pattern → Bool
  | .apply label [_] => label == declaration.quoteConstructor
  | _ => false

variable (declaration) in
mutual
  /-- Every explicit substitution puts an explicit quotation into a captured body that occurs
  with a variable spine. -/
  def substQuoted (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite) :
      List Nat → Pattern → Bool
    | _, .fvar _ => true
    | _, .bvar _ => true
    | path, .apply _ arguments => argumentsQuoted rule spec site path 0 arguments
    | path, .lambda _ body => substQuoted rule spec site (path ++ [0]) body
    | path, .multiLambda _ _ body => substQuoted rule spec site (path ++ [0]) body
    | path, .subst body replacement =>
        spineBody rule spec site (path ++ [0]) body && isQuotation declaration replacement &&
        substQuoted rule spec site (path ++ [1]) replacement
    | path, .collection _ elements _ => argumentsQuoted rule spec site path 0 elements

  def argumentsQuoted (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite) :
      List Nat → Nat → List Pattern → Bool
    | _, _, [] => true
    | path, index, pattern :: patterns =>
        substQuoted rule spec site (path ++ [index]) pattern && argumentsQuoted rule spec site path (index + 1) patterns
end

/-- A binder operation that maps forward chains of its arguments to a forward chain, for bodies
replaced by their normal forms and replacements with one normalized form. -/
def BinderRespects (declaration : ReflectivePresentationDecl) (operation : Pattern → Pattern → Pattern) : Prop :=
  ∀ {replacement replacement' body : Pattern},
    normalizeReflectiveReplacement declaration replacement = normalizeReflectiveReplacement declaration replacement' →
    QuoteDropForward declaration replacement replacement' → dropsNamed declaration body = true →
    QuoteDropForward declaration (operation replacement body) (operation replacement' (normal declaration body))

theorem binderRespects_ordinary : BinderRespects declaration Substitution.instantiateBVar :=
  fun _ forwardReplacement _ => instantiateBVar_quoteDrop forwardReplacement (quoteDrop_forward _)

theorem binderRespects_reflective (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    BinderRespects declaration (ScopedRuleInstantiation.reflectiveOperation declaration) :=
  fun sameNormalized _ _ => by rw [reflectiveOperation_normal distinct sameNormalized]

/-- Every captured body has its drops applied to names. -/
def CapturesNamed (declaration : ReflectivePresentationDecl) (assignment : ScopedRuleMatching.Assignment) : Prop :=
  ∀ entry ∈ assignment, dropsNamed declaration entry.2.body = true

theorem lookup_normal_of_mem {assignment : ScopedRuleMatching.Assignment} {name : String} {value : ContextualValue}
    (found : lookup assignment name = some value) : ∃ entry ∈ assignment, entry.2 = value := by
  unfold lookup at found
  cases search : assignment.find? (fun entry => entry.1 == name) with
  | none => rw [search] at found; cases found
  | some entry =>
    rw [search] at found
    exact ⟨entry, List.mem_of_find?_eq_some search, by simpa using found⟩

theorem instantiateArgsWith?_single {operation : Pattern → Pattern → Pattern} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {assignment : ScopedRuleMatching.Assignment} {index : Nat} {pattern : Pattern} {results : List Pattern}
    (found : ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth assignment index [pattern] =
      some results) : ∃ result, results = [result] := by
  rw [ScopedRuleMatching.instantiateArgsWith?] at found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found
  obtain ⟨head, _, tail, tailFound, rfl⟩ := found
  rw [ScopedRuleMatching.instantiateArgsWith?] at tailFound
  simp only [Option.some.injEq] at tailFound
  subst tailFound
  exact ⟨head, rfl⟩

mutual
  /-- **Instantiating an admissible right side with the normal forms of the captures** gives a
  result reached by a forward chain. -/
  theorem instantiateWith?_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
      (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (operation : Pattern → Pattern → Pattern) (respects : BinderRespects declaration operation) :
      ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
        (assignment : ScopedRuleMatching.Assignment) (result : Pattern),
        substQuoted declaration rule spec site path pattern = true → CapturesNamed declaration assignment →
        ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth assignment pattern = some result →
        ∃ result', ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth
            (normalAssignment declaration assignment) pattern = some result' ∧ QuoteDropForward declaration result result'
    | .fvar name, site, path, depth, assignment, result, _, _, found => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
      obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := found
      obtain ⟨result', found', same, _, _⟩ := instantiateValue?_normalValue (declaration := declaration) instantiated
      refine ⟨result', ⟨normalValue declaration value, ?_, arguments, argumentsFound, found'⟩, same⟩
      rw [lookup_normalAssignment, valueFound]; rfl
    | .bvar index, site, path, depth, assignment, result, _, _, found => by
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      exact ⟨result, found, .refl⟩
    | .apply constructor arguments, site, path, depth, assignment, result, quoted, named, found => by
      rw [substQuoted] at quoted
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨results, resultsFound, rfl⟩ := found
      obtain ⟨otherResults, otherFound, pointwise⟩ := instantiateArgsWith?_normal distinct rule spec ambient operation
        respects arguments site path depth assignment 0 results quoted named resultsFound
      exact ⟨_, ⟨otherResults, otherFound, rfl⟩, quoteDropForward_apply_congr _ pointwise⟩
    | .lambda binder body, site, path, depth, assignment, result, quoted, named, found => by
      rw [substQuoted] at quoted
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨otherInner, otherFound, innerSame⟩ := instantiateWith?_normal distinct rule spec ambient operation respects
        body site (path ++ [0]) (depth + 1) assignment inner quoted named innerFound
      exact ⟨_, ⟨otherInner, otherFound, rfl⟩, quoteDropForward_lambda_congr _ innerSame⟩
    | .multiLambda arity binders body, site, path, depth, assignment, result, quoted, named, found => by
      rw [substQuoted] at quoted
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨otherInner, otherFound, innerSame⟩ := instantiateWith?_normal distinct rule spec ambient operation respects
        body site (path ++ [0]) (depth + arity) assignment inner quoted named innerFound
      exact ⟨_, ⟨otherInner, otherFound, rfl⟩, quoteDropForward_multiLambda_congr _ _ innerSame⟩
    | .subst body (.apply label [payload]), site, path, depth, assignment, result, quoted, named, found => by
      rw [substQuoted, Bool.and_eq_true, Bool.and_eq_true] at quoted
      obtain ⟨⟨bodyShape, replacementShape⟩, replacementQuoted⟩ := quoted
      have quoteLabel : label = declaration.quoteConstructor := by simpa [isQuotation] using replacementShape
      subst quoteLabel
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨body', bodyFound, replacement', replacementFound, rfl⟩ := found
      -- the replacement is an explicit quotation of quote-drop equal payloads
      rw [substQuoted] at replacementQuoted
      rw [ScopedRuleMatching.instantiateWith?] at replacementFound
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at replacementFound
      obtain ⟨results, resultsFound, rfl⟩ := replacementFound
      obtain ⟨otherResults, otherResultsFound, pointwise⟩ := instantiateArgsWith?_normal distinct rule spec ambient
        operation respects [payload] site (path ++ [1]) depth assignment 0 results replacementQuoted named resultsFound
      have otherReplacement : ScopedRuleMatching.instantiateWith? operation rule spec ambient site (path ++ [1]) depth
          (normalAssignment declaration assignment) (.apply declaration.quoteConstructor [payload]) =
          some (.apply declaration.quoteConstructor otherResults) := by
        rw [ScopedRuleMatching.instantiateWith?]
        simp [otherResultsFound]
      have single := instantiateArgsWith?_single resultsFound
      obtain ⟨result, rfl⟩ := single
      obtain ⟨other, rfl, same⟩ : ∃ other, otherResults = [other] ∧ QuoteDropForward declaration result other := by
        cases pointwise with
        | cons same rest => cases rest; exact ⟨_, rfl, same⟩
      cases body with
      | fvar name =>
        -- the body is a captured value occurring with a variable spine
        rw [ScopedRuleMatching.instantiateWith?] at bodyFound
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at bodyFound
        obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := bodyFound
        rw [spineBody, argumentsFound] at bodyShape
        have bvars := allIndices_bvars bodyShape
        have normalBody : ScopedRuleMatching.instantiateWith? operation rule spec ambient site (path ++ [0]) (depth + 1)
            (normalAssignment declaration assignment) (.fvar name) = some (normal declaration body') := by
          rw [ScopedRuleMatching.instantiateWith?]
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
          refine ⟨normalValue declaration value, by rw [lookup_normalAssignment, valueFound]; rfl, arguments,
            argumentsFound, ?_⟩
          rw [instantiateValue?_normal bvars, instantiated]; rfl
        have bodyNamed : dropsNamed declaration body' = true := by
          obtain ⟨_, _, _, _, substituted, _⟩ := (instantiateValue?_eq_some_iff _ _ _ _ _).mp instantiated
          rw [← substituted]
          obtain ⟨entry, member, sameEntry⟩ := lookup_normal_of_mem valueFound
          exact dropsNamed_substitute _ (occurrenceAssignment_renaming bvars) (sameEntry ▸ named entry member)
        refine ⟨_, ⟨normal declaration body', normalBody, _, otherReplacement, rfl⟩, ?_⟩
        exact respects (normalizeReflectiveReplacement_quote _ _ (same.same.normalize_eq distinct))
          (quoteDropForward_apply_congr _ (.cons same .nil)) bodyNamed
      | bvar _ => simp [spineBody] at bodyShape
      | apply _ _ => simp [spineBody] at bodyShape
      | lambda _ _ => simp [spineBody] at bodyShape
      | multiLambda _ _ _ => simp [spineBody] at bodyShape
      | subst _ _ => simp [spineBody] at bodyShape
      | collection _ _ _ => simp [spineBody] at bodyShape
    | .subst _ (.apply _ []), _, _, _, _, _, quoted, _, _ => by
      rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.apply _ (_ :: _ :: _)), _, _, _, _, _, quoted, _, _ => by
      rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.bvar _), _, _, _, _, _, quoted, _, _ => by rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.fvar _), _, _, _, _, _, quoted, _, _ => by rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.lambda _ _), _, _, _, _, _, quoted, _, _ => by rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.multiLambda _ _ _), _, _, _, _, _, quoted, _, _ => by
      rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.subst _ _), _, _, _, _, _, quoted, _, _ => by rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .subst _ (.collection _ _ _), _, _, _, _, _, quoted, _, _ => by
      rw [substQuoted] at quoted; simp [isQuotation] at quoted
    | .collection kind elements rest, site, path, depth, assignment, result, quoted, named, found => by
      rw [substQuoted] at quoted
      rw [ScopedRuleMatching.instantiateWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
      obtain ⟨explicit, explicitFound, finish⟩ := found
      obtain ⟨otherExplicit, otherExplicitFound, pointwise⟩ := instantiateArgsWith?_normal distinct rule spec ambient
        operation respects elements site path depth assignment 0 explicit quoted named explicitFound
      cases rest with
      | none =>
        simp only [Option.some.injEq] at finish
        subst finish
        exact ⟨_, ⟨otherExplicit, otherExplicitFound, rfl⟩, quoteDropForward_collection_congr _ _ pointwise⟩
      | some name =>
        simp only [Option.bind_eq_some_iff] at finish
        obtain ⟨value, valueFound, arguments, argumentsFound, produced, instantiated, finish⟩ := finish
        obtain ⟨produced', found', _, producedEq', producedEq⟩ := instantiateValue?_normalValue (declaration := declaration)
          instantiated
        cases produced with
        | collection actualKind residual residualRest =>
          cases residualRest with
          | some _ => simp at finish
          | none =>
            obtain ⟨residual', shape', residualSame⟩ := substitute_collection_normal (declaration := declaration)
              producedEq.symm
            rw [← producedEq'] at shape'
            simp only at finish
            split at finish
            · rename_i sameKind
              simp only [Option.some.injEq] at finish
              subst finish
              refine ⟨_, ⟨otherExplicit, otherExplicitFound, ?_⟩,
                quoteDropForward_collection_congr _ _ (List.rel_append pointwise residualSame)⟩
              simp only [Option.bind_eq_some_iff]
              exact ⟨normalValue declaration value, by rw [lookup_normalAssignment, valueFound]; rfl, arguments,
                argumentsFound, produced', found', by simp [shape', sameKind]⟩
            · cases finish
        | _ => simp at finish
  termination_by pattern => sizeOf pattern

  theorem instantiateArgsWith?_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
      (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (operation : Pattern → Pattern → Pattern) (respects : BinderRespects declaration operation) :
      ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
        (assignment : ScopedRuleMatching.Assignment) (index : Nat) (results : List Pattern),
        argumentsQuoted declaration rule spec site path index patterns = true → CapturesNamed declaration assignment →
        ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth assignment index patterns =
          some results →
        ∃ otherResults, ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth
            (normalAssignment declaration assignment) index patterns = some otherResults ∧
          List.Forall₂ (QuoteDropForward declaration) results otherResults
    | [], site, path, depth, assignment, index, results, _, _, found => by
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, .nil⟩
    | pattern :: patterns, site, path, depth, assignment, index, results, quoted, named, found => by
      rw [argumentsQuoted, Bool.and_eq_true] at quoted
      rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
      obtain ⟨head, headFound, tail, tailFound, rfl⟩ := found
      obtain ⟨otherHead, otherHeadFound, headSame⟩ := instantiateWith?_normal distinct rule spec ambient operation respects
        pattern site (path ++ [index]) depth assignment head quoted.1 named headFound
      obtain ⟨otherTail, otherTailFound, tailSame⟩ := instantiateArgsWith?_normal distinct rule spec ambient operation
        respects patterns site path depth assignment (index + 1) tail quoted.2 named tailFound
      exact ⟨_, ⟨otherHead, otherHeadFound, otherTail, otherTailFound, rfl⟩, .cons headSame tailSame⟩
  termination_by patterns => sizeOf patterns
end

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
