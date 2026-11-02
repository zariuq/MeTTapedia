import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileExecution
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileCoverage
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.ContextualBindingExtension
import Mettapedia.OSLF.MeTTaIL.ScopedMatchingInversion

/-!
# Generated presentation and alpha admission for the finite binder profile

The guarded extrusion declares its binding dependencies, so its instances are
read through the scoped matcher, which ignores source binder display names.
Consequently the equation class contains noncanonical named presentations even
when its source is canonical. The admitted semantic carrier uses the existing alpha quotient;
erasure retains all binding indices, keys, constructor shapes and observations.
The comparison below is with the authored equation and operational relations,
not a definition of those relations from the finite executor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated

open Mettapedia.OSLF.MeTTaIL
open Syntax Engine Match ContextualStep DerivedContexts
open ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open RuleBinding (ContextualValue instantiateValue? recoverValue?)

def base (allowed : List Token) : BasePremiseEvaluator :=
  engineBasePremises (provider allowed)

/-- Binder display metadata is retained outside the admitted alpha boundary. -/
def displayedPattern {ambient : Nat} (binder : Option String) (state : State ambient) : Pattern :=
  match state.phase with
  | .tucked => .apply "Nu" [.lambda binder (pair (cell state.name.val) (guard state.key))]
  | .exposed => pair (.apply "Nu" [.lambda binder (cell state.name.val)]) (guard state.key)
  | .finished => .apply "Nu" [.lambda binder (done (pair (cell state.name.val) (guard state.key)))]

theorem displayed_erasure {ambient : Nat} (binder : Option String) (state : State ambient) :
    (displayedPattern binder state).eraseBinderMetadata = state.pattern := by
  cases state with
  | mk phase name key =>
    cases phase <;> simp [displayedPattern, State.pattern, nu, pair, cell, EquationFrontierBinderProfile.guard,
      done, Token.pattern, Pattern.eraseBinderMetadata]

theorem displayed_none {ambient : Nat} (state : State ambient) :
    displayedPattern none state = state.pattern := by
  cases state with
  | mk phase name key => cases phase <;> rfl

theorem displayed_alpha {ambient : Nat} (binder : Option String) (state : State ambient) :
    Pattern.AlphaEquiv (displayedPattern binder state) state.pattern := by
  rw [Pattern.AlphaEquiv, displayed_erasure]
  exact (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical state)).symm

theorem displayed_alpha_iff {ambient : Nat} (leftBinder rightBinder : Option String)
    (left right : State ambient) :
    Pattern.AlphaEquiv (displayedPattern leftBinder left) (displayedPattern rightBinder right) ↔
      left = right := by
  rw [Pattern.AlphaEquiv, displayed_erasure, displayed_erasure]
  exact state_pattern_injective.eq_iff

/-- The rules' guard premise, read by the ordinary matcher. -/
theorem raw_premises_spec (allowed : List Token) (index : Nat) (key : Token)
    (fuel : Nat) (result : Bindings) :
    PremisesAt (base allowed) language fuel (rawCaptured index key)
      extrusionEquation.premises result ↔
        result = rawCaptured index key ∧ key ∈ allowed := by
  change PremisesAt (engineBasePremises (provider allowed)) language fuel
    (rawCaptured index key) extrusionEquation.premises result ↔ _
  rw [premisesAt_engineBase_iff_mem_applyPremisesWithEnv
    (show NoncontextualPremises extrusionEquation.premises from by
      exact .relationQuery .nil)]
  simp [extrusionEquation, applyPremisesWithEnv, premiseStepWithEnv,
    relation_query_results, and_comm]

section Declared

open RuleBinding ScopedRuleMatching
open ScopedEquationExecution (Orientation orientedRule)

theorem extrusion_not_raw : readsRaw extrusionEquation = false := by decide +kernel

private theorem builtin_allow (arguments : List Pattern) :
    builtinRelationTuples language "allow" arguments = [] := by
  cases arguments with
  | nil => rfl
  | cons _ rest => cases rest <;> rfl

private theorem query_row (value : Pattern) (key : Token) :
    matchRelationArgs [("Q", value)] [.fvar "Q"] [guard key] =
      if guard key = value then [[]] else [] := by
  by_cases equal : guard key = value
  · subst value
    simp [matchRelationArgs, matchRelationArgument, Match.mergeBindings, Bindings.lookup]
  · have other : value ≠ guard key := fun same => equal same.symm
    simp [matchRelationArgs, matchRelationArgument, Match.mergeBindings, Bindings.lookup, equal, other]

/-- The guard relation answers one row per allowed key whose guard is the component. -/
private theorem allow_results (allowed : List Token) (value : Pattern) :
    relationQueryStep (provider allowed) language [("Q", value)] "allow" [.fvar "Q"] =
      (allowed.filter (fun key => guard key == value)).map (fun _ => [("Q", value)]) := by
  simp only [relationQueryStep, provider, if_true, builtin_allow, List.nil_append, List.flatMap_map, query_row]
  induction allowed with
  | nil => rfl
  | cons key rest inductionHypothesis =>
    by_cases equal : guard key = value
    · simpa [equal, Match.mergeBindings] using congrArg (List.cons [("Q", value)]) inductionHypothesis
    · simpa [equal] using inductionHypothesis

/-- **The guard premise** admits a component exactly when it is the guard of an allowed key, and binds nothing. -/
theorem declared_premises_spec (allowed : List Token) (fuel : Nat) (value : Pattern) (result : Bindings) :
    PremisesAt (base allowed) language fuel [("Q", value)] extrusionEquation.premises result ↔
      result = [("Q", value)] ∧ ∃ key ∈ allowed, guard key = value := by
  change PremisesAt (engineBasePremises (provider allowed)) language fuel [("Q", value)]
    extrusionEquation.premises result ↔ _
  rw [premisesAt_engineBase_iff_mem_applyPremisesWithEnv
    (show NoncontextualPremises extrusionEquation.premises from by exact .relationQuery .nil)]
  simp only [extrusionEquation, applyPremisesWithEnv, premiseStepWithEnv, List.foldl_cons, List.foldl_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, allow_results, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨key, ⟨member, sameGuard⟩, rfl⟩
    exact ⟨rfl, key, member, sameGuard⟩
  · rintro ⟨rfl, key, member, sameGuard⟩
    exact ⟨key, ⟨member, sameGuard⟩, rfl⟩

private theorem recovery_zero (ambient : Nat) : recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

private theorem occurrence_zero : occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

/-- At the root, recovery reads a component as it is. -/
theorem recoverValue?_root {ambient : Nat} {term : Pattern} {value : ContextualValue}
    (recovered : recoverValue? [] ambient 0 [] term = some value) : value = ⟨[], ambient, term⟩ := by
  unfold recoverValue? at recovered
  split at recovered
  · cases recovered
  simp only [variableSpine?, List.mapM_nil, List.nodup_nil, if_true, Option.bind_eq_bind, Option.pure_def,
    Option.bind_some, List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false, recovery_zero,
    ContextSubstitution.substitute_id] at recovered
  split at recovered
  · cases recovered
    rfl
  · cases recovered

/-- A closed component read at the root is its body. -/
theorem instantiateValue?_root {ambient : Nat} {body inner : Pattern}
    (shifted : instantiateValue? ⟨[], ambient, body⟩ ambient 1 [] = some inner) :
    instantiateValue? ⟨[], ambient, body⟩ ambient 0 [] = some body := by
  have wellScoped : body.isWellScopedAt (0 + ambient) = true := by
    unfold instantiateValue? at shifted
    simp only [List.length_nil, Nat.zero_add] at shifted ⊢
    split at shifted
    · cases shifted
    split at shifted
    · cases shifted
    split at shifted
    · cases shifted
    · rename_i good
      simpa using good
  unfold instantiateValue?
  simp only [List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false, List.all_nil, Bool.not_true,
    occurrence_zero, ContextSubstitution.substitute_id]
  have atAmbient : body.isWellScopedAt ambient = true := by simpa using wellScoped
  simp [atAmbient]

/-- Shifting context variables leaves a guard as it is, and only a guard shifts to a guard. -/
theorem shift_eq_guard {body : Pattern} {key : Token} {offset : Nat}
    (shifted : ContextSubstitution.substitute (fun index => .bvar (offset + index)) body = guard key) :
    body = guard key := by
  cases body with
  | apply constructor arguments =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        EquationFrontierBinderProfile.guard, Pattern.apply.injEq, List.map_eq_cons_iff,
        List.map_eq_nil_iff] at shifted
      obtain ⟨rfl, argument, rest, rfl, argumentShifted, rfl⟩ := shifted
      cases argument with
      | apply label inner =>
          simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
            Token.pattern, Pattern.apply.injEq, List.map_eq_nil_iff] at argumentShifted
          obtain ⟨rfl, rfl⟩ := argumentShifted
          rfl
      | _ => simp [ContextSubstitution.substitute, Token.pattern] at argumentShifted
  | _ => simp [ContextSubstitution.substitute, EquationFrontierBinderProfile.guard] at shifted

/-- A closed component that reads as a guard under one binder is that guard. -/
theorem instantiateValue?_guard {scope : Nat} {body : Pattern} {key : Token}
    (shifted : instantiateValue? ⟨[], scope, body⟩ scope 1 [] = some (guard key)) : body = guard key := by
  have occurrence : occurrenceAssignment 0 1 [] = fun index => Pattern.bvar (1 + index) := by
    funext index
    simp [occurrenceAssignment]
  unfold instantiateValue? at shifted
  simp only [List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false, List.all_nil, Bool.not_true,
    occurrence] at shifted
  split at shifted
  · cases shifted
  split at shifted
  · exact shift_eq_guard (Option.some.inj shifted)
  · cases shifted

/-- **Every declared instance of the guarded extrusion**: a restriction over a pair moves out over a component that
uses no bound name, or back in; the component is read in both scopes and its guard is admitted. -/
theorem declared_instance_shape (allowed : List Token) {fuel ambient : Nat} {orientation : Orientation}
    {source target : Pattern}
    (declared : DeclaredInstanceAt (base allowed) language fuel ambient extrusionEquation orientation source
      target) :
    ∃ (binder : Option String) (left inner outer : Pattern) (result : Bindings),
      instantiateValue? ⟨[], ambient, outer⟩ ambient 1 [] = some inner ∧
      PremisesAt (base allowed) language fuel [("Q", outer)] extrusionEquation.premises result ∧
      ((source = .apply "Nu" [.lambda binder (pair left inner)] ∧ target = pair (nu left) outer ∧
          recoverValue? [] ambient 1 [] inner = some ⟨[], ambient, outer⟩) ∨
        (source = pair (.apply "Nu" [.lambda binder left]) outer ∧ target = nu (pair left inner) ∧
          recoverValue? [] ambient 0 [] outer = some ⟨[], ambient, outer⟩)) := by
  obtain ⟨spec, captured, final, bound, -, -, matched, premises, applied, -⟩ := declared
  cases orientation with
  | forward =>
      obtain rfl : spec = (orientedRule extrusionEquation .forward).bindings.getD { dependencies := [] } := by
        rw [bound]; rfl
      simp only [matchRuleAt, matchRuleWithAt] at matched
      rw [show (orientedRule extrusionEquation .forward).left =
          .apply "Nu" [.lambda none (.apply "Pair" [.fvar "P", .fvar "Q"])] from rfl,
        mem_matchAtWith_apply] at matched
      obtain ⟨arguments, rfl, matched⟩ := matched
      rw [mem_matchArgsAtWith_cons] at matched
      obtain ⟨argument, rest, middle, rfl, first, matched⟩ := matched
      rw [mem_matchArgsAtWith_nil] at matched
      obtain ⟨rfl, rfl⟩ := matched
      rw [mem_matchAtWith_lambda] at first
      obtain ⟨binder, body, rfl, first⟩ := first
      rw [mem_matchAtWith_apply] at first
      obtain ⟨components, rfl, first⟩ := first
      rw [mem_matchArgsAtWith_cons] at first
      obtain ⟨left, rest, afterLeft, rfl, capturedLeft, first⟩ := first
      rw [mem_matchArgsAtWith_cons] at first
      obtain ⟨inner, rest, afterInner, rfl, capturedInner, first⟩ := first
      rw [mem_matchArgsAtWith_nil] at first
      obtain ⟨rfl, rfl⟩ := first
      rw [mem_matchAtWith_fvar, captureWith?_literal] at capturedLeft capturedInner
      simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at capturedLeft capturedInner
      obtain ⟨leftDependencies, leftDeclared, leftArguments, leftSupplied, leftValue, leftRecovered,
        leftAssigned⟩ := capturedLeft
      obtain ⟨innerDependencies, innerDeclared, innerArguments, innerSupplied, innerValue, innerRecovered,
        innerAssigned⟩ := capturedInner
      simp [orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation, dependencies?,
        arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?] at leftDeclared leftSupplied innerDeclared innerSupplied
      subst leftDeclared leftSupplied innerDeclared innerSupplied
      have innerContext := recoverValue?_context _ _ _ _ _ _ innerRecovered
      have leftContext := recoverValue?_context _ _ _ _ _ _ leftRecovered
      have innerForward := recoverValue?_forward _ _ _ _ _ _ innerRecovered
      have leftForward := recoverValue?_forward _ _ _ _ _ _ leftRecovered
      obtain ⟨innerDeps, innerAmbient, outer⟩ := innerValue
      simp only at innerContext
      obtain ⟨rfl, ambientEq⟩ := innerContext
      subst innerAmbient
      simp only [assign, lookup, List.find?_nil, Option.map_none, Option.some.injEq] at leftAssigned
      subst leftAssigned
      simp [assign, lookup] at innerAssigned
      subst innerAssigned
      have root : closedRoot [("Q", (⟨[], ambient, outer⟩ : ContextualValue)), ("P", leftValue)] =
          [("Q", outer)] := by
        simp [closedRoot, leftContext.1]
      rw [root] at premises
      have kept := ((declared_premises_spec allowed fuel outer final).mp premises).1
      subst kept
      have extended : extendClosed ambient [("Q", (⟨[], ambient, outer⟩ : ContextualValue)), ("P", leftValue)]
          [("Q", outer)] = [("Q", ⟨[], ambient, outer⟩), ("P", leftValue)] := by
        rw [← root, extendClosed_closedRoot]
      rw [extended] at applied
      have rootRead := instantiateValue?_root innerForward
      simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, extrusionEquation,
        ScopedEquationControls.extrusionEquation, arguments?, dependencies?, occurrenceDeclared, sitePattern?,
        occurrenceAt?, lookup, leftForward, rootRead] at applied
      subst applied
      exact ⟨binder, left, inner, outer, [("Q", outer)], innerForward, premises,
        Or.inl ⟨rfl, rfl, innerRecovered⟩⟩
  | reverse =>
      obtain rfl : spec = (orientedRule extrusionEquation .reverse).bindings.getD { dependencies := [] } := by
        rw [bound]; rfl
      simp only [matchRuleAt, matchRuleWithAt] at matched
      rw [show (orientedRule extrusionEquation .reverse).left =
          .apply "Pair" [.apply "Nu" [.lambda none (.fvar "P")], .fvar "Q"] from rfl,
        mem_matchAtWith_apply] at matched
      obtain ⟨components, rfl, matched⟩ := matched
      rw [mem_matchArgsAtWith_cons] at matched
      obtain ⟨restriction, rest, middle, rfl, first, matched⟩ := matched
      rw [mem_matchArgsAtWith_cons] at matched
      obtain ⟨outer, rest, afterOuter, rfl, capturedOuter, matched⟩ := matched
      rw [mem_matchArgsAtWith_nil] at matched
      obtain ⟨rfl, rfl⟩ := matched
      rw [mem_matchAtWith_apply] at first
      obtain ⟨arguments, rfl, first⟩ := first
      rw [mem_matchArgsAtWith_cons] at first
      obtain ⟨argument, rest, afterBinder, rfl, binderMatched, first⟩ := first
      rw [mem_matchArgsAtWith_nil] at first
      obtain ⟨rfl, rfl⟩ := first
      rw [mem_matchAtWith_lambda] at binderMatched
      obtain ⟨binder, left, rfl, capturedLeft⟩ := binderMatched
      rw [mem_matchAtWith_fvar, captureWith?_literal] at capturedLeft capturedOuter
      simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at capturedLeft capturedOuter
      obtain ⟨leftDependencies, leftDeclared, leftArguments, leftSupplied, leftValue, leftRecovered,
        leftAssigned⟩ := capturedLeft
      obtain ⟨outerDependencies, outerDeclared, outerArguments, outerSupplied, outerValue, outerRecovered,
        outerAssigned⟩ := capturedOuter
      simp [orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation, dependencies?,
        arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, ScopedEquationExecution.exchangeBindings,
        ScopedEquationExecution.exchangeOccurrence, ScopedEquationExecution.exchangeSite] at leftDeclared leftSupplied outerDeclared outerSupplied
      subst leftDeclared leftSupplied outerDeclared outerSupplied
      have leftContext := recoverValue?_context _ _ _ _ _ _ leftRecovered
      have leftForward := recoverValue?_forward _ _ _ _ _ _ leftRecovered
      have outerRead := recoverValue?_root outerRecovered
      subst outerRead
      simp only [assign, lookup, List.find?_nil, Option.map_none, Option.some.injEq] at leftAssigned
      subst leftAssigned
      simp [assign, lookup] at outerAssigned
      subst outerAssigned
      have root : closedRoot [("Q", (⟨[], ambient, outer⟩ : ContextualValue)), ("P", leftValue)] =
          [("Q", outer)] := by
        simp [closedRoot, leftContext.1]
      rw [root] at premises
      have kept := ((declared_premises_spec allowed fuel outer final).mp premises).1
      subst kept
      have extended : extendClosed ambient [("Q", (⟨[], ambient, outer⟩ : ContextualValue)), ("P", leftValue)]
          [("Q", outer)] = [("Q", ⟨[], ambient, outer⟩), ("P", leftValue)] := by
        rw [← root, extendClosed_closedRoot]
      rw [extended] at applied
      simp only [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, extrusionEquation,
        ScopedEquationControls.extrusionEquation, Option.bind_eq_bind, Option.bind_eq_some_iff] at applied
      simp [arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup, leftForward,
        ScopedEquationExecution.exchangeBindings, ScopedEquationExecution.exchangeOccurrence,
        ScopedEquationExecution.exchangeSite] at applied
      obtain ⟨inner, shifted, rfl⟩ := applied
      exact ⟨binder, left, inner, outer, [("Q", outer)], shifted, premises,
        Or.inr ⟨rfl, rfl, outerRecovered⟩⟩

/-- Read through its declaration, the extrusion moves a named restriction out over its guard. -/
theorem declared_named_forward {ambient : Nat} (allowed : List Token) (binder : Option String)
    (name : Fin (ambient + 1)) (key : Token) (admitted : key ∈ allowed) :
    EquationInstance (base allowed) language
      (displayedPattern binder ⟨.tucked, name, key⟩)
      (State.pattern (⟨.exposed, name, key⟩ : State ambient)) := by
  have matched : captured ambient name key ∈ matchRuleAt (orientedRule extrusionEquation .forward)
      ((orientedRule extrusionEquation .forward).bindings.getD { dependencies := [] }) ambient
      (displayedPattern binder ⟨.tucked, name, key⟩) := by
    have computed : matchRuleAt (orientedRule extrusionEquation .forward)
        ((orientedRule extrusionEquation .forward).bindings.getD { dependencies := [] }) ambient
        (displayedPattern binder ⟨.tucked, name, key⟩) = [captured ambient name key] := by
      simp [displayedPattern, matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith, captureWith?_literal,
        capture?, orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation, pair,
        dependencies?, arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, recover_cellValue,
        recover_guardValue, captured, assign, lookup]
    rw [computed]
    exact List.mem_singleton_self _
  have root : closedRoot (captured ambient name key) = [("Q", guard key)] := by
    simp [closedRoot, captured, guardValue, cellValue]
  have extended : extendClosed ambient (captured ambient name key) [("Q", guard key)] =
      captured ambient name key := by
    rw [← root, extendClosed_closedRoot]
  refine ⟨0, .declared (orientation := .forward) (ambient := ambient) (List.Mem.head _) extrusion_not_raw
    ⟨_, captured ambient name key, [("Q", guard key)], rfl, extrusion_admitted .forward, ?_, matched, ?_, ?_,
      ?_⟩⟩
  · simp [displayedPattern, pair, cell, EquationFrontierBinderProfile.guard, Token.pattern,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
  · rw [root]
    exact (declared_premises_spec allowed 0 _ _).mpr ⟨rfl, key, admitted, rfl⟩
  · rw [extended]
    exact reduct_extrusion_forward ambient name key
  · simp [State.pattern, pair, nu, cell, EquationFrontierBinderProfile.guard, Token.pattern,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

end Declared

/-- The raw equation class of a canonical source contains arbitrarily named
presentations. Exact raw-state coverage by canonical endpoints would be false. -/
theorem raw_metadata_separator {ambient : Nat} (allowed : List Token) (binder : String)
    (name : Fin (ambient + 1)) (key : Token) (admitted : key ∈ allowed) :
    EquationEquiv (base allowed) language
      (State.pattern (⟨.exposed, name, key⟩ : State ambient))
      (displayedPattern (some binder) ⟨.tucked, name, key⟩) ∧
      (displayedPattern (some binder) (⟨.tucked, name, key⟩ : State ambient)).hasCanonicalBinderMetadata
        = false := by
  constructor
  · exact Relation.EqvGen.symm _ _ (equationInstance_equivalent
      (declared_named_forward allowed (some binder) name key admitted))
  · simp [displayedPattern, pair, cell, EquationFrontierBinderProfile.guard, Token.pattern,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- Root matching and primitive interpretation cannot discover an equation in
a tree whose every subterm is inert for both authored orientations. -/
inductive EquationInert : Pattern → Prop where
  | bvar (index : Nat) : EquationInert (.bvar index)
  | apply (constructor : String) (arguments : List Pattern) :
      matchPattern extrusionEquation.left (.apply constructor arguments) = [] →
      matchPattern extrusionEquation.right (.apply constructor arguments) = [] →
      (∀ argument ∈ arguments, EquationInert argument) →
      EquationInert (.apply constructor arguments)
  | lambda (binder : Option String) (body : Pattern) :
      EquationInert body → EquationInert (.lambda binder body)

theorem EquationInert.no_root {pattern : Pattern} (inert : EquationInert pattern) :
    matchPattern extrusionEquation.left pattern = [] ∧
      matchPattern extrusionEquation.right pattern = [] := by
  cases inert with
  | bvar index => simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  | apply _ _ left right _ => exact ⟨left, right⟩
  | lambda _ _ _ => simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]

theorem EquationInert.of_fill (context : OneHoleContext) (redex : Pattern)
    (inert : EquationInert (context.fill redex)) : EquationInert redex := by
  induction context with
  | hole => exact inert
  | apply constructor before inner after ih =>
    cases inert with
    | apply _ _ _ _ arguments =>
      exact ih (arguments (inner.fill redex) (by simp))
  | lambda binder inner ih =>
    cases inert with
    | lambda _ _ body => exact ih body
  | multiLambda _ _ _ _ => cases inert
  | substBody _ _ _ => cases inert
  | substReplacement _ _ _ => cases inert
  | collection _ _ _ _ _ _ => cases inert

theorem inert_token (key : Token) : EquationInert key.pattern := by
  apply EquationInert.apply
  · cases key <;> simp [Token.label, extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · cases key <;> simp [Token.label, extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · simp

theorem inert_guard (key : Token) : EquationInert (EquationFrontierBinderProfile.guard key) := by
  apply EquationInert.apply
  · simp [extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact inert_token key

theorem inert_cell (index : Nat) : EquationInert (cell index) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact .bvar index

theorem inert_cell_guard (index : Nat) (key : Token) :
    EquationInert (pair (cell index) (EquationFrontierBinderProfile.guard key)) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [cell, extrusionEquation, ScopedEquationControls.extrusionEquation,
      matchPattern, matchArgs]
  · intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact inert_cell index
    · exact inert_guard key

theorem inert_nu_cell (binder : Option String) (index : Nat) :
    EquationInert (.apply "Nu" [.lambda binder (cell index)]) := by
  apply EquationInert.apply
  · simp [cell, extrusionEquation, ScopedEquationControls.extrusionEquation,
      matchPattern, matchArgs]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact .lambda binder _ (inert_cell index)

theorem inert_done_cell_guard (index : Nat) (key : Token) :
    EquationInert (done (pair (cell index) (EquationFrontierBinderProfile.guard key))) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact inert_cell_guard index key

theorem displayed_arguments_inert {ambient : Nat} (binder : Option String)
    (state : State ambient) (constructor : String) (arguments : List Pattern)
    (shape : displayedPattern binder state = .apply constructor arguments) :
    ∀ argument ∈ arguments, EquationInert argument := by
  cases state with
  | mk phase name key =>
    cases phase <;>
      simp only [displayedPattern, pair, Pattern.apply.injEq] at shape
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      have equal := List.mem_singleton.mp member
      subst argument
      exact .lambda binder _ (inert_cell_guard name.val key)
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact inert_nu_cell binder name.val
      · exact inert_guard key
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      have equal := List.mem_singleton.mp member
      subst argument
      exact .lambda binder _ (inert_done_cell_guard name.val key)

theorem no_collection_carrier {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule language rule kind) : False := by
  obtain ⟨parameter, element, parameters⟩ := declaration.selfSorted
  have authored := declaration.authored
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tokenRule, guardRule, cellRule, pairRule, nuRule, doneRule,
    TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at parameters

theorem no_collection_algebra {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (declaration : AlgebraRule language rule kind algebra) : False := by
  have authored := declaration.authored
  have declared := declaration.declared
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tokenRule, guardRule, cellRule, pairRule, nuRule, doneRule] at declared

theorem no_collection_type {rule : GrammarRule} {kind : CollType} {elements : List Pattern}
    (member : rule ∈ language.terms)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind elements) : False := by
  have declared := usesCollection_eq_true_of_collectionTypedAt member typed
  have absent : language.usesCollection kind = false := by cases kind <;> rfl
  rw [absent] at declared
  cases declared

theorem no_derived {source target : Pattern} (derived : DerivedInstance language source target) :
    False := by
  cases derived with
  | bagPerm member kindTyped _ => exact no_collection_type member kindTyped
  | setPerm member kindTyped _ => exact no_collection_type member kindTyped
  | setDedup member kindTyped => exact no_collection_type member kindTyped
  | flatten declaration _ _ => exact no_collection_algebra declaration
  | singleton declaration _ _ => exact no_collection_algebra declaration
  | unitElim declaration _ _ => exact no_collection_algebra declaration
  | emptyUnit declaration _ _ => exact no_collection_algebra declaration

theorem authored_equation_unique {equation : Equation}
    (authored : List.Mem equation language.equations) : equation = extrusionEquation := by
  change List.Mem equation [extrusionEquation] at authored
  cases authored with
  | head => rfl
  | tail _ rest => cases rest

/-- The guarded extrusion is read only through its declaration. -/
theorem instance_declared (allowed : List Token) {fuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt (base allowed) language fuel source target) :
    ∃ ambient orientation,
      DeclaredInstanceAt (base allowed) language fuel ambient extrusionEquation orientation source target := by
  cases equationInstance with
  | forward authored raw =>
    rw [authored_equation_unique authored, extrusion_not_raw] at raw
    cases raw
  | reverse authored raw =>
    rw [authored_equation_unique authored, extrusion_not_raw] at raw
    cases raw
  | @declared equation orientation ambient _ _ authored _ declared =>
    rw [authored_equation_unique authored] at declared
    exact ⟨ambient, orientation, declared⟩

theorem inert_no_instance (allowed : List Token) {source target : Pattern}
    (inert : EquationInert source) (equationInstance : EquationInstance (base allowed) language source target) :
    False := by
  obtain ⟨_, equationInstance⟩ := equationInstance
  obtain ⟨_, _, declared⟩ := instance_declared allowed equationInstance
  obtain ⟨binder, left, inner, outer, _, -, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := declared_instance_shape allowed declared
  · have none := inert.no_root.1
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation, pair, matchPattern, matchArgs,
      mergeBindings] at none
  · have none := inert.no_root.2
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation, pair, matchPattern, matchArgs,
      mergeBindings] at none

theorem inert_no_generator (allowed : List Token) {source target : Pattern}
    (inert : EquationInert source) (generator : EquationGenerator (base allowed) language source target) :
    False := by
  rcases generator with equationInstance | derived
  · exact inert_no_instance allowed inert equationInstance
  · exact no_derived derived

/-- Every proper subterm of the admitted family is equation-inert. Structural
equation contexts therefore cannot hide another conversion below its root. -/
theorem equation_context_root {ambient : Nat} (allowed : List Token) (binder : Option String)
    (state : State ambient) (context : OneHoleContext) (redex contractum : Pattern)
    (generator : EquationGenerator (base allowed) language redex contractum)
    (source : context.fill redex = displayedPattern binder state) : context = .hole := by
  cases context with
  | hole => rfl
  | apply constructor before inner after =>
    have children := displayed_arguments_inert binder state constructor
      (before ++ inner.fill redex :: after) source.symm
    have inert := children (inner.fill redex) (by simp)
    exact False.elim (inert_no_generator allowed (inert.of_fill inner redex) generator)
  | lambda _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | multiLambda _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | substBody _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | substReplacement _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | collection _ _ _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source

theorem inert_no_instance_target (allowed : List Token) {source target : Pattern}
    (inert : EquationInert target)
    (equationInstance : EquationInstance (base allowed) language source target) : False := by
  obtain ⟨_, equationInstance⟩ := equationInstance
  obtain ⟨_, _, declared⟩ := instance_declared allowed equationInstance
  obtain ⟨binder, left, inner, outer, _, -, -, ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩⟩ :=
    declared_instance_shape allowed declared
  · have none := inert.no_root.2
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation, pair, nu, matchPattern, matchArgs,
      mergeBindings] at none
  · have none := inert.no_root.1
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation, pair, nu, matchPattern, matchArgs,
      mergeBindings] at none

theorem inert_no_generator_target (allowed : List Token) {source target : Pattern}
    (inert : EquationInert target)
    (generator : EquationGenerator (base allowed) language source target) : False := by
  rcases generator with equationInstance | derived
  · exact inert_no_instance_target allowed inert equationInstance
  · exact no_derived derived

theorem equation_context_root_target {ambient : Nat} (allowed : List Token)
    (binder : Option String) (state : State ambient) (context : OneHoleContext)
    (redex contractum : Pattern)
    (generator : EquationGenerator (base allowed) language redex contractum)
    (target : context.fill contractum = displayedPattern binder state) : context = .hole := by
  cases context with
  | hole => rfl
  | apply constructor before inner after =>
    have children := displayed_arguments_inert binder state constructor
      (before ++ inner.fill contractum :: after) target.symm
    have inert := children (inner.fill contractum) (by simp)
    exact False.elim (inert_no_generator_target allowed (inert.of_fill inner contractum) generator)
  | lambda _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | multiLambda _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | substBody _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | substReplacement _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | collection _ _ _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target

theorem list_length_one {α : Type} (list : List α) (length : list.length = 1) :
    ∃ value, list = [value] := by
  cases list with
  | nil => simp at length
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons _ _ => simp at length

theorem list_length_two {α : Type} (list : List α) (length : list.length = 2) :
    ∃ first second, list = [first, second] := by
  cases list with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons second rest =>
      cases rest with
      | nil => exact ⟨first, second, rfl⟩
      | cons _ _ => simp at length

theorem erasure_apply_shape (constructor : String) (arguments : List Pattern)
    (source : Pattern) (equal : source.eraseBinderMetadata = .apply constructor arguments) :
    ∃ rawArguments, source = .apply constructor rawArguments ∧
      rawArguments.map Pattern.eraseBinderMetadata = arguments := by
  cases source <;> simp only [Pattern.eraseBinderMetadata, Pattern.apply.injEq] at equal
  all_goals try contradiction
  obtain ⟨rfl, argumentsEqual⟩ := equal
  exact ⟨_, rfl, argumentsEqual⟩

theorem erasure_apply_one (constructor : String) (argument source : Pattern)
    (equal : source.eraseBinderMetadata = .apply constructor [argument]) :
    ∃ rawArgument, source = .apply constructor [rawArgument] ∧
      rawArgument.eraseBinderMetadata = argument := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape constructor [argument] source equal
  have length : arguments.length = 1 := by
    simpa using congrArg List.length erased
  obtain ⟨rawArgument, rfl⟩ := list_length_one arguments length
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at erased
  exact ⟨rawArgument, rfl, erased⟩

theorem erasure_apply_two (constructor : String) (first second source : Pattern)
    (equal : source.eraseBinderMetadata = .apply constructor [first, second]) :
    ∃ rawFirst rawSecond, source = .apply constructor [rawFirst, rawSecond] ∧
      rawFirst.eraseBinderMetadata = first ∧ rawSecond.eraseBinderMetadata = second := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape constructor [first, second] source equal
  have length : arguments.length = 2 := by
    simpa using congrArg List.length erased
  obtain ⟨rawFirst, rawSecond, rfl⟩ := list_length_two arguments length
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at erased
  exact ⟨rawFirst, rawSecond, rfl, erased⟩

theorem erasure_lambda_shape (body source : Pattern)
    (equal : source.eraseBinderMetadata = .lambda none body) :
    ∃ binder rawBody, source = .lambda binder rawBody ∧ rawBody.eraseBinderMetadata = body := by
  cases source <;> simp only [Pattern.eraseBinderMetadata, Pattern.lambda.injEq] at equal
  all_goals try contradiction
  exact ⟨_, _, rfl, equal.2⟩

theorem erasure_token (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = key.pattern) : source = key.pattern := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape key.label [] source equal
  have empty : arguments = [] := List.map_eq_nil_iff.mp erased
  subst arguments
  rfl

theorem erasure_guard (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = guard key) : source = guard key := by
  obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Guard" key.pattern source equal
  rw [erasure_token key argument erased]
  rfl

theorem erasure_cell (index : Nat) (source : Pattern)
    (equal : source.eraseBinderMetadata = cell index) : source = cell index := by
  obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Cell" (.bvar index) source equal
  have argumentEqual : argument = .bvar index := by
    cases argument <;> simp_all [Pattern.eraseBinderMetadata]
  rw [argumentEqual]
  rfl

theorem erasure_cell_guard (index : Nat) (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = pair (cell index) (guard key)) :
    source = pair (cell index) (guard key) := by
  obtain ⟨first, second, rfl, firstEq, secondEq⟩ :=
    erasure_apply_two "Pair" (cell index) (guard key) source equal
  rw [erasure_cell index first firstEq, erasure_guard key second secondEq]
  rfl

theorem erasure_done_cell_guard (index : Nat) (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = done (pair (cell index) (guard key))) :
    source = done (pair (cell index) (guard key)) := by
  obtain ⟨argument, rfl, erased⟩ :=
    erasure_apply_one "Done" (pair (cell index) (guard key)) source equal
  rw [erasure_cell_guard index key argument erased]
  rfl

theorem erasure_inverse {ambient : Nat} (source : Pattern) (state : State ambient)
    (equal : source.eraseBinderMetadata = state.pattern) :
    ∃ binder, source = displayedPattern binder state := by
  cases state with
  | mk phase name key =>
    cases phase with
    | tucked =>
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ source equal
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_cell_guard name.val key body erasedBody]
      exact ⟨binder, rfl⟩
    | exposed =>
      obtain ⟨first, second, rfl, firstEq, secondEq⟩ := erasure_apply_two "Pair" _ _ source equal
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ first firstEq
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_cell name.val body erasedBody, erasure_guard key second secondEq]
      exact ⟨binder, rfl⟩
    | finished =>
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ source equal
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_done_cell_guard name.val key body erasedBody]
      exact ⟨binder, rfl⟩

theorem raw_instance_from_displayed {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern)
    (equationInstance : EquationInstance (base allowed) language
      (displayedPattern sourceBinder source) target) :
    ∃ next : State ambient, target = next.pattern ∧
      (EquationEdge allowed source next ∨ EquationEdge allowed next source) := by
  obtain ⟨fuel, equationInstance⟩ := equationInstance
  obtain ⟨scope, _, declared⟩ := instance_declared allowed equationInstance
  obtain ⟨binder, left, inner, outer, result, shifted, premises, shape⟩ := declared_instance_shape allowed declared
  cases source with
  | mk phase name key =>
    rcases shape with ⟨sourceEq, targetEq, recovered⟩ | ⟨sourceEq, targetEq, recovered⟩
    · cases phase with
      | tucked =>
        simp only [displayedPattern, pair, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        rcases sourceEq with ⟨rfl, rfl, rfl⟩
        rw [recover_guardValue] at recovered
        have outerEq : outer = guard key := by
          simpa [guardValue] using (congrArg ContextualValue.body (Option.some.inj recovered)).symm
        subst outerEq
        obtain ⟨-, found, member, sameGuard⟩ := (declared_premises_spec allowed _ _ result).mp premises
        rw [guard_eq_iff] at sameGuard
        subst sameGuard
        exact ⟨⟨.exposed, name, found⟩, targetEq, Or.inl (.extrusion name found member)⟩
      | exposed => simp [displayedPattern, pair] at sourceEq
      | finished => simp [displayedPattern, done, pair] at sourceEq
    · cases phase with
      | tucked => simp [displayedPattern, pair] at sourceEq
      | exposed =>
        simp only [displayedPattern, pair, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        rcases sourceEq with ⟨⟨rfl, rfl⟩, rfl⟩
        have read : instantiateValue? (guardValue scope key) scope 1 [] = some inner := shifted
        rw [instantiate_guardValue] at read
        have innerEq := Option.some.inj read
        subst innerEq
        obtain ⟨-, found, member, sameGuard⟩ := (declared_premises_spec allowed _ _ result).mp premises
        rw [guard_eq_iff] at sameGuard
        subst sameGuard
        exact ⟨⟨.tucked, name, found⟩, targetEq, Or.inr (.extrusion name found member)⟩
      | finished => simp [displayedPattern, pair] at sourceEq

theorem raw_instance_into_displayed {ambient : Nat} (allowed : List Token)
    (targetBinder : Option String) (target : State ambient) (source : Pattern)
    (equationInstance : EquationInstance (base allowed) language source
      (displayedPattern targetBinder target)) :
    ∃ (binder : Option String) (previous : State ambient), source = displayedPattern binder previous ∧
      (EquationEdge allowed previous target ∨ EquationEdge allowed target previous) := by
  obtain ⟨fuel, equationInstance⟩ := equationInstance
  obtain ⟨scope, _, declared⟩ := instance_declared allowed equationInstance
  obtain ⟨binder, left, inner, outer, result, shifted, premises, shape⟩ := declared_instance_shape allowed declared
  cases target with
  | mk phase name key =>
    rcases shape with ⟨sourceEq, targetEq, recovered⟩ | ⟨sourceEq, targetEq, recovered⟩
    · cases phase with
      | tucked => simp [displayedPattern, pair, nu] at targetEq
      | exposed =>
        simp only [displayedPattern, pair, nu, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at targetEq
        rcases targetEq with ⟨⟨rfl, rfl⟩, rfl⟩
        have read : instantiateValue? (guardValue scope key) scope 1 [] = some inner := shifted
        rw [instantiate_guardValue] at read
        have innerEq := Option.some.inj read
        subst innerEq
        obtain ⟨-, found, member, sameGuard⟩ := (declared_premises_spec allowed _ _ result).mp premises
        rw [guard_eq_iff] at sameGuard
        subst sameGuard
        exact ⟨binder, ⟨.tucked, name, found⟩, sourceEq, Or.inl (.extrusion name found member)⟩
      | finished => simp [displayedPattern, pair, nu] at targetEq
    · cases phase with
      | tucked =>
        simp only [displayedPattern, pair, nu, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at targetEq
        rcases targetEq with ⟨rfl, rfl, rfl⟩
        have outerEq := instantiateValue?_guard shifted
        subst outerEq
        obtain ⟨-, found, member, sameGuard⟩ := (declared_premises_spec allowed _ _ result).mp premises
        rw [guard_eq_iff] at sameGuard
        subst sameGuard
        exact ⟨binder, ⟨.exposed, name, found⟩, sourceEq, Or.inr (.extrusion name found member)⟩
      | exposed => simp [displayedPattern, pair, nu] at targetEq
      | finished => simp [displayedPattern, pair, nu, done] at targetEq

theorem raw_context_from_displayed {ambient : Nat} (allowed : List Token)
    (binder : Option String) (source : State ambient) (target : Pattern)
    (contextual : EquationContextStep (base allowed) language
      (displayedPattern binder source) target) :
    ∃ next : State ambient, target = next.pattern ∧
      (EquationEdge allowed source next ∨ EquationEdge allowed next source) := by
  generalize sourceEq : displayedPattern binder source = rawSource at contextual
  cases contextual with
  | inContext context generator =>
    have root := equation_context_root allowed binder source context _ _ generator sourceEq.symm
    subst context
    simp only [OneHoleContext.fill] at sourceEq ⊢
    rw [← sourceEq] at generator
    rcases generator with equationInstance | derived
    · exact raw_instance_from_displayed allowed binder source _ equationInstance
    · exact False.elim (no_derived derived)

theorem raw_context_into_displayed {ambient : Nat} (allowed : List Token)
    (binder : Option String) (target : State ambient) (source : Pattern)
    (contextual : EquationContextStep (base allowed) language source
      (displayedPattern binder target)) :
    ∃ (previousBinder : Option String) (previous : State ambient),
      source = displayedPattern previousBinder previous ∧
        (EquationEdge allowed previous target ∨ EquationEdge allowed target previous) := by
  generalize targetEq : displayedPattern binder target = rawTarget at contextual
  cases contextual with
  | inContext context generator =>
    have root := equation_context_root_target allowed binder target context _ _ generator targetEq.symm
    subst context
    simp only [OneHoleContext.fill] at targetEq ⊢
    rw [← targetEq] at generator
    rcases generator with equationInstance | derived
    · exact raw_instance_into_displayed allowed binder target _ equationInstance
    · exact False.elim (no_derived derived)

theorem neighbor_equivalent {ambient : Nat} (allowed : List Token)
    {source target : State ambient}
    (neighbor : EquationEdge allowed source target ∨ EquationEdge allowed target source) :
    Relation.EqvGen (EquationEdge allowed) source target := by
  rcases neighbor with forward | reverse
  · exact .rel _ _ forward
  · exact .symm _ _ (.rel _ _ reverse)

/-- Full raw contextual closure retains the finite carrier after alpha
normalization. Both directions matter: `EqvGen` also admits incoming raw
instances, whose binder display names need not have been canonical. -/
theorem raw_equiv_admitted {ambient : Nat} (allowed : List Token) {left right : Pattern}
    (equivalent : EquationEquiv (base allowed) language left right) :
    (∀ source : State ambient, left.eraseBinderMetadata = source.pattern →
      ∃ target : State ambient, right.eraseBinderMetadata = target.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) ∧
    (∀ target : State ambient, right.eraseBinderMetadata = target.pattern →
      ∃ source : State ambient, left.eraseBinderMetadata = source.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) := by
  induction equivalent with
  | rel left right contextual =>
    constructor
    · intro source admitted
      obtain ⟨binder, rfl⟩ := erasure_inverse left source admitted
      obtain ⟨target, rfl, neighbor⟩ := raw_context_from_displayed allowed binder source right contextual
      exact ⟨target, Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
        neighbor_equivalent allowed neighbor⟩
    · intro target admitted
      obtain ⟨binder, rfl⟩ := erasure_inverse right target admitted
      obtain ⟨sourceBinder, source, rfl, neighbor⟩ :=
        raw_context_into_displayed allowed binder target left contextual
      exact ⟨source, displayed_erasure sourceBinder source, neighbor_equivalent allowed neighbor⟩
  | refl pattern =>
    constructor
    · intro source admitted
      exact ⟨source, admitted, .refl source⟩
    · intro target admitted
      exact ⟨target, admitted, .refl target⟩
  | symm left right equivalent ih =>
    constructor
    · intro source admitted
      obtain ⟨target, targetAdmitted, relation⟩ := ih.2 source admitted
      exact ⟨target, targetAdmitted, .symm _ _ relation⟩
    · intro target admitted
      obtain ⟨source, sourceAdmitted, relation⟩ := ih.1 target admitted
      exact ⟨source, sourceAdmitted, .symm _ _ relation⟩
  | trans left middle right first second firstIH secondIH =>
    constructor
    · intro source admitted
      obtain ⟨midpoint, midpointAdmitted, firstRelation⟩ := firstIH.1 source admitted
      obtain ⟨target, targetAdmitted, secondRelation⟩ := secondIH.1 midpoint midpointAdmitted
      exact ⟨target, targetAdmitted, .trans _ _ _ firstRelation secondRelation⟩
    · intro target admitted
      obtain ⟨midpoint, midpointAdmitted, secondRelation⟩ := secondIH.2 target admitted
      obtain ⟨source, sourceAdmitted, firstRelation⟩ := firstIH.2 midpoint midpointAdmitted
      exact ⟨source, sourceAdmitted, .trans _ _ _ firstRelation secondRelation⟩

theorem finite_equiv_raw {ambient : Nat} (allowed : List Token)
    {source target : State ambient}
    (equivalent : Relation.EqvGen (EquationEdge allowed) source target) :
    EquationEquiv (base allowed) language source.pattern target.pattern := by
  induction equivalent with
  | rel source target edge =>
    cases edge with
    | extrusion name key admitted =>
      simpa only [displayed_none] using equationInstance_equivalent
        (declared_named_forward allowed none name key admitted)
  | refl source => exact .refl source.pattern
  | symm source target relation ih => exact .symm _ _ ih
  | trans source middle target first second firstIH secondIH =>
    exact .trans _ _ _ firstIH secondIH

/-- Finite representatives are complete for the authored contextual equation
theory on its canonical alpha section, for every ambient context and snapshot. -/
theorem canonical_equation_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    EquationEquiv (base allowed) language source.pattern target.pattern ↔
      Relation.EqvGen (EquationEdge allowed) source target := by
  constructor
  · intro equivalent
    obtain ⟨next, normalized, relation⟩ :=
      (raw_equiv_admitted allowed equivalent).1 source
        (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical source))
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target)] at normalized
    have equal := state_pattern_injective normalized
    subst next
    exact relation
  · exact finite_equiv_raw allowed

/-- Raw equation detours never leave the admitted finite alpha carrier. The
normalization readout preserves the exact indexed name and provider key. -/
theorem raw_class_normalization {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern)
    (equivalent : EquationEquiv (base allowed) language source.pattern rawTarget) :
    ∃ target : State ambient, rawTarget.eraseBinderMetadata = target.pattern ∧
      Relation.EqvGen (EquationEdge allowed) source target :=
  (raw_equiv_admitted allowed equivalent).1 source
    (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical source))

theorem rewrite_noncontextual (rule : RewriteRule) (authored : rule ∈ language.rewrites) :
    NoncontextualPremises rule.premises := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> exact .relationQuery .nil

theorem rewrite_matching (rule : RewriteRule) (authored : rule ∈ language.rewrites)
    (source : Pattern) :
    matchPatternForRule language rule source = matchPattern consumeRule.left source := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> rw [matchPatternForRule_eq_syntactic]

theorem rewrite_premises (rule : RewriteRule) (authored : rule ∈ language.rewrites) :
    rule.premises = extrusionEquation.premises := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> rfl

theorem raw_rule_target {ambient : Nat} (rule : RewriteRule)
    (authored : rule ∈ language.rewrites) (name : Fin (ambient + 1)) (key : Token) :
    applyBindingsForRule language rule (rawCaptured name.val key) =
      State.pattern (⟨.finished, name, key⟩ : State ambient) := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl
  all_goals rw [applyBindingsForRule_eq_syntactic]
  all_goals simp [applyRuleBindings, consumeRule, rawCaptured,
    applyBindingsScoped, applyBindingsScopedList, captureDepth, captureDepthList,
    State.pattern, nu, done, pair, cell, EquationFrontierBinderProfile.guard,
    Token.pattern, Substitution.liftBVars, Substitution.liftBVarsList]

theorem raw_consume_displayed {ambient : Nat} (sourceBinder : Option String)
    (name : Fin (ambient + 1)) (key : Token) :
    matchPattern consumeRule.left (displayedPattern sourceBinder ⟨.exposed, name, key⟩) =
      [rawCaptured name.val key] := by
  simp [consumeRule, displayedPattern, nu, pair, matchPattern, matchArgs,
    mergeBindings, rawCaptured]

theorem raw_step_displayed_spec {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern) :
    Step (base allowed) language (displayedPattern sourceBinder source) target ↔
      source.phase = .exposed ∧ source.key ∈ allowed ∧
        target = State.pattern (⟨.finished, source.name, source.key⟩ : State ambient) := by
  change Step (engineBasePremises (provider allowed)) language _ _ ↔ _
  rw [step_iff_rootStep_of_noncontextualRules rewrite_noncontextual]
  constructor
  · rintro ⟨rule, authored, initial, matched, final, premises, reduct⟩
    rw [rewrite_matching rule authored] at matched
    rw [rewrite_premises rule authored] at premises
    have premisesRel : PremisesAt (base allowed) language 0 initial
        extrusionEquation.premises final :=
      (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
        (show NoncontextualPremises extrusionEquation.premises from .relationQuery .nil)).mpr premises
    cases source with
    | mk phase name key =>
      cases phase with
      | tucked => simp [consumeRule, displayedPattern, pair, nu, matchPattern] at matched
      | finished => simp [consumeRule, displayedPattern, pair, nu, matchPattern] at matched
      | exposed =>
        rw [raw_consume_displayed] at matched
        have initialEq := List.mem_singleton.mp matched
        subst initial
        obtain ⟨finalEq, admitted⟩ := (raw_premises_spec allowed name.val key 0 final).mp premisesRel
        subst final
        rw [raw_rule_target rule authored] at reduct
        exact ⟨rfl, admitted, reduct.symm⟩
  · rintro ⟨phase, admitted, targetEq⟩
    cases source with
    | mk sourcePhase name key =>
      simp only at phase
      subst sourcePhase
      subst target
      refine ⟨consumeRule, by simp [language], rawCaptured name.val key, ?_,
        rawCaptured name.val key, ?_, ?_⟩
      · rw [matchPatternForRule_eq_syntactic, raw_consume_displayed]
        simp
      · rw [show consumeRule.premises = extrusionEquation.premises from rfl]
        exact (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (show NoncontextualPremises extrusionEquation.premises from .relationQuery .nil)).mp
            ((raw_premises_spec allowed name.val key 0 _).mpr ⟨rfl, admitted⟩)
      · exact raw_rule_target consumeRule (by simp [language]) name key

theorem raw_step_comparison {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern) :
    Step (base allowed) language (displayedPattern sourceBinder source) target ↔
      ∃ (origin : Origin) (next : State ambient),
        Firing allowed source origin next ∧ target = next.pattern := by
  rw [raw_step_displayed_spec]
  constructor
  · rintro ⟨phase, admitted, targetEq⟩
    obtain ⟨row, found⟩ := List.mem_iff_getElem?.mp admitted
    cases source with
    | mk sourcePhase name key =>
      simp only at phase
      subst sourcePhase
      exact ⟨⟨0, row⟩, ⟨.finished, name, key⟩, .consume name key 0 row found, targetEq⟩
  · rintro ⟨origin, next, firing, targetEq⟩
    cases firing with
    | consume name key declaration row found =>
      exact ⟨rfl, List.mem_of_getElem? found, targetEq⟩

/-- Raw execution is invariant under the declared alpha section on this
whole binder-aware carrier, rather than only on selected ground examples. -/
theorem raw_step_normalization {ambient : Nat} (allowed : List Token)
    (source : Pattern) (state : State ambient) (target : Pattern)
    (admitted : source.eraseBinderMetadata = state.pattern) :
    Step (base allowed) language source target ↔
      Step (base allowed) language state.pattern target := by
  obtain ⟨binder, rfl⟩ := erasure_inverse source state admitted
  rw [raw_step_displayed_spec, ← displayed_none state, raw_step_displayed_spec]

/-- The finite operational profile is a proved restriction of the genuinely
generated GSLT relation, including arbitrary contextual equation detours at
both ends. The original raw relation has not been replaced by the enumerator. -/
theorem generated_gslt_step_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    StepModuloEquations (base allowed) language source.pattern target.pattern ↔
      EquationFrontierBinderProfile.Step allowed source target := by
  constructor
  · rintro ⟨redex, contractum, before, firing, after⟩
    obtain ⟨representative, normalized, beforeFinite⟩ :=
      raw_class_normalization allowed source redex before
    obtain ⟨binder, redexEq⟩ := erasure_inverse redex representative normalized
    rw [redexEq] at firing
    obtain ⟨origin, next, primitive, contractumEq⟩ :=
      (raw_step_comparison allowed binder representative contractum).mp firing
    rw [contractumEq] at after
    have afterFinite := (canonical_equation_comparison allowed next target).mp after
    exact ⟨representative, ⟨origin, next⟩, beforeFinite, primitive, afterFinite⟩
  · rintro ⟨representative, event, before, firing, after⟩
    refine ⟨representative.pattern, event.target.pattern, finite_equiv_raw allowed before,
      ?_, finite_equiv_raw allowed after⟩
    simpa only [displayed_none] using
      (raw_step_comparison allowed none representative event.target.pattern).mpr
        ⟨event.origin, event.target, firing, rfl⟩

theorem raw_modulo_class_normalization {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern)
    (step : StepModuloEquations (base allowed) language source.pattern rawTarget) :
    ∃ target : State ambient, rawTarget.eraseBinderMetadata = target.pattern ∧
      EquationFrontierBinderProfile.Step allowed source target := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  obtain ⟨representative, normalized, beforeFinite⟩ :=
    raw_class_normalization allowed source redex before
  obtain ⟨binder, redexEq⟩ := erasure_inverse redex representative normalized
  rw [redexEq] at firing
  obtain ⟨origin, next, primitive, contractumEq⟩ :=
    (raw_step_comparison allowed binder representative contractum).mp firing
  rw [contractumEq] at after
  obtain ⟨target, targetNormalized, afterFinite⟩ :=
    raw_class_normalization allowed next rawTarget after
  exact ⟨target, targetNormalized, representative, ⟨origin, next⟩,
    beforeFinite, primitive, afterFinite⟩

/-- The checked finite certificate covers the raw equation class after its
existing alpha quotient. A named raw endpoint need not itself be the canonical
representative: the comparison quantifies the represented member of its class. -/
theorem alpha_equation_certificate_comparison {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern) :
    (∃ representative : Pattern,
      EquationEquiv (base allowed) language source.pattern representative ∧
        Pattern.AlphaEquiv representative rawTarget) ↔
      ∃ target ∈ (certificate allowed source).representatives source,
        Pattern.AlphaEquiv target.pattern rawTarget := by
  constructor
  · rintro ⟨raw, equivalent, alpha⟩
    obtain ⟨target, normalized, finite⟩ := raw_class_normalization allowed source raw equivalent
    refine ⟨target, (representatives_complete allowed source target).mpr finite, ?_⟩
    change target.pattern.eraseBinderMetadata = rawTarget.eraseBinderMetadata
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
      ← normalized]
    exact alpha
  · rintro ⟨target, represented, alpha⟩
    exact ⟨target.pattern,
      finite_equiv_raw allowed ((representatives_complete allowed source target).mp represented),
      alpha⟩

/-- Both raw equation detours and operational targets are covered on the
alpha quotient by the actual checked occurrence frontier. Endpoint coverage
forgets authored origins; the occurrence theorem remains a separate readout. -/
theorem alpha_operational_frontier_comparison {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern) :
    (∃ representative : Pattern,
      StepModuloEquations (base allowed) language source.pattern representative ∧
        Pattern.AlphaEquiv representative rawTarget) ↔
      ∃ target : State ambient, EquationFrontierBinderProfile.Step allowed source target ∧
        Pattern.AlphaEquiv target.pattern rawTarget := by
  constructor
  · rintro ⟨raw, step, alpha⟩
    obtain ⟨target, normalized, finite⟩ := raw_modulo_class_normalization allowed source raw step
    refine ⟨target, finite, ?_⟩
    change target.pattern.eraseBinderMetadata = rawTarget.eraseBinderMetadata
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
      ← normalized]
    exact alpha
  · rintro ⟨target, step, alpha⟩
    exact ⟨target.pattern, (generated_gslt_step_comparison allowed source target).mpr step, alpha⟩

theorem generated_frontier_target_classes {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Quotient.mk (Relation.EqvGen.setoid (EquationEdge allowed)) target ∈
      FiniteEquationCoverage.classFrontier (EquationEdge allowed) (occurrences allowed) Event.target
        (certificate allowed source) source ↔
      (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern := by
  change _ ↔ StepModuloEquations (base allowed) language source.pattern target.pattern
  rw [generated_gslt_step_comparison]
  exact frontier_target_classes allowed source target

theorem generated_frontier_diamond {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (FiniteEquationCoverage.endpoints Event.target (frontier allowed source)).any test = true ↔
      ∃ target : State ambient,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern ∧
          test target = true := by
  simp only [show (gsltModuloEquations (base allowed) language).rewrites =
    StepModuloEquations (base allowed) language from rfl, generated_gslt_step_comparison]
  exact frontier_diamond allowed source test invariant

/-- This is the outgoing universal modality. It is distinct from OSLF's
incoming adjoint box, whose predicate lives on predecessors. -/
theorem generated_frontier_outgoing_universal {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (FiniteEquationCoverage.endpoints Event.target (frontier allowed source)).all test = true ↔
      ∀ target : State ambient,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern →
          test target = true := by
  simp only [show (gsltModuloEquations (base allowed) language).rewrites =
    StepModuloEquations (base allowed) language from rfl, generated_gslt_step_comparison]
  exact frontier_outgoing_universal allowed source test invariant

theorem generated_frontier_empty_iff {ambient : Nat} (allowed : List Token)
    (source : State ambient) :
    frontier allowed source = [] ↔
      ¬ ∃ target : Pattern,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target := by
  rw [frontier_empty_iff]
  constructor
  · intro noFinite ⟨rawTarget, rawStep⟩
    obtain ⟨target, _, finite⟩ := raw_modulo_class_normalization allowed source rawTarget rawStep
    exact noFinite ⟨target, finite⟩
  · intro noRaw ⟨target, finite⟩
    exact noRaw ⟨target.pattern, (generated_gslt_step_comparison allowed source target).mpr finite⟩

end Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated
