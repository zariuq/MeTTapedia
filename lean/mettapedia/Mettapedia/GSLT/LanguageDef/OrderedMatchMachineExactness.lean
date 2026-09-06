import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
import Mettapedia.GSLT.LanguageDef.BindingDecisionExactness

/-!
# Exactness of the ordered-match machine language against its reference machine

Each state family of the ordered-match machine language has one executor
equation: the generic root executor applied to an encoded typed state is the
list of encoded successors that the typed reference machine produces, in the
order the authored rules list them.  From these, the language's step relation
on encoded states is exactly the machine's successor relation, and the
encodings are injective, so the language never confuses two typed states.

The reference machine is a proof device.  Downstream theorems consume the
language step through the exactness theorem, never the machine directly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation (PatternPlan PremisePlan)
open Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
  (encodeName decodeName? encodePath decodePath? encodeBindings decodeBindings? encodeDecision
    decodeDecision? isBoundAt isConstructorOf metavariable runPattern retPattern donePattern
    succeedPattern capturePattern checkBoundPattern checkConstructorPattern joinPattern
    nilBindingsPattern bindPattern joinRightPattern joinMergePattern knilPattern kconsPattern
    projectRelation boundRelation constructorRelation mergeRelation succeedRewrite
    captureRewrite checkBoundRewrite checkConstructorRewrite joinRewrite joinRightRewrite
    joinMergeRewrite finishRewrite rowWhen)
open Mettapedia.GSLT.Core.ConservativeExtension (encodeNat decodeNat? decodeNat?_encodeNat)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Decoders and injectivity -/

def decodeLeaf? : Pattern → Option Leaf
  | .apply "mm-plan" [occurrence, decision, premises, template] => do
      let index ← decodeNat? occurrence
      let decodedDecision ← decodeDecision? decision
      let decodedPremises ← decodeQueries? premises
      let decodedTemplate ← decodeTemplate? template
      some ⟨index, ⟨decodedDecision, decodedPremises, decodedTemplate⟩⟩
  | _ => none

@[simp] theorem decodeLeaf?_encodeLeaf (leaf : Leaf) : decodeLeaf? (encodeLeaf leaf) = some leaf := by
  simp [encodeLeaf, decodeLeaf?]

mutual
  def decodeProgram? : Pattern → Option Program
    | .apply "mm-failure" [] => some .failure
    | .apply "mm-drop" [next] => (decodeProgram? next).map .drop
    | .apply "mm-try" [leaf, patterns, next] => do
        let decodedLeaf ← decodeLeaf? leaf
        let decodedPatterns ← decodePatterns? patterns
        let decodedNext ← decodeProgram? next
        some (.tryRule decodedLeaf decodedPatterns decodedNext)
    | .apply "mm-switch" [branches, default] => do
        let decodedBranches ← decodeBranches? branches
        let decodedDefault ← decodeProgram? default
        some (.switch decodedBranches decodedDefault)
    | _ => none

  def decodeBranches? : Pattern → Option Branches
    | .apply "mm-bnil" [] => some .nil
    | .apply "mm-bcons" [key, program, rest] => do
        let decodedKey ← decodeKey? key
        let decodedProgram ← decodeProgram? program
        let decodedRest ← decodeBranches? rest
        some (.cons decodedKey decodedProgram decodedRest)
    | _ => none
end

mutual
  theorem decodeProgram?_encodeProgram : ∀ program : Program,
      decodeProgram? (encodeProgram program) = some program
    | .failure => rfl
    | .drop next => by simp [encodeProgram, decodeProgram?, decodeProgram?_encodeProgram next]
    | .tryRule leaf patterns onFailure => by
        simp [encodeProgram, decodeProgram?, decodeProgram?_encodeProgram onFailure]
    | .switch branches default => by
        simp [encodeProgram, decodeProgram?, decodeBranches?_encodeBranches branches,
          decodeProgram?_encodeProgram default]

  theorem decodeBranches?_encodeBranches : ∀ branches : Branches,
      decodeBranches? (encodeBranches branches) = some branches
    | .nil => rfl
    | .cons key program rest => by
        simp [encodeBranches, decodeBranches?, decodeProgram?_encodeProgram program,
          decodeBranches?_encodeBranches rest]
end

attribute [simp] decodeProgram?_encodeProgram decodeBranches?_encodeBranches

def decodeFrame? : Pattern → Option Frame
  | .apply "bd-join-right" [tail] => (decodeDecision? tail).map .joinRight
  | .apply "bd-join-merge" [bindings] => (decodeBindings? bindings).map .joinMerge
  | .apply "mm-after" [premises, template] => do
      let decodedPremises ← decodeQueries? premises
      let decodedTemplate ← decodeTemplate? template
      some (.afterMatch decodedPremises decodedTemplate)
  | _ => none

@[simp] theorem decodeFrame?_encodeFrame : ∀ frame : Frame,
    decodeFrame? (encodeFrame frame) = some frame
  | .joinRight tail => by simp [encodeFrame, decodeFrame?]
  | .joinMerge bindings => by simp [encodeFrame, decodeFrame?]
  | .afterMatch premises template => by simp [encodeFrame, decodeFrame?]

def decodeKont? : Pattern → Option (List Frame)
  | .apply "bd-knil" [] => some []
  | .apply "bd-kcons" [frame, rest] => do
      let head ← decodeFrame? frame
      let tail ← decodeKont? rest
      some (head :: tail)
  | _ => none

@[simp] theorem decodeKont?_encodeKont : ∀ kont : List Frame,
    decodeKont? (encodeKont kont) = some kont
  | [] => rfl
  | frame :: rest => by simp [encodeKont, decodeKont?, decodeKont?_encodeKont rest]

def decodeInstantiateFrame? : Pattern → Option InstantiateFrame
  | .apply "mm-arg" [constructor, accumulated, remaining] => do
      let head ← decodeName? constructor
      let decodedAccumulated ← decodeCursor? accumulated
      let decodedRemaining ← decodeTemplates? remaining
      some (.argument head decodedAccumulated decodedRemaining)
  | _ => none

@[simp] theorem decodeInstantiateFrame?_encodeInstantiateFrame : ∀ frame : InstantiateFrame,
    decodeInstantiateFrame? (encodeInstantiateFrame frame) = some frame
  | .argument constructor accumulated remaining => by
      simp [encodeInstantiateFrame, decodeInstantiateFrame?, encodeName, decodeName?]

def decodeInstantiateKont? : Pattern → Option (List InstantiateFrame)
  | .apply "mm-inil" [] => some []
  | .apply "mm-icons" [frame, rest] => do
      let head ← decodeInstantiateFrame? frame
      let tail ← decodeInstantiateKont? rest
      some (head :: tail)
  | _ => none

@[simp] theorem decodeInstantiateKont?_encodeInstantiateKont : ∀ kont : List InstantiateFrame,
    decodeInstantiateKont? (encodeInstantiateKont kont) = some kont
  | [] => rfl
  | frame :: rest => by
      simp [encodeInstantiateKont, decodeInstantiateKont?,
        decodeInstantiateKont?_encodeInstantiateKont rest]

def decodeState? : Pattern → Option MachineState
  | .apply "mm-run" [program, subject, cursor] => do
      let decodedProgram ← decodeProgram? program
      let decodedCursor ← decodeCursor? cursor
      some (.run decodedProgram subject decodedCursor)
  | .apply "mm-dispatch" [branches, subject, focused, cursor] => do
      let decodedBranches ← decodeBranches? branches
      let decodedCursor ← decodeCursor? cursor
      some (.dispatch decodedBranches subject focused decodedCursor)
  | .apply "mm-prefilter" [patterns, cursor, leaf, subject] => do
      let decodedPatterns ← decodePatterns? patterns
      let decodedCursor ← decodeCursor? cursor
      let decodedLeaf ← decodeLeaf? leaf
      some (.prefilter decodedPatterns decodedCursor decodedLeaf subject)
  | .apply "bd-run" [decision, subject, kont] => do
      let decodedDecision ← decodeDecision? decision
      let decodedKont ← decodeKont? kont
      some (.bdRun decodedDecision subject decodedKont)
  | .apply "bd-ret" [bindings, subject, kont] => do
      let decodedBindings ← decodeBindings? bindings
      let decodedKont ← decodeKont? kont
      some (.bdRet decodedBindings subject decodedKont)
  | .apply "bd-done" [bindings] => (decodeBindings? bindings).map .bdDone
  | .apply "mm-premises" [queries, template, bindings] => do
      let decodedQueries ← decodeQueries? queries
      let decodedTemplate ← decodeTemplate? template
      let decodedBindings ← decodeBindings? bindings
      some (.premises decodedQueries decodedTemplate decodedBindings)
  | .apply "mm-inst" [template, bindings, kont] => do
      let decodedTemplate ← decodeTemplate? template
      let decodedBindings ← decodeBindings? bindings
      let decodedKont ← decodeInstantiateKont? kont
      some (.instantiate decodedTemplate decodedBindings decodedKont)
  | .apply "mm-instargs" [constructor, accumulated, remaining, bindings, kont] => do
      let head ← decodeName? constructor
      let decodedAccumulated ← decodeCursor? accumulated
      let decodedRemaining ← decodeTemplates? remaining
      let decodedBindings ← decodeBindings? bindings
      let decodedKont ← decodeInstantiateKont? kont
      some (.instantiateArguments head decodedAccumulated decodedRemaining decodedBindings
        decodedKont)
  | .apply "mm-iret" [value, bindings, kont] => do
      let decodedBindings ← decodeBindings? bindings
      let decodedKont ← decodeInstantiateKont? kont
      some (.instantiated value decodedBindings decodedKont)
  | .apply "mm-done" [result] => some (.done result)
  | _ => none

@[simp] theorem decodeState?_encodeState : ∀ state : MachineState,
    decodeState? (encodeState state) = some state
  | .run program subject cursor => by simp [encodeState, decodeState?]
  | .dispatch branches subject focused cursor => by simp [encodeState, decodeState?]
  | .prefilter patterns cursor leaf subject => by simp [encodeState, decodeState?]
  | .bdRun decision subject kont => by simp [encodeState, decodeState?]
  | .bdRet bindings subject kont => by simp [encodeState, decodeState?]
  | .bdDone bindings => by simp [encodeState, decodeState?]
  | .premises queries template bindings => by simp [encodeState, decodeState?]
  | .instantiate template bindings kont => by simp [encodeState, decodeState?]
  | .instantiateArguments constructor accumulated remaining bindings kont => by
      simp [encodeState, decodeState?, encodeName, decodeName?]
  | .instantiated value bindings kont => by simp [encodeState, decodeState?]
  | .done result => by simp [encodeState, decodeState?]

theorem encodeState_injective : Function.Injective encodeState := by
  intro left right equal
  have := congrArg decodeState? equal
  simpa using this

variable (relations : RelationEnv) (source : LanguageDef)

/-! ## Rule applications that cannot match -/

/-- A rule whose left-hand side has a different head never applies. -/
private theorem applyRule_head_mismatch (rule : RewriteRule) (ruleHead : String)
    (ruleArguments : List Pattern) (ruleLeft : rule.left = .apply ruleHead ruleArguments)
    (head : String) (arguments : List Pattern) (distinct : head ≠ ruleHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head arguments) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, Ne.symm distinct]

/-- A rule whose first argument constructor differs never applies. -/
private theorem applyRule_first_mismatch (rule : RewriteRule) (head ruleFirstHead : String)
    (ruleFirstArguments ruleRest : List Pattern)
    (ruleLeft : rule.left = .apply head (.apply ruleFirstHead ruleFirstArguments :: ruleRest))
    (firstHead : String) (firstArguments rest : List Pattern) (distinct : firstHead ≠ ruleFirstHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head (.apply firstHead firstArguments :: rest)) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    Ne.symm distinct]

/-- A rule whose first argument's own first constructor differs never applies. -/
private theorem applyRule_first_nested_mismatch (rule : RewriteRule)
    (head firstHead ruleInnerHead : String) (ruleInnerArguments ruleInnerRest ruleRest : List Pattern)
    (ruleLeft : rule.left =
      .apply head (.apply firstHead (.apply ruleInnerHead ruleInnerArguments :: ruleInnerRest) :: ruleRest))
    (innerHead : String) (innerArguments innerRest rest : List Pattern)
    (distinct : innerHead ≠ ruleInnerHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head (.apply firstHead (.apply innerHead innerArguments :: innerRest) :: rest)) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-- A rule whose second argument constructor differs never applies. -/
private theorem applyRule_second_mismatch (rule : RewriteRule) (head : String) (ruleFirst : Pattern)
    (ruleSecondHead : String) (ruleSecondArguments ruleRest : List Pattern)
    (ruleLeft : rule.left = .apply head (ruleFirst :: .apply ruleSecondHead ruleSecondArguments :: ruleRest))
    (first : Pattern) (secondHead : String) (secondArguments rest : List Pattern)
    (distinct : secondHead ≠ ruleSecondHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head (first :: .apply secondHead secondArguments :: rest)) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-- A rule whose third argument constructor differs never applies. -/
private theorem applyRule_third_mismatch (rule : RewriteRule) (head : String)
    (ruleFirst ruleSecond : Pattern) (ruleThirdHead : String) (ruleThirdArguments ruleRest : List Pattern)
    (ruleLeft : rule.left =
      .apply head (ruleFirst :: ruleSecond :: .apply ruleThirdHead ruleThirdArguments :: ruleRest))
    (first second : Pattern) (thirdHead : String) (thirdArguments rest : List Pattern)
    (distinct : thirdHead ≠ ruleThirdHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head (first :: second :: .apply thirdHead thirdArguments :: rest)) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-- A rule whose third argument's own first constructor differs never applies. -/
private theorem applyRule_third_nested_mismatch (rule : RewriteRule) (head : String)
    (ruleFirst ruleSecond : Pattern) (thirdHead ruleInnerHead : String)
    (ruleInnerArguments ruleInnerRest ruleRest : List Pattern)
    (ruleLeft : rule.left =
      .apply head (ruleFirst :: ruleSecond ::
        .apply thirdHead (.apply ruleInnerHead ruleInnerArguments :: ruleInnerRest) :: ruleRest))
    (first second : Pattern) (innerHead : String) (innerArguments innerRest rest : List Pattern)
    (distinct : innerHead ≠ ruleInnerHead) :
    applyRuleWithPremisesUsing (relationEnv relations source) language rule
      (.apply head (first :: second ::
        .apply thirdHead (.apply innerHead innerArguments :: innerRest) :: rest)) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-! ## The catalog on encoded arguments -/

private theorem tuples_keyIs (focused : Pattern) (key : Key) :
    (relationEnv relations source).tuples keyIsRelation [focused, encodeKey key] =
      if subjectKey focused = key then [[focused, encodeKey key]] else [] := by
  simp [relationEnv, rowWhen, encodeKey_injective.eq_iff]

private theorem tuples_keyNot (focused : Pattern) (key : Key) :
    (relationEnv relations source).tuples keyNotRelation [focused, encodeKey key] =
      if subjectKey focused = key then [] else [[focused, encodeKey key]] := by
  simp [relationEnv, keyNotRelation, keyIsRelation, rowWhen, encodeKey_injective.eq_iff]

private theorem tuples_unfold (focused : Pattern) (cursor : List Pattern) (name : String) :
    (relationEnv relations source).tuples unfoldRelation [focused, encodeCursor cursor, .fvar name] =
      [[focused, encodeCursor cursor, encodeCursor (subjectChildren focused ++ cursor)]] := by
  simp [relationEnv, unfoldRelation, keyIsRelation, keyNotRelation]

private theorem tuples_append (children patterns : List MatrixPattern) (name : String) :
    (relationEnv relations source).tuples appendRelation
        [encodePatterns children, encodePatterns patterns, .fvar name] =
      [[encodePatterns children, encodePatterns patterns, encodePatterns (children ++ patterns)]] := by
  simp [relationEnv, appendRelation, unfoldRelation, keyIsRelation, keyNotRelation]

private theorem tuples_sourceQuery (relation : String) (names : List String) (bindings : Bindings)
    (name : String) :
    (relationEnv relations source).tuples sourceQueryRelation
        [encodeName relation, encodeNames names, encodeBindings bindings, .fvar name] =
      (relationQueryStep relations source bindings relation (names.map Pattern.fvar)).map
        fun extended =>
          [encodeName relation, encodeNames names, encodeBindings bindings, encodeBindings extended] := by
  simp [relationEnv, sourceQueryRelation, appendRelation, unfoldRelation, keyIsRelation,
    keyNotRelation, encodeName, decodeName?]

private theorem tuples_lookup (bindings : Bindings) (variableName name : String) :
    (relationEnv relations source).tuples lookupRelation
        [encodeBindings bindings, encodeName variableName, .fvar name] =
      [[encodeBindings bindings, encodeName variableName, lookupOrVariable bindings variableName]] := by
  simp [relationEnv, lookupRelation, sourceQueryRelation, appendRelation, unfoldRelation,
    keyIsRelation, keyNotRelation, encodeName, decodeName?]

private theorem tuples_bvar (index : Nat) (name : String) :
    (relationEnv relations source).tuples bvarRelation [encodeNat index, .fvar name] =
      [[encodeNat index, .bvar index]] := by
  simp [relationEnv, bvarRelation, lookupRelation, sourceQueryRelation, appendRelation,
    unfoldRelation, keyIsRelation, keyNotRelation]

private theorem tuples_build (constructor : String) (accumulated : List Pattern) (name : String) :
    (relationEnv relations source).tuples buildRelation
        [encodeName constructor, encodeCursor accumulated, .fvar name] =
      [[encodeName constructor, encodeCursor accumulated, .apply constructor accumulated.reverse]] := by
  simp [relationEnv, buildRelation, bvarRelation, lookupRelation, sourceQueryRelation,
    appendRelation, unfoldRelation, keyIsRelation, keyNotRelation, encodeName, decodeName?]

private theorem tuples_project_some (path : AccessPath) (subject focused : Pattern) (name : String)
    (projection : path.project? subject = some focused) :
    (relationEnv relations source).tuples projectRelation [encodePath path, subject, .fvar name] =
      [[encodePath path, subject, focused]] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, projectRelation, buildRelation,
    bvarRelation, lookupRelation, sourceQueryRelation, appendRelation, unfoldRelation,
    keyIsRelation, keyNotRelation, projection]

private theorem tuples_project_none (path : AccessPath) (subject : Pattern) (name : String)
    (projection : path.project? subject = none) :
    (relationEnv relations source).tuples projectRelation [encodePath path, subject, .fvar name] =
      [] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, projectRelation, buildRelation,
    bvarRelation, lookupRelation, sourceQueryRelation, appendRelation, unfoldRelation,
    keyIsRelation, keyNotRelation, projection]

private theorem tuples_bound (focused : Pattern) (expected : Nat) :
    (relationEnv relations source).tuples boundRelation [focused, encodeNat expected] =
      rowWhen (isBoundAt focused expected) [focused, encodeNat expected] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, boundRelation, projectRelation,
    buildRelation, bvarRelation, lookupRelation, sourceQueryRelation, appendRelation,
    unfoldRelation, keyIsRelation, keyNotRelation]

private theorem tuples_constructor (focused : Pattern) (expected : String) (arity : Nat) :
    (relationEnv relations source).tuples constructorRelation
        [focused, encodeName expected, encodeNat arity] =
      rowWhen (isConstructorOf focused expected arity) [focused, encodeName expected, encodeNat arity] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, constructorRelation, boundRelation,
    projectRelation, buildRelation, bvarRelation, lookupRelation, sourceQueryRelation,
    appendRelation, unfoldRelation, keyIsRelation, keyNotRelation]

private theorem tuples_merge_some (headBindings tailBindings merged : Bindings) (name : String)
    (merge : mergeBindings headBindings tailBindings = some merged) :
    (relationEnv relations source).tuples mergeRelation
        [encodeBindings headBindings, encodeBindings tailBindings, .fvar name] =
      [[encodeBindings headBindings, encodeBindings tailBindings, encodeBindings merged]] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, mergeRelation, constructorRelation,
    boundRelation, projectRelation, buildRelation, bvarRelation, lookupRelation,
    sourceQueryRelation, appendRelation, unfoldRelation, keyIsRelation, keyNotRelation, merge]

private theorem tuples_merge_none (headBindings tailBindings : Bindings) (name : String)
    (merge : mergeBindings headBindings tailBindings = none) :
    (relationEnv relations source).tuples mergeRelation
        [encodeBindings headBindings, encodeBindings tailBindings, .fvar name] = [] := by
  simp [relationEnv, BindingDecisionLanguage.relationEnv, mergeRelation, constructorRelation,
    boundRelation, projectRelation, buildRelation, bvarRelation, lookupRelation,
    sourceQueryRelation, appendRelation, unfoldRelation, keyIsRelation, keyNotRelation, merge]


private theorem map_flatMap_singleton {α β γ : Type} (F : β → γ) (G : α → β) (l : List α) :
    (l.flatMap fun a => [G a]).map F = l.map fun a => F (G a) := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-! ## Rule applications that match, one per authored rule -/

private theorem apply_succeed (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language succeedRewrite
        (encodeState (.bdRun .succeed subject kont)) =
      [encodeState (.bdRet [] subject kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, succeedRewrite, runPattern, retPattern, succeedPattern,
    nilBindingsPattern, metavariable, encodeState, encodeDecision, encodeBindings,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_capture (path : AccessPath) (name : String) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language captureRewrite
        (encodeState (.bdRun (.capture path name) subject kont)) =
      match path.project? subject with
      | some focused => [encodeState (.bdRet [(name, focused)] subject kont)]
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, captureRewrite, runPattern, retPattern,
        capturePattern, nilBindingsPattern, bindPattern, metavariable, encodeState,
        encodeDecision, matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        tuples_project_none relations source path subject _ projection]
  | some focused =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, captureRewrite, runPattern, retPattern,
        capturePattern, nilBindingsPattern, bindPattern, metavariable, encodeState,
        encodeDecision, encodeBindings, matchPatternForRule, matchPatternForRuleUsing,
        applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs,
        mergeBindings, applyBindings, matchRelationArgs, matchRelationArgument,
        Bindings.lookup,
        tuples_project_some relations source path subject focused _ projection]

private theorem apply_checkBound (path : AccessPath) (expected : Nat) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language checkBoundRewrite
        (encodeState (.bdRun (.checkBound path expected) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isBoundAt focused expected then [encodeState (.bdRet [] subject kont)] else []
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, checkBoundRewrite, runPattern, retPattern,
        checkBoundPattern, nilBindingsPattern, metavariable, encodeState, encodeDecision,
        matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        tuples_project_none relations source path subject _ projection]
  | some focused =>
      cases bound : isBoundAt focused expected <;>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, checkBoundRewrite, runPattern, retPattern,
        checkBoundPattern, nilBindingsPattern, metavariable, encodeState, encodeDecision,
        encodeBindings, matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        matchRelationArgs, matchRelationArgument, Bindings.lookup, rowWhen,
        tuples_project_some relations source path subject focused _ projection,
        tuples_bound relations source, bound]

private theorem apply_checkConstructor (path : AccessPath) (expected : String) (arity : Nat) (children : Decision)
    (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language checkConstructorRewrite
        (encodeState (.bdRun (.checkConstructor path expected arity children) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then [encodeState (.bdRun children subject kont)]
          else []
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, checkConstructorRewrite, runPattern,
        checkConstructorPattern, metavariable, encodeState, encodeDecision,
        matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        tuples_project_none relations source path subject _ projection]
  | some focused =>
      cases constructorTest : isConstructorOf focused expected arity <;>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, checkConstructorRewrite, runPattern,
        checkConstructorPattern, metavariable, encodeState, encodeDecision,
        matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        matchRelationArgs, matchRelationArgument, Bindings.lookup, rowWhen,
        tuples_project_some relations source path subject focused _ projection,
        tuples_constructor relations source, constructorTest]

private theorem apply_join (head tail : Decision) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language joinRewrite
        (encodeState (.bdRun (.join head tail) subject kont)) =
      [encodeState (.bdRun head subject (.joinRight tail :: kont))] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, joinRewrite, runPattern, joinPattern, joinRightPattern,
    kconsPattern, metavariable, encodeState, encodeKont, encodeFrame, encodeDecision,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_joinRight (bindings : Bindings) (tail : Decision) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language joinRightRewrite
        (encodeState (.bdRet bindings subject (.joinRight tail :: kont))) =
      [encodeState (.bdRun tail subject (.joinMerge bindings :: kont))] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, joinRightRewrite, runPattern, retPattern, joinRightPattern,
    joinMergePattern, kconsPattern, metavariable, encodeState, encodeKont, encodeFrame,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_joinMerge (tailBindings headBindings : Bindings) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language joinMergeRewrite
        (encodeState (.bdRet tailBindings subject (.joinMerge headBindings :: kont))) =
      match mergeBindings headBindings tailBindings with
      | some merged => [encodeState (.bdRet merged subject kont)]
      | none => [] := by
  cases merge : mergeBindings headBindings tailBindings with
  | none =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, joinMergeRewrite, retPattern,
        joinMergePattern, kconsPattern, metavariable, encodeState, encodeKont, encodeFrame,
        matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        tuples_merge_none relations source headBindings tailBindings _ merge]
  | some merged =>
      simp +decide [
        applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv,
        relationQueryStep, builtinRelationTuples, joinMergeRewrite, retPattern,
        joinMergePattern, kconsPattern, metavariable, encodeState, encodeKont, encodeFrame,
        matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
        matchRelationArgs, matchRelationArgument, Bindings.lookup,
        tuples_merge_some relations source headBindings tailBindings merged _ merge]

private theorem apply_finish (bindings : Bindings) (subject : Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language finishRewrite
        (encodeState (.bdRet bindings subject [])) =
      [encodeState (.bdDone bindings)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, finishRewrite, retPattern, donePattern, knilPattern, metavariable,
    encodeState, encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_drop (next : Program) (subject focused : Pattern) (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language dropRewrite
        (encodeState (.run (.drop next) subject (focused :: cursor))) =
      [encodeState (.run next subject cursor)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, dropRewrite, metavariable, mmRunPattern, dropPattern, cconsPattern,
    encodeState, encodeProgram, encodeCursor, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_tryLeaf (leaf : Leaf) (patterns : List MatrixPattern) (onFailure : Program) (subject : Pattern)
    (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language tryLeafRewrite
        (encodeState (.run (.tryRule leaf patterns onFailure) subject cursor)) =
      [encodeState (.prefilter patterns cursor leaf subject)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, tryLeafRewrite, metavariable, mmRunPattern, prefilterPattern,
    tryPattern, encodeState, encodeProgram, encodeLeaf, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings]

private theorem apply_tryNext (leaf : Leaf) (patterns : List MatrixPattern) (onFailure : Program) (subject : Pattern)
    (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language tryNextRewrite
        (encodeState (.run (.tryRule leaf patterns onFailure) subject cursor)) =
      [encodeState (.run onFailure subject cursor)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, tryNextRewrite, metavariable, mmRunPattern, tryPattern, encodeState,
    encodeProgram, encodeLeaf, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_switchDefault (branches : Branches) (default : Program) (subject : Pattern) (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language switchDefaultRewrite
        (encodeState (.run (.switch branches default) subject cursor)) =
      [encodeState (.run default subject cursor)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, switchDefaultRewrite, metavariable, mmRunPattern, switchPattern,
    encodeState, encodeProgram, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_switchDispatch (branches : Branches) (default : Program) (subject focused : Pattern)
    (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language switchDispatchRewrite
        (encodeState (.run (.switch branches default) subject (focused :: cursor))) =
      [encodeState (.dispatch branches subject focused cursor)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, switchDispatchRewrite, metavariable, mmRunPattern, dispatchPattern,
    switchPattern, cconsPattern, encodeState, encodeProgram, encodeCursor, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings]

private theorem apply_dispatchHit (key : Key) (program : Program) (rest : Branches) (subject focused : Pattern)
    (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language dispatchHitRewrite
        (encodeState (.dispatch (.cons key program rest) subject focused cursor)) =
      if subjectKey focused = key then
        [encodeState (.run program subject (subjectChildren focused ++ cursor))]
      else [] := by
  by_cases keyTest : subjectKey focused = key
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, dispatchHitRewrite, metavariable, mmRunPattern, dispatchPattern,
    bconsPattern, encodeState, encodeBranches, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_keyIs relations source focused key, tuples_unfold relations source focused cursor,
    keyTest]
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, dispatchHitRewrite, metavariable, mmRunPattern, dispatchPattern,
    bconsPattern, encodeState, encodeBranches, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_keyIs relations source focused key, keyTest]

private theorem apply_dispatchMiss (key : Key) (program : Program) (rest : Branches) (subject focused : Pattern)
    (cursor : List Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language dispatchMissRewrite
        (encodeState (.dispatch (.cons key program rest) subject focused cursor)) =
      if subjectKey focused = key then []
      else [encodeState (.dispatch rest subject focused cursor)] := by
  by_cases keyTest : subjectKey focused = key
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, dispatchMissRewrite, metavariable, dispatchPattern, bconsPattern,
    encodeState, encodeBranches, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_keyNot relations source focused key, keyTest]
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, dispatchMissRewrite, metavariable, dispatchPattern, bconsPattern,
    encodeState, encodeBranches, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_keyNot relations source focused key, keyTest]

private theorem apply_prefilterDone (leaf : Leaf) (subject : Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language prefilterDoneRewrite
        (encodeState (.prefilter [] [] leaf subject)) =
      [encodeState (.bdRun leaf.plan.decision subject [.afterMatch leaf.plan.premises leaf.plan.template])] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, prefilterDoneRewrite, runPattern, knilPattern, kconsPattern,
    metavariable, prefilterPattern, cnilPattern, pnilPattern, planPattern, afterPattern,
    encodeState, encodeLeaf, encodePatterns, encodeCursor, encodeKont, encodeFrame,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_prefilterWild (patterns : List MatrixPattern) (focused : Pattern) (cursor : List Pattern) (leaf : Leaf)
    (subject : Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language prefilterWildRewrite
        (encodeState (.prefilter (.wildcard :: patterns) (focused :: cursor) leaf subject)) =
      [encodeState (.prefilter patterns cursor leaf subject)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, prefilterWildRewrite, metavariable, prefilterPattern, cconsPattern,
    pconsPattern, wildPattern, encodeState, encodeLeaf, encodePatterns, encodeMatrixPattern,
    encodeCursor, matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_prefilterNode (head : Head) (children patterns : List MatrixPattern) (focused : Pattern)
    (cursor : List Pattern) (leaf : Leaf) (subject : Pattern) :
    applyRuleWithPremisesUsing (relationEnv relations source) language prefilterNodeRewrite
        (encodeState (.prefilter (.node head children :: patterns) (focused :: cursor) leaf subject)) =
      if subjectKey focused = ⟨head, children.length⟩ then
        [encodeState (.prefilter (children ++ patterns) (subjectChildren focused ++ cursor) leaf subject)]
      else [] := by
  by_cases keyTest : subjectKey focused = (⟨head, children.length⟩ : Key)
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, prefilterNodeRewrite, metavariable, prefilterPattern, cconsPattern,
    pconsPattern, nodePattern, encodeState, encodeLeaf, encodePatterns, encodeMatrixPattern,
    encodeCursor, matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
    matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_keyIs relations source focused ⟨head, children.length⟩,
    tuples_append relations source children patterns,
    tuples_unfold relations source focused cursor, keyTest]
  · simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, prefilterNodeRewrite, metavariable, prefilterPattern, cconsPattern,
    pconsPattern, nodePattern, encodeState, encodeLeaf, encodePatterns, encodeMatrixPattern,
    encodeCursor, matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings,
    tuples_keyIs relations source focused ⟨head, children.length⟩, keyTest]

private theorem apply_afterMatch (bindings : Bindings) (subject : Pattern) (premises : List PremisePlan) (template : PatternPlan)
    (kont : List Frame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language afterMatchRewrite
        (encodeState (.bdRet bindings subject (.afterMatch premises template :: kont))) =
      [encodeState (.premises premises template bindings)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, afterMatchRewrite, retPattern, kconsPattern, metavariable,
    premisesPattern, afterPattern, encodeState, encodeKont, encodeFrame, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings]

private theorem apply_premise (query : PremisePlan) (queries : List PremisePlan) (template : PatternPlan) (bindings : Bindings) :
    applyRuleWithPremisesUsing (relationEnv relations source) language premiseRewrite
        (encodeState (.premises (query :: queries) template bindings)) =
      (PremisePlan.run relations source bindings query).map fun extended =>
        encodeState (.premises queries template extended) := by
  have key := tuples_sourceQuery relations source query.relation query.arguments bindings "extended"
  unfold PremisePlan.run
  generalize relationQueryStep relations source bindings query.relation
    (query.arguments.map Pattern.fvar) = results at key ⊢
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, premiseRewrite, metavariable, premisesPattern, qconsPattern,
    queryPattern, encodeState, encodeQueries, encodeQuery, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings, matchRelationArgs, matchRelationArgument,
    Bindings.lookup, key, map_flatMap_singleton, List.flatMap_map]

private theorem apply_premisesDone (template : PatternPlan) (bindings : Bindings) :
    applyRuleWithPremisesUsing (relationEnv relations source) language premisesDoneRewrite
        (encodeState (.premises [] template bindings)) =
      [encodeState (.instantiate template bindings [])] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, premisesDoneRewrite, metavariable, premisesPattern, instPattern,
    qnilPattern, inilPattern, encodeState, encodeInstantiateKont, encodeQueries,
    matchPatternForRule, matchPatternForRuleUsing, applyBindingsForRule,
    applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings, applyBindings]

private theorem apply_instVar (name : String) (bindings : Bindings) (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language instVarRewrite
        (encodeState (.instantiate (.metavariable name) bindings kont)) =
      [encodeState (.instantiated (lookupOrVariable bindings name) bindings kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, instVarRewrite, metavariable, instPattern, iretPattern, tvarPattern,
    encodeState, encodeTemplate, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_lookup relations source bindings name]

private theorem apply_instBvar (index : Nat) (bindings : Bindings) (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language instBvarRewrite
        (encodeState (.instantiate (.bound index) bindings kont)) =
      [encodeState (.instantiated (.bvar index) bindings kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, instBvarRewrite, metavariable, instPattern, iretPattern,
    tbvarPattern, encodeState, encodeTemplate, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_bvar relations source index]

private theorem apply_instApp (constructor : String) (arguments : List PatternPlan) (bindings : Bindings)
    (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language instAppRewrite
        (encodeState (.instantiate (.application constructor arguments) bindings kont)) =
      [encodeState (.instantiateArguments constructor [] arguments bindings kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, instAppRewrite, metavariable, instPattern, instargsPattern,
    cnilPattern, tappPattern, encodeState, encodeCursor, encodeTemplate, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings]

private theorem apply_instargsDone (constructor : String) (accumulated : List Pattern) (bindings : Bindings)
    (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language instargsDoneRewrite
        (encodeState (.instantiateArguments constructor accumulated [] bindings kont)) =
      [encodeState (.instantiated (.apply constructor accumulated.reverse) bindings kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, instargsDoneRewrite, metavariable, instargsPattern, iretPattern,
    tnilPattern, encodeState, encodeTemplates, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup,
    tuples_build relations source constructor accumulated]

private theorem apply_instargsNext (constructor : String) (accumulated : List Pattern) (template : PatternPlan)
    (templates : List PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language instargsNextRewrite
        (encodeState (.instantiateArguments constructor accumulated (template :: templates) bindings kont)) =
      [encodeState (.instantiate template bindings (.argument constructor accumulated templates :: kont))] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, instargsNextRewrite, metavariable, instPattern, instargsPattern,
    tconsPattern, iconsPattern, argPattern, encodeState, encodeInstantiateKont,
    encodeInstantiateFrame, encodeTemplates, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_iretArg (value : Pattern) (bindings : Bindings) (constructor : String) (accumulated : List Pattern)
    (templates : List PatternPlan) (kont : List InstantiateFrame) :
    applyRuleWithPremisesUsing (relationEnv relations source) language iretArgRewrite
        (encodeState (.instantiated value bindings (.argument constructor accumulated templates :: kont))) =
      [encodeState (.instantiateArguments constructor (value :: accumulated) templates bindings kont)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, iretArgRewrite, metavariable, instargsPattern, iretPattern,
    cconsPattern, iconsPattern, argPattern, encodeState, encodeCursor, encodeInstantiateKont,
    encodeInstantiateFrame, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_iretDone (value : Pattern) (bindings : Bindings) :
    applyRuleWithPremisesUsing (relationEnv relations source) language iretDoneRewrite
        (encodeState (.instantiated value bindings [])) =
      [encodeState (.done value)] := by
  simp +decide [
    applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, iretDoneRewrite, metavariable, iretPattern, mmDonePattern,
    inilPattern, encodeState, encodeInstantiateKont, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, matchPattern,
    matchArgs, mergeBindings, applyBindings]

/-! ## Executor equations, one per state family -/

private theorem executor_eq (state : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language state =
      applyRuleWithPremisesUsing (relationEnv relations source) language succeedRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language captureRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language checkBoundRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language checkConstructorRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language joinRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language joinRightRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language joinMergeRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language finishRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language dropRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language tryLeafRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language tryNextRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language switchDefaultRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language switchDispatchRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language dispatchHitRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language dispatchMissRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language prefilterDoneRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language prefilterWildRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language prefilterNodeRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language afterMatchRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language premiseRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language premisesDoneRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language instVarRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language instBvarRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language instAppRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language instargsDoneRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language instargsNextRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language iretArgRewrite state ++
      (applyRuleWithPremisesUsing (relationEnv relations source) language iretDoneRewrite state))))))))))))))))))))))))))) := by
  simp [rewriteStepWithPremisesUsing, language]

private theorem execute_run_failure (subject : Pattern) (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run .failure subject cursor)) =
      (machineStep relations source (.run .failure subject cursor)).map encodeState := by
  simp only [
    encodeState, encodeProgram, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source dropRewrite "mm-run" "mm-drop" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryLeafRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryNextRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDefaultRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDispatchRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_run_drop_nil (next : Program) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run (.drop next) subject [])) =
      (machineStep relations source (.run (.drop next) subject [])).map encodeState := by
  simp only [
    encodeState, encodeProgram, encodeCursor, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_third_mismatch relations source dropRewrite "mm-run" _ _ "mm-ccons" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_first_mismatch relations source tryLeafRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryNextRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDefaultRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDispatchRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_run_drop_cons (next : Program) (subject focused : Pattern) (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run (.drop next) subject (focused :: cursor))) =
      (machineStep relations source (.run (.drop next) subject (focused :: cursor))).map encodeState := by
  have matched_drop := apply_drop relations source next subject focused cursor
  simp only [
    encodeState, encodeProgram, encodeCursor, machineStep, List.map] at matched_drop ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    matched_drop,
    applyRule_first_mismatch relations source tryLeafRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryNextRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDefaultRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDispatchRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_run_try (leaf : Leaf) (patterns : List MatrixPattern) (onFailure : Program) (subject : Pattern)
    (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run (.tryRule leaf patterns onFailure) subject cursor)) =
      (machineStep relations source (.run (.tryRule leaf patterns onFailure) subject cursor)).map encodeState := by
  have matched_tryLeaf := apply_tryLeaf relations source leaf patterns onFailure subject cursor
  have matched_tryNext := apply_tryNext relations source leaf patterns onFailure subject cursor
  simp only [
    encodeState, encodeProgram, encodeLeaf, machineStep, List.map] at matched_tryLeaf matched_tryNext ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source dropRewrite "mm-run" "mm-drop" _ _ rfl _ _ _ (by decide),
    matched_tryLeaf,
    matched_tryNext,
    applyRule_first_mismatch relations source switchDefaultRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source switchDispatchRewrite "mm-run" "mm-switch" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_run_switch_nil (branches : Branches) (default : Program) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run (.switch branches default) subject [])) =
      (machineStep relations source (.run (.switch branches default) subject [])).map encodeState := by
  have matched_switchDefault := apply_switchDefault relations source branches default subject []
  simp only [
    encodeState, encodeProgram, encodeCursor, machineStep, List.map] at matched_switchDefault ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source dropRewrite "mm-run" "mm-drop" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryLeafRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryNextRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    matched_switchDefault,
    applyRule_third_mismatch relations source switchDispatchRewrite "mm-run" _ _ "mm-ccons" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_run_switch_cons (branches : Branches) (default : Program) (subject focused : Pattern)
    (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.run (.switch branches default) subject (focused :: cursor))) =
      (machineStep relations source (.run (.switch branches default) subject (focused :: cursor))).map encodeState := by
  have matched_switchDefault := apply_switchDefault relations source branches default subject (focused :: cursor)
  have matched_switchDispatch := apply_switchDispatch relations source branches default subject focused cursor
  simp only [
    encodeState, encodeProgram, encodeCursor, machineStep, List.map] at matched_switchDefault matched_switchDispatch ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source dropRewrite "mm-run" "mm-drop" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryLeafRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source tryNextRewrite "mm-run" "mm-try" _ _ rfl _ _ _ (by decide),
    matched_switchDefault,
    matched_switchDispatch,
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_dispatch_nil (subject focused : Pattern) (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.dispatch .nil subject focused cursor)) =
      (machineStep relations source (.dispatch .nil subject focused cursor)).map encodeState := by
  simp only [
    encodeState, encodeBranches, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source dispatchHitRewrite "mm-dispatch" "mm-bcons" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source dispatchMissRewrite "mm-dispatch" "mm-bcons" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_dispatch_cons (key : Key) (program : Program) (rest : Branches) (subject focused : Pattern)
    (cursor : List Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.dispatch (.cons key program rest) subject focused cursor)) =
      (machineStep relations source (.dispatch (.cons key program rest) subject focused cursor)).map encodeState := by
  have matched_dispatchHit := apply_dispatchHit relations source key program rest subject focused cursor
  have matched_dispatchMiss := apply_dispatchMiss relations source key program rest subject focused cursor
  simp only [
    encodeState, encodeBranches, machineStep] at matched_dispatchHit matched_dispatchMiss ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    matched_dispatchHit,
    matched_dispatchMiss,
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  by_cases keyTest : subjectKey focused = key <;> simp [keyTest, encodeState]

private theorem execute_prefilter_nil_nil (leaf : Leaf) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.prefilter [] [] leaf subject)) =
      (machineStep relations source (.prefilter [] [] leaf subject)).map encodeState := by
  have matched_prefilterDone := apply_prefilterDone relations source leaf subject
  simp only [
    encodeState, encodeLeaf, encodePatterns, encodeCursor, encodeKont, encodeFrame,
    machineStep, List.map] at matched_prefilterDone ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    matched_prefilterDone,
    applyRule_first_mismatch relations source prefilterWildRewrite "mm-prefilter" "mm-pcons" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source prefilterNodeRewrite "mm-prefilter" "mm-pcons" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_prefilter_nil_cons (focused : Pattern) (cursor : List Pattern) (leaf : Leaf) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.prefilter [] (focused :: cursor) leaf subject)) =
      (machineStep relations source (.prefilter [] (focused :: cursor) leaf subject)).map encodeState := by
  simp only [
    encodeState, encodeLeaf, encodePatterns, encodeCursor, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_second_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ "mm-cnil" _ _ rfl _ _ _ _ (by decide),
    applyRule_first_mismatch relations source prefilterWildRewrite "mm-prefilter" "mm-pcons" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source prefilterNodeRewrite "mm-prefilter" "mm-pcons" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_prefilter_cons_nil (pattern : MatrixPattern) (patterns : List MatrixPattern) (leaf : Leaf) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.prefilter (pattern :: patterns) [] leaf subject)) =
      (machineStep relations source (.prefilter (pattern :: patterns) [] leaf subject)).map encodeState := by
  simp only [
    encodeState, encodeLeaf, encodePatterns, encodeCursor, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source prefilterDoneRewrite "mm-prefilter" "mm-pnil" _ _ rfl _ _ _ (by decide),
    applyRule_second_mismatch relations source prefilterWildRewrite "mm-prefilter" _ "mm-ccons" _ _ rfl _ _ _ _ (by decide),
    applyRule_second_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ "mm-ccons" _ _ rfl _ _ _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_prefilter_wild (patterns : List MatrixPattern) (focused : Pattern) (cursor : List Pattern) (leaf : Leaf)
    (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.prefilter (.wildcard :: patterns) (focused :: cursor) leaf subject)) =
      (machineStep relations source (.prefilter (.wildcard :: patterns) (focused :: cursor) leaf subject)).map encodeState := by
  have matched_prefilterWild := apply_prefilterWild relations source patterns focused cursor leaf subject
  simp only [
    encodeState, encodeLeaf, encodePatterns, encodeMatrixPattern, encodeCursor, machineStep,
    List.map] at matched_prefilterWild ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source prefilterDoneRewrite "mm-prefilter" "mm-pnil" _ _ rfl _ _ _ (by decide),
    matched_prefilterWild,
    applyRule_first_nested_mismatch relations source prefilterNodeRewrite "mm-prefilter" "mm-pcons" "mm-node" _ _ _ rfl _ _ _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_prefilter_node (head : Head) (children patterns : List MatrixPattern) (focused : Pattern)
    (cursor : List Pattern) (leaf : Leaf) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.prefilter (.node head children :: patterns) (focused :: cursor) leaf subject)) =
      (machineStep relations source (.prefilter (.node head children :: patterns) (focused :: cursor) leaf subject)).map encodeState := by
  have matched_prefilterNode := apply_prefilterNode relations source head children patterns focused cursor leaf subject
  simp only [
    encodeState, encodeLeaf, encodePatterns, encodeMatrixPattern, encodeCursor, machineStep] at matched_prefilterNode ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source prefilterDoneRewrite "mm-prefilter" "mm-pnil" _ _ rfl _ _ _ (by decide),
    applyRule_first_nested_mismatch relations source prefilterWildRewrite "mm-prefilter" "mm-pcons" "mm-wild" _ _ _ rfl _ _ _ _ (by decide),
    matched_prefilterNode,
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  by_cases keyTest : subjectKey focused = (⟨head, children.length⟩ : Key) <;> simp [
    keyTest, encodeState, encodeLeaf]

private theorem execute_bdRun_succeed (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRun .succeed subject kont)) =
      (machineStep relations source (.bdRun .succeed subject kont)).map encodeState := by
  have matched_succeed := apply_succeed relations source subject kont
  simp only [
    encodeState, encodeDecision, encodeBindings, machineStep, List.map] at matched_succeed ⊢
  rw [executor_eq relations source,
    matched_succeed,
    applyRule_first_mismatch relations source captureRewrite "bd-run" "bd-capture" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkBoundRewrite "bd-run" "bd-check-bound" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkConstructorRewrite "bd-run" "bd-check-constructor" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source joinRewrite "bd-run" "bd-join" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_bdRun_capture (path : AccessPath) (name : String) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRun (.capture path name) subject kont)) =
      (machineStep relations source (.bdRun (.capture path name) subject kont)).map encodeState := by
  have matched_capture := apply_capture relations source path name subject kont
  simp only [
    encodeState, encodeDecision, encodeBindings, machineStep] at matched_capture ⊢
  rw [executor_eq relations source,
    applyRule_first_mismatch relations source succeedRewrite "bd-run" "bd-succeed" _ _ rfl _ _ _ (by decide),
    matched_capture,
    applyRule_first_mismatch relations source checkBoundRewrite "bd-run" "bd-check-bound" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkConstructorRewrite "bd-run" "bd-check-constructor" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source joinRewrite "bd-run" "bd-join" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  cases projection : path.project? subject <;> simp [encodeState, encodeBindings]

private theorem execute_bdRun_checkBound (path : AccessPath) (expected : Nat) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRun (.checkBound path expected) subject kont)) =
      (machineStep relations source (.bdRun (.checkBound path expected) subject kont)).map encodeState := by
  have matched_checkBound := apply_checkBound relations source path expected subject kont
  simp only [
    encodeState, encodeDecision, encodeBindings, machineStep] at matched_checkBound ⊢
  rw [executor_eq relations source,
    applyRule_first_mismatch relations source succeedRewrite "bd-run" "bd-succeed" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source captureRewrite "bd-run" "bd-capture" _ _ rfl _ _ _ (by decide),
    matched_checkBound,
    applyRule_first_mismatch relations source checkConstructorRewrite "bd-run" "bd-check-constructor" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source joinRewrite "bd-run" "bd-join" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  cases projection : path.project? subject with
  | none => simp []
  | some focused =>
      cases bound : isBoundAt focused expected <;> simp [bound, encodeState, encodeBindings]

private theorem execute_bdRun_checkConstructor (path : AccessPath) (expected : String) (arity : Nat) (children : Decision)
    (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRun (.checkConstructor path expected arity children) subject kont)) =
      (machineStep relations source (.bdRun (.checkConstructor path expected arity children) subject kont)).map encodeState := by
  have matched_checkConstructor := apply_checkConstructor relations source path expected arity children subject kont
  simp only [
    encodeState, encodeDecision, machineStep] at matched_checkConstructor ⊢
  rw [executor_eq relations source,
    applyRule_first_mismatch relations source succeedRewrite "bd-run" "bd-succeed" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source captureRewrite "bd-run" "bd-capture" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkBoundRewrite "bd-run" "bd-check-bound" _ _ rfl _ _ _ (by decide),
    matched_checkConstructor,
    applyRule_first_mismatch relations source joinRewrite "bd-run" "bd-join" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  cases projection : path.project? subject with
  | none => simp []
  | some focused =>
      cases constructorTest : isConstructorOf focused expected arity <;>
        simp [constructorTest, encodeState]

private theorem execute_bdRun_join (head tail : Decision) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRun (.join head tail) subject kont)) =
      (machineStep relations source (.bdRun (.join head tail) subject kont)).map encodeState := by
  have matched_join := apply_join relations source head tail subject kont
  simp only [
    encodeState, encodeKont, encodeFrame, encodeDecision, machineStep, List.map] at matched_join ⊢
  rw [executor_eq relations source,
    applyRule_first_mismatch relations source succeedRewrite "bd-run" "bd-succeed" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source captureRewrite "bd-run" "bd-capture" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkBoundRewrite "bd-run" "bd-check-bound" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source checkConstructorRewrite "bd-run" "bd-check-constructor" _ _ rfl _ _ _ (by decide),
    matched_join,
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_bdRet_nil (bindings : Bindings) (subject : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRet bindings subject [])) =
      (machineStep relations source (.bdRet bindings subject [])).map encodeState := by
  have matched_finish := apply_finish relations source bindings subject
  simp only [
    encodeState, encodeKont, machineStep, List.map] at matched_finish ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_third_mismatch relations source joinRightRewrite "bd-ret" _ _ "bd-kcons" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_third_mismatch relations source joinMergeRewrite "bd-ret" _ _ "bd-kcons" _ _ rfl _ _ _ _ _ (by decide),
    matched_finish,
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_third_mismatch relations source afterMatchRewrite "bd-ret" _ _ "bd-kcons" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_bdRet_joinRight (bindings : Bindings) (tail : Decision) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRet bindings subject (.joinRight tail :: kont))) =
      (machineStep relations source (.bdRet bindings subject (.joinRight tail :: kont))).map encodeState := by
  have matched_joinRight := apply_joinRight relations source bindings tail subject kont
  simp only [
    encodeState, encodeKont, encodeFrame, machineStep, List.map] at matched_joinRight ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    matched_joinRight,
    applyRule_third_nested_mismatch relations source joinMergeRewrite "bd-ret" _ _ "bd-kcons" "bd-join-merge" _ _ _ rfl _ _ _ _ _ _ (by decide),
    applyRule_third_mismatch relations source finishRewrite "bd-ret" _ _ "bd-knil" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_third_nested_mismatch relations source afterMatchRewrite "bd-ret" _ _ "bd-kcons" "mm-after" _ _ _ rfl _ _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_bdRet_joinMerge (tailBindings headBindings : Bindings) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRet tailBindings subject (.joinMerge headBindings :: kont))) =
      (machineStep relations source (.bdRet tailBindings subject (.joinMerge headBindings :: kont))).map encodeState := by
  have matched_joinMerge := apply_joinMerge relations source tailBindings headBindings subject kont
  simp only [
    encodeState, encodeKont, encodeFrame, machineStep] at matched_joinMerge ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_third_nested_mismatch relations source joinRightRewrite "bd-ret" _ _ "bd-kcons" "bd-join-right" _ _ _ rfl _ _ _ _ _ _ (by decide),
    matched_joinMerge,
    applyRule_third_mismatch relations source finishRewrite "bd-ret" _ _ "bd-knil" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_third_nested_mismatch relations source afterMatchRewrite "bd-ret" _ _ "bd-kcons" "mm-after" _ _ _ rfl _ _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  cases merge : mergeBindings headBindings tailBindings <;> simp [encodeState]

private theorem execute_bdRet_afterMatch (bindings : Bindings) (subject : Pattern) (premises : List PremisePlan)
    (template : PatternPlan) (kont : List Frame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdRet bindings subject (.afterMatch premises template :: kont))) =
      (machineStep relations source (.bdRet bindings subject (.afterMatch premises template :: kont))).map encodeState := by
  have matched_afterMatch := apply_afterMatch relations source bindings subject premises template kont
  simp only [
    encodeState, encodeKont, encodeFrame, machineStep, List.map] at matched_afterMatch ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_third_nested_mismatch relations source joinRightRewrite "bd-ret" _ _ "bd-kcons" "bd-join-right" _ _ _ rfl _ _ _ _ _ _ (by decide),
    applyRule_third_nested_mismatch relations source joinMergeRewrite "bd-ret" _ _ "bd-kcons" "bd-join-merge" _ _ _ rfl _ _ _ _ _ _ (by decide),
    applyRule_third_mismatch relations source finishRewrite "bd-ret" _ _ "bd-knil" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    matched_afterMatch,
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_bdDone (bindings : Bindings) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.bdDone bindings)) =
      (machineStep relations source (.bdDone bindings)).map encodeState := by
  simp only [
    encodeState, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_premises_nil (template : PatternPlan) (bindings : Bindings) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.premises [] template bindings)) =
      (machineStep relations source (.premises [] template bindings)).map encodeState := by
  have matched_premisesDone := apply_premisesDone relations source template bindings
  simp only [
    encodeState, encodeInstantiateKont, encodeQueries, machineStep, List.map] at matched_premisesDone ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source premiseRewrite "mm-premises" "mm-qcons" _ _ rfl _ _ _ (by decide),
    matched_premisesDone,
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_premises_cons (query : PremisePlan) (queries : List PremisePlan) (template : PatternPlan)
    (bindings : Bindings) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.premises (query :: queries) template bindings)) =
      (machineStep relations source (.premises (query :: queries) template bindings)).map encodeState := by
  have matched_premise := apply_premise relations source query queries template bindings
  simp only [
    encodeState, encodeQueries, encodeQuery, machineStep] at matched_premise ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    matched_premise,
    applyRule_first_mismatch relations source premisesDoneRewrite "mm-premises" "mm-qnil" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  simp [List.map_map, Function.comp_def, encodeState]

private theorem execute_instantiate_var (name : String) (bindings : Bindings) (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiate (.metavariable name) bindings kont)) =
      (machineStep relations source (.instantiate (.metavariable name) bindings kont)).map encodeState := by
  have matched_instVar := apply_instVar relations source name bindings kont
  simp only [
    encodeState, encodeTemplate, machineStep, List.map] at matched_instVar ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    matched_instVar,
    applyRule_first_mismatch relations source instBvarRewrite "mm-inst" "mm-tbvar" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source instAppRewrite "mm-inst" "mm-tapp" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_instantiate_bvar (index : Nat) (bindings : Bindings) (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiate (.bound index) bindings kont)) =
      (machineStep relations source (.instantiate (.bound index) bindings kont)).map encodeState := by
  have matched_instBvar := apply_instBvar relations source index bindings kont
  simp only [
    encodeState, encodeTemplate, machineStep, List.map] at matched_instBvar ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source instVarRewrite "mm-inst" "mm-tvar" _ _ rfl _ _ _ (by decide),
    matched_instBvar,
    applyRule_first_mismatch relations source instAppRewrite "mm-inst" "mm-tapp" _ _ rfl _ _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_instantiate_app (constructor : String) (arguments : List PatternPlan) (bindings : Bindings)
    (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiate (.application constructor arguments) bindings kont)) =
      (machineStep relations source (.instantiate (.application constructor arguments) bindings kont)).map encodeState := by
  have matched_instApp := apply_instApp relations source constructor arguments bindings kont
  simp only [
    encodeState, encodeCursor, encodeTemplate, machineStep, List.map] at matched_instApp ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_first_mismatch relations source instVarRewrite "mm-inst" "mm-tvar" _ _ rfl _ _ _ (by decide),
    applyRule_first_mismatch relations source instBvarRewrite "mm-inst" "mm-tbvar" _ _ rfl _ _ _ (by decide),
    matched_instApp,
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_instantiateArguments_nil (constructor : String) (accumulated : List Pattern) (bindings : Bindings)
    (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiateArguments constructor accumulated [] bindings kont)) =
      (machineStep relations source (.instantiateArguments constructor accumulated [] bindings kont)).map encodeState := by
  have matched_instargsDone := apply_instargsDone relations source constructor accumulated bindings kont
  simp only [
    encodeState, encodeTemplates, machineStep, List.map] at matched_instargsDone ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    matched_instargsDone,
    applyRule_third_mismatch relations source instargsNextRewrite "mm-instargs" _ _ "mm-tcons" _ _ rfl _ _ _ _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_instantiateArguments_cons (constructor : String) (accumulated : List Pattern) (template : PatternPlan)
    (templates : List PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiateArguments constructor accumulated (template :: templates) bindings kont)) =
      (machineStep relations source (.instantiateArguments constructor accumulated (template :: templates) bindings kont)).map encodeState := by
  have matched_instargsNext := apply_instargsNext relations source constructor accumulated template templates bindings kont
  simp only [
    encodeState, encodeInstantiateKont, encodeInstantiateFrame, encodeTemplates, machineStep,
    List.map] at matched_instargsNext ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_third_mismatch relations source instargsDoneRewrite "mm-instargs" _ _ "mm-tnil" _ _ rfl _ _ _ _ _ (by decide),
    matched_instargsNext,
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl

private theorem execute_instantiated_arg (value : Pattern) (bindings : Bindings) (constructor : String)
    (accumulated : List Pattern) (templates : List PatternPlan) (kont : List InstantiateFrame) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiated value bindings (.argument constructor accumulated templates :: kont))) =
      (machineStep relations source (.instantiated value bindings (.argument constructor accumulated templates :: kont))).map encodeState := by
  have matched_iretArg := apply_iretArg relations source value bindings constructor accumulated templates kont
  simp only [
    encodeState, encodeCursor, encodeInstantiateKont, encodeInstantiateFrame, machineStep,
    List.map] at matched_iretArg ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    matched_iretArg,
    applyRule_third_mismatch relations source iretDoneRewrite "mm-iret" _ _ "mm-inil" _ _ rfl _ _ _ _ _ (by decide)]
  rfl

private theorem execute_instantiated_nil (value : Pattern) (bindings : Bindings) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.instantiated value bindings [])) =
      (machineStep relations source (.instantiated value bindings [])).map encodeState := by
  have matched_iretDone := apply_iretDone relations source value bindings
  simp only [
    encodeState, encodeInstantiateKont, machineStep, List.map] at matched_iretDone ⊢
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_third_mismatch relations source iretArgRewrite "mm-iret" _ _ "mm-icons" _ _ rfl _ _ _ _ _ (by decide),
    matched_iretDone]
  rfl

private theorem execute_done (result : Pattern) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language
        (encodeState (.done result)) =
      (machineStep relations source (.done result)).map encodeState := by
  simp only [
    encodeState, machineStep, List.map]
  rw [executor_eq relations source,
    applyRule_head_mismatch relations source succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source finishRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dropRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryLeafRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source tryNextRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDefaultRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source switchDispatchRewrite "mm-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchHitRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source dispatchMissRewrite "mm-dispatch" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterDoneRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterWildRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source prefilterNodeRewrite "mm-prefilter" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source afterMatchRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premiseRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source premisesDoneRewrite "mm-premises" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instVarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instBvarRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instAppRewrite "mm-inst" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsDoneRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source instargsNextRewrite "mm-instargs" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretArgRewrite "mm-iret" _ rfl _ _ (by decide),
    applyRule_head_mismatch relations source iretDoneRewrite "mm-iret" _ rfl _ _ (by decide)]
  rfl


/-! ## Exactness -/

/-- On every encoded state the executor is the encoded successor list. -/
theorem executor_eq_machineStep (state : MachineState) :
    rewriteStepWithPremisesUsing (relationEnv relations source) language (encodeState state) =
      (machineStep relations source state).map encodeState := by
  cases state with
  | run program subject cursor =>
      cases program with
      | failure => exact execute_run_failure relations source subject cursor
      | drop next =>
          cases cursor with
          | nil => exact execute_run_drop_nil relations source next subject
          | cons focused cursor => exact execute_run_drop_cons relations source next subject focused cursor
      | tryRule leaf patterns onFailure =>
          exact execute_run_try relations source leaf patterns onFailure subject cursor
      | switch branches default =>
          cases cursor with
          | nil => exact execute_run_switch_nil relations source branches default subject
          | cons focused cursor =>
              exact execute_run_switch_cons relations source branches default subject focused cursor
  | dispatch branches subject focused cursor =>
      cases branches with
      | nil => exact execute_dispatch_nil relations source subject focused cursor
      | cons key program rest =>
          exact execute_dispatch_cons relations source key program rest subject focused cursor
  | prefilter patterns cursor leaf subject =>
      cases patterns with
      | nil =>
          cases cursor with
          | nil => exact execute_prefilter_nil_nil relations source leaf subject
          | cons focused cursor => exact execute_prefilter_nil_cons relations source focused cursor leaf subject
      | cons pattern patterns =>
          cases cursor with
          | nil => exact execute_prefilter_cons_nil relations source pattern patterns leaf subject
          | cons focused cursor =>
              cases pattern with
              | wildcard => exact execute_prefilter_wild relations source patterns focused cursor leaf subject
              | node head children =>
                  exact execute_prefilter_node relations source head children patterns focused cursor
                    leaf subject
  | bdRun decision subject kont =>
      cases decision with
      | succeed => exact execute_bdRun_succeed relations source subject kont
      | capture path name => exact execute_bdRun_capture relations source path name subject kont
      | checkBound path expected => exact execute_bdRun_checkBound relations source path expected subject kont
      | checkConstructor path expected arity children =>
          exact execute_bdRun_checkConstructor relations source path expected arity children subject kont
      | join head tail => exact execute_bdRun_join relations source head tail subject kont
  | bdRet bindings subject kont =>
      cases kont with
      | nil => exact execute_bdRet_nil relations source bindings subject
      | cons frame rest =>
          cases frame with
          | joinRight tail => exact execute_bdRet_joinRight relations source bindings tail subject rest
          | joinMerge headBindings =>
              exact execute_bdRet_joinMerge relations source bindings headBindings subject rest
          | afterMatch premises template =>
              exact execute_bdRet_afterMatch relations source bindings subject premises template rest
  | bdDone bindings => exact execute_bdDone relations source bindings
  | premises queries template bindings =>
      cases queries with
      | nil => exact execute_premises_nil relations source template bindings
      | cons query queries => exact execute_premises_cons relations source query queries template bindings
  | instantiate template bindings kont =>
      cases template with
      | metavariable name => exact execute_instantiate_var relations source name bindings kont
      | bound index => exact execute_instantiate_bvar relations source index bindings kont
      | application constructor arguments =>
          exact execute_instantiate_app relations source constructor arguments bindings kont
  | instantiateArguments constructor accumulated remaining bindings kont =>
      cases remaining with
      | nil => exact execute_instantiateArguments_nil relations source constructor accumulated bindings kont
      | cons template templates =>
          exact execute_instantiateArguments_cons relations source constructor accumulated template
            templates bindings kont
  | instantiated value bindings kont =>
      cases kont with
      | nil => exact execute_instantiated_nil relations source value bindings
      | cons frame rest =>
          cases frame with
          | argument constructor accumulated templates =>
              exact execute_instantiated_arg relations source value bindings constructor accumulated
                templates rest
  | done result => exact execute_done relations source result

/-- On encoded states the language steps exactly as the reference machine. -/
theorem step_iff_machineStep (state : MachineState) (target : Pattern) :
    (ir relations source).semantics.Step (encodeState state) target ↔
      ∃ next ∈ machineStep relations source state, target = encodeState next := by
  rw [step_iff_mem_executor, executor_eq_machineStep, List.mem_map]
  constructor
  · rintro ⟨next, member, equal⟩
    exact ⟨next, member, equal.symm⟩
  · rintro ⟨next, member, equal⟩
    exact ⟨next, member, equal.symm⟩

/-- A machine step is a language step. -/
theorem step_of_machineStep {state next : MachineState}
    (step : next ∈ machineStep relations source state) :
    (ir relations source).semantics.Step (encodeState state) (encodeState next) :=
  (step_iff_machineStep relations source state (encodeState next)).mpr ⟨next, step, rfl⟩

/-- Encoded states only ever step to encoded states, and only by the machine. -/
theorem machineStep_of_step {state : MachineState} {target : Pattern}
    (step : (ir relations source).semantics.Step (encodeState state) target) :
    ∃ next ∈ machineStep relations source state, target = encodeState next :=
  (step_iff_machineStep relations source state target).mp step

/-! ## The host machine is a GSLT implementation, not another semantic IR -/

/-- The typed state machine implements the language-defined GSLT. -/
def machineImplementation : OperationalImplementation (ir relations source).semantics where
  State := MachineState
  encode := encodeState
  encode_injective := encodeState_injective
  step := fun state next => next ∈ machineStep relations source state
  sound := step_of_machineStep relations source
  complete := by
    intro state target step
    obtain ⟨next, machineStep, targetEqual⟩ := machineStep_of_step relations source step
    subst target
    exact ⟨next, machineStep, (ir relations source).semantics.equations.iseqv.refl _⟩

theorem languageStep_iff_machineImplementationStep (state : MachineState) (target : Pattern) :
    (ir relations source).semantics.Step (encodeState state) target ↔
      ∃ next : MachineState,
        (machineImplementation relations source).asGSLT.Step state next ∧
          (ir relations source).semantics.Equiv (encodeState next) target :=
  (machineImplementation relations source).semanticStep_iff_exists_implementationStep state target

#print axioms step_iff_machineStep
#print axioms encodeState_injective
#print axioms machineImplementation
#print axioms languageStep_iff_machineImplementationStep

end Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
