import Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage

/-!
# Exactness of the binding-decision language against its reference machine

Each state family of the binding-decision language has one executor
equation: the generic root executor applied to an encoded typed state is the
list of encoded successors that the typed reference machine produces.  The
families are the eight authored rules.  From these, the language's step
relation on encoded states is exactly the deterministic machine step, and
the encodings are injective, so the language never confuses two typed
states.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.Core.ConservativeExtension (encodeNat decodeNat? decodeNat?_encodeNat)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Decoders and injectivity -/

def decodeDecision? : Pattern → Option Decision
  | .apply "bd-succeed" [] => some .succeed
  | .apply "bd-capture" [path, name] => do
      let accessPath ← decodePath? path
      let boundName ← decodeName? name
      some (.capture accessPath boundName)
  | .apply "bd-check-bound" [path, index] => do
      let accessPath ← decodePath? path
      let expected ← decodeNat? index
      some (.checkBound accessPath expected)
  | .apply "bd-check-constructor" [path, head, arity, child] => do
      let accessPath ← decodePath? path
      let expected ← decodeName? head
      let count ← decodeNat? arity
      let children ← decodeDecision? child
      some (.checkConstructor accessPath expected count children)
  | .apply "bd-join" [head, tail] => do
      let headDecision ← decodeDecision? head
      let tailDecision ← decodeDecision? tail
      some (.join headDecision tailDecision)
  | _ => none

@[simp] theorem decodeDecision?_encodeDecision : ∀ decision : Decision,
    decodeDecision? (encodeDecision decision) = some decision
  | .succeed => rfl
  | .capture path name => by simp [encodeDecision, decodeDecision?]
  | .checkBound path expected => by simp [encodeDecision, decodeDecision?]
  | .checkConstructor path expected arity children => by
      simp [encodeDecision, decodeDecision?, decodeDecision?_encodeDecision children]
  | .join head tail => by
      simp [encodeDecision, decodeDecision?, decodeDecision?_encodeDecision head,
        decodeDecision?_encodeDecision tail]

theorem encodeDecision_injective : Function.Injective encodeDecision := by
  intro left right equal
  have := congrArg decodeDecision? equal
  simpa using this

def decodeFrame? : Pattern → Option Frame
  | .apply "bd-join-right" [tail] => (decodeDecision? tail).map .joinRight
  | .apply "bd-join-merge" [bindings] => (decodeBindings? bindings).map .joinMerge
  | _ => none

@[simp] theorem decodeFrame?_encodeFrame : ∀ frame : Frame,
    decodeFrame? (encodeFrame frame) = some frame
  | .joinRight tail => by simp [encodeFrame, decodeFrame?]
  | .joinMerge bindings => by simp [encodeFrame, decodeFrame?]

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

def decodeState? : Pattern → Option MachineState
  | .apply "bd-run" [decision, subject, kont] => do
      let typedDecision ← decodeDecision? decision
      let typedKont ← decodeKont? kont
      some (.run typedDecision subject typedKont)
  | .apply "bd-ret" [bindings, subject, kont] => do
      let typedBindings ← decodeBindings? bindings
      let typedKont ← decodeKont? kont
      some (.ret typedBindings subject typedKont)
  | .apply "bd-done" [bindings] => (decodeBindings? bindings).map .done
  | _ => none

@[simp] theorem decodeState?_encodeState : ∀ state : MachineState,
    decodeState? (encodeState state) = some state
  | .run decision subject kont => by simp [encodeState, decodeState?]
  | .ret bindings subject kont => by simp [encodeState, decodeState?]
  | .done bindings => by simp [encodeState, decodeState?]

theorem encodeState_injective : Function.Injective encodeState := by
  intro left right equal
  have := congrArg decodeState? equal
  simpa using this

/-! ## Rule applications that cannot match -/

/-- A rule whose left-hand side has a different head never applies. -/
private theorem applyRule_head_mismatch (rule : RewriteRule) (ruleHead : String)
    (ruleArguments : List Pattern) (ruleLeft : rule.left = .apply ruleHead ruleArguments)
    (head : String) (arguments : List Pattern) (distinct : head ≠ ruleHead) :
    applyRuleWithPremisesUsing relationEnv language rule (.apply head arguments) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, 
    Ne.symm distinct]

/-- A running rule whose decision constructor differs never applies to a running state. -/
private theorem applyRule_run_decision_mismatch (rule : RewriteRule) (ruleDecisionHead : String)
    (ruleDecisionArguments : List Pattern) (ruleSubject ruleKont : Pattern)
    (ruleLeft : rule.left =
      .apply "bd-run" [.apply ruleDecisionHead ruleDecisionArguments, ruleSubject, ruleKont])
    (decisionHead : String) (decisionArguments : List Pattern) (subject kont : Pattern)
    (distinct : decisionHead ≠ ruleDecisionHead) :
    applyRuleWithPremisesUsing relationEnv language rule
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    Ne.symm distinct]

/-- A returning rule whose continuation constructor differs never applies. -/
private theorem applyRule_ret_kont_mismatch (rule : RewriteRule) (ruleBindings ruleSubject : Pattern)
    (ruleKontHead : String) (ruleKontArguments : List Pattern)
    (ruleLeft : rule.left =
      .apply "bd-ret" [ruleBindings, ruleSubject, .apply ruleKontHead ruleKontArguments])
    (bindings subject : Pattern) (kontHead : String) (kontArguments : List Pattern)
    (distinct : kontHead ≠ ruleKontHead) :
    applyRuleWithPremisesUsing relationEnv language rule
      (.apply "bd-ret" [bindings, subject, .apply kontHead kontArguments]) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-- A returning rule whose top frame constructor differs never applies. -/
private theorem applyRule_ret_frame_mismatch (rule : RewriteRule) (ruleBindings ruleSubject : Pattern)
    (ruleFrameHead : String) (ruleFrameArguments : List Pattern) (ruleRest : Pattern)
    (ruleLeft : rule.left =
      .apply "bd-ret" [ruleBindings, ruleSubject,
        .apply "bd-kcons" [.apply ruleFrameHead ruleFrameArguments, ruleRest]])
    (bindings subject : Pattern) (frameHead : String) (frameArguments : List Pattern)
    (rest : Pattern) (distinct : frameHead ≠ ruleFrameHead) :
    applyRuleWithPremisesUsing relationEnv language rule
      (.apply "bd-ret" [bindings, subject,
        .apply "bd-kcons" [.apply frameHead frameArguments, rest]]) = [] := by
  simp [applyRuleWithPremisesUsing, matchPatternForRule, ruleLeft, matchPattern, matchArgs,
    mergeBindings, Ne.symm distinct]

/-! ## The catalog on encoded arguments -/

private theorem tuples_project_some (path : AccessPath) (subject focused : Pattern) (name : String)
    (projection : path.project? subject = some focused) :
    relationEnv.tuples projectRelation [encodePath path, subject, .fvar name] =
      [[encodePath path, subject, focused]] := by
  simp [relationEnv, projection]

private theorem tuples_project_none (path : AccessPath) (subject : Pattern) (name : String)
    (projection : path.project? subject = none) :
    relationEnv.tuples projectRelation [encodePath path, subject, .fvar name] = [] := by
  simp [relationEnv, projection]

private theorem tuples_bound (focused : Pattern) (expected : Nat) :
    relationEnv.tuples boundRelation [focused, encodeNat expected] =
      rowWhen (isBoundAt focused expected) [focused, encodeNat expected] := by
  simp [relationEnv, boundRelation, projectRelation]

private theorem tuples_constructor (focused : Pattern) (expected : String) (arity : Nat) :
    relationEnv.tuples constructorRelation [focused, encodeName expected, encodeNat arity] =
      rowWhen (isConstructorOf focused expected arity)
        [focused, encodeName expected, encodeNat arity] := by
  simp [relationEnv, constructorRelation, boundRelation, projectRelation]

private theorem tuples_merge_some (headBindings tailBindings merged : Bindings) (name : String)
    (merge : mergeBindings headBindings tailBindings = some merged) :
    relationEnv.tuples mergeRelation
        [encodeBindings headBindings, encodeBindings tailBindings, .fvar name] =
      [[encodeBindings headBindings, encodeBindings tailBindings, encodeBindings merged]] := by
  simp [relationEnv, mergeRelation, constructorRelation, boundRelation, projectRelation, merge]

private theorem tuples_merge_none (headBindings tailBindings : Bindings) (name : String)
    (merge : mergeBindings headBindings tailBindings = none) :
    relationEnv.tuples mergeRelation
        [encodeBindings headBindings, encodeBindings tailBindings, .fvar name] = [] := by
  simp [relationEnv, mergeRelation, constructorRelation, boundRelation, projectRelation, merge]

/-! ## Rule applications that match, one per authored rule -/

private theorem apply_succeed (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language succeedRewrite
        (encodeState (.run .succeed subject kont)) =
      [encodeState (.ret [] subject kont)] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, succeedRewrite, 
    
    runPattern, retPattern, succeedPattern, 
    nilBindingsPattern, 
    metavariable, encodeState, encodeDecision,
    encodeBindings, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_capture (path : AccessPath) (name : String) (subject : Pattern)
    (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language captureRewrite
        (encodeState (.run (.capture path name) subject kont)) =
      match path.project? subject with
      | some focused => [encodeState (.ret [(name, focused)] subject kont)]
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, captureRewrite, 
    
    runPattern, retPattern, capturePattern, 
    nilBindingsPattern, bindPattern, 
    metavariable, encodeState, encodeDecision,
    matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_project_none path subject _ projection]
  | some focused =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, captureRewrite, 
    
    runPattern, retPattern, capturePattern, 
    nilBindingsPattern, bindPattern, 
    metavariable, encodeState, encodeDecision,
    encodeBindings, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup, tuples_project_some path subject focused _ projection]

private theorem apply_checkBound (path : AccessPath) (expected : Nat) (subject : Pattern)
    (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language checkBoundRewrite
        (encodeState (.run (.checkBound path expected) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isBoundAt focused expected then [encodeState (.ret [] subject kont)] else []
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, checkBoundRewrite,
    
    runPattern, retPattern, checkBoundPattern,
    nilBindingsPattern, 
    metavariable, encodeState, encodeDecision,
    matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_project_none path subject _ projection]
  | some focused =>
      cases bound : isBoundAt focused expected <;>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, checkBoundRewrite,
    
    runPattern, retPattern, checkBoundPattern,
    nilBindingsPattern, 
    metavariable, encodeState, encodeDecision,
    encodeBindings, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup, tuples_project_some path subject focused _ projection, tuples_bound,
        rowWhen, bound]

private theorem apply_checkConstructor (path : AccessPath) (expected : String) (arity : Nat)
    (children : Decision) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language checkConstructorRewrite
        (encodeState (.run (.checkConstructor path expected arity children) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then [encodeState (.run children subject kont)]
          else []
      | none => [] := by
  cases projection : path.project? subject with
  | none =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    checkConstructorRewrite, 
    runPattern, 
    checkConstructorPattern, 
    metavariable, encodeState, encodeDecision,
    matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_project_none path subject _ projection]
  | some focused =>
      cases constructorTest : isConstructorOf focused expected arity <;>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    checkConstructorRewrite, 
    runPattern, 
    checkConstructorPattern, 
    metavariable, encodeState, encodeDecision,
    matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup, tuples_project_some path subject focused _ projection,
        tuples_constructor, rowWhen, constructorTest]

private theorem apply_join (head tail : Decision) (subject : Pattern) (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language joinRewrite
        (encodeState (.run (.join head tail) subject kont)) =
      [encodeState (.run head subject (.joinRight tail :: kont))] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    joinRewrite, 
    runPattern, 
    joinPattern, joinRightPattern,
    kconsPattern, metavariable, encodeState, encodeDecision,
    encodeFrame, encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_joinRight (bindings : Bindings) (tail : Decision) (subject : Pattern)
    (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language joinRightRewrite
        (encodeState (.ret bindings subject (.joinRight tail :: kont))) =
      [encodeState (.run tail subject (.joinMerge bindings :: kont))] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    joinRightRewrite, 
    runPattern, retPattern, 
    joinRightPattern,
    joinMergePattern, kconsPattern, metavariable, encodeState, 
    encodeFrame, encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

private theorem apply_joinMerge (tailBindings headBindings : Bindings) (subject : Pattern)
    (kont : List Frame) :
    applyRuleWithPremisesUsing relationEnv language joinMergeRewrite
        (encodeState (.ret tailBindings subject (.joinMerge headBindings :: kont))) =
      match mergeBindings headBindings tailBindings with
      | some merged => [encodeState (.ret merged subject kont)]
      | none => [] := by
  cases merge : mergeBindings headBindings tailBindings with
  | none =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    joinMergeRewrite, 
    retPattern, 
    
    joinMergePattern, kconsPattern, metavariable, encodeState, 
    encodeFrame, encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, tuples_merge_none headBindings tailBindings _ merge]
  | some merged =>
      simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    joinMergeRewrite, 
    retPattern, 
    
    joinMergePattern, kconsPattern, metavariable, encodeState, 
    encodeFrame, encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings, matchRelationArgs, matchRelationArgument, Bindings.lookup, tuples_merge_some headBindings tailBindings merged _ merge]

private theorem apply_finish (bindings : Bindings) (subject : Pattern) :
    applyRuleWithPremisesUsing relationEnv language finishRewrite
        (encodeState (.ret bindings subject [])) =
      [encodeState (.done bindings)] := by
  simp +decide [applyRuleWithPremisesUsing, applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, 
    finishRewrite,
    retPattern, donePattern, 
    
    knilPattern, metavariable, encodeState, 
    encodeKont, matchPatternForRule, matchPatternForRuleUsing,
    applyBindingsForRule, applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
    applyBindings]

/-! ## Executor equations, one per state family -/

private theorem executor_eq (source : Pattern) :
    rewriteStepWithPremisesUsing relationEnv language source =
      applyRuleWithPremisesUsing relationEnv language succeedRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language captureRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language checkBoundRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language checkConstructorRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language joinRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language joinRightRewrite source ++
      (applyRuleWithPremisesUsing relationEnv language joinMergeRewrite source ++
      applyRuleWithPremisesUsing relationEnv language finishRewrite source)))))) := by
  simp [rewriteStepWithPremisesUsing, language]

private theorem run_ret_rules_silent (decision subject kont : Pattern) :
    applyRuleWithPremisesUsing relationEnv language joinRightRewrite
        (.apply "bd-run" [decision, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language joinMergeRewrite
        (.apply "bd-run" [decision, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language finishRewrite
        (.apply "bd-run" [decision, subject, kont]) = [] :=
  ⟨applyRule_head_mismatch _ "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-ret" _ rfl _ _ (by decide)⟩

private theorem ret_run_rules_silent (bindings subject kont : Pattern) :
    applyRuleWithPremisesUsing relationEnv language succeedRewrite
        (.apply "bd-ret" [bindings, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language captureRewrite
        (.apply "bd-ret" [bindings, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language checkBoundRewrite
        (.apply "bd-ret" [bindings, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language checkConstructorRewrite
        (.apply "bd-ret" [bindings, subject, kont]) = [] ∧
      applyRuleWithPremisesUsing relationEnv language joinRewrite
        (.apply "bd-ret" [bindings, subject, kont]) = [] :=
  ⟨applyRule_head_mismatch _ "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch _ "bd-run" _ rfl _ _ (by decide)⟩

private theorem done_rules_silent (bindings : Pattern) :
    rewriteStepWithPremisesUsing relationEnv language (.apply "bd-done" [bindings]) = [] := by
  rw [executor_eq,
    applyRule_head_mismatch succeedRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch captureRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch checkBoundRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch checkConstructorRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch joinRewrite "bd-run" _ rfl _ _ (by decide),
    applyRule_head_mismatch joinRightRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch joinMergeRewrite "bd-ret" _ rfl _ _ (by decide),
    applyRule_head_mismatch finishRewrite "bd-ret" _ rfl _ _ (by decide)]
  rfl

/-- Assemble a running family: the three returning rules are silent, the four
other running rules mismatch on the decision constructor, and one rule
matches. -/
private theorem execute_run (decisionHead : String) (decisionArguments : List Pattern)
    (subject kont : Pattern) (result : List Pattern)
    (succeedCase : applyRuleWithPremisesUsing relationEnv language succeedRewrite
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
        if decisionHead = "bd-succeed" then result else [])
    (captureCase : applyRuleWithPremisesUsing relationEnv language captureRewrite
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
        if decisionHead = "bd-capture" then result else [])
    (checkBoundCase : applyRuleWithPremisesUsing relationEnv language checkBoundRewrite
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
        if decisionHead = "bd-check-bound" then result else [])
    (checkConstructorCase :
      applyRuleWithPremisesUsing relationEnv language checkConstructorRewrite
        (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
          if decisionHead = "bd-check-constructor" then result else [])
    (joinCase : applyRuleWithPremisesUsing relationEnv language joinRewrite
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
        if decisionHead = "bd-join" then result else [])
    (oneMatches : decisionHead = "bd-succeed" ∨ decisionHead = "bd-capture" ∨
      decisionHead = "bd-check-bound" ∨ decisionHead = "bd-check-constructor" ∨
      decisionHead = "bd-join") :
    rewriteStepWithPremisesUsing relationEnv language
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) = result := by
  rw [executor_eq, succeedCase, captureCase, checkBoundCase, checkConstructorCase, joinCase]
  have silent := run_ret_rules_silent (.apply decisionHead decisionArguments) subject kont
  rw [silent.1, silent.2.1, silent.2.2]
  rcases oneMatches with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The running mismatch cases, packaged for `execute_run`. -/
private theorem run_case_of_mismatch (rule : RewriteRule) (ruleDecisionHead : String)
    (ruleDecisionArguments : List Pattern) (ruleSubject ruleKont : Pattern)
    (ruleLeft : rule.left =
      .apply "bd-run" [.apply ruleDecisionHead ruleDecisionArguments, ruleSubject, ruleKont])
    (decisionHead : String) (decisionArguments : List Pattern) (subject kont : Pattern)
    (result : List Pattern) (distinct : decisionHead ≠ ruleDecisionHead) :
    applyRuleWithPremisesUsing relationEnv language rule
      (.apply "bd-run" [.apply decisionHead decisionArguments, subject, kont]) =
        if decisionHead = ruleDecisionHead then result else [] := by
  rw [if_neg distinct]
  exact applyRule_run_decision_mismatch rule ruleDecisionHead ruleDecisionArguments ruleSubject
    ruleKont ruleLeft decisionHead decisionArguments subject kont distinct

private theorem execute_run_succeed (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language (encodeState (.run .succeed subject kont)) =
      [encodeState (.ret [] subject kont)] := by
  have matched := apply_succeed subject kont
  simp only [encodeState, encodeDecision] at matched ⊢
  refine execute_run "bd-succeed" [] subject (encodeKont kont) _ ?_ ?_ ?_ ?_ ?_ (Or.inl rfl)
  · rw [if_pos rfl]; exact matched
  · exact run_case_of_mismatch captureRewrite "bd-capture" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkBoundRewrite "bd-check-bound" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkConstructorRewrite "bd-check-constructor" _ _ _ rfl _ _ _ _ _
      (by decide)
  · exact run_case_of_mismatch joinRewrite "bd-join" _ _ _ rfl _ _ _ _ _ (by decide)

private theorem execute_run_capture (path : AccessPath) (name : String) (subject : Pattern)
    (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.run (.capture path name) subject kont)) =
      match path.project? subject with
      | some focused => [encodeState (.ret [(name, focused)] subject kont)]
      | none => [] := by
  have matched := apply_capture path name subject kont
  simp only [encodeState, encodeDecision] at matched ⊢
  refine execute_run "bd-capture" _ subject (encodeKont kont) _ ?_ ?_ ?_ ?_ ?_
    (Or.inr (Or.inl rfl))
  · exact run_case_of_mismatch succeedRewrite "bd-succeed" _ _ _ rfl _ _ _ _ _ (by decide)
  · rw [if_pos rfl]; exact matched
  · exact run_case_of_mismatch checkBoundRewrite "bd-check-bound" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkConstructorRewrite "bd-check-constructor" _ _ _ rfl _ _ _ _ _
      (by decide)
  · exact run_case_of_mismatch joinRewrite "bd-join" _ _ _ rfl _ _ _ _ _ (by decide)

private theorem execute_run_checkBound (path : AccessPath) (expected : Nat) (subject : Pattern)
    (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.run (.checkBound path expected) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isBoundAt focused expected then [encodeState (.ret [] subject kont)] else []
      | none => [] := by
  have matched := apply_checkBound path expected subject kont
  simp only [encodeState, encodeDecision] at matched ⊢
  refine execute_run "bd-check-bound" _ subject (encodeKont kont) _ ?_ ?_ ?_ ?_ ?_
    (Or.inr (Or.inr (Or.inl rfl)))
  · exact run_case_of_mismatch succeedRewrite "bd-succeed" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch captureRewrite "bd-capture" _ _ _ rfl _ _ _ _ _ (by decide)
  · rw [if_pos rfl]; exact matched
  · exact run_case_of_mismatch checkConstructorRewrite "bd-check-constructor" _ _ _ rfl _ _ _ _ _
      (by decide)
  · exact run_case_of_mismatch joinRewrite "bd-join" _ _ _ rfl _ _ _ _ _ (by decide)

private theorem execute_run_checkConstructor (path : AccessPath) (expected : String) (arity : Nat)
    (children : Decision) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.run (.checkConstructor path expected arity children) subject kont)) =
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then [encodeState (.run children subject kont)]
          else []
      | none => [] := by
  have matched := apply_checkConstructor path expected arity children subject kont
  simp only [encodeState, encodeDecision] at matched ⊢
  refine execute_run "bd-check-constructor" _ subject (encodeKont kont) _ ?_ ?_ ?_ ?_ ?_
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact run_case_of_mismatch succeedRewrite "bd-succeed" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch captureRewrite "bd-capture" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkBoundRewrite "bd-check-bound" _ _ _ rfl _ _ _ _ _ (by decide)
  · rw [if_pos rfl]; exact matched
  · exact run_case_of_mismatch joinRewrite "bd-join" _ _ _ rfl _ _ _ _ _ (by decide)

private theorem execute_run_join (head tail : Decision) (subject : Pattern) (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.run (.join head tail) subject kont)) =
      [encodeState (.run head subject (.joinRight tail :: kont))] := by
  have matched := apply_join head tail subject kont
  simp only [encodeState, encodeDecision] at matched ⊢
  refine execute_run "bd-join" _ subject (encodeKont kont) _ ?_ ?_ ?_ ?_ ?_
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact run_case_of_mismatch succeedRewrite "bd-succeed" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch captureRewrite "bd-capture" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkBoundRewrite "bd-check-bound" _ _ _ rfl _ _ _ _ _ (by decide)
  · exact run_case_of_mismatch checkConstructorRewrite "bd-check-constructor" _ _ _ rfl _ _ _ _ _
      (by decide)
  · rw [if_pos rfl]; exact matched

/-- Assemble a returning family with an empty continuation. -/
private theorem execute_ret_finish (bindings : Bindings) (subject : Pattern) :
    rewriteStepWithPremisesUsing relationEnv language (encodeState (.ret bindings subject [])) =
      [encodeState (.done bindings)] := by
  have matched := apply_finish bindings subject
  simp only [encodeState, encodeKont] at matched ⊢
  rw [executor_eq]
  have silent := ret_run_rules_silent (encodeBindings bindings) subject (.apply "bd-knil" [])
  rw [silent.1, silent.2.1, silent.2.2.1, silent.2.2.2.1, silent.2.2.2.2,
    applyRule_ret_kont_mismatch joinRightRewrite _ _ "bd-kcons" _ rfl _ _ _ _ (by decide),
    applyRule_ret_kont_mismatch joinMergeRewrite _ _ "bd-kcons" _ rfl _ _ _ _ (by decide),
    matched]
  rfl

private theorem execute_ret_joinRight (bindings : Bindings) (tail : Decision) (subject : Pattern)
    (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.ret bindings subject (.joinRight tail :: kont))) =
      [encodeState (.run tail subject (.joinMerge bindings :: kont))] := by
  have matched := apply_joinRight bindings tail subject kont
  simp only [encodeState, encodeKont, encodeFrame] at matched ⊢
  rw [executor_eq]
  have silent := ret_run_rules_silent (encodeBindings bindings) subject
    (.apply "bd-kcons" [.apply "bd-join-right" [encodeDecision tail], encodeKont kont])
  rw [silent.1, silent.2.1, silent.2.2.1, silent.2.2.2.1, silent.2.2.2.2,
    applyRule_ret_frame_mismatch joinMergeRewrite _ _ "bd-join-merge" _ _ rfl _ _ _ _ _
      (by decide),
    applyRule_ret_kont_mismatch finishRewrite _ _ "bd-knil" _ rfl _ _ _ _ (by decide),
    matched]
  rfl

private theorem execute_ret_joinMerge (tailBindings headBindings : Bindings) (subject : Pattern)
    (kont : List Frame) :
    rewriteStepWithPremisesUsing relationEnv language
        (encodeState (.ret tailBindings subject (.joinMerge headBindings :: kont))) =
      match mergeBindings headBindings tailBindings with
      | some merged => [encodeState (.ret merged subject kont)]
      | none => [] := by
  have matched := apply_joinMerge tailBindings headBindings subject kont
  simp only [encodeState, encodeKont, encodeFrame] at matched ⊢
  rw [executor_eq]
  have silent := ret_run_rules_silent (encodeBindings tailBindings) subject
    (.apply "bd-kcons" [.apply "bd-join-merge" [encodeBindings headBindings], encodeKont kont])
  rw [silent.1, silent.2.1, silent.2.2.1, silent.2.2.2.1, silent.2.2.2.2,
    applyRule_ret_frame_mismatch joinRightRewrite _ _ "bd-join-right" _ _ rfl _ _ _ _ _
      (by decide),
    applyRule_ret_kont_mismatch finishRewrite _ _ "bd-knil" _ rfl _ _ _ _ (by decide),
    matched]
  cases mergeBindings headBindings tailBindings <;> rfl

private theorem execute_done (bindings : Bindings) :
    rewriteStepWithPremisesUsing relationEnv language (encodeState (.done bindings)) = [] :=
  done_rules_silent (encodeBindings bindings)

/-! ## Exactness -/

/-- On encoded states the language steps exactly as the reference machine. -/
theorem step_iff_machineStep (state : MachineState) (target : Pattern) :
    ir.semantics.Step (encodeState state) target ↔
      ∃ next, machineStep? state = some next ∧ target = encodeState next := by
  rw [step_iff_mem_executor]
  cases state with
  | run decision subject kont =>
      cases decision with
      | succeed => simp [execute_run_succeed, machineStep?]
      | capture path name =>
          rw [execute_run_capture]
          cases projection : path.project? subject <;> simp [machineStep?, projection]
      | checkBound path expected =>
          rw [execute_run_checkBound]
          cases projection : path.project? subject with
          | none => simp [machineStep?, projection]
          | some focused =>
              cases bound : isBoundAt focused expected <;> simp [machineStep?, projection, bound]
      | checkConstructor path expected arity children =>
          rw [execute_run_checkConstructor]
          cases projection : path.project? subject with
          | none => simp [machineStep?, projection]
          | some focused =>
              cases constructorTest : isConstructorOf focused expected arity <;>
                simp [machineStep?, projection, constructorTest]
      | join head tail => simp [execute_run_join, machineStep?]
  | ret bindings subject kont =>
      cases kont with
      | nil => simp [execute_ret_finish, machineStep?]
      | cons frame rest =>
          cases frame with
          | joinRight tail => simp [execute_ret_joinRight, machineStep?]
          | joinMerge headBindings =>
              rw [execute_ret_joinMerge]
              cases merged : mergeBindings headBindings bindings <;> simp [machineStep?, merged]
  | done bindings => simp [execute_done, machineStep?]

/-- A machine step is a language step. -/
theorem step_of_machineStep {state next : MachineState} (step : machineStep? state = some next) :
    ir.semantics.Step (encodeState state) (encodeState next) :=
  (step_iff_machineStep state (encodeState next)).mpr ⟨next, step, rfl⟩

/-- Encoded states only ever step to encoded states, and only by the machine. -/
theorem machineStep_of_step {state : MachineState} {target : Pattern}
    (step : ir.semantics.Step (encodeState state) target) :
    ∃ next, machineStep? state = some next ∧ target = encodeState next :=
  (step_iff_machineStep state target).mp step

#print axioms step_iff_machineStep
#print axioms encodeState_injective

end Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
