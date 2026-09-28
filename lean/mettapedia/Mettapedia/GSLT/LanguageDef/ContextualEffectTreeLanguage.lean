import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# An authored language for Boolean-state effect trees

The source is the existing finite-choice `Program`. A Boolean read is
compiled with both actual continuation branches. Answer and intent payloads
are opaque `Pattern` values: compilation neither evaluates nor substitutes
inside them. The target's request-to-completion rules recursively evaluate
the authored tree, preserving the complete ordered list of private worlds.

The external premise boundary performs only list concatenation and intent
prefixing. It never evaluates a program. There are no authored equations,
payload-reduction rules, or implicit collection congruences. Completion is a
macrostep whose finite contextual depth is made explicit by `depth`.
This is an operational backend, not a textual parser or a payload typechecker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

abbrev EffectProgram := Program Bool Pattern Pattern
abbrev EffectWorld := WorldResult Bool Pattern Pattern

def nilPattern : Pattern := .apply "effect-nil" []
def consPattern (head tail : Pattern) : Pattern := .apply "effect-cons" [head, tail]
def encodeBool (value : Bool) : Pattern :=
  .apply (if value then "effect-true" else "effect-false") []

def decodeBool? : Pattern → Option Bool
  | .apply "effect-false" [] => some false
  | .apply "effect-true" [] => some true
  | _ => none

@[simp] theorem decodeBool?_encodeBool (value : Bool) :
    decodeBool? (encodeBool value) = some value := by cases value <;> rfl

def encodeList : List Pattern → Pattern
  | [] => nilPattern
  | head :: tail => consPattern head (encodeList tail)

def decodeList? : Pattern → Option (List Pattern)
  | .apply "effect-nil" [] => some []
  | .apply "effect-cons" [head, tail] => (decodeList? tail).map (head :: ·)
  | _ => none

@[simp] theorem decodeList?_encodeList (values : List Pattern) :
    decodeList? (encodeList values) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [encodeList, consPattern, decodeList?, ih]

def encodeBranch (branch : BranchTrace) : Pattern := encodeList (branch.map encodeBool)

def decodeBranch? (encoded : Pattern) : Option BranchTrace := do
  let values ← decodeList? encoded
  values.mapM decodeBool?

@[simp] theorem decodeBranch?_encodeBranch (branch : BranchTrace) :
    decodeBranch? (encodeBranch branch) = some branch := by
  simp only [decodeBranch?, encodeBranch, decodeList?_encodeList]
  change (branch.map encodeBool).mapM decodeBool? = some branch
  induction branch with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons, decodeBool?_encodeBool, ih]
      rfl

def worldPattern (branch answer state intents : Pattern) : Pattern :=
  .apply "effect-world" [branch, answer, state, intents]

def encodeWorld (world : EffectWorld) : Pattern :=
  worldPattern (encodeBranch world.branch) world.answer
    (encodeBool world.state) (encodeList world.intents)

def decodeWorld? : Pattern → Option EffectWorld
  | .apply "effect-world" [branch, answer, state, intents] => do
      let decodedBranch ← decodeBranch? branch
      let decodedState ← decodeBool? state
      let decodedIntents ← decodeList? intents
      pure ⟨decodedBranch, answer, decodedState, decodedIntents⟩
  | _ => none

@[simp] theorem decodeWorld?_encodeWorld (world : EffectWorld) :
    decodeWorld? (encodeWorld world) = some world := by
  cases world
  simp [encodeWorld, worldPattern, decodeWorld?]

theorem encodeWorld_injective : Function.Injective encodeWorld := by
  intro left right equal
  simpa using congrArg decodeWorld? equal

def encodeWorlds (worlds : List EffectWorld) : Pattern := encodeList (worlds.map encodeWorld)

def decodeWorlds? (encoded : Pattern) : Option (List EffectWorld) := do
  let values ← decodeList? encoded
  values.mapM decodeWorld?

@[simp] theorem decodeWorlds?_encodeWorlds (worlds : List EffectWorld) :
    decodeWorlds? (encodeWorlds worlds) = some worlds := by
  simp only [decodeWorlds?, encodeWorlds, decodeList?_encodeList]
  change (worlds.map encodeWorld).mapM decodeWorld? = some worlds
  induction worlds with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons, decodeWorld?_encodeWorld, ih]
      rfl

theorem encodeWorlds_injective : Function.Injective encodeWorlds := by
  intro left right equal
  simpa using congrArg decodeWorlds? equal

def purePattern (answer : Pattern) : Pattern := .apply "effect-pure" [answer]
def choosePattern (left right : Pattern) : Pattern := .apply "effect-choose" [left, right]
def readPattern (onFalse onTrue : Pattern) : Pattern := .apply "effect-read" [onFalse, onTrue]
def writePattern (state next : Pattern) : Pattern := .apply "effect-write" [state, next]
def intentPattern (intent next : Pattern) : Pattern := .apply "effect-intent" [intent, next]

def encodeProgram : EffectProgram → Pattern
  | .pure answer => purePattern answer
  | .choose left right => choosePattern (encodeProgram left) (encodeProgram right)
  | .read next => readPattern (encodeProgram (next false)) (encodeProgram (next true))
  | .write state next => writePattern (encodeBool state) (encodeProgram next)
  | .intent intent next => intentPattern intent (encodeProgram next)

/-- An adequate bound on the authored recursive-premise depth. Both read
branches contribute to this state-independent bound. -/
def depth : EffectProgram → Nat
  | .pure _ => 1
  | .choose left right => max (depth left) (depth right) + 1
  | .read next => max (depth (next false)) (depth (next true)) + 1
  | .write _ next | .intent _ next => depth next + 1

theorem depth_positive (program : EffectProgram) : 0 < depth program := by
  cases program <;> simp [depth]

def runPattern (program state branch : Pattern) : Pattern :=
  .apply "effect-run" [program, state, branch]
def donePattern (worlds : Pattern) : Pattern := .apply "effect-done" [worlds]

def request (program : EffectProgram) (state : Bool) (branch : BranchTrace) : Pattern :=
  runPattern (encodeProgram program) (encodeBool state) (encodeBranch branch)

def completion (worlds : List EffectWorld) : Pattern := donePattern (encodeWorlds worlds)

theorem completion_injective : Function.Injective completion := by
  intro left right equal
  apply encodeWorlds_injective
  simpa [completion, donePattern] using equal

/-! ## Pure data operations at the premise boundary -/

def appendLists? (first second : Pattern) : Option Pattern := do
  let left ← decodeList? first
  let right ← decodeList? second
  pure (encodeList (left ++ right))

def prefixIntent (intent : Pattern) (world : EffectWorld) : EffectWorld :=
  { world with intents := intent :: world.intents }

def prefixIntents? (intent worlds : Pattern) : Option Pattern := do
  let decoded ← decodeWorlds? worlds
  pure (encodeWorlds (decoded.map (prefixIntent intent)))

@[simp] theorem appendLists?_encodeWorlds (first second : List EffectWorld) :
    appendLists? (encodeWorlds first) (encodeWorlds second) =
      some (encodeWorlds (first ++ second)) := by
  simp [appendLists?, encodeWorlds]

@[simp] theorem prefixIntents?_encodeWorlds (intent : Pattern) (worlds : List EffectWorld) :
    prefixIntents? intent (encodeWorlds worlds) =
      some (encodeWorlds (worlds.map (prefixIntent intent))) := by
  simp [prefixIntents?]

def appendRelation : String := "EffectTreeAppend"
def prefixRelation : String := "EffectTreePrefixIntent"

/-- Only structural list operations; no source evaluator is called here. -/
def relationEnv : RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | "EffectTreeAppend", [first, second, _] =>
        ((appendLists? first second).map fun result => [first, second, result]).toList
    | "EffectTreePrefixIntent", [intent, worlds, _] =>
        ((prefixIntents? intent worlds).map fun result => [intent, worlds, result]).toList
    | _, _ => []

/-! ## Authored constructor rules -/

def metavariable (name : String) : Pattern := .fvar name

private def dataType : TypeExpr := .base "EffectTreeData"

def rule (name : String) (names : List String)
    (premises : List Premise) (left right : Pattern) : RewriteRule :=
  { name
    typeContext := names.map (·, dataType)
    premises
    left
    right }

def pureRewrite : RewriteRule :=
  rule "effect-pure" ["answer", "state", "branch"] []
    (runPattern (purePattern (metavariable "answer"))
      (metavariable "state") (metavariable "branch"))
    (donePattern (consPattern
      (worldPattern (metavariable "branch") (metavariable "answer")
        (metavariable "state") nilPattern) nilPattern))

def chooseRewrite : RewriteRule :=
  rule "effect-choose" ["left", "right", "state", "branch", "xs", "ys", "zs"]
    [.congruence
       (runPattern (metavariable "left") (metavariable "state")
         (consPattern (encodeBool false) (metavariable "branch")))
       (donePattern (metavariable "xs")),
     .congruence
       (runPattern (metavariable "right") (metavariable "state")
         (consPattern (encodeBool true) (metavariable "branch")))
       (donePattern (metavariable "ys")),
     .relationQuery appendRelation
       [metavariable "xs", metavariable "ys", metavariable "zs"]]
    (runPattern (choosePattern (metavariable "left") (metavariable "right"))
      (metavariable "state") (metavariable "branch"))
    (donePattern (metavariable "zs"))

def readRewrite (state : Bool) : RewriteRule :=
  rule (if state then "effect-read-true" else "effect-read-false")
    ["left", "right", "branch", "worlds"]
    [.congruence
      (runPattern (metavariable (if state then "right" else "left"))
        (encodeBool state) (metavariable "branch"))
      (donePattern (metavariable "worlds"))]
    (runPattern (readPattern (metavariable "left") (metavariable "right"))
      (encodeBool state) (metavariable "branch"))
    (donePattern (metavariable "worlds"))

def writeRewrite : RewriteRule :=
  rule "effect-write" ["newState", "next", "state", "branch", "worlds"]
    [.congruence
      (runPattern (metavariable "next") (metavariable "newState") (metavariable "branch"))
      (donePattern (metavariable "worlds"))]
    (runPattern (writePattern (metavariable "newState") (metavariable "next"))
      (metavariable "state") (metavariable "branch"))
    (donePattern (metavariable "worlds"))

def intentRewrite : RewriteRule :=
  rule "effect-intent" ["intent", "next", "state", "branch", "worlds", "prefixed"]
    [.congruence
      (runPattern (metavariable "next") (metavariable "state") (metavariable "branch"))
      (donePattern (metavariable "worlds")),
     .relationQuery prefixRelation
       [metavariable "intent", metavariable "worlds", metavariable "prefixed"]]
    (runPattern (intentPattern (metavariable "intent") (metavariable "next"))
      (metavariable "state") (metavariable "branch"))
    (donePattern (metavariable "prefixed"))

private def constructor (label category : String) (parameters : List TypeExpr) : GrammarRule :=
  { label, category
    params := parameters.zipIdx |>.map fun entry => .simple s!"field{entry.2}" entry.1
    syntaxPattern := [] }

def language : LanguageDef where
  name := "contextual-effect-tree"
  types := [TypeDecl.plain "EffectTreeData", TypeDecl.plain "EffectTreeCommand"]
  terms :=
    [constructor "effect-nil" "EffectTreeData" [],
     constructor "effect-cons" "EffectTreeData" [dataType, dataType],
     constructor "effect-false" "EffectTreeData" [],
     constructor "effect-true" "EffectTreeData" [],
     constructor "effect-world" "EffectTreeData" [dataType, dataType, dataType, dataType],
     constructor "effect-pure" "EffectTreeData" [dataType],
     constructor "effect-choose" "EffectTreeData" [dataType, dataType],
     constructor "effect-read" "EffectTreeData" [dataType, dataType],
     constructor "effect-write" "EffectTreeData" [dataType, dataType],
     constructor "effect-intent" "EffectTreeData" [dataType, dataType],
     constructor "effect-run" "EffectTreeCommand" [dataType, dataType, dataType],
     constructor "effect-done" "EffectTreeCommand" [dataType]]
  equations := []
  rewrites := [pureRewrite, chooseRewrite, readRewrite false, readRewrite true,
    writeRewrite, intentRewrite]

local macro "validate_effect_tree_rule" : tactic =>
  `(tactic| (
    dsimp only [LanguageDef.validateRewrite, pureRewrite, chooseRewrite, readRewrite,
      writeRewrite, intentRewrite, rule]
    simp [language, runPattern, donePattern, purePattern, choosePattern, readPattern,
      writePattern, intentPattern, worldPattern, consPattern, nilPattern, encodeBool,
      metavariable, appendRelation, prefixRelation, constructor, dataType,
      LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.typeNames]
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    simp [TypeDecl.plain, TypeExpr.baseNames]))

private theorem pureRewrite_valid : language.validateRewrite pureRewrite = [] := by
  validate_effect_tree_rule

private theorem chooseRewrite_valid : language.validateRewrite chooseRewrite = [] := by
  validate_effect_tree_rule

private theorem readFalseRewrite_valid : language.validateRewrite (readRewrite false) = [] := by
  validate_effect_tree_rule

private theorem readTrueRewrite_valid : language.validateRewrite (readRewrite true) = [] := by
  validate_effect_tree_rule

private theorem writeRewrite_valid : language.validateRewrite writeRewrite = [] := by
  validate_effect_tree_rule

private theorem intentRewrite_valid : language.validateRewrite intentRewrite = [] := by
  validate_effect_tree_rule

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  intro rewrite member
  change rewrite ∈ [pureRewrite, chooseRewrite, readRewrite false, readRewrite true,
    writeRewrite, intentRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pureRewrite_valid
  · exact chooseRewrite_valid
  · exact readFalseRewrite_valid
  · exact readTrueRewrite_valid
  · exact writeRewrite_valid
  · exact intentRewrite_valid

theorem language_equation_free : language.isEquationFree = true := by decide

def execute (fuel : Nat) (term : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises relationEnv) language fuel term

/-- The semantic theory comes from the authored rules, not the source
evaluator's graph. -/
def theory : Mettapedia.GSLT.GSLT :=
  EquationSemantics.gsltModuloEquations (engineBasePremises relationEnv) language

end Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage
