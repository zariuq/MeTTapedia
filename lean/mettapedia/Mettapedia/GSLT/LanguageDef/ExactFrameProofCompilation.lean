import Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation
import Mettapedia.GSLT.LanguageDef.TwoPhaseFrameMachinePhysicalRefinement

/-!
# Exact-selection compilation for first-order proof machines

An exact generated selector and the generic two-phase frame compiler are
useful together only if their composition preserves a complete proof run.
This module supplies that whole-machine theorem.  Source rules either push a
known premise or apply an admitted first-order frame to the current stack
suffix.  Compilation replaces every admitted source frame with its physical
split-array program and lowers the duplicate-free rule table to one exact
lookup.

The result describes the direct native execution path: a successful compiled
fold has exactly the source fold's stack, including every failure.  No proof
article is replayed to establish this equality.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactFrameProofCompilation

open FirstOrderFrameCompilation
open TwoPhaseFrameMachinePhysicalRefinement

universe uKey uToken

abbrev Formula (Token : Type uToken) := List Token
abbrev Stack (Token : Type uToken) := List (Formula Token)

/-- Apply an exact-arity frame to the top suffix of a bottom-to-top stack. -/
def runAtSuffix (arity : Nat)
    (execute : List (Formula Token) -> Option (Formula Token))
    (stack : Stack Token) : Option (Stack Token) :=
  if arity <= stack.length then
    let base := stack.length - arity
    match execute (stack.drop base) with
    | none => none
    | some result => some (stack.take base ++ [result])
  else
    none

/-- Pointwise-equivalent frame interpreters remain equivalent when installed
at the proof-stack suffix boundary. -/
theorem runAtSuffix_congr
    (arity : Nat)
    (left right : List (Formula Token) -> Option (Formula Token))
    (same : forall inputs, left inputs = right inputs)
    (stack : Stack Token) :
    runAtSuffix arity left stack = runAtSuffix arity right stack := by
  unfold runAtSuffix
  split
  · simp only [same]
  · rfl

/-- A source proof action before physical frame lowering. -/
inductive SourceAction (Token : Type uToken) (width : Nat) where
  | push (formula : Formula Token)
  | apply (frame : AdmittedSource Token width)

/-- The physical action carrier used by the direct native machine. -/
inductive PhysicalAction (Token : Type uToken) (width : Nat) where
  | push (formula : Formula Token)
  | apply (frame : PhysicalFrame Token width)

/-- Lower one action without introducing guest-specific opcodes. -/
def compileAction : SourceAction Token width -> PhysicalAction Token width
  | .push formula => .push formula
  | .apply frame => .apply (compile frame.source)

def runSourceAction [DecidableEq Token]
    (apartCheck : ApartCheck Token) :
    SourceAction Token width -> Stack Token -> Option (Stack Token)
  | .push formula, stack => some (stack ++ [formula])
  | .apply frame, stack =>
      runAtSuffix frame.source.frame.instructions.length
        (runSource apartCheck frame.source) stack

def runPhysicalAction [DecidableEq Token]
    (apartCheck : ApartCheck Token) :
    PhysicalAction Token width -> Stack Token -> Option (Stack Token)
  | .push formula, stack => some (stack ++ [formula])
  | .apply frame, stack =>
      runAtSuffix frame.stackArity (runPhysical apartCheck frame) stack

/-- Per-action physical lowering preserves the complete stack transformer. -/
theorem runPhysicalAction_compileAction [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (action : SourceAction Token width) (stack : Stack Token) :
    runPhysicalAction apartCheck (compileAction action) stack =
      runSourceAction apartCheck action stack := by
  cases action with
  | push formula => rfl
  | apply frame =>
      apply runAtSuffix_congr
      intro inputs
      exact runPhysical_compile apartCheck frame.source inputs

/-- One keyed source action.  Exact compilation rejects duplicate keys. -/
structure SourceRule (Key : Type uKey) (Token : Type uToken)
    (width : Nat) where
  key : Key
  action : SourceAction Token width

/-- Physical rule stored in the exact selector table. -/
structure PhysicalRule (Key : Type uKey) (Token : Type uToken)
    (width : Nat) where
  key : Key
  action : PhysicalAction Token width

def compileRule (rule : SourceRule Key Token width) :
    PhysicalRule Key Token width :=
  { key := rule.key, action := compileAction rule.action }

def sourceKey? (rule : SourceRule Key Token width) : Option Key :=
  some rule.key

def physicalKey? (rule : PhysicalRule Key Token width) : Option Key :=
  some rule.key

/-- Compile every action and accept the complete table only when its keys are
exact selectors. -/
def compileProgram? [DecidableEq Key]
    (rules : List (SourceRule Key Token width)) :
    Option (ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width)) :=
  ExactRuleSelectorCompilation.compile? physicalKey?
    (rules.map compileRule)

/-- Compiling a rule inventory preserves the source candidate bag exactly. -/
theorem sourceCandidates_map_compileRule [DecidableEq Key]
    (rules : List (SourceRule Key Token width)) (query : Key) :
    (FiniteRuleIndexCompilation.sourceCandidates sourceKey? rules query).map
        compileRule =
      FiniteRuleIndexCompilation.sourceCandidates physicalKey?
        (rules.map compileRule) query := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      change
        (List.filter (fun candidate => candidate.key == query) rules).map
            compileRule =
          List.filter (fun candidate => candidate.key == query)
            (rules.map compileRule) at inductionHypothesis
      change
        (List.filter (fun candidate => candidate.key == query)
            (rule :: rules)).map compileRule =
          List.filter (fun candidate => candidate.key == query)
            (compileRule rule :: rules.map compileRule)
      rw [List.filter_cons, List.filter_cons]
      by_cases same : rule.key = query
      · simp [same, compileRule, inductionHypothesis]
      · simp [same, compileRule, inductionHypothesis]

def runSourceCandidates [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (query : Key) (stack : Stack Token) : List (Option (Stack Token)) :=
  (FiniteRuleIndexCompilation.sourceCandidates sourceKey? rules query).map
    fun rule => runSourceAction apartCheck rule.action stack

def runPhysicalCandidates [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (query : Key) (stack : Stack Token) : List (Option (Stack Token)) :=
  (ExactRuleSelectorCompilation.lookup query index).toList.map
    fun rule => runPhysicalAction apartCheck rule.action stack

/-- Exact lookup plus physical frame lowering preserves every selected source
result, including action rejection. -/
theorem runPhysicalCandidates_eq_runSourceCandidates_of_compileProgram?
    [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (accepted : compileProgram? rules = some index)
    (query : Key) (stack : Stack Token) :
    runPhysicalCandidates apartCheck index query stack =
      runSourceCandidates apartCheck rules query stack := by
  unfold compileProgram? at accepted
  unfold runPhysicalCandidates runSourceCandidates
  rw [<- ExactRuleSelectorCompilation.sourceCandidates_eq_lookup_toList_of_compile?
    physicalKey? (rules.map compileRule) index accepted query]
  rw [<- sourceCandidates_map_compileRule rules query]
  simp only [List.map_map]
  apply List.map_congr_left
  intro rule _member
  exact runPhysicalAction_compileAction apartCheck rule.action stack

/-- A proof step is accepted only when exact selection yields one successful
stack transformer.  Absence and ambiguity fail closed. -/
def selectOne : List (Option alpha) -> Option alpha
  | [some result] => some result
  | _ => none

def runSourceStep [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (query : Key) (stack : Stack Token) : Option (Stack Token) :=
  selectOne (runSourceCandidates apartCheck rules query stack)

def runPhysicalStep [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (query : Key) (stack : Stack Token) : Option (Stack Token) :=
  selectOne (runPhysicalCandidates apartCheck index query stack)

theorem runPhysicalStep_eq_runSourceStep_of_compileProgram?
    [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (accepted : compileProgram? rules = some index)
    (query : Key) (stack : Stack Token) :
    runPhysicalStep apartCheck index query stack =
      runSourceStep apartCheck rules query stack := by
  unfold runPhysicalStep runSourceStep
  rw [runPhysicalCandidates_eq_runSourceCandidates_of_compileProgram?
    apartCheck rules index accepted query stack]

def runSourceProofFrom [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (queries : List Key) (initial : Stack Token) : Option (Stack Token) :=
  queries.foldlM (fun stack query =>
    runSourceStep apartCheck rules query stack) initial

def runPhysicalProofFrom [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (queries : List Key) (initial : Stack Token) : Option (Stack Token) :=
  queries.foldlM (fun stack query =>
    runPhysicalStep apartCheck index query stack) initial

/-- Whole proof folds are identical after exact selection and physical frame
lowering.  This is the direct-execution theorem needed to avoid a second
article replay. -/
theorem runPhysicalProofFrom_eq_runSourceProofFrom_of_compileProgram?
    [DecidableEq Key] [DecidableEq Token]
    (apartCheck : ApartCheck Token)
    (rules : List (SourceRule Key Token width))
    (index : ExactRuleSelectorCompilation.ExactIndex Key
      (PhysicalRule Key Token width))
    (accepted : compileProgram? rules = some index)
    (queries : List Key) (initial : Stack Token) :
    runPhysicalProofFrom apartCheck index queries initial =
      runSourceProofFrom apartCheck rules queries initial := by
  induction queries generalizing initial with
  | nil => rfl
  | cons query queries inductionHypothesis =>
      simp only [runPhysicalProofFrom, runSourceProofFrom, List.foldlM_cons]
      rw [runPhysicalStep_eq_runSourceStep_of_compileProgram?
        apartCheck rules index accepted query initial]
      cases runSourceStep apartCheck rules query initial with
      | none => rfl
      | some next =>
          exact inductionHypothesis next

/-! ## Independent witnesses and fail-closed cases -/

private def noApart {Token : Type} : ApartCheck Token :=
  fun _ _ => some ()

private def constantFrame (token : Nat) : AdmittedSource Nat 0 where
  source :=
    { frame :=
        { instructions := []
          conclusion := .separated token [] }
      apart := [] }
  accepted := rfl

private def proofRules : List (SourceRule String Nat 0) :=
  [ { key := "hyp", action := .push [3] }
  , { key := "assert", action := .apply (constantFrame 7) } ]

private def proofIndex :
    ExactRuleSelectorCompilation.ExactIndex String
      (PhysicalRule String Nat 0) :=
  [ ("hyp", { key := "hyp", action := .push [3] })
  , ("assert",
      { key := "assert",
        action := .apply (compile (constantFrame 7).source) }) ]

/-- A proof-language inventory reaches the same singleton result through the
compiled fold. -/
example :
    runPhysicalProofFrom noApart proofIndex ["hyp", "assert"] [] =
      some [[3], [7]] := by
  decide

private def equationRules : List (SourceRule String Nat 0) :=
  [ { key := "equation", action := .apply (constantFrame 11) } ]

private def equationIndex :
    ExactRuleSelectorCompilation.ExactIndex String
      (PhysicalRule String Nat 0) :=
  [ ("equation",
      { key := "equation",
        action := .apply (compile (constantFrame 11).source) }) ]

/-- The same compiler executes an equation-language rule inventory. -/
example :
    runPhysicalProofFrom noApart equationIndex ["equation"] [] =
      some [[11]] := by
  decide

/-- Duplicate selectors are rejected before a physical program exists. -/
example :
    compileProgram?
      ([ { key := "duplicate", action := .push ([1] : Formula Nat) }
       , { key := "duplicate", action := .push ([2] : Formula Nat) } ] :
        List (SourceRule String Nat 0)) =
        none := by
  decide

/-- Missing selectors reject the proof step rather than preserving the old
stack. -/
example :
    runSourceStep noApart equationRules "missing" [] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.ExactFrameProofCompilation
