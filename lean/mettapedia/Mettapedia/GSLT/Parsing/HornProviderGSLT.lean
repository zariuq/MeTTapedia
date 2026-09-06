import Mettapedia.GSLT.Parsing.HornIntegerProvider

/-!
# Occurrence-indexed Horn execution with source-authenticated providers

States are the existing ordered lists of fuel-indexed ground obligations.
Clause actions select a source occurrence and ground substitution. Provider
actions select both an empty-body capability declaration and an authored
equation occurrence, whose independently interpreted answer must be exactly
the outstanding query. Neither an unrelated answer nor an empty answer can
discharge that query.

The interpreted provider fragment yields zero or one answer per selected
equation occurrence; this is not general multi-answer provider semantics.
Two matching source occurrences still give two distinct labelled paths,
even when their states and answers coincide.

The executable functions check proposed finite actions and paths. Rejection
does not establish semantic refutation. Completeness needs range safety only
for the provider equation occurrences used by the proposed path. Native
PeTTa/C execution and source-to-target representation are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornProviderGSLT

open HornCertificate HornEquationInstantiation HornEquationContextual HornIntegerProvider
open HornCertificateGSLT (State Obligation goalsAt)

def argumentCount : GroundTerms → Nat
  | .nil => 0
  | .cons _ tail => argumentCount tail + 1

def queryTerm (goal : GroundAtom) : GroundTerm := .app goal.relation goal.arguments

def providerCall (goal : GroundAtom) : GroundTerm :=
  .app ("gslt:" ++ goal.relation) (.cons (queryTerm goal) .nil)

/-- The actual capability fact must name this relation, declare exactly its
positive ground arity, and have no premises. -/
def CapabilityDeclaration (rule : Rule) (goal : GroundAtom) : Prop :=
  rule.body = [] ∧
    rule.head = ⟨"oslf-external-relation-decl-v1",
      .cons (.atom goal.relation) (.cons (.integer (argumentCount goal.arguments)) .nil)⟩ ∧
    0 < argumentCount goal.arguments

def checkCapability (rule : Rule) (goal : GroundAtom) : Bool :=
  rule.body.isEmpty &&
    decide (rule.head = ⟨"oslf-external-relation-decl-v1",
      .cons (.atom goal.relation) (.cons (.integer (argumentCount goal.arguments)) .nil)⟩) &&
    decide (0 < argumentCount goal.arguments)

theorem checkCapability_iff (rule : Rule) (goal : GroundAtom) :
    checkCapability rule goal = true ↔ CapabilityDeclaration rule goal := by
  simp [checkCapability, CapabilityDeclaration, and_assoc]

inductive Action where
  | rule (occurrence : Nat) (substitution : Substitution)
  | provider (capabilityOccurrence equationOccurrence : Nat)
  deriving DecidableEq, Repr

def ActionSafe (program : Program) : Action → Prop
  | .rule _ _ => True
  | .provider _ occurrence => OccurrenceRangeSafe program occurrence

def TraceSafe (program : Program) (actions : List Action) : Prop :=
  ∀ action ∈ actions, ActionSafe program action

/-- Declarative steps refer to actual source instances and independently
specified provider answers, not to acceptance by the replay function. -/
inductive Step (program : Program) : Action → State → State → Prop where
  | rule {fuel occurrence : Nat} {goal : GroundAtom} {rest : State}
      {rule : Rule} {substitution : Substitution} {goals : List GroundAtom}
      (selected : program[occurrence]? = some rule)
      (valid : substitutionValid substitution = true)
      (head : instantiateAtom substitution rule.head = some goal)
      (body : instantiateAtoms substitution rule.body = some goals) :
      Step program (.rule occurrence substitution) ((fuel + 1, goal) :: rest)
        (goalsAt fuel goals ++ rest)
  | provider {fuel capabilityOccurrence equationOccurrence : Nat}
      {goal : GroundAtom} {rest : State} {declaration : Rule} {residual : GroundTerm}
      (selected : program[capabilityOccurrence]? = some declaration)
      (capability : CapabilityDeclaration declaration goal)
      (equation : StepAt program equationOccurrence [] (providerCall goal) residual)
      (answer : AnswersEval residual [queryTerm goal]) :
      Step program (.provider capabilityOccurrence equationOccurrence)
        ((fuel + 1, goal) :: rest) rest

def replayStep? (program : Program) : Action → State → Option State
  | .rule occurrence substitution, (fuel + 1, goal) :: rest => do
      let rule ← program[occurrence]?
      if substitutionValid substitution then
        let head ← instantiateAtom substitution rule.head
        if head = goal then
          let goals ← instantiateAtoms substitution rule.body
          pure (goalsAt fuel goals ++ rest)
        else none
      else none
  | .provider capabilityOccurrence equationOccurrence, (_fuel + 1, goal) :: rest => do
      let declaration ← program[capabilityOccurrence]?
      if checkCapability declaration goal then
        let answers ← runAt? program equationOccurrence (providerCall goal)
        if answers = [queryTerm goal] then some rest else none
      else none
  | _, _ => none

private theorem runAt_source_sound {program : Program} {occurrence : Nat}
    {call : GroundTerm} {answers : List GroundTerm}
    (produced : runAt? program occurrence call = some answers) :
    ∃ residual, StepAt program occurrence [] call residual ∧ AnswersEval residual answers := by
  cases selected : instantiateEquationAt? program occurrence call with
  | none => simp [runAt?, selected] at produced
  | some pair =>
    rcases pair with ⟨residual, certificate⟩
    exact ⟨residual, rewriteAt?_sound program occurrence [] call residual
      (by simp [rewriteAt?, selected]),
      evalAnswers?_sound residual answers (by simpa [runAt?, selected] using produced)⟩

theorem replayStep?_sound (program : Program) (action : Action) (source target : State)
    (produced : replayStep? program action source = some target) :
    Step program action source target := by
  cases source with
  | nil => cases action <;> simp [replayStep?] at produced
  | cons obligation rest =>
    rcases obligation with ⟨fuel, goal⟩
    cases fuel with
    | zero => cases action <;> simp [replayStep?] at produced
    | succ fuel =>
      cases action with
      | rule occurrence substitution =>
        cases selected : program[occurrence]? with
        | none => simp [replayStep?, selected] at produced
        | some rule =>
          by_cases valid : substitutionValid substitution = true
          · cases head : instantiateAtom substitution rule.head with
            | none => simp [replayStep?, selected, valid, head] at produced
            | some query =>
              by_cases equal : query = goal
              · subst query
                cases body : instantiateAtoms substitution rule.body with
                | none => simp [replayStep?, selected, valid, head, body] at produced
                | some goals =>
                  have output : goalsAt fuel goals ++ rest = target := by
                    simpa [replayStep?, selected, valid, head, body] using produced
                  subst target
                  exact .rule selected valid head body
              · simp [replayStep?, selected, valid, head, equal] at produced
          · simp [replayStep?, selected, valid] at produced
      | provider capabilityOccurrence equationOccurrence =>
        cases selected : program[capabilityOccurrence]? with
        | none => simp [replayStep?, selected] at produced
        | some declaration =>
          by_cases capability : checkCapability declaration goal = true
          · cases returned : runAt? program equationOccurrence (providerCall goal) with
            | none => simp [replayStep?, selected, returned] at produced
            | some answers =>
              by_cases exactAnswer : answers = [queryTerm goal]
              · subst answers
                have output : rest = target := by
                  simpa [replayStep?, selected, capability, returned] using produced
                subst target
                obtain ⟨residual, equation, answer⟩ := runAt_source_sound returned
                exact .provider selected ((checkCapability_iff declaration goal).mp capability)
                  equation answer
              · simp [replayStep?, selected, returned, exactAnswer] at produced
          · simp [replayStep?, selected, capability] at produced

theorem replayStep?_complete {program : Program} {action : Action}
    (safe : ActionSafe program action) {source target : State}
    (step : Step program action source target) :
    replayStep? program action source = some target := by
  cases step with
  | rule selected valid head body =>
    simp [replayStep?, selected, valid, head, body]
  | provider selected capability equation answer =>
    have returned := runAt?_of_step safe equation (evalAnswers?_complete answer)
    simp [replayStep?, selected, (checkCapability_iff _ _).mpr capability, returned]

theorem replayStep?_iff {program : Program} {action : Action}
    (safe : ActionSafe program action) (source target : State) :
    replayStep? program action source = some target ↔ Step program action source target :=
  ⟨replayStep?_sound program action source target, replayStep?_complete safe⟩

theorem provider_wrong_answers_are_refused {program : Program}
    {capabilityOccurrence equationOccurrence fuel : Nat} {goal : GroundAtom}
    {answers : List GroundTerm} (rest : State)
    (returned : runAt? program equationOccurrence (providerCall goal) = some answers)
    (wrong : answers ≠ [queryTerm goal]) :
    replayStep? program (.provider capabilityOccurrence equationOccurrence)
      ((fuel + 1, goal) :: rest) = none := by
  cases selected : program[capabilityOccurrence]? <;>
    simp [replayStep?, selected, returned, wrong]

theorem provider_empty_answers_are_refused {program : Program}
    {capabilityOccurrence equationOccurrence fuel : Nat} {goal : GroundAtom}
    (rest : State)
    (returned : runAt? program equationOccurrence (providerCall goal) = some []) :
    replayStep? program (.provider capabilityOccurrence equationOccurrence)
      ((fuel + 1, goal) :: rest) = none :=
  provider_wrong_answers_are_refused rest returned (by simp)

/-- A boundary of the interpreted fragment, not a duplicate-output test. -/
theorem interpreted_answers_zero_or_one {term : GroundTerm} {answers : List GroundTerm}
    (evaluated : AnswersEval term answers) :
    answers = [] ∨ ∃ value, answers = [value] := by
  induction evaluated with
  | quote value => exact Or.inr ⟨value, rfl⟩
  | empty => exact Or.inl rfl
  | ifTrue _ _ ih => exact ih
  | ifFalse _ _ ih => exact ih

def replayPath? (program : Program) : List Action → State → Option State
  | [], state => some state
  | action :: rest, state => do
      let next ← replayStep? program action state
      replayPath? program rest next

inductive Path (program : Program) : List Action → State → State → Prop where
  | nil (state : State) : Path program [] state state
  | cons {action : Action} {actions : List Action} {source middle target : State}
      (first : Step program action source middle) (rest : Path program actions middle target) :
      Path program (action :: actions) source target

theorem replayPath?_sound (program : Program) (actions : List Action) (source target : State)
    (produced : replayPath? program actions source = some target) :
    Path program actions source target := by
  induction actions generalizing source with
  | nil =>
    have equal : source = target := by simpa [replayPath?] using produced
    subst target
    exact .nil source
  | cons action actions ih =>
    cases next : replayStep? program action source with
    | none => simp [replayPath?, next] at produced
    | some middle =>
      exact .cons (replayStep?_sound program action source middle next)
        (ih middle (by simpa [replayPath?, next] using produced))

theorem replayPath?_complete {program : Program} {actions : List Action}
    (safe : TraceSafe program actions) {source target : State}
    (path : Path program actions source target) :
    replayPath? program actions source = some target := by
  induction path with
  | nil state => rfl
  | @cons action actions source middle target first rest ih =>
    have headSafe := safe action (by simp)
    have tailSafe : TraceSafe program actions := by
      intro candidate member
      exact safe candidate (by simp [member])
    simp [replayPath?, replayStep?_complete headSafe first, ih tailSafe]

theorem replayPath?_iff {program : Program} {actions : List Action}
    (safe : TraceSafe program actions) (source target : State) :
    replayPath? program actions source = some target ↔ Path program actions source target :=
  ⟨replayPath?_sound program actions source target, replayPath?_complete safe⟩

theorem Path.append {program : Program} {first second : List Action}
    {source middle target : State} (left : Path program first source middle)
    (right : Path program second middle target) :
    Path program (first ++ second) source target := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

theorem replayPath?_append (program : Program) (first second : List Action)
    (source : State) :
    replayPath? program (first ++ second) source =
      (replayPath? program first source).bind (replayPath? program second) := by
  induction first generalizing source with
  | nil => rfl
  | cons action actions ih =>
    cases next : replayStep? program action source <;>
      simp [replayPath?, next, ih]

/-- The semantic GSLT forgets action labels only at this explicit observation;
the `Path` carrier above retains every selected source occurrence. -/
def theory (program : Program) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => ∃ action, Step program action source target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem Path.to_multiStep {program : Program} {actions : List Action}
    {source target : State} (path : Path program actions source target) :
    (theory program).MultiStep source target := by
  induction path with
  | nil state => exact @GSLT.MultiStep.refl (theory program) state
  | cons first _ ih => exact @GSLT.MultiStep.step (theory program) _ _ _ ⟨_, first⟩ ih

theorem multiStep_iff_path (program : Program) (source target : State) :
    (theory program).MultiStep source target ↔
      ∃ actions, Path program actions source target := by
  constructor
  · intro path
    refine @GSLT.MultiStep.rec (theory program)
      (fun first last _ => ∃ actions, Path program actions first last)
      ?_ ?_ source target path
    · intro state
      exact ⟨[], .nil state⟩
    · intro first middle last step _ ih
      obtain ⟨action, step⟩ := step
      obtain ⟨actions, rest⟩ := ih
      exact ⟨action :: actions, .cons step rest⟩
  · rintro ⟨actions, path⟩
    exact path.to_multiStep

theorem Step.append_suffix {program : Program} {action : Action} {source target : State}
    (step : Step program action source target) (suffix : State) :
    Step program action (source ++ suffix) (target ++ suffix) := by
  cases step with
  | rule selected valid head body =>
    simpa [List.append_assoc] using
      (Step.rule (rest := _ ++ suffix) selected valid head body)
  | provider selected capability equation answer =>
    exact .provider selected capability equation answer

theorem Path.append_suffix {program : Program} {actions : List Action}
    {source target : State} (path : Path program actions source target) (suffix : State) :
    Path program actions (source ++ suffix) (target ++ suffix) := by
  induction path with
  | nil => exact .nil _
  | cons first _ ih => exact .cons (first.append_suffix suffix) ih

/-! ## Independent local models and backward reflection

The meaning predicate is supplied independently of execution. The two local
soundness conditions inspect actual clause instances and authenticated provider
answers. They do not assume anything about whole paths or replay acceptance.
-/

def StateHolds (Meaning : GroundAtom → Prop) (state : State) : Prop :=
  ∀ obligation ∈ state, Meaning obligation.2

def ClauseSound (program : Program) (Meaning : GroundAtom → Prop) : Prop :=
  ∀ (occurrence : Nat) (rule : Rule) (substitution : Substitution)
    (goal : GroundAtom) (premises : List GroundAtom),
    program[occurrence]? = some rule →
    substitutionValid substitution = true →
    instantiateAtom substitution rule.head = some goal →
    instantiateAtoms substitution rule.body = some premises →
    (∀ premise ∈ premises, Meaning premise) → Meaning goal

def ProviderSound (program : Program) (Meaning : GroundAtom → Prop) : Prop :=
  ∀ (capabilityOccurrence equationOccurrence : Nat) (declaration : Rule)
    (goal : GroundAtom) (residual : GroundTerm),
    program[capabilityOccurrence]? = some declaration →
    CapabilityDeclaration declaration goal →
    StepAt program equationOccurrence [] (providerCall goal) residual →
    AnswersEval residual [queryTerm goal] → Meaning goal

@[simp] theorem stateHolds_nil (Meaning : GroundAtom → Prop) : StateHolds Meaning [] := by
  simp [StateHolds]

@[simp] theorem stateHolds_cons (Meaning : GroundAtom → Prop)
    (obligation : Obligation) (rest : State) :
    StateHolds Meaning (obligation :: rest) ↔
      Meaning obligation.2 ∧ StateHolds Meaning rest := by
  simp [StateHolds]

@[simp] theorem stateHolds_append (Meaning : GroundAtom → Prop) (left right : State) :
    StateHolds Meaning (left ++ right) ↔ StateHolds Meaning left ∧ StateHolds Meaning right := by
  simp [StateHolds, or_imp, forall_and]

@[simp] theorem stateHolds_goalsAt (Meaning : GroundAtom → Prop)
    (fuel : Nat) (goals : List GroundAtom) :
    StateHolds Meaning (goalsAt fuel goals) ↔ ∀ goal ∈ goals, Meaning goal := by
  simp [StateHolds, goalsAt]

theorem Step.reflect_meaning {program : Program} {Meaning : GroundAtom → Prop}
    (clauses : ClauseSound program Meaning) (providers : ProviderSound program Meaning)
    {action : Action} {source target : State} (step : Step program action source target)
    (holds : StateHolds Meaning target) : StateHolds Meaning source := by
  cases step with
  | rule selected valid head body =>
    obtain ⟨premises, rest⟩ := (stateHolds_append _ _ _).mp holds
    exact (stateHolds_cons _ _ _).mpr
      ⟨clauses _ _ _ _ _ selected valid head body ((stateHolds_goalsAt _ _ _).mp premises),
        rest⟩
  | provider selected capability equation answer =>
    exact (stateHolds_cons _ _ _).mpr
      ⟨providers _ _ _ _ _ selected capability equation answer, holds⟩

theorem Path.reflect_meaning {program : Program} {Meaning : GroundAtom → Prop}
    (clauses : ClauseSound program Meaning) (providers : ProviderSound program Meaning)
    {actions : List Action} {source target : State} (path : Path program actions source target)
    (holds : StateHolds Meaning target) : StateHolds Meaning source := by
  induction path with
  | nil => exact holds
  | cons first _ ih => exact first.reflect_meaning clauses providers (ih holds)

theorem Path.terminal_soundness {program : Program} {Meaning : GroundAtom → Prop}
    (clauses : ClauseSound program Meaning) (providers : ProviderSound program Meaning)
    {actions : List Action} {source : State} (path : Path program actions source []) :
    StateHolds Meaning source :=
  path.reflect_meaning clauses providers (stateHolds_nil Meaning)

theorem Path.goal_soundness {program : Program} {Meaning : GroundAtom → Prop}
    (clauses : ClauseSound program Meaning) (providers : ProviderSound program Meaning)
    {actions : List Action} {fuel : Nat} {goal : GroundAtom}
    (path : Path program actions [(fuel, goal)] []) : Meaning goal :=
  path.terminal_soundness clauses providers (fuel, goal) (by simp)

theorem terminal_replay_soundness {program : Program} {Meaning : GroundAtom → Prop}
    (clauses : ClauseSound program Meaning) (providers : ProviderSound program Meaning)
    {actions : List Action} {source : State}
    (produced : replayPath? program actions source = some []) : StateHolds Meaning source :=
  (replayPath?_sound _ _ _ _ produced).terminal_soundness clauses providers

theorem no_step_from_empty (program : Program) (action : Action) (target : State) :
    ¬ Step program action [] target := by intro step; cases step

theorem exhausted_head_has_no_step (program : Program) (action : Action)
    (goal : GroundAtom) (rest target : State) :
    ¬ Step program action ((0, goal) :: rest) target := by intro step; cases step

/-! ## Occurrence-sensitive controls -/

private def demoQuery : GroundAtom :=
  ⟨"less", .cons (.integer 0) (.cons (.integer 1) .nil)⟩

private def demoGoal : GroundAtom := ⟨"accepted", .nil⟩

private def demoClause : Rule :=
  ⟨"client", ⟨"accepted", .nil⟩,
    [⟨"less", .cons (.integer 0) (.cons (.integer 1) .nil)⟩]⟩

private def demoCapability : Rule :=
  ⟨"capability", ⟨"oslf-external-relation-decl-v1",
    .cons (.atom "less") (.cons (.integer 2) .nil)⟩, []⟩

private def demoEquation : Rule :=
  let query := Term.app "less" (.cons (.integer 0) (.cons (.integer 1) .nil))
  ⟨"provider", ⟨"metta-equation",
    .cons (.app "gslt:less" (.cons query .nil))
      (.cons (.app "if"
        (.cons (.app "<" (.cons (.integer 0) (.cons (.integer 1) .nil)))
          (.cons (.app "quote" (.cons query .nil))
            (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil)) .nil)))) .nil)⟩, []⟩

private def demoResidual : GroundTerm :=
  .app "if" (.cons (.app "<" (.cons (.integer 0) (.cons (.integer 1) .nil)))
    (.cons (.app "quote" (.cons (queryTerm demoQuery) .nil))
      (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil)) .nil)))

private def demoProgram : Program :=
  [demoClause, demoCapability, demoEquation, demoClause]

private theorem demoProviderResult :
    runAt? demoProgram 2 (providerCall demoQuery) = some [queryTerm demoQuery] := by
  have instantiated : instantiateEquationAt? demoProgram 2 (providerCall demoQuery) =
      some (demoResidual, .node demoEquation [] .nil) := by decide
  simp [runAt?, instantiated, demoResidual, evalAnswers?, evalBoolean?, evalInteger?]

private theorem demoRuleStep :
    replayStep? demoProgram (.rule 0 []) [(2, demoGoal)] = some [(1, demoQuery)] := by
  decide

private theorem demoProviderStep :
    replayStep? demoProgram (.provider 1 2) [(1, demoQuery)] = some [] := by
  have selected : demoProgram[1]? = some demoCapability := rfl
  have capability : checkCapability demoCapability demoQuery = true := by decide
  simp [replayStep?, selected, capability, demoProviderResult]

theorem clause_then_provider_executes :
    replayPath? demoProgram [.rule 0 [], .provider 1 2] [(2, demoGoal)] = some [] := by
  simp [replayPath?, demoRuleStep, demoProviderStep]

theorem clause_then_provider_has_semantic_path :
    Path demoProgram [.rule 0 [], .provider 1 2] [(2, demoGoal)] [] :=
  replayPath?_sound _ _ _ _ clause_then_provider_executes

theorem wrong_capability_occurrence_is_refused :
    replayStep? demoProgram (.provider 0 2) [(1, demoQuery)] = none := by decide

theorem absent_equation_occurrence_is_refused :
    replayStep? demoProgram (.provider 1 9) [(1, demoQuery)] = none := by decide

theorem wrong_query_is_refused :
    replayStep? demoProgram (.provider 1 2)
      [(1, ⟨"less", .cons (.integer 1) (.cons (.integer 0) .nil)⟩)] = none := by decide

private def forgedEquation : Rule :=
  ⟨"forged", ⟨"metta-equation",
    .cons (.app "gslt:less" (.cons
      (.app "less" (.cons (.integer 0) (.cons (.integer 1) .nil))) .nil))
      (.cons (.app "quote" (.cons (.atom "unrelated-answer") .nil)) .nil)⟩, []⟩

theorem actual_forged_answer_is_refused :
    replayStep? [demoCapability, forgedEquation] (.provider 0 1)
      [(1, demoQuery)] = none := by
  have instantiated : instantiateEquationAt? [demoCapability, forgedEquation] 1
      (providerCall demoQuery) =
      some (.app "quote" (.cons (.atom "unrelated-answer") .nil),
        .node forgedEquation [] .nil) := by decide
  have returned : runAt? [demoCapability, forgedEquation] 1 (providerCall demoQuery) =
      some [.atom "unrelated-answer"] := by
    simp [runAt?, instantiated, evalAnswers?]
  exact provider_wrong_answers_are_refused [] returned (by decide)

private def emptyEquation : Rule :=
  ⟨"empty-provider", ⟨"metta-equation",
    .cons (.app "gslt:less" (.cons
      (.app "less" (.cons (.integer 0) (.cons (.integer 1) .nil))) .nil))
      (.cons (.app "metta-nullary" (.cons (.atom "empty") .nil)) .nil)⟩, []⟩

theorem actual_empty_answer_is_refused :
    replayStep? [demoCapability, emptyEquation] (.provider 0 1)
      [(1, demoQuery)] = none := by
  have instantiated : instantiateEquationAt? [demoCapability, emptyEquation] 1
      (providerCall demoQuery) =
      some (.app "metta-nullary" (.cons (.atom "empty") .nil),
        .node emptyEquation [] .nil) := by decide
  have returned : runAt? [demoCapability, emptyEquation] 1 (providerCall demoQuery) =
      some [] := by
    simp [runAt?, instantiated, evalAnswers?]
  exact provider_empty_answers_are_refused [] returned

theorem wrong_declared_arity_is_refused :
    checkCapability demoCapability ⟨"less", .cons (.integer 0) .nil⟩ = false := by decide

theorem zero_arity_capability_is_refused :
    checkCapability
      ⟨"zero", ⟨"oslf-external-relation-decl-v1",
        .cons (.atom "zero") (.cons (.integer 0) .nil)⟩, []⟩
      ⟨"zero", .nil⟩ = false := by decide

theorem duplicate_source_occurrences_remain_distinct :
    Action.rule 0 [] ≠ Action.rule 3 [] ∧
      replayStep? demoProgram (.rule 0 []) [(2, demoGoal)] = some [(1, demoQuery)] ∧
      replayStep? demoProgram (.rule 3 []) [(2, demoGoal)] = some [(1, demoQuery)] := by
  decide

theorem duplicate_source_occurrences_give_distinct_paths :
    ([Action.rule 0 [], .provider 1 2] ≠ [.rule 3 [], .provider 1 2]) ∧
      Path demoProgram [.rule 0 [], .provider 1 2] [(2, demoGoal)] [] ∧
      Path demoProgram [.rule 3 [], .provider 1 2] [(2, demoGoal)] [] := by
  refine ⟨by decide, clause_then_provider_has_semantic_path, ?_⟩
  apply replayPath?_sound
  simp [replayPath?, duplicate_source_occurrences_remain_distinct.2.2, demoProviderStep]

theorem clause_preserves_duplicate_premises (goal : GroundAtom) (fuel : Nat) (rest : State) :
    goalsAt fuel [goal, goal] ++ rest = (fuel, goal) :: (fuel, goal) :: rest := rfl

/-! ## Independent vocabulary model controls

This model states only a finite vocabulary invariant, not arithmetic truth.
It is defined without paths, certificates, or replay. The negative controls
show that local semantic soundness is additional to executable well-formedness.
-/

private def demoVocabulary (goal : GroundAtom) : Prop :=
  goal.relation ∈ ["accepted", "less", "oslf-external-relation-decl-v1", "metta-equation"]

private theorem instantiateAtom_preserves_relation {substitution : Substitution}
    {atom : Atom} {goal : GroundAtom}
    (instantiated : instantiateAtom substitution atom = some goal) :
    goal.relation = atom.relation := by
  cases values : instantiateTerms substitution atom.arguments with
  | none => simp [instantiateAtom, values] at instantiated
  | some arguments =>
    have equal : ({ relation := atom.relation, arguments := arguments } : GroundAtom) = goal := by
      simpa [instantiateAtom, values] using instantiated
    exact (congrArg GroundAtom.relation equal).symm

private theorem demoClausesSound : ClauseSound demoProgram demoVocabulary := by
  intro occurrence rule substitution goal premises selected _ head _ _
  have member : rule ∈ demoProgram := List.mem_of_getElem? selected
  have relation := instantiateAtom_preserves_relation head
  simp only [demoVocabulary, relation]
  simp [demoProgram] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

private theorem demoProvidersSound : ProviderSound demoProgram demoVocabulary := by
  intro capabilityOccurrence equationOccurrence declaration goal residual selected capability _ _
  have member : declaration ∈ demoProgram := List.mem_of_getElem? selected
  simp [demoProgram] at member
  rcases member with rfl | rfl | rfl | rfl
  · have relation := congrArg Atom.relation capability.2.1
    simp [demoClause] at relation
  · have arguments := congrArg Atom.arguments capability.2.1
    simp [demoCapability] at arguments
    simp [demoVocabulary, ← arguments.1]
  · have relation := congrArg Atom.relation capability.2.1
    simp [demoEquation] at relation
  · have relation := congrArg Atom.relation capability.2.1
    simp [demoClause] at relation

theorem terminal_path_preserves_independent_vocabulary :
    StateHolds demoVocabulary [(2, demoGoal)] :=
  clause_then_provider_has_semantic_path.terminal_soundness demoClausesSound demoProvidersSound

private def forbiddenFact : Rule := ⟨"forbidden-fact", ⟨"forbidden", .nil⟩, []⟩

theorem executable_fact_can_violate_independent_meaning :
    replayStep? [forbiddenFact] (.rule 0 []) [(1, ⟨"forbidden", .nil⟩)] = some [] ∧
      ¬ ClauseSound [forbiddenFact] demoVocabulary := by
  refine ⟨by decide, ?_⟩
  intro sound
  have forbidden := sound 0 forbiddenFact [] ⟨"forbidden", .nil⟩ []
    rfl (by decide) rfl rfl (by simp)
  simp [demoVocabulary] at forbidden

theorem authenticated_provider_can_violate_an_unjustified_meaning :
    ¬ ProviderSound demoProgram (fun goal => goal.relation ≠ "less") := by
  intro sound
  obtain ⟨residual, equation, answer⟩ := runAt_source_sound demoProviderResult
  have forbidden := sound 1 2 demoCapability demoQuery residual rfl
    ((checkCapability_iff _ _).mp (by decide)) equation answer
  exact forbidden rfl

#print axioms checkCapability_iff
#print axioms replayStep?_iff
#print axioms replayPath?_iff
#print axioms multiStep_iff_path
#print axioms Path.append
#print axioms Path.reflect_meaning
#print axioms Path.terminal_soundness

end Mettapedia.GSLT.Parsing.HornProviderGSLT
