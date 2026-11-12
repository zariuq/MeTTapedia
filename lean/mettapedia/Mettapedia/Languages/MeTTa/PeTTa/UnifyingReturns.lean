import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement

/-!
# Source continuations that return a protected variable

The return obligation follows the actual source control and saved frames.
Expressions before a return continuation may call other equations, change
spaces or branch. Their results are not replaced by a value-only oracle.
The recognized tail grammar is a profile of the existing source machine;
constructor-pattern returns and normalization of other surface forms are
separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi

inductive ReturnsVariable (name : String) : Atom → Prop where
  | variable : ReturnsVariable name (.var name)
  | letE (pattern value : Atom) {body : Atom} : ReturnsVariable name body →
      ReturnsVariable name (.expression [.symbol "let", pattern, value, body])
  | letMany (pairs : List Atom) {body : Atom} : ReturnsVariable name body →
      ReturnsVariable name (.expression [.symbol "let*", .expression pairs, body])
  | branch (condition : Atom) {yes no : Atom} : ReturnsVariable name yes → ReturnsVariable name no →
      ReturnsVariable name (.expression [.symbol "if", condition, yes, no])
  | caseE (key : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) :
      Eval.readCases rows = some cases → (∀ branch ∈ cases, ReturnsVariable name branch.2) →
      ReturnsVariable name (.expression [.symbol "case", key, .expression rows])
  | matchE (space pattern : Atom) {body : Atom} : ReturnsVariable name body →
      ReturnsVariable name (.expression [.symbol "match", space, pattern, body])
  | empty : ReturnsVariable name (.expression [.symbol "empty"])

theorem ReturnsVariable.control_or_variable {name : String} {expression : Atom}
    (returns : ReturnsVariable name expression) :
    expression = .var name ∨ sourceControlForm expression = true := by
  cases returns <;> simp [sourceControlForm]

/-- A bounded source-syntax recognizer. Its budget limits the inspection,
not execution of the recognized program. Native plan decoding is separate. -/
def checksReturnVariable (name : String) : Nat → Atom → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if expression == .var name then true
      else match expression with
      | .expression [.symbol "let", _, _, body] => checksReturnVariable name fuel body
      | .expression [.symbol "let*", .expression _, body] => checksReturnVariable name fuel body
      | .expression [.symbol "if", _, yes, no] => checksReturnVariable name fuel yes && checksReturnVariable name fuel no
      | .expression [.symbol "case", _, .expression rows] =>
          match Eval.readCases rows with
          | none => false
          | some cases => cases.all fun branch => checksReturnVariable name fuel branch.2
      | .expression [.symbol "match", _, _, body] => checksReturnVariable name fuel body
      | .expression [.symbol "empty"] => true
      | _ => false

theorem checksReturnVariable_sound (name : String) (fuel : Nat) : ∀ expression,
    checksReturnVariable name fuel expression = true → ReturnsVariable name expression := by
  induction fuel with
  | zero => intro expression checked; cases checked
  | succ fuel ih =>
      intro expression checked
      simp only [checksReturnVariable] at checked
      split at checked
      · next same =>
          have equal : expression = .var name := by simpa using same
          subst expression
          exact .variable
      · split at checked
        · exact .letE _ _ (ih _ checked)
        · exact .letMany _ (ih _ checked)
        · have branches := Bool.and_eq_true_iff.mp checked
          exact .branch _ (ih _ branches.1) (ih _ branches.2)
        · rename_i key rows _
          cases parsed : Eval.readCases rows with
          | none => simp [parsed] at checked
          | some cases =>
              simp only [parsed] at checked
              exact .caseE key rows cases parsed
                (fun branch member => ih branch.2 ((List.all_eq_true.mp checked) branch member))
        · exact .matchE _ _ (ih _ checked)
        · exact .empty
        · cases checked

theorem nestedLets_returns_variable {name : String} {body : Atom} (returns : ReturnsVariable name body) :
    ∀ pairs nested, Eval.nestedLets pairs body = some nested → ReturnsVariable name nested := by
  intro pairs
  induction pairs with
  | nil => intro nested parsed; cases parsed; exact returns
  | cons pair rest ih =>
      intro nested parsed
      cases pair with
      | var => simp [Eval.nestedLets] at parsed
      | symbol => simp [Eval.nestedLets] at parsed
      | grounded => simp [Eval.nestedLets] at parsed
      | expression items =>
          cases items with
          | nil => simp [Eval.nestedLets] at parsed
          | cons pattern items =>
              cases items with
              | nil => simp [Eval.nestedLets] at parsed
              | cons value items =>
                  cases items with
                  | cons => simp [Eval.nestedLets] at parsed
                  | nil =>
                      simp only [Eval.nestedLets] at parsed
                      cases inside : Eval.nestedLets rest body with
                      | none => simp [inside] at parsed
                      | some inner =>
                          simp [inside] at parsed
                          subst nested
                          exact .letE pattern value (ih inner inside)

def ReturnedValue (expected : Atom) (answers : List Answer) : Prop :=
  ∀ answer ∈ answers, answer.value = expected

inductive ReturnControl (name : String) (expected : Atom) : Control → Prop where
  | evaluate (bindings : MORK.Subst) {expression : Atom} : ReturnsVariable name expression →
      ReturnControl name expected (.evaluate bindings expression)
  | sequence {pending : List Control} {answers : List Answer} :
      (∀ control ∈ pending, ReturnControl name expected control) → ReturnedValue expected answers →
      ReturnControl name expected (.sequence pending answers)
  | returned {answers : List Answer} : ReturnedValue expected answers →
      ReturnControl name expected (.returned answers)
  | fault (reason : Effects.Fault) : ReturnControl name expected (.fault reason)

inductive ReturnFrames (name : String) (expected : Atom) : List Frame → Prop where
  | nil : ReturnFrames name expected []
  | sequence {pending : List Control} {answers : List Answer} {rest : List Frame} :
      (∀ control ∈ pending, ReturnControl name expected control) → ReturnedValue expected answers →
      ReturnFrames name expected rest → ReturnFrames name expected (.sequence pending answers :: rest)

inductive ReturnContinuation (name : String) : Frame → Prop where
  | bind (pattern : Atom) {body : Atom} : ReturnsVariable name body → ReturnContinuation name (.bind pattern body)
  | branch {yes no : Atom} : ReturnsVariable name yes → ReturnsVariable name no →
      ReturnContinuation name (.branch yes no)
  | select (cases : SpaceSemantics.Cases) : (∀ branch ∈ cases, ReturnsVariable name branch.2) →
      ReturnContinuation name (.select cases)
  | query (pattern : Atom) {body : Atom} : ReturnsVariable name body → ReturnContinuation name (.query pattern body)

/-- Arbitrary prefix-computation frames may sit above the return boundary.
Below it only answer-collecting branch frames remain. -/
inductive ProtectedFrames (name : String) (expected : Atom) : List Frame → Prop where
  | boundary {frame : Frame} {rest : List Frame} : ReturnContinuation name frame →
      ReturnFrames name expected rest → ProtectedFrames name expected (frame :: rest)
  | nested (frame : Frame) {rest : List Frame} : ProtectedFrames name expected rest →
      ProtectedFrames name expected (frame :: rest)

theorem ReturnFrames.no_recovery {name : String} {expected : Atom} {frames : List Frame}
    (good : ReturnFrames name expected frames) (earned : List Answer) :
    recoverDynamic earned frames = none := by
  induction good generalizing earned with
  | nil => rfl
  | sequence pending completed rest ih => exact ih _

theorem ProtectedFrames.after_recovery {name : String} {expected : Atom} {frames : List Frame}
    (good : ProtectedFrames name expected frames) (earned answers : List Answer) (remaining : List Frame)
    (recovered : recoverDynamic earned frames = some (answers, remaining)) :
    ProtectedFrames name expected remaining := by
  induction good generalizing earned with
  | boundary promise tail =>
      have noHandler := tail.no_recovery []
      cases promise <;> simp only [recoverDynamic, noHandler] at recovered <;> cases recovered
  | nested frame later ih =>
      cases frame with
      | dynamicCall =>
          simp only [recoverDynamic, Option.some.injEq, Prod.mk.injEq] at recovered
          rcases recovered with ⟨rfl, rfl⟩
          exact later
      | sequence pending completed => exact ih (completed ++ earned) recovered
      | _ => exact ih [] recovered

def ReturnConfiguration (name : String) (expected : Atom) (configuration : Configuration) : Prop :=
  ProtectedFrames name expected configuration.frames ∨
    (ReturnFrames name expected configuration.frames ∧ ReturnControl name expected configuration.control)

theorem bindAnswers_returning {name : String} (expected pattern body : Atom)
    (returns : ReturnsVariable name body) : ∀ answers continued,
    bindAnswers pattern body answers = some continued →
      ∀ control ∈ continued, ReturnControl name expected control := by
  intro answers
  induction answers with
  | nil => intro continued chosen; simp [bindAnswers] at chosen; subst continued; simp
  | cons answer rest ih =>
      intro continued chosen
      simp only [bindAnswers] at chosen
      cases tailRun : bindAnswers pattern body rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases unified : unifyBinding answer.bindings pattern answer.value with
          | exhausted => simp [unified] at chosen
          | clash => simp [unified] at chosen; subst continued; exact ih tail tailRun
          | ok bound =>
              simp [unified] at chosen
              subst continued
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · exact .evaluate bound returns
              · exact ih tail tailRun control present

theorem selectCase_returning {name : String} (bindings : MORK.Subst) (value : Atom) :
    ∀ cases bound body, (∀ branch ∈ cases, ReturnsVariable name branch.2) →
      selectCase bindings value cases = some (some (bound, body)) → ReturnsVariable name body := by
  intro cases
  induction cases with
  | nil => intro bound body returns chosen; cases chosen
  | cons branch rest ih =>
      intro bound body returns chosen
      simp only [selectCase] at chosen
      cases unified : unifyAsPattern bindings branch.1 value with
      | exhausted => simp [unified] at chosen
      | clash => simp only [unified] at chosen; exact ih bound body (fun branch present => returns branch (by simp [present])) chosen
      | ok next =>
          simp [unified] at chosen
          obtain ⟨rfl, rfl⟩ := chosen
          exact returns branch (by simp)

theorem selectAnswers_returning {name : String} (expected : Atom) (cases : SpaceSemantics.Cases)
    (returns : ∀ branch ∈ cases, ReturnsVariable name branch.2) : ∀ answers continued,
    selectAnswers cases answers = some continued →
      ∀ control ∈ continued, ReturnControl name expected control := by
  intro answers
  induction answers with
  | nil => intro continued chosen; simp [selectAnswers] at chosen; subst continued; simp
  | cons answer rest ih =>
      intro continued chosen
      simp only [selectAnswers] at chosen
      cases tailRun : selectAnswers cases rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases selected : selectCase answer.bindings answer.value cases with
          | none => simp [selected] at chosen
          | some selection =>
              cases selection with
              | none => simp [selected] at chosen; subst continued; exact ih tail tailRun
              | some pair =>
                  obtain ⟨bindings, body⟩ := pair
                  simp [selected] at chosen
                  subst continued
                  intro control member
                  rcases List.mem_cons.mp member with rfl | present
                  · exact .evaluate bindings (selectCase_returning _ _ _ _ _ returns selected)
                  · exact ih tail tailRun control present

theorem queryBodies_returning {name : String} (expected : Atom) (bindings : MORK.Subst) (pattern body : Atom)
    (returns : ReturnsVariable name body) : ∀ use rows continued,
    queryBodies bindings pattern body use rows = some continued →
      ∀ control ∈ continued, ReturnControl name expected control := by
  intro use rows
  induction rows generalizing use with
  | nil => intro continued chosen; simp [queryBodies] at chosen; subst continued; simp
  | cons row rest ih =>
      intro continued chosen
      simp only [queryBodies] at chosen
      cases tailRun : queryBodies bindings pattern body (use + 1) rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases unified : unify bindings pattern (rename use row) with
          | exhausted => simp [unified] at chosen
          | clash => simp [unified] at chosen; subst continued; exact ih _ _ tailRun
          | ok bound =>
              simp [unified] at chosen
              subst continued
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · exact .evaluate bound returns
              · exact ih _ _ tailRun control present

theorem queries_returning {name : String} (expected : Atom) (state : Effects.State) (pattern body : Atom)
    (returns : ReturnsVariable name body) : ∀ use answers continued used,
    queries state pattern body use answers = some (continued, used) →
      ∀ control ∈ continued, ReturnControl name expected control := by
  intro use answers
  induction answers generalizing use with
  | nil =>
      intro continued used chosen
      simp only [queries, Option.some.injEq, Prod.mk.injEq] at chosen
      obtain ⟨rfl, rfl⟩ := chosen
      simp
  | cons answer rest ih =>
      intro continued used chosen
      simp only [queries] at chosen
      split at chosen
      · rename_i rows read
        cases here : queryBodies answer.bindings pattern body use rows with
        | none => simp [here] at chosen
        | some controls =>
            cases there : queries state pattern body (use + rows.length) rest with
            | none => simp [here, there] at chosen
            | some tail =>
                obtain ⟨others, count⟩ := tail
                simp [here, there] at chosen
                obtain ⟨rfl, rfl⟩ := chosen
                intro control member
                rcases List.mem_append.mp member with present | present
                · exact queryBodies_returning expected _ _ _ returns _ _ _ here control present
                · exact ih _ _ _ there control present
      · cases there : queries state pattern body use rest with
        | none => simp [there] at chosen
        | some tail =>
            obtain ⟨others, count⟩ := tail
            simp [there] at chosen
            obtain ⟨rfl, rfl⟩ := chosen
            intro control member
            rcases List.mem_cons.mp member with rfl | present
            · exact .fault _
            · exact ih _ _ _ there control present

theorem protected_transition {registry : SpaceSemantics.Program} {source target : Configuration}
    {name : String} {expected : Atom} (transition : Transition registry source target)
    (protectedFrames : ProtectedFrames name expected source.frames) : ReturnConfiguration name expected target := by
  cases transition
  all_goals try exact Or.inl protectedFrames
  all_goals try exact Or.inl (.nested _ protectedFrames)
  case collapse_return answers outer rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail => cases promise
  case dispatch_return answers rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail => cases promise
  case dynamic_return answers rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail => cases promise
  case fault_caught reason earned rest control recovered =>
    exact .inl (protectedFrames.after_recovery [] earned rest recovered)
  case dynamic_equations bindings callee supplied head selected used control resolved notNative registered chosen =>
    cases selected
    all_goals first | exact .inl protectedFrames | exact .inl (.nested _ protectedFrames)
  case sequence_return answers collected pending rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail => cases promise
  case argument_return answers values pending target index rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail => cases promise
  case binding_return answers pattern body rest continued control frames bound =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail =>
        cases promise with
        | bind pattern returns =>
            exact .inr ⟨tail, .sequence (bindAnswers_returning expected pattern body returns answers continued bound)
              (by simp [ReturnedValue])⟩
  case case_return answers cases rest continued control frames selected =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail =>
        cases promise with
        | select cases returns =>
            exact .inr ⟨tail, .sequence (selectAnswers_returning expected cases returns answers continued selected)
              (by simp [ReturnedValue])⟩
  case if_return answers yes no rest control frames =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail =>
        cases promise with
        | branch yesReturns noReturns =>
            refine .inr ⟨tail, .sequence ?_ (by simp [ReturnedValue])⟩
            intro control member
            obtain ⟨answer, present, rfl⟩ := List.mem_map.mp member
            apply ReturnControl.evaluate answer.bindings
            split <;> assumption
  case query_return answers pattern body rest continued used control frames queried =>
    rw [frames] at protectedFrames
    cases protectedFrames with
    | nested frame later => exact .inl later
    | boundary promise tail =>
        cases promise with
        | query pattern returns =>
            exact .inr ⟨tail, .sequence
              (queries_returning expected source.state pattern body returns source.uses answers continued used queried)
              (by simp [ReturnedValue])⟩

theorem ReturnedValue.append {expected : Atom} {first second : List Answer}
    (one : ReturnedValue expected first) (two : ReturnedValue expected second) :
    ReturnedValue expected (first ++ second) := by
  intro answer member
  rcases List.mem_append.mp member with left | right
  · exact one answer left
  · exact two answer right

theorem tail_step {registry : SpaceSemantics.Program} {source target : Configuration}
    {initial : MORK.Subst} {name : String} {expected : Atom}
    (computed : step registry source = some target)
    (refined : ConfigurationRefines initial source)
    (initialValue : resolve initial (.var name) = expected)
    (ground : MORK.isGroundAtom expected = true)
    (framesGood : ReturnFrames name expected source.frames)
    (controlGood : ReturnControl name expected source.control) : ReturnConfiguration name expected target := by
  cases source with
  | mk state control frames input output uses =>
    cases controlGood with
    | evaluate bindings returns =>
      cases returns with
      | «variable» =>
          have bound : BindingRefines initial bindings := by
            simpa only [ControlRefines] using refined.1
          have fixed : resolve bindings (.var name) = expected := by
            rw [← bound.2 (.var name), initialValue]
            exact applySubst_ground bindings expected ground
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .inr ⟨framesGood, .returned (by simpa [ReturnedValue] using fixed)⟩
      | letE pattern value returns =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .inl (.boundary (.bind pattern returns) framesGood)
      | letMany pairs returns =>
          rename_i body
          cases parsed : Eval.nestedLets pairs body with
          | none =>
              simp [step, parsed] at computed
              subst target
              exact .inr ⟨framesGood, .fault _⟩
          | some nested =>
              simp [step, parsed] at computed
              subst target
              exact .inr ⟨framesGood, .evaluate bindings (nestedLets_returns_variable returns pairs nested parsed)⟩
      | branch condition yesReturns noReturns =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .inl (.boundary (.branch yesReturns noReturns) framesGood)
      | caseE key rows cases parsed returns =>
          simp [step, parsed] at computed
          subst target
          exact .inl (.boundary (.select cases returns) framesGood)
      | matchE space pattern returns =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .inl (.boundary (.query pattern returns) framesGood)
      | empty =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .inr ⟨framesGood, .returned (by simp [ReturnedValue])⟩
    | @sequence pending answers pendingGood answersGood =>
        cases pending with
        | nil =>
            simp only [step, Option.some.injEq] at computed
            subst target
            exact .inr ⟨framesGood, .returned answersGood⟩
        | cons first rest =>
            simp only [step, Option.some.injEq] at computed
            subst target
            exact .inr ⟨.sequence (fun control present => pendingGood control (by simp [present])) answersGood framesGood,
              pendingGood first (by simp)⟩
    | returned answersGood =>
        cases framesGood with
        | nil => simp [step] at computed
        | sequence pendingGood collectedGood restGood =>
            simp only [step, Option.some.injEq] at computed
            subst target
            exact .inr ⟨restGood, .sequence pendingGood (collectedGood.append answersGood)⟩
    | fault =>
        have noHandler := framesGood.no_recovery []
        simp only [step, noHandler] at computed
        cases computed

theorem return_configuration_step {registry : SpaceSemantics.Program} {source target : Configuration}
    {initial : MORK.Subst} {name : String} {expected : Atom}
    (computed : step registry source = some target)
    (refined : ConfigurationRefines initial source)
    (initialValue : resolve initial (.var name) = expected) (ground : MORK.isGroundAtom expected = true)
    (returns : ReturnConfiguration name expected source) : ReturnConfiguration name expected target := by
  rcases returns with protectedFrames | ⟨framesGood, controlGood⟩
  · exact protected_transition ((step_iff_transition registry source target).mp computed) protectedFrames
  · exact tail_step computed refined initialValue ground framesGood controlGood

theorem return_configuration_steps {registry : SpaceSemantics.Program} {source target : Configuration}
    {initial : MORK.Subst} {name : String} {expected : Atom}
    (steps : Relation.ReflTransGen (Transition registry) source target)
    (refined : ConfigurationRefines initial source)
    (initialValue : resolve initial (.var name) = expected) (ground : MORK.isGroundAtom expected = true)
    (returns : ReturnConfiguration name expected source) : ReturnConfiguration name expected target := by
  induction steps with
  | refl => exact returns
  | tail previous taken ih =>
      exact return_configuration_step (transition_step taken) (steps_refine previous refined) initialValue ground ih

theorem reached_return_values {registry : SpaceSemantics.Program} {source target : Configuration}
    {initial : MORK.Subst} {name : String} {expected : Atom}
    (steps : Relation.ReflTransGen (Transition registry) source target)
    (refined : ConfigurationRefines initial source)
    (initialValue : resolve initial (.var name) = expected) (ground : MORK.isGroundAtom expected = true)
    (returns : ReturnConfiguration name expected source) (answers : List Answer)
    (returned : target.control = .returned answers) (finished : target.frames = []) :
    ReturnedValue expected answers := by
  have after := return_configuration_steps steps refined initialValue ground returns
  rcases after with waiting | ⟨_, controlGood⟩
  · rw [finished] at waiting
    cases waiting
  · rw [returned] at controlGood
    cases controlGood with
    | returned values => exact values

/-- A syntax-derived compound return, through arbitrary real source prefix
computations, yields the original ground variable in each actual answer
packet. The final configuration and exact answer list remain explicit. -/
theorem completed_protected_return {registry : SpaceSemantics.Program}
    (bindings : MORK.Subst) (valid : Idempotent bindings) (name : String)
    (expression : Atom) (returns : ReturnsVariable name expression)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (ground : MORK.isGroundAtom (resolve bindings (.var name)) = true)
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) :
    ∃ final answers,
      Relation.ReflTransGen (Transition registry)
        { state, control := .evaluate bindings expression, input, output, uses := use } final ∧
      final.control = .returned answers ∧ final.frames = [] ∧
      final.state = after ∧ final.input = remaining ∧ final.output = printed ∧
      ReturnedValue (resolve bindings (.var name)) answers ∧
      values = List.replicate answers.length (resolve bindings (.var name)) := by
  have good := evaluation_entry_refines bindings valid state expression input output use
  obtain ⟨final, answers, steps, returned, finished, finalState, finalInput, finalOutput, results, _⟩ :=
    completed_run_refines good completed
  have checked := reached_return_values steps good rfl ground
    (Or.inr ⟨ReturnFrames.nil, ReturnControl.evaluate bindings returns⟩) answers returned finished
  refine ⟨final, answers, steps, returned, finished, finalState, finalInput, finalOutput, checked, ?_⟩
  rw [results]
  have observed : answers.map (fun answer => resolve answer.bindings answer.value) =
      answers.map (fun _ => resolve bindings (.var name)) := by
    apply List.map_congr_left
    intro answer member
    rw [checked answer member]
    exact applySubst_ground answer.bindings _ ground
  rw [observed]
  exact List.map_const

namespace ReturnControls

def registry : SpaceSemantics.Program := { equations := [], declarations := [] }
def num (n : Int) : Atom := .grounded (.int n)
def call (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
def bindings : MORK.Subst := [("protected", num 7)]
def branchAndPrint : Atom := call "let" [.var "choice", call "superpose" [.expression [num 1, num 1, num 2]],
  call "let" [.var "ignored", call "println!" [.var "choice"], .var "protected"]]

theorem print_prefix_returns_protected : ReturnsVariable "protected" branchAndPrint :=
  .letE _ _ (.letE _ _ .variable)

theorem return_recognizer_controls :
    checksReturnVariable "protected" 3 branchAndPrint = true ∧
      checksReturnVariable "protected" 2 branchAndPrint = false ∧
      checksReturnVariable "protected" 3
        (call "if" [num 1, .var "protected", .symbol "Known"]) = false := by decide +kernel

theorem duplicate_answers_keep_effect_order :
    shown (run registry 200 { state := Effects.empty, control := .evaluate bindings branchAndPrint }) =
      .printed [num 1, num 1, num 2] [num 7, num 7, num 7] := by decide +kernel

def matchedRegistry : SpaceSemantics.Program where
  equations := []
  declarations := []
  facts := [call "hit" [num 1], call "hit" [num 2]]
  layout := [.fact, .fact]

def matchReturn : Atom := call "match" [.symbol "&self", call "hit" [.var "found"], .var "protected"]

theorem match_body_returns_protected : ReturnsVariable "protected" matchReturn :=
  .matchE _ _ .variable

theorem matched_occurrences_are_not_collapsed :
    observed (run matchedRegistry 200 { state := Effects.loaded matchedRegistry, control := .evaluate bindings matchReturn }) =
      .answers [num 7, num 7] := by decide +kernel

def openBindings : MORK.Subst := [("protected", .var "shared")]
def rebindOpen : Atom := call "let" [.var "shared", .symbol "Known", .var "protected"]

theorem open_return_syntax_is_not_value_stability :
    ReturnsVariable "protected" rebindOpen ∧
      MORK.isGroundAtom (resolve openBindings (.var "protected")) = false ∧
      observed (run registry 100 { state := Effects.empty, control := .evaluate openBindings rebindOpen }) =
        .answers [.symbol "Known"] := by
  refine ⟨.letE _ _ .variable, ?_, ?_⟩ <;> decide +kernel

end ReturnControls

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
