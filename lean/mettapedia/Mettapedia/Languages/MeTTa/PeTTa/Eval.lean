import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.GSLT.Core.GSLT

set_option autoImplicit false

/-!
# Executable PeTTa evaluation and finite execution laws

## Migration from the separate source modules

The former Source modules interpreted retained program text over OSLFCore.Atom.
They were introduced because lowering source into Pattern merged bare symbols
with nullary expressions, while the older PeTTaEval relation selected rewrites
without recursively running their bodies. Their contents now belong to the
existing semantic layers:

- SourceProgram: SpaceSemantics owns reading, equations and pattern selection.
- SourcePrimitives: SpaceSemantics owns queries, Effects owns storage and
  outcomes, and StdLib owns the ground primitive table.
- SourceEvaluation and SourceExecution: this module owns the machine and its
  execution laws.
- SourceOSLF: OperationalGSLT owns the executable configuration readout.
- SourceMain: Main owns the pettaRun executable.
- SourceQuotation: ProgramQuotation owns pinned text and constructor quotation.

The Pattern relations remain explicitly scoped views. The independent
whole-program judgment in DeclarativeSpec is proved adequate to this machine;
connecting the Pattern views requires a separate fragment simulation.

The machine interprets the closed, saturated fragment reached by the MM0
service. Captured values remain inert, equation alternatives retain order and
multiplicity, and case selection commits before its body runs. Effects use the
shared named-space store. Fuel exhaustion, primitive faults and completed empty
answers have different outcomes. Finite execution is equivalent to a path in
the judgment's operational graph. Native agreement and guest-kernel correctness
are separate obligations; the text reader remains a named boundary.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State Fault)
open DeclarativeSpec (Transition Runs controlForm)

/-- A source transition is chosen from syntax and the existing program, never
from a guest kernel's answer. -/
def step (program : Program) (configuration : Configuration) : Option Configuration :=
  let state := configuration.state
  let frames := configuration.frames
  let advance := fun control => some { configuration with control }
  let push := fun frame bindings expression =>
    some { configuration with control := .evaluate bindings expression, frames := frame :: frames }
  match configuration.control with
  | .fault _ => none
  | .sequence [] answers => advance (.returned answers)
  | .sequence (first :: rest) answers =>
      some { configuration with control := first, frames := .sequence rest answers :: frames }
  | .arguments _ target [] values _ =>
      match target with
      | .data => advance (.returned [.expression values])
      | .function head =>
          if ioHead head then
            match head, values with
            | "readln!", [] =>
                match configuration.input with
                | [] => advance (.returned [.symbol "end_of_file"])
                | first :: rest => some { configuration with input := rest, control := .returned [first] }
            | "println!", [value] =>
                some { configuration with
                  output := configuration.output ++ [value]
                  control := .returned [Effects.boolean true] }
            | "eval", [code] => advance (.evaluate [] code)
            | _, _ => advance (.fault (.invalidArguments head))
          else if StdLib.known head then
            match StdLib.apply state head values with
            | .ok (after, answers) => some { configuration with state := after, control := .returned answers }
            | .error fault => advance (.fault fault)
          else advance (.sequence (clauses program head values) [])
  | .arguments bindings target (first :: rest) values index =>
      let frame := Frame.argument bindings target rest values index
      let raw := match target with
        | .function head => argumentIsRaw program head index
        | .data => false
      if raw then
        some { configuration with control := .returned [applySubst bindings first], frames := frame :: frames }
      else push frame bindings first
  | .evaluate bindings expression =>
      match expression with
      | .var _ => advance (.returned [applySubst bindings expression])
      | .symbol _ | .grounded _ => advance (.returned [expression])
      | .expression [.symbol "let", pattern, value, body] =>
          push (.bind bindings pattern body) bindings value
      | .expression [.symbol "let*", .expression pairs, body] =>
          match nestedLets pairs body with
          | some nested => advance (.evaluate bindings nested)
          | none => advance (.fault (.invalidArguments "let*"))
      | .expression [.symbol "case", value, .expression rows] =>
          match readCases rows with
          | some cases => push (.select bindings cases) bindings value
          | none => advance (.fault (.invalidArguments "case"))
      | .expression [.symbol "if", condition, yes, no] =>
          push (.branch bindings yes no) bindings condition
      | .expression [.symbol "collapse", expression] => push .collect bindings expression
      | .expression [.symbol "superpose", .expression alternatives] =>
          advance (.sequence (alternatives.map (.evaluate bindings)) [])
      | .expression [.symbol "empty"] => advance (.returned [])
      | .expression [.symbol "quote", expression] =>
          advance (.returned [applySubst bindings expression])
      | .expression (.symbol head :: arguments) =>
          if ioHead head || StdLib.known head || program.equations.any (·.head == head) then
            advance (.arguments bindings (.function head) arguments [] 0)
          else advance (.arguments bindings .data (.symbol head :: arguments) [] 0)
      | .expression items => advance (.arguments bindings .data items [] 0)
  | .returned answers =>
      match frames with
      | [] => none
      | frame :: rest =>
          let resume := fun control => some { configuration with control, frames := rest }
          match frame with
          | .collect => resume (.returned [.expression answers])
          | .sequence pending collected => resume (.sequence pending (collected ++ answers))
          | .argument bindings target pending values index =>
              resume (.sequence (answers.map fun value =>
                .arguments bindings target pending (values ++ [value]) (index + 1)) [])
          | .bind bindings pattern body =>
              resume (.sequence (answers.filterMap fun value =>
                (SpaceSemantics.matchBinding bindings pattern value).map
                  fun bound => .evaluate bound body) [])
          | .select bindings cases =>
              resume (.sequence (answers.filterMap fun value =>
                (SpaceSemantics.selectCase bindings value cases).map
                  fun (bound, body) => .evaluate bound body) [])
          | .branch bindings yes no =>
              resume (.sequence (answers.map fun value =>
                .evaluate bindings (if value == Effects.boolean true then yes else no)) [])

def run (program : Program) : Nat → Configuration → Outcome
  | fuel, configuration =>
      match configuration.control, configuration.frames with
      | .returned answers, [] => .complete configuration.state answers configuration.input configuration.output
      | .fault fault, _ => .fault fault
      | _, _ =>
          match fuel with
          | 0 => .exhausted configuration
          | fuel + 1 =>
              match step program configuration with
              | some next => run program fuel next
              | none => .exhausted configuration

def start (state : State) (expression : Atom) : Configuration :=
  { state, control := .evaluate [] expression }

def evaluate (program : Program) (fuel : Nat) (state : State) (expression : Atom) : Outcome :=
  run program fuel (start state expression)

theorem transition_step {program : Program} {source target : Configuration}
    (derivation : Transition program source target) :
    step program source = some target := by
  cases derivation
  all_goals try solve | simp_all [step, controlForm, ioHead]
  case raw_argument bindings target first rest values index control raw =>
    cases target <;> simp_all [step]
  case evaluated_argument bindings target first rest values index control demanded =>
    cases target <;> simp_all [step]
  case call_enter bindings head arguments control notControl callable =>
    simp only [step, control]
    split <;> simp_all [controlForm] <;> aesop
  case data_enter bindings head arguments control notControl notCallable =>
    simp only [step, control]
    split <;> simp_all [controlForm]

theorem step_transition {program : Program} {source target : Configuration}
    (computed : step program source = some target) :
    Transition program source target := by
  cases source with
  | mk state control frames input output =>
    cases control with
    | fault reason => simp [step] at computed
    | sequence pending answers =>
      cases pending with
      | nil =>
        simp only [step, Option.some.injEq] at computed
        subst target
        exact .sequence_done rfl
      | cons first rest =>
        simp only [step, Option.some.injEq] at computed
        subst target
        exact .sequence_enter rfl
    | arguments bindings destination pending values index =>
      cases pending with
      | nil =>
        cases destination with
        | data =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .construct rfl
        | function head =>
          simp only [step] at computed
          split at computed
          · rename_i isIO
            simp [ioHead] at isIO
            rcases isIO with read | print | evaluate
            · subst head
              cases values with
              | nil =>
                cases input with
                | nil =>
                  simp at computed
                  subst target
                  exact .read_end rfl rfl
                | cons first rest =>
                  simp at computed
                  subst target
                  exact .read_line rfl rfl
              | cons first rest =>
                simp at computed
                subst target
                exact .read_bad rfl (by simp)
            · subst head
              cases values with
              | nil =>
                simp at computed
                subst target
                exact .print_bad rfl (by simp)
              | cons first rest =>
                cases rest with
                | nil =>
                  simp at computed
                  subst target
                  exact .print rfl
                | cons second rest =>
                  simp at computed
                  subst target
                  exact .print_bad rfl (by simp)
            · subst head
              cases values with
              | nil =>
                simp at computed
                subst target
                exact .eval_bad rfl (by simp)
              | cons first rest =>
                cases rest with
                | nil =>
                  simp at computed
                  subst target
                  exact .evaluate_code rfl
                | cons second rest =>
                  simp at computed
                  subst target
                  exact .eval_bad rfl (by simp)
          · rename_i ordinary
            split at computed
            · rename_i native
              split at computed
              · cases computed
                exact .primitive rfl (by simpa using ordinary) native (by assumption)
              · cases computed
                exact .primitive_fault rfl (by simpa using ordinary) native (by assumption)
            · rename_i notNative
              cases computed
              exact .equations rfl (by simpa using ordinary) (by simpa using notNative)
      | cons first rest =>
        cases destination with
        | data =>
          simp only [step, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at computed
          subst target
          exact .evaluated_argument rfl rfl
        | function head =>
          simp only [step] at computed
          split at computed
          · cases computed
            exact .raw_argument rfl (by assumption)
          · cases computed
            exact .evaluated_argument rfl (by simpa using ‹¬ argumentIsRaw program head index = true›)
    | evaluate bindings expression =>
      simp only [step] at computed
      split at computed
      · cases computed
        exact .value_variable rfl
      · cases computed
        exact .symbol rfl
      · cases computed
        exact .grounded rfl
      · cases computed
        exact .let_enter rfl
      · split at computed
        · cases computed
          exact .let_star rfl (by assumption)
        · cases computed
          exact .let_star_bad rfl (by assumption)
      · split at computed
        · cases computed
          exact .case_enter rfl (by assumption)
        · cases computed
          exact .case_bad rfl (by assumption)
      · cases computed
        exact .if_enter rfl
      · cases computed
        exact .collapse_enter rfl
      · cases computed
        exact .superpose_enter rfl
      · cases computed
        exact .empty_enter rfl
      · cases computed
        exact .quote_enter rfl
      · split at computed
        · cases computed
          apply Transition.call_enter rfl _ (by assumption)
          simp only [controlForm]
          split <;> simp_all
        · rename_i notCallable
          cases computed
          apply Transition.data_enter rfl _ (Bool.eq_false_iff.mpr notCallable)
          simp only [controlForm]
          split <;> simp_all
      · cases computed
        apply Transition.expression_enter rfl
        aesop
    | returned answers =>
      cases frames with
      | nil => simp [step] at computed
      | cons frame rest =>
        cases frame with
        | collect =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .collapse_return rfl rfl
        | sequence pending collected =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .sequence_return rfl rfl
        | argument bindings destination pending values index =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .argument_return rfl rfl
        | bind bindings pattern body =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .binding_return rfl rfl
        | select bindings rows =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .case_return rfl rfl
        | branch bindings yes no =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .if_return rfl rfl


theorem step_iff_transition (program : Program) (source target : Configuration) :
    step program source = some target ↔ Transition program source target :=
  ⟨step_transition, transition_step⟩

/-- The operational graph has the same source controls and private store as
the executable machine. Equations are literal configuration equality: lexical
binding is represented by environments, not by name-changing graph equations. -/
def theory (program : Program) : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition program
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

/-- The one GSLT is generated from the declarative rules. This theorem is the
executable interface to that graph, not a second GSLT construction. -/
@[simp] theorem theory_step_iff (program : Program) (source target : Configuration) :
    (theory program).Step source target ↔ step program source = some target :=
  (step_iff_transition program source target).symm

/-- A configuration reads only the program's dispatch, argument demand and
selected equation bodies. Agreement is required at the control being executed;
an extension may introduce unrelated functions. -/
structure ProgramAgreementAt (first second : Program) (source : Configuration) : Prop where
  dispatch : ∀ bindings head arguments,
    source.control = .evaluate bindings (.expression (.symbol head :: arguments)) →
      first.equations.any (·.head == head) = second.equations.any (·.head == head)
  demand : ∀ bindings head argument pending values index,
    source.control = .arguments bindings (.function head) (argument :: pending) values index →
      argumentIsRaw first head index = argumentIsRaw second head index
  bodies : ∀ bindings head values index,
    source.control = .arguments bindings (.function head) [] values index →
      clauses first head values = clauses second head values

theorem step_eq_of_program_agreement {first second : Program} {source : Configuration}
    (agreement : ProgramAgreementAt first second source) :
    step first source = step second source := by
  rcases agreement with ⟨dispatch, demand, bodies⟩
  cases source with
  | mk state control frames input output =>
      cases control with
      | fault reason => rfl
      | sequence pending answers => cases pending <;> rfl
      | returned answers => rfl
      | arguments bindings target pending values index =>
          cases target with
          | data => cases pending <;> rfl
          | function head =>
              cases pending with
              | nil =>
                  have same := bodies bindings head values index rfl
                  simp only [step]
                  rw [same]
              | cons argument rest =>
                  have same := demand bindings head argument rest values index rfl
                  simp only [step]
                  rw [same]
      | evaluate bindings expression =>
          cases expression with
          | var name => rfl
          | symbol name => rfl
          | grounded value => rfl
          | expression items =>
              simp only [step]
              split <;> try rfl
              rename_i _ head arguments _ _ _ _ _ _ _ _ shape
              rw [dispatch bindings head arguments (congrArg (Control.evaluate bindings) shape)]

/-- Transport a finite path after checking the program observations along it.
The initial and final configurations, ordered answers and private store are
retained exactly. -/
theorem path_of_program_agreement {first second : Program} :
    {source target : Configuration} →
    (theory first).MultiStep source target →
    (∀ current, (theory first).MultiStep source current →
      (theory first).MultiStep current target → ProgramAgreementAt first second current) →
    (theory second).MultiStep source target
  | _, _, .refl current, _ =>
      Mettapedia.GSLT.GSLT.MultiStep.refl (S := theory second) current
  | _, _, .step transition rest, agreement => by
      have agreed := agreement _ (.refl _) (.step transition rest)
      have moved := (theory_step_iff second _ _).mpr
        ((step_eq_of_program_agreement agreed).symm.trans (transition_step transition))
      refine Mettapedia.GSLT.GSLT.MultiStep.step (S := theory second) moved
        (path_of_program_agreement rest ?_)
      intro intermediate before after
      exact agreement intermediate (.step transition before) after

/-- The literal application head of a code expression. Values held in an
environment are not inspected: returning a captured value does not execute it.
The dynamic `eval` operation requires a separate code-support premise. -/
def expressionHeadWithin (allowed : String → Bool) : List Atom → Bool
  | .symbol head :: _ => allowed head && head != "eval"
  | _ => true

mutual
  def codeWithin (allowed : String → Bool) : Atom → Bool
    | .expression items => expressionHeadWithin allowed items && atomsWithin allowed items
    | _ => true

  def atomsWithin (allowed : String → Bool) : List Atom → Bool
    | [] => true
    | first :: rest => codeWithin allowed first && atomsWithin allowed rest
end

@[simp] theorem atomsWithin_eq_all (allowed : String → Bool) (items : List Atom) :
    atomsWithin allowed items = items.all (codeWithin allowed) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [atomsWithin, List.all_cons, ih]

def targetWithin (allowed : String → Bool) : Target → Bool
  | .data => true
  | .function head => allowed head && head != "eval"

mutual
  def controlWithin (allowed : String → Bool) : Control → Bool
    | .evaluate _ code => codeWithin allowed code
    | .arguments _ target pending _ _ => targetWithin allowed target && atomsWithin allowed pending
    | .sequence pending _ => controlsWithin allowed pending
    | .returned _ | .fault _ => true

  def controlsWithin (allowed : String → Bool) : List Control → Bool
    | [] => true
    | first :: rest => controlWithin allowed first && controlsWithin allowed rest
end

@[simp] theorem controlsWithin_eq_all (allowed : String → Bool) (items : List Control) :
    controlsWithin allowed items = items.all (controlWithin allowed) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [controlsWithin, List.all_cons, ih]

def frameWithin (allowed : String → Bool) : Frame → Bool
  | .collect => true
  | .sequence pending _ => controlsWithin allowed pending
  | .argument _ target pending _ _ => targetWithin allowed target && atomsWithin allowed pending
  | .bind _ _ body => codeWithin allowed body
  | .select _ cases => cases.all (fun row => codeWithin allowed row.2)
  | .branch _ yes no => codeWithin allowed yes && codeWithin allowed no

/-- Only pending code and continuation bodies constrain execution. Stores,
answers and captured environments remain ordinary data of the same machine. -/
def configurationWithin (allowed : String → Bool) (configuration : Configuration) : Prop :=
  controlWithin allowed configuration.control = true ∧
    configuration.frames.all (frameWithin allowed) = true

structure ProgramClosed (allowed : String → Bool) (program : Program) : Prop where
  binding : allowed "let" = true
  bodies : ∀ equation ∈ program.equations, allowed equation.head = true →
    codeWithin allowed equation.body = true

theorem nestedLets_within (allowed : String → Bool) (binding : allowed "let" = true)
    {pairs : List Atom} {body nested : Atom}
    (expanded : nestedLets pairs body = some nested)
    (pairCodes : atomsWithin allowed pairs = true) (bodyCode : codeWithin allowed body = true) :
    codeWithin allowed nested = true := by
  induction pairs generalizing nested with
  | nil =>
      simp only [nestedLets, Option.some.injEq] at expanded
      subst nested
      exact bodyCode
  | cons first rest ih =>
      cases first <;> try simp only [nestedLets] at expanded
      all_goals try contradiction
      rename_i items
      cases items with
      | nil => contradiction
      | cons pattern tail =>
          cases tail with
          | nil => contradiction
          | cons value tail =>
              cases tail with
              | cons _ _ => contradiction
              | nil =>
                  cases result : nestedLets rest body with
                  | none => simp [nestedLets, result] at expanded
                  | some following =>
                      simp only [nestedLets, result] at expanded
                      change some (.expression [.symbol "let", pattern, value, following]) = some nested at expanded
                      have same := Option.some.inj expanded
                      subst nested
                      have codes := pairCodes
                      simp only [atomsWithin, codeWithin, Bool.and_eq_true] at codes
                      have tailCode := ih result codes.2
                      simp [codeWithin, expressionHeadWithin, atomsWithin, binding,
                        codes.1.2.1, codes.1.2.2.1, tailCode]

theorem readCases_within (allowed : String → Bool) {rows : List Atom} {cases : Cases}
    (parsed : readCases rows = some cases) (codes : atomsWithin allowed rows = true) :
    cases.all (fun row => codeWithin allowed row.2) = true := by
  induction rows generalizing cases with
  | nil =>
      simp only [readCases, Option.some.injEq] at parsed
      subst cases
      rfl
  | cons first rest ih =>
      cases first <;> try simp only [readCases] at parsed
      all_goals try contradiction
      rename_i items
      cases items with
      | nil => contradiction
      | cons pattern tail =>
          cases tail with
          | nil => contradiction
          | cons body tail =>
              cases tail with
              | cons _ _ => contradiction
              | nil =>
                  cases result : readCases rest with
                  | none => simp [readCases, result] at parsed
                  | some following =>
                      simp only [readCases, result] at parsed
                      change some ((pattern, body) :: following) = some cases at parsed
                      have same := Option.some.inj parsed
                      subst cases
                      have supported := codes
                      simp only [atomsWithin, codeWithin, Bool.and_eq_true] at supported
                      simp only [List.all_cons, Bool.and_eq_true]
                      exact ⟨supported.1.2.2.1, ih result supported.2⟩

theorem selected_body_within (allowed : String → Bool) {bindings bound : Subst}
    {value body : Atom} {cases : Cases}
    (selected : SpaceSemantics.Selected bindings value cases bound body)
    (codes : cases.all (fun row => codeWithin allowed row.2) = true) :
    codeWithin allowed body = true := by
  induction selected with
  | first _ =>
      simp only [List.all_cons, Bool.and_eq_true] at codes
      exact codes.1
  | later _ _ ih =>
      simp only [List.all_cons, Bool.and_eq_true] at codes
      exact ih codes.2

theorem clauses_within (allowed : String → Bool) {program : Program} {head : String}
    (closed : ProgramClosed allowed program) (supported : allowed head = true) (values : List Atom) :
    controlsWithin allowed (clauses program head values) = true := by
  rw [controlsWithin_eq_all, List.all_eq_true]
  intro control member
  unfold clauses at member
  obtain ⟨equation, equationMember, selected⟩ := List.mem_filterMap.mp member
  by_cases same : equation.head = head
  · simp only [same, if_true] at selected
    cases matched : SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values) with
    | none => simp [matched] at selected
    | some bindings =>
        simp only [matched, Option.map_some, Option.some.injEq] at selected
        subst control
        exact closed.bodies equation equationMember (same ▸ supported)
  · simp [same] at selected

theorem transition_within {allowed : String → Bool} {program : Program}
    {source target : Configuration} (closed : ProgramClosed allowed program)
    (transition : Transition program source target)
    (within : configurationWithin allowed source) : configurationWithin allowed target := by
  rcases within with ⟨controlCode, frameCodes⟩
  cases transition
  all_goals simp only [configurationWithin]
  all_goals try solve |
    simp_all [controlWithin, controlsWithin, frameWithin, targetWithin,
      codeWithin, atomsWithin, expressionHeadWithin, Bool.and_eq_true]
  case equations bindings head index values control _ _ =>
    rw [control] at controlCode
    simp only [controlWithin, targetWithin, atomsWithin, Bool.and_true,
      Bool.and_eq_true] at controlCode
    exact ⟨clauses_within allowed closed controlCode.1 values, frameCodes⟩
  case let_star bindings pairs body nested control expanded =>
    refine ⟨nestedLets_within allowed closed.binding expanded ?_ ?_, frameCodes⟩
    all_goals
      simp_all [controlWithin, codeWithin, atomsWithin, expressionHeadWithin, Bool.and_eq_true]
  case case_enter bindings value rows cases control parsed =>
    constructor
    · simp_all [controlWithin, codeWithin, atomsWithin, expressionHeadWithin, Bool.and_eq_true]
    · simp only [List.all_cons, frameWithin, Bool.and_eq_true]
      refine ⟨readCases_within allowed parsed ?_, frameCodes⟩
      simp_all [controlWithin, codeWithin, atomsWithin, expressionHeadWithin, Bool.and_eq_true]
  case binding_return answers bindings pattern body rest _ frames =>
    rw [frames] at frameCodes
    simp only [List.all_cons, frameWithin, Bool.and_eq_true] at frameCodes
    refine ⟨?_, frameCodes.2⟩
    rw [controlWithin, controlsWithin_eq_all, List.all_eq_true]
    intro control member
    obtain ⟨value, _, mapped⟩ := List.mem_filterMap.mp member
    cases matched : SpaceSemantics.matchBinding bindings pattern value with
    | none => simp [matched] at mapped
    | some bound =>
        simp only [matched, Option.map_some, Option.some.injEq] at mapped
        subst control
        exact frameCodes.1
  case case_return answers bindings cases rest _ frames =>
    rw [frames] at frameCodes
    simp only [List.all_cons, frameWithin, Bool.and_eq_true] at frameCodes
    refine ⟨?_, frameCodes.2⟩
    rw [controlWithin, controlsWithin_eq_all, List.all_eq_true]
    intro control member
    obtain ⟨value, _, mapped⟩ := List.mem_filterMap.mp member
    cases chosen : SpaceSemantics.selectCase bindings value cases with
    | none => simp [chosen] at mapped
    | some selected =>
        rcases selected with ⟨bound, body⟩
        simp only [chosen, Option.map_some, Option.some.injEq] at mapped
        subst control
        exact selected_body_within allowed (SpaceSemantics.selectCase_sound chosen) frameCodes.1
  case if_return answers bindings yes no rest _ frames =>
    rw [frames] at frameCodes
    simp only [List.all_cons, frameWithin, Bool.and_eq_true] at frameCodes
    refine ⟨?_, frameCodes.2⟩
    simp only [controlWithin, controlsWithin_eq_all, List.all_map, List.all_eq_true]
    intro value _
    change codeWithin allowed (if value == Effects.boolean true then yes else no) = true
    split
    · exact frameCodes.1.1
    · exact frameCodes.1.2

/-- A finite execution retains the code support earned at its start. -/
theorem path_within {allowed : String → Bool} {program : Program}
    (closed : ProgramClosed allowed program) :
    {source target : Configuration} → (theory program).MultiStep source target →
    configurationWithin allowed source → configurationWithin allowed target
  | _, _, .refl _, within => within
  | _, _, .step transition rest, within =>
      path_within closed rest (transition_within closed transition within)

/-- Static agreement can be checked on the supported function heads, before
running the machine. -/
structure ProgramAgreementOn (allowed : String → Bool) (first second : Program) : Prop where
  dispatch : ∀ head, allowed head = true →
    first.equations.any (·.head == head) = second.equations.any (·.head == head)
  demand : ∀ head index, allowed head = true →
    argumentIsRaw first head index = argumentIsRaw second head index
  bodies : ∀ head values, allowed head = true →
    clauses first head values = clauses second head values

theorem configuration_agreement_on {allowed : String → Bool} {first second : Program}
    {source : Configuration} (agreement : ProgramAgreementOn allowed first second)
    (within : configurationWithin allowed source) : ProgramAgreementAt first second source := by
  constructor
  · intro bindings head arguments shape
    have supported := within.1
    rw [shape] at supported
    simp only [controlWithin, codeWithin, expressionHeadWithin, atomsWithin,
      Bool.true_and, Bool.and_eq_true] at supported
    exact agreement.dispatch head supported.1.1
  · intro bindings head argument pending values index shape
    have supported := within.1
    rw [shape] at supported
    simp only [controlWithin, targetWithin, Bool.and_eq_true] at supported
    exact agreement.demand head index supported.1.1
  · intro bindings head values index shape
    have supported := within.1
    rw [shape] at supported
    simp only [controlWithin, targetWithin, atomsWithin, Bool.and_true,
      Bool.and_eq_true] at supported
    exact agreement.bodies head values supported.1

/-- An extension preserves every finite execution whose supported source
bodies and pending code were checked independently. Captured arguments and
the entire resulting store, answers and I/O are retained literally. -/
theorem path_of_closed_agreement {allowed : String → Bool} {first second : Program}
    {source target : Configuration} (closed : ProgramClosed allowed first)
    (agreement : ProgramAgreementOn allowed first second)
    (within : configurationWithin allowed source)
    (path : (theory first).MultiStep source target) : (theory second).MultiStep source target := by
  apply path_of_program_agreement path
  intro current before _
  exact configuration_agreement_on agreement (path_within closed before within)

theorem appended_program_agreement (allowed : String → Bool) (first extension : Program)
    (freshEquations : ∀ equation ∈ extension.equations, allowed equation.head = false)
    (freshDeclarations : ∀ name types,
      .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)] ∈
        extension.declarations → allowed name = false) :
    ProgramAgreementOn allowed first (first.append extension) := by
  have unequal (head : String) (supported : allowed head = true)
      (equation : SpaceSemantics.Equation) (member : equation ∈ extension.equations) :
      equation.head ≠ head := by
    intro same
    have fresh := freshEquations equation member
    rw [same, supported] at fresh
    contradiction
  constructor
  · intro head supported
    have absent : extension.equations.any (·.head == head) = false := by
      rw [List.any_eq_false]
      intro equation member
      simp [unequal head supported equation member]
    simp only [SpaceSemantics.Program.append, List.any_append, absent, Bool.or_false]
  · intro head index supported
    by_cases native : StdLib.known head = true
    · simp [argumentIsRaw, native]
    · have notNative : StdLib.known head = false := Bool.eq_false_iff.mpr native
      have combination : argumentIsRaw (first.append extension) head index =
          (argumentIsRaw first head index || argumentIsRaw extension head index) := by
        simp only [argumentIsRaw, notNative, Bool.false_eq_true, ↓reduceIte,
          SpaceSemantics.Program.append, List.any_append]
      have absent : argumentIsRaw extension head index = false := by
        simp only [argumentIsRaw, notNative, Bool.false_eq_true, ↓reduceIte]
        rw [List.any_eq_false]
        intro declaration member
        split
        · rename_i _ name types
          have different : name ≠ head := by
            intro same
            have fresh := freshDeclarations name types member
            rw [same, supported] at fresh
            contradiction
          simp [different]
        · simp
      rw [combination, absent, Bool.or_false]
  · intro head values supported
    have absent : clauses extension head values = [] := by
      unfold clauses
      rw [List.filterMap_eq_nil_iff]
      intro equation member
      simp [unequal head supported equation member]
    simp only [clauses, SpaceSemantics.Program.append, List.filterMap_append]
    change clauses first head values = clauses first head values ++ clauses extension head values
    rw [absent, List.append_nil]

theorem captured_values_need_no_code_support (allowed : String → Bool) (bindings : Subst)
    (state : State) (name : String) :
    configurationWithin allowed { state, control := .evaluate bindings (.var name) } := ⟨rfl, rfl⟩

theorem dynamic_eval_requires_separate_support (allowed : String → Bool) (code : Atom) :
    codeWithin allowed (.expression [.symbol "eval", code]) = false := by
  simp [codeWithin, expressionHeadWithin]

/-- Fresh function definitions can change a previously inert data expression;
the agreement restriction is necessary for execution transport. -/
theorem an_extension_can_activate_data (state : State) :
    (step { equations := [], declarations := [] }
      { state, control := .evaluate [] (.expression [.symbol "fresh-function"]) }).map
        (·.control) ≠
    (step { equations := [⟨"fresh-function", [], .grounded (.int 1)⟩], declarations := [] }
      { state, control := .evaluate [] (.expression [.symbol "fresh-function"]) }).map
        (·.control) := by
  simp [step, ioHead, StdLib.known]

theorem step_deterministic (program : Program) (source first second : Configuration)
    (left : (theory program).Step source first)
    (right : (theory program).Step source second) : first = second :=
  Option.some.inj ((transition_step left).symm.trans (transition_step right))

/-! ## Control boundaries -/

theorem computed_pattern_is_outside_the_profile :
    passivePattern { equations := [⟨"compute", [.var "x"], .var "x"⟩], declarations := [] }
      (.expression [.symbol "Some", .expression [.symbol "compute", .grounded (.int 7)]]) =
      false := by
  simp [passivePattern, SpaceSemantics.patternHeads, SpaceSemantics.patternHeads.nested]

theorem constructor_pattern_is_in_the_profile :
    passivePattern { equations := [⟨"compute", [.var "x"], .var "x"⟩], declarations := [] }
      (.expression [.symbol "Some", .expression [.var "head", .grounded (.int 7)]]) = true := by
  simp [passivePattern, SpaceSemantics.patternHeads, SpaceSemantics.patternHeads.nested]
  decide

theorem list_view_pattern_is_in_the_profile :
    passivePattern { equations := [], declarations := [] }
      (.expression [.symbol "cons", .var "first", .var "rest"]) = true := by
  simp [passivePattern, SpaceSemantics.patternHeads, SpaceSemantics.patternHeads.nested]

theorem value_occurrence_is_inert (program : Program) (state : State) (bindings : Subst)
    (name : String) (frames : List Frame) :
    step program { state, control := .evaluate bindings (.var name), frames } =
      some { state, control := .returned [applySubst bindings (.var name)], frames } := rfl

theorem completed_empty_is_not_exhausted (program : Program) (fuel : Nat) (state : State) :
    run program fuel { state, control := .returned [], frames := [] } = .complete state [] [] [] := by
  cases fuel <;> simp [run]

theorem returned_false_is_completed (program : Program) (fuel : Nat) (state : State) :
    run program fuel { state, control := .returned [Effects.boolean false], frames := [] } =
      .complete state [Effects.boolean false] [] [] := by
  cases fuel <;> simp [run]

theorem unfinished_zero_fuel (program : Program) (state : State) (expression : Atom) :
    evaluate program 0 state expression = .exhausted (start state expression) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Eval

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open SpaceSemantics (Program)
open Effects (State Fault)
open Eval
open DeclarativeSpec (Transition Runs controlForm)

def finished (state : State) (answers input output : List Atom) : Configuration :=
  { state, control := .returned answers, input, output }

@[simp] theorem run_finished (program : Program) (fuel : Nat)
    (state : State) (answers input output : List Atom) :
    run program fuel (finished state answers input output) =
      .complete state answers input output := by
  cases fuel <;> simp [run, finished]

theorem run_succ_of_step (program : Program) (fuel : Nat)
    (source target : Configuration) (transition : step program source = some target) :
    run program (fuel + 1) source = run program fuel target := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals try solve | simp [step] at transition
      all_goals simp only [run, transition]

theorem derivation_has_run {program : Program} {source : Configuration} {result : Outcome}
    (derivation : Runs program source result) :
    ∃ fuel, run program fuel source = result := by
  induction derivation with
  | completed control frames =>
    refine ⟨0, ?_⟩
    rename_i source answers
    cases source
    simp_all [run]
  | fault control =>
    refine ⟨0, ?_⟩
    rename_i source reason
    cases source
    simp_all [run]
  | next transition _ ih =>
    obtain ⟨fuel, computed⟩ := ih
    exact ⟨fuel + 1, (run_succ_of_step _ _ _ _ (transition_step transition)).trans computed⟩

theorem run_has_derivation (program : Program) (fuel : Nat) (source : Configuration)
    (result : Outcome) (notExhausted : ∀ unfinished, result ≠ .exhausted unfinished)
    (computed : run program fuel source = result) :
    Runs program source result := by
  induction fuel generalizing source with
  | zero =>
    cases source with
    | mk state control frames input output =>
      cases control <;> cases frames <;> simp only [run] at computed
      all_goals first
        | exact False.elim (notExhausted _ computed.symm)
        | (subst result; exact .completed rfl rfl)
        | (subst result; exact .fault rfl)
  | succ fuel ih =>
    have advance (current : Configuration)
        (computed : run program (fuel + 1) current = result)
        (unfolded : run program (fuel + 1) current =
          match step program current with
          | some next => run program fuel next
          | none => .exhausted current) :
        Runs program current result := by
      rw [unfolded] at computed
      cases transition : step program current with
      | none =>
        simp only [transition] at computed
        exact False.elim (notExhausted _ computed.symm)
      | some next =>
        exact .next (step_transition transition) (ih next (by simpa [transition] using computed))
    cases source with
    | mk state control frames input output =>
      cases control <;> cases frames
      all_goals try solve
        | simp only [run] at computed
          subst result
          first | exact .completed rfl rfl | exact .fault rfl
      all_goals exact advance _ computed rfl

/-- The executable runner and the whole-program judgment agree on the entire
store and the ordered answer, remaining-input and output observations. -/
theorem completed_run_iff_derivation (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel source = .complete state answers input output) ↔
      Runs program source (.complete state answers input output) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact run_has_derivation program fuel source _ (by simp) computed
  · exact derivation_has_run

/-- Primitive faults have their own derivations; they are distinct from a
completed empty answer list and from running out of fuel. -/
theorem fault_run_iff_derivation (program : Program) (source : Configuration)
    (reason : Fault) :
    (∃ fuel, run program fuel source = .fault reason) ↔ Runs program source (.fault reason) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact run_has_derivation program fuel source _ (by simp) computed
  · exact derivation_has_run

theorem path_lifts_completed_run (program : Program) {source target : Configuration}
    (path : (theory program).MultiStep source target) (fuel : Nat)
    (state : State) (answers input output : List Atom)
    (completed : run program fuel target = .complete state answers input output) :
    ∃ fuel, run program fuel source = .complete state answers input output := by
  have lift {system : Mettapedia.GSLT.GSLT} {property : system.Term → Prop}
      (backwards : ∀ {first second}, system.Step first second → property second → property first)
      {first last} (path : system.MultiStep first last) (atLast : property last) :
      property first := by
    induction path with
    | refl _ => exact atLast
    | step transition _ ih => exact backwards transition (ih atLast)
  apply lift (system := theory program)
    (property := fun configuration =>
      ∃ fuel, run program fuel configuration = .complete state answers input output)
    (path := path) (atLast := ⟨fuel, completed⟩)
  intro first second transition ⟨fuel, completed⟩
  exact ⟨fuel + 1, (run_succ_of_step program fuel first second (transition_step transition)).trans completed⟩

theorem path_has_sufficient_fuel (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom)
    (path : (theory program).MultiStep source (finished state answers input output)) :
    ∃ fuel, run program fuel source = .complete state answers input output :=
  path_lifts_completed_run program path 0 state answers input output (run_finished ..)

theorem completed_run_has_path (program : Program) (fuel : Nat)
    (source : Configuration) (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    (theory program).MultiStep source (finished state answers input output) := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames <;> simp only [run] at completed
          all_goals first | contradiction | cases completed; exact .refl _
  | succ fuel ih =>
      have advance (current : Configuration)
          (completed : run program (fuel + 1) current = .complete state answers input output)
          (unfolded : run program (fuel + 1) current =
            match step program current with
            | some next => run program fuel next
            | none => .exhausted current) :
          (theory program).MultiStep current (finished state answers input output) := by
        rw [unfolded] at completed
        cases transition : step program current with
        | none => simp [transition] at completed
        | some next =>
            exact .step (step_transition transition) (ih next (by simpa [transition] using completed))
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames
          all_goals try solve | simp only [run] at completed; cases completed; all_goals exact .refl _
          all_goals exact advance _ completed rfl

theorem completed_run_iff_path (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel source = .complete state answers input output) ↔
      (theory program).MultiStep source (finished state answers input output) :=
  ⟨fun ⟨fuel, completed⟩ => completed_run_has_path program fuel source state answers input output completed,
    path_has_sufficient_fuel program source state answers input output⟩

/-- Finite derivations are precisely paths to the completed observation in
this one GSLT, generated from the operational rules. -/
theorem completed_derivation_iff_path (program : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    Runs program source (.complete state answers input output) ↔
      (theory program).MultiStep source (finished state answers input output) :=
  (completed_run_iff_derivation program source state answers input output).symm.trans
    (completed_run_iff_path program source state answers input output)

theorem completed_run_more_fuel (program : Program) (fuel extra : Nat)
    (source : Configuration) (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    run program (fuel + extra) source = .complete state answers input output := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames <;> simp only [run] at completed
          all_goals first
            | contradiction
            | cases completed
              all_goals cases extra <;> rfl
  | succ fuel ih =>
      have advance (current : Configuration)
          (completed : run program (fuel + 1) current = .complete state answers input output)
          (unfolded : run program (fuel + 1) current =
            match step program current with
            | some next => run program fuel next
            | none => .exhausted current) :
          run program (fuel + 1 + extra) current = .complete state answers input output := by
        rw [unfolded] at completed
        cases transition : step program current with
        | none => simp [transition] at completed
        | some next =>
            have later := ih next (by simpa [transition] using completed)
            simpa [Nat.add_right_comm] using
              (run_succ_of_step program (fuel + extra) current next transition).trans later
      cases source with
      | mk initial control frames pending printed =>
          cases control <;> cases frames
          all_goals try solve
            | simp only [run] at completed
              cases completed
              all_goals exact run_finished program (fuel + 1 + extra) state answers input output
          all_goals exact advance _ completed rfl

theorem completed_result_unique (program : Program) (firstFuel secondFuel : Nat)
    (source : Configuration) (first second : State)
    (firstAnswers firstInput firstOutput secondAnswers secondInput secondOutput : List Atom)
    (one : run program firstFuel source = .complete first firstAnswers firstInput firstOutput)
    (two : run program secondFuel source = .complete second secondAnswers secondInput secondOutput) :
    first = second ∧ firstAnswers = secondAnswers ∧
      firstInput = secondInput ∧ firstOutput = secondOutput := by
  have left := completed_run_more_fuel program firstFuel secondFuel source first
    firstAnswers firstInput firstOutput one
  have right := completed_run_more_fuel program secondFuel firstFuel source second
    secondAnswers secondInput secondOutput two
  rw [Nat.add_comm secondFuel firstFuel] at right
  exact Outcome.complete.inj (left.symm.trans right)

/-- Caller frames are suspended beneath the current computation. -/
def withFrames (configuration : Configuration) (caller : List Frame) : Configuration :=
  { configuration with frames := configuration.frames ++ caller }

theorem step_with_caller_frames (program : Program) (source target : Configuration)
    (caller : List Frame) (transition : step program source = some target) :
    step program (withFrames source caller) = some (withFrames target caller) := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals simp only [withFrames, step, List.nil_append, List.cons_append]
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve | cases transition; simp_all

theorem path_with_caller_frames (program : Program) (caller : List Frame) :
    {source target : Configuration} → (theory program).MultiStep source target →
      (theory program).MultiStep (withFrames source caller) (withFrames target caller)
  | _, _, .refl _ => .refl _
  | _, _, .step transition rest =>
      .step (step_transition (step_with_caller_frames program _ _ caller (transition_step transition)))
        (path_with_caller_frames program caller rest)

theorem completed_computation_in_caller (program : Program) (fuel : Nat)
    (source : Configuration) (caller : List Frame)
    (state : State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    (theory program).MultiStep (withFrames source caller)
      (withFrames (finished state answers input output) caller) :=
  path_with_caller_frames program caller
    (completed_run_has_path program fuel source state answers input output completed)

/-! ## Composition of single-answer computations

These laws use the source machine's paths and frames. They do not prescribe a
guest algorithm. A function proof can compose its actual expression bodies
without unfolding the caller or expanding a stored proof into certificates.
-/

private theorem path_trans {system : Mettapedia.GSLT.GSLT}
    {first middle last : system.Term}
    (one : system.MultiStep first middle) (two : system.MultiStep middle last) :
    system.MultiStep first last := by
  induction one with
  | refl _ => exact two
  | step transition _ ih => exact .step transition (ih two)

/-- Ordered answers, retaining both repeated occurrences and empty results. -/
abbrev Returns (program : Program) (bindings : MORK.Subst)
    (before : State) (expression : Atom) (after : State) (answers : List Atom) : Prop :=
  (theory program).MultiStep { state := before, control := .evaluate bindings expression }
    (finished after answers [] [])

abbrev PureReturns (program : Program) (bindings : MORK.Subst)
    (before : State) (expression : Atom) (after : State) (value : Atom) : Prop :=
  Returns program bindings before expression after [value]

theorem variable_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (name : String) :
    PureReturns program bindings state (.var name) state (MORK.applySubst bindings (.var name)) :=
  .step (step_transition rfl) (.refl _)

theorem symbol_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (name : String) :
    PureReturns program bindings state (.symbol name) state (.symbol name) :=
  .step (step_transition rfl) (.refl _)

theorem grounded_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    PureReturns program bindings state (.grounded value) state (.grounded value) :=
  .step (step_transition rfl) (.refl _)

/-- Empty alternatives complete without producing a value or changing the store. -/
theorem empty_returns (program : Program) (bindings : MORK.Subst) (state : State) :
    Returns program bindings state (.expression [.symbol "empty"]) state [] :=
  .step (.empty_enter rfl) (.refl _)

/-- Quotation substitutes captured values and leaves executable heads inert. -/
theorem quote_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (expression : Atom) :
    PureReturns program bindings state (.expression [.symbol "quote", expression]) state
      (MORK.applySubst bindings expression) :=
  .step (.quote_enter rfl) (.refl _)

/-- Literal superposition evaluates its alternatives in the caller's environment
using the same ordered, state-threading sequence as equation alternatives. -/
theorem superpose_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (alternatives answers : List Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .sequence (alternatives.map (.evaluate bindings)) [] }
      (finished after answers [] [])) :
    Returns program bindings before
      (.expression [.symbol "superpose", .expression alternatives]) after answers :=
  .step (.superpose_enter rfl) computed

/-- Ordered sequencing adapted from PLeaTTa's `RunsMany.cons` law
(`godelclaw/LeaTTa` at `64a6ae3`). This statement is about the existing
configuration machine: the second control sees the first control's store,
and every occurrence is appended before the tail runs. -/
theorem sequence_cons_answers (program : Program) (before middle after : State)
    (control : Control) (pending : List Control) (collected answers result : List Atom)
    (head : (theory program).MultiStep { state := before, control }
      (finished middle answers [] []))
    (tail : (theory program).MultiStep
      { state := middle, control := .sequence pending (collected ++ answers) }
      (finished after result [] [])) :
    (theory program).MultiStep
      { state := before, control := .sequence (control :: pending) collected }
      (finished after result [] []) := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.sequence pending collected] head) ?_)
  exact .step (step_transition rfl) tail

theorem single_sequence_answers (program : Program) (before after : State)
    (control : Control) (value : List Atom)
    (computed : (theory program).MultiStep { state := before, control }
      (finished after value [] [])) :
    (theory program).MultiStep { state := before, control := .sequence [control] [] }
      (finished after value [] []) := by
  exact sequence_cons_answers program before after after control [] [] value value
    computed (.step (step_transition rfl) (.refl _))


theorem single_sequence_returns (program : Program) (before after : State)
    (control : Control) (value : Atom)
    (computed : (theory program).MultiStep { state := before, control }
      (finished after [value] [] [])) :
    (theory program).MultiStep { state := before, control := .sequence [control] [] }
      (finished after [value] [] []) :=
  single_sequence_answers program before after control [value] computed


/-- Collection preserves the exact ordered occurrence list, not its set. -/
theorem collapse_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (expression : Atom) (answers : List Atom)
    (returned : Returns program bindings before expression after answers) :
    PureReturns program bindings before (.expression [.symbol "collapse", expression]) after
      (.expression answers) := by
  refine .step (step_transition rfl) (path_trans (path_with_caller_frames program [.collect] returned) ?_)
  exact .step (step_transition rfl) (.refl _)

theorem let_returns (program : Program) (bindings bound : MORK.Subst)
    (before middle after : State) (pattern expression body value answer : Atom)
    (first : PureReturns program bindings before expression middle value)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound)
    (second : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let", pattern, expression, body]) after answer := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] first) ?_)
  refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer second)
  apply step_transition

  simp [withFrames, finished, step, matched]

/-- Sequential binding uses the existing nested-let elaboration and preserves
the whole returned state and answer observation. -/
theorem let_star_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (pairs : List Atom) (body nested answer : Atom)
    (expanded : nestedLets pairs body = some nested)
    (returned : PureReturns program bindings before nested after answer) :
    PureReturns program bindings before
      (.expression [.symbol "let*", .expression pairs, body]) after answer := by
  refine .step ?_ returned
  apply step_transition
  simp [step, expanded]

/-- Entering the body records its caller, without assuming that body returns. -/
theorem let_enters (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (pattern expression body value : Atom)
    (computed : PureReturns program bindings before expression after value)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "let", pattern, expression, body]) }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.bind bindings pattern body] computed) ?_)
  have entered : (theory program).Step
      { state := after, control := .sequence [.evaluate bound body] [] }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := step_transition rfl
  refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
    ?_ (.step entered (.refl _))
  apply step_transition

  simp [withFrames, finished, step, matched]

theorem let_reaches (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (pattern expression body value : Atom) (target : Configuration)
    (computed : PureReturns program bindings before expression after value)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound)
    (continuation : (theory program).MultiStep
      { state := after, control := .evaluate bound body } target) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "let", pattern, expression, body]) }
      (withFrames target [.sequence [] []]) :=
  path_trans (let_enters program bindings bound before after pattern expression body value computed matched)
    (path_with_caller_frames program [.sequence [] []] continuation)

theorem read_cases_encoded (cases : SpaceSemantics.Cases) :
    readCases (cases.map fun row => .expression [row.1, row.2]) = some cases := by
  induction cases with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      simp [readCases, ih]

theorem case_returns (program : Program) (bindings bound : MORK.Subst)
    (before middle after : State) (expression value body answer : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : readCases rows = some cases)
    (first : PureReturns program bindings before expression middle value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (second : PureReturns program bound middle body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "case", expression, .expression rows]) after answer := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] first) ?_)
  · apply step_transition
    simp [step, withFrames, decoded]
  · refine .step ?_ (single_sequence_returns program middle after (.evaluate bound body) answer second)
    apply step_transition

    simp [withFrames, finished, step, selected]

theorem case_enters (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (expression value body : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program bindings before expression after value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body)) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "case", expression, .expression rows]) }
      { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := by
  refine .step ?_
    (path_trans (path_with_caller_frames program [.select bindings cases] computed) ?_)
  · apply step_transition
    simp [step, withFrames, decoded]
  · have entered : (theory program).Step
        { state := after, control := .sequence [.evaluate bound body] [] }
        { state := after, control := .evaluate bound body, frames := [.sequence [] []] } := step_transition rfl
    refine .step (u := ({ state := after, control := .sequence [.evaluate bound body] [] } : Configuration))
      ?_ (.step entered (.refl _))
    apply step_transition

    simp [withFrames, finished, step, selected]

theorem case_reaches (program : Program) (bindings bound : MORK.Subst)
    (before after : State) (expression value body : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases) (target : Configuration)
    (decoded : readCases rows = some cases)
    (computed : PureReturns program bindings before expression after value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (continuation : (theory program).MultiStep
      { state := after, control := .evaluate bound body } target) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings (.expression [.symbol "case", expression, .expression rows]) }
      (withFrames target [.sequence [] []]) :=
  path_trans (case_enters program bindings bound before after expression value body rows cases
    decoded computed selected) (path_with_caller_frames program [.sequence [] []] continuation)

theorem if_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (condition value yes no answer : Atom)
    (tested : PureReturns program bindings before condition middle value)
    (chosen : PureReturns program bindings middle
      (if value == Effects.boolean true then yes else no) after answer) :
    PureReturns program bindings before
      (.expression [.symbol "if", condition, yes, no]) after answer := by
  refine .step (step_transition rfl)
    (path_trans (path_with_caller_frames program [.branch bindings yes no] tested) ?_)
  exact .step (step_transition rfl) (single_sequence_returns program middle after _ answer chosen)

theorem pure_returns_has_sufficient_fuel (program : Program) (bindings : MORK.Subst)
    (before after : State) (expression value : Atom)
    (computed : PureReturns program bindings before expression after value) :
    ∃ fuel, run program fuel { state := before, control := .evaluate bindings expression } =
      .complete after [value] [] [] :=
  path_has_sufficient_fuel program _ after [value] [] [] computed

theorem clauses_use_only_the_named_equations (program : Program) (head : String)
    (values : List Atom) :
    clauses program head values =
      (program.equations.filter (fun equation => equation.head == head)).filterMap
        (fun equation =>
          (SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values)).map
            fun bindings => .evaluate bindings equation.body) := by
  cases program with
  | mk equations declarations initializers =>
      unfold clauses
      induction equations with
      | nil => rfl
      | cons equation equations ih =>
          dsimp only at ih ⊢
          by_cases same : equation.head = head <;> simp [List.filterMap_cons, same, ih]

theorem authored_function_arguments_return (program : Program) (bindings callee : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (body answer : Atom) (ordinary : ioHead head = false)
    (authored : StdLib.known head = false)
    (selected : clauses program head values = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) := by
  refine .step ?_ (single_sequence_returns program before after (.evaluate callee body) answer computed)
  apply step_transition

  simp [step, ordinary, authored, selected]

theorem native_function_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (answer : List Atom) (ordinary : ioHead head = false)
    (native : StdLib.known head = true)
    (computed : StdLib.apply before head values = .ok (after, answer)) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after answer [] []) := by
  refine .step ?_ (.refl _)
  apply step_transition

  simp [step, ordinary, native, computed, finished]


theorem native_function_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (values : List Atom) (index : Nat)
    (answer : Atom) (ordinary : ioHead head = false)
    (native : StdLib.known head = true)
    (computed : StdLib.apply before head values = .ok (after, [answer])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] values index }
      (finished after [answer] [] []) :=
  native_function_arguments_answers program bindings before after head values index [answer] ordinary native computed

theorem raw_argument_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (argument : Atom)
    (arguments values : List Atom) (index : Nat) (answers : List Atom)
    (raw : argumentIsRaw program head index = true)
    (rest : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments
          (values ++ [MORK.applySubst bindings argument]) (index + 1) }
      (finished after answers [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) (argument :: arguments) values index }
      (finished after answers [] []) := by
  let intermediate : Configuration :=
    { state := before, control := .returned [MORK.applySubst bindings argument]
      frames := [.argument bindings (.function head) arguments values index] }
  refine .step (u := intermediate) ?_
    (.step ?_ (single_sequence_answers program before after _ answers rest))
  · apply step_transition
    simp [step, raw, intermediate]
  · apply step_transition
    simp [step, intermediate]

theorem raw_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments values : List Atom) (index : Nat)
    (answer : List Atom)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (values ++ arguments.map (MORK.applySubst bindings)) (index + arguments.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments values index }
      (finished after answer [] []) := by
  induction arguments generalizing values index with
  | nil => simpa using computed
  | cons argument arguments ih =>
      have firstRaw : argumentIsRaw program head index = true := by simpa using raw 0 (by simp)
      have tailRaw : ∀ offset < arguments.length,
          argumentIsRaw program head (index + 1 + offset) = true := by
        intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using raw (offset + 1) (by simpa using bounded)
      have tailComputed := ih (values ++ [MORK.applySubst bindings argument]) (index + 1)
        tailRaw (by simpa [List.map, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using computed)
      exact raw_argument_answers program bindings before after head argument arguments values index
        answer firstRaw tailComputed


theorem raw_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments values : List Atom) (index : Nat)
    (answer : Atom)
    (raw : ∀ offset < arguments.length, argumentIsRaw program head (index + offset) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (values ++ arguments.map (MORK.applySubst bindings)) (index + arguments.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments values index }
      (finished after [answer] [] []) :=
  raw_arguments_answers program bindings before after head arguments values index [answer] raw computed

theorem evaluated_argument_answers (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (target : Target) (argument value : Atom) (answer : List Atom)
    (arguments values : List Atom) (index : Nat)
    (demanded : (match target with
      | .function head => argumentIsRaw program head index
      | .data => false) = false)
    (first : PureReturns program bindings before argument middle value)
    (rest : (theory program).MultiStep
      { state := middle, control := .arguments bindings target arguments
          (values ++ [value]) (index + 1) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (argument :: arguments) values index }
      (finished after answer [] []) := by
  refine .step ?_ (path_trans
    (path_with_caller_frames program [.argument bindings target arguments values index] first) ?_)
  · apply step_transition
    simp [step, withFrames]
    exact demanded
  · refine .step ?_ (single_sequence_answers program middle after _ answer rest)
    apply step_transition

    simp [step, withFrames, finished]


theorem evaluated_argument_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (target : Target) (argument value answer : Atom)
    (arguments values : List Atom) (index : Nat)
    (demanded : (match target with
      | .function head => argumentIsRaw program head index
      | .data => false) = false)
    (first : PureReturns program bindings before argument middle value)
    (rest : (theory program).MultiStep
      { state := middle, control := .arguments bindings target arguments
          (values ++ [value]) (index + 1) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (argument :: arguments) values index }
      (finished after [answer] [] []) :=
  evaluated_argument_answers program bindings before middle after target argument value [answer] arguments values index demanded first rest

theorem variable_prefix_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (remaining values : List Atom)
    (index : Nat) (answer : List Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target remaining
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var ++ remaining) values index }
      (finished after answer [] []) := by
  induction names generalizing values index with
  | nil => simpa using computed
  | cons name names ih =>
      have rest := ih (values ++ [MORK.applySubst bindings (.var name)]) (index + 1)
        (by simpa [List.map, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using computed)
      cases demand : (match target with
        | .function head => argumentIsRaw program head index
        | .data => false) with
      | false =>
          exact evaluated_argument_answers program bindings before before after target
            (.var name) (MORK.applySubst bindings (.var name)) answer _ values index demand
            (variable_returns program bindings before name) rest
      | true =>
          let intermediate : Configuration :=
            { state := before, control := .returned [MORK.applySubst bindings (.var name)]
              frames := [.argument bindings target (names.map Atom.var ++ remaining) values index] }
          refine .step (u := intermediate) ?_
            (.step ?_ (single_sequence_answers program before after _ answer rest))
          · apply step_transition
            simp [step, intermediate]
            exact demand
          · apply step_transition
            simp [step, intermediate]

theorem variable_arguments_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (values : List Atom)
    (index : Nat) (answer : List Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target []
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after answer [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var) values index }
      (finished after answer [] []) := by
  simpa only [List.append_nil] using variable_prefix_arguments_answers program bindings
    before after target names [] values index answer computed

theorem variable_prefix_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (remaining values : List Atom)
    (index : Nat) (answer : Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target remaining
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var ++ remaining) values index }
      (finished after [answer] [] []) :=
  variable_prefix_arguments_answers program bindings before after target names remaining values index [answer] computed


theorem variable_arguments_return (program : Program) (bindings : MORK.Subst)
    (before after : State) (target : Target) (names : List String) (values : List Atom)
    (index : Nat) (answer : Atom)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings target []
          (values ++ names.map (fun name => MORK.applySubst bindings (.var name)))
          (index + names.length) }
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      { state := before, control := .arguments bindings target
          (names.map Atom.var) values index }
      (finished after [answer] [] []) :=
  variable_arguments_answers program bindings before after target names values index [answer] computed

theorem call_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : List Atom)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after answer [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    Returns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  refine .step ?_ computed
  apply step_transition

  simp at ordinary
  rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
  simp only [step]
  split <;> simp_all <;> grind


theorem call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  call_answers program bindings before after head arguments [answer] dispatch computed ordinary

theorem raw_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (raw : ∀ index < arguments.length, argumentIsRaw program head index = true)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) []
          (arguments.map (MORK.applySubst bindings)) arguments.length }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer :=
  call_returns program bindings before after head arguments answer dispatch
    (raw_arguments_return program bindings before after head arguments [] 0 answer
      (by simpa using raw) (by simpa using computed)) ordinary

theorem native_variable_call_answers (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (names : List String) (answers : List Atom)
    (ordinary : ioHead head = false)
    (native : StdLib.known head = true)
    (computed : StdLib.apply before head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = .ok (after, answers))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    Returns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answers := by
  apply call_answers program bindings before after head (names.map Atom.var) answers
    (by simp [native]) _ notControl
  exact variable_arguments_answers program bindings before after (.function head) names [] 0 answers
    (by simpa using (native_function_arguments_answers program bindings before after head
      (names.map (fun name => MORK.applySubst bindings (.var name))) names.length
      answers ordinary native computed))

theorem native_variable_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (names : List String) (answer : Atom)
    (ordinary : ioHead head = false)
    (native : StdLib.known head = true)
    (computed : StdLib.apply before head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer :=
  native_variable_call_answers program bindings before after head names [answer] ordinary native computed notControl

theorem native_binary_call_returns (program : Program) (bindings : MORK.Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue answer : Atom)
    (ordinary : ioHead head = false) (native : StdLib.known head = true)
    (leftDemanded : argumentIsRaw program head 0 = false)
    (rightDemanded : argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (computed : StdLib.apply secondState head [leftValue, rightValue] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply call_returns program bindings before after head [left, right] answer
    (by simp [native]) _ notControl
  have last := native_function_arguments_return program bindings secondState after head
    [leftValue, rightValue] 2 answer ordinary native computed
  have rest := evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns last
  exact evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns rest

theorem native_unary_call_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (head : String) (argument value answer : Atom)
    (ordinary : ioHead head = false) (native : StdLib.known head = true)
    (demanded : argumentIsRaw program head 0 = false)
    (argumentReturns : PureReturns program bindings before argument middle value)
    (computed : StdLib.apply middle head [value] = .ok (after, [answer]))
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression [.symbol head, argument]) after answer := by
  apply call_returns program bindings before after head [argument] answer
    (by simp [native]) _ notControl
  exact evaluated_argument_returns program bindings before middle after (.function head) argument value answer
    [] [] 0 demanded argumentReturns
    (native_function_arguments_return program bindings middle after head [value] 1 answer ordinary native computed)

theorem authored_variable_call_returns (program : Program) (bindings callee : MORK.Subst)
    (before after : State) (head : String) (names : List String) (body answer : Atom)
    (ordinary : ioHead head = false)
    (authored : StdLib.known head = false)
    (dispatch : program.equations.any (·.head == head) = true)
    (selected : clauses program head
      (names.map (fun name => MORK.applySubst bindings (.var name))) = [.evaluate callee body])
    (computed : PureReturns program callee before body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before
      (.expression (.symbol head :: names.map Atom.var)) after answer := by
  apply call_returns program bindings before after head (names.map Atom.var) answer
    (by simp [dispatch]) _ notControl
  exact variable_arguments_return program bindings before after (.function head) names [] 0 answer
    (by simpa using (authored_function_arguments_return program bindings callee before after head
      (names.map (fun name => MORK.applySubst bindings (.var name))) names.length body answer
      ordinary authored selected computed))

theorem authored_binary_call_returns (program : Program) (bindings callee : MORK.Subst)
    (before firstState secondState after : State) (head : String)
    (left right leftValue rightValue body answer : Atom)
    (ordinary : ioHead head = false) (authored : StdLib.known head = false)
    (dispatch : program.equations.any (·.head == head) = true)
    (leftDemanded : argumentIsRaw program head 0 = false)
    (rightDemanded : argumentIsRaw program head 1 = false)
    (leftReturns : PureReturns program bindings before left firstState leftValue)
    (rightReturns : PureReturns program bindings firstState right secondState rightValue)
    (selected : clauses program head [leftValue, rightValue] = [.evaluate callee body])
    (computed : PureReturns program callee secondState body after answer)
    (notControl : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after answer := by
  apply call_returns program bindings before after head [left, right] answer (by simp [dispatch]) _ notControl
  apply evaluated_argument_returns program bindings before firstState after (.function head)
    left leftValue answer [right] [] 0 leftDemanded leftReturns
  apply evaluated_argument_returns program bindings firstState secondState after (.function head)
    right rightValue answer [] [leftValue] 1 rightDemanded rightReturns
  exact authored_function_arguments_return program bindings callee secondState after head
    [leftValue, rightValue] 2 body answer ordinary authored selected computed

theorem data_arguments_values_return (program : Program) (bindings : MORK.Subst)
    (state : State) (values : List Atom) (index : Nat) :
    (theory program).MultiStep
      { state, control := .arguments bindings .data [] values index }
      (finished state [.expression values] [] []) :=
  .step (step_transition rfl) (.refl _)

theorem data_call_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (arguments : List Atom) (answer : Atom)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings .data (.symbol head :: arguments) [] 0 }
      (finished after [answer] [] []))
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings before (.expression (.symbol head :: arguments)) after answer := by
  refine .step ?_ computed
  apply step_transition

  simp at ordinary
  rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
  simp only [step]
  split <;> simp_all

theorem constructor_variables_return (program : Program) (bindings : MORK.Subst)
    (state : State) (head : String) (names : List String)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings state
      (.expression (.symbol head :: names.map Atom.var)) state
      (.expression (.symbol head :: names.map (fun name => MORK.applySubst bindings (.var name)))) := by
  apply data_call_returns program bindings state state head (names.map Atom.var) _ inert _ ordinary
  have captured := variable_arguments_return program bindings state state .data names [.symbol head] 1 _
    (data_arguments_values_return program bindings state _ (1 + names.length))
  exact evaluated_argument_returns program bindings state state state .data (.symbol head) (.symbol head)
    _ (names.map Atom.var) [] 0 rfl (symbol_returns program bindings state head) captured

/-- A tuple whose first source element is a variable is data syntax. Captured
elements remain values even when one of them contains an executable head. -/
theorem tuple_variables_return (program : Program) (bindings : MORK.Subst)
    (state : State) (names : List String) :
    PureReturns program bindings state (.expression (names.map Atom.var)) state
      (.expression (names.map (fun name => MORK.applySubst bindings (.var name)))) := by
  let intermediate : Configuration :=
    { state := state, control := .arguments bindings .data (names.map Atom.var) [] 0 }
  refine .step (u := intermediate) ?_ ?_
  · apply step_transition
    cases names <;> rfl
  · exact variable_arguments_return program bindings state state .data names [] 0 _
      (by simpa using data_arguments_values_return program bindings state _ names.length)

theorem unary_constructor_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (head name : String)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings state (.expression [.symbol head, .var name]) state
      (.expression [.symbol head, MORK.applySubst bindings (.var name)]) :=
  constructor_variables_return program bindings state head [name] inert ordinary

theorem empty_constructor_returns (program : Program) (bindings : MORK.Subst)
    (state : State) (head : String)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    PureReturns program bindings state
      (.expression [.symbol head, .expression []]) state
      (.expression [.symbol head, .expression []]) := by
  apply data_call_returns program bindings state state head [.expression []] _ inert _ ordinary
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol head) (.symbol head) _ [.expression []] [] 0 rfl
    (symbol_returns program bindings state head)
  apply evaluated_argument_returns program bindings state state state .data
    (.expression []) (.expression []) _ [] [.symbol head] 1 rfl
    (.step (step_transition rfl) (.step (step_transition rfl) (.refl _)))
  exact data_arguments_values_return program bindings state _ 2

theorem unary_constructor_of_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (head : String) (expression value : Atom)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (computed : PureReturns program bindings before expression after value) :
    PureReturns program bindings before (.expression [.symbol head, expression]) after
      (.expression [.symbol head, value]) := by
  apply data_call_returns program bindings before after head [expression] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data
    (.symbol head) (.symbol head) _ [expression] [] 0 rfl
    (symbol_returns program bindings before head)
  apply evaluated_argument_returns program bindings before after after .data
    expression value _ [] [.symbol head] 1 rfl computed
  exact data_arguments_values_return program bindings after _ 2

theorem binary_constructor_returns (program : Program) (bindings : MORK.Subst)
    (before middle after : State) (head : String) (left right leftValue rightValue : Atom)
    (inert : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (leftReturns : PureReturns program bindings before left middle leftValue)
    (rightReturns : PureReturns program bindings middle right after rightValue) :
    PureReturns program bindings before (.expression [.symbol head, left, right]) after
      (.expression [.symbol head, leftValue, rightValue]) := by
  apply data_call_returns program bindings before after head [left, right] _ inert _ ordinary
  apply evaluated_argument_returns program bindings before before after .data
    (.symbol head) (.symbol head) _ [left, right] [] 0 rfl
    (symbol_returns program bindings before head)
  apply evaluated_argument_returns program bindings before middle after .data
    left leftValue _ [right] [.symbol head] 1 rfl leftReturns
  apply evaluated_argument_returns program bindings middle after after .data
    right rightValue _ [] [.symbol head, leftValue] 2 rfl rightReturns
  exact data_arguments_values_return program bindings after _ 3

/-- A native space query followed by `collapse` retains its ordered answers,
including empty queries and duplicate occurrences. -/
theorem match_collapse_returns (program : Program) (bindings : MORK.Subst)
    (before after : State) (spaceName : String) (pattern template : Atom) (answers : List Atom)
    (queried : StdLib.apply before "match"
      [MORK.applySubst bindings (.var spaceName), MORK.applySubst bindings pattern,
        MORK.applySubst bindings template] = .ok (after, answers)) :
    PureReturns program bindings before (.expression [.symbol "collapse",
      .expression [.symbol "match", .var spaceName, pattern, template]]) after (.expression answers) := by
  apply collapse_returns program bindings before after _ answers
  apply call_answers program bindings before after "match" [.var spaceName, pattern, template]
    answers (by simp [StdLib.known]) _ (by decide)
  have queriedPath := native_function_arguments_answers program bindings before after "match"
    [MORK.applySubst bindings (.var spaceName), MORK.applySubst bindings pattern,
      MORK.applySubst bindings template] 3 answers (by decide) (by decide) queried
  have tailPath := raw_arguments_answers program bindings before after "match" [pattern, template]
    [MORK.applySubst bindings (.var spaceName)] 1 answers
    (by intro offset bounded; have : offset < 2 := bounded
        have positions : offset = 0 ∨ offset = 1 := by omega
        rcases positions with rfl | rfl <;>
          simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa using queriedPath)
  exact evaluated_argument_answers program bindings before before after (.function "match")
    (.var spaceName) (MORK.applySubst bindings (.var spaceName)) answers [pattern, template] [] 0
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (variable_returns program bindings before spaceName) tailPath

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

private theorem raw_unary_stage (program : Program) (bindings : Subst)
    (state : State) (head : String) (argument : Atom) (fuel : Nat)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (raw : argumentIsRaw program head 0 = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    run program (fuel + 4)
      { state, control := .evaluate bindings (.expression [.symbol head, argument]) } =
    run program fuel
      { state, control := .arguments bindings (.function head) [] [applySubst bindings argument] 1,
        frames := [.sequence [] []] } := by
  have first : step program
      { state, control := .evaluate bindings (.expression [.symbol head, argument]) } =
      some { state, control := .arguments bindings (.function head) [argument] [] 0 } := by
    simp at ordinary
    rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
    simp only [step]
    split <;> simp_all <;> grind
  rw [show fuel + 4 = (fuel + 3) + 1 by omega, run_succ_of_step program _ _ _ first]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [run_succ_of_step program _ _ _ (show step program
      { state, control := .arguments bindings (.function head) [argument] [] 0 } =
      some { state, control := .returned [applySubst bindings argument], frames := [.argument bindings (.function head) [] [] 0] } by simp [step, raw])]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_succ_of_step program _ _ _ (show step program
      { state, control := .returned [applySubst bindings argument], frames := [.argument bindings (.function head) [] [] 0] } =
      some { state, control := .sequence [.arguments bindings (.function head) [] [applySubst bindings argument] 1] [] } by
        simp [step])]
  exact run_succ_of_step program _ _ _ rfl

/-- Equal captured raw arguments enter the same actual computation after
the capture prefix, even when their caller environments differ. -/
theorem raw_unary_capture_run_eq (program : Program) (first second : Subst)
    (state : State) (head : String) (one two : Atom) (fuel : Nat)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (raw : argumentIsRaw program head 0 = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (captured : applySubst first one = applySubst second two) :
    run program (fuel + 5)
      { state, control := .evaluate first (.expression [.symbol head, one]) } =
    run program (fuel + 5)
      { state, control := .evaluate second (.expression [.symbol head, two]) } := by
  rw [show fuel + 5 = (fuel + 1) + 4 by omega]
  rw [raw_unary_stage program first state head one _ dispatch raw ordinary,
    raw_unary_stage program second state head two _ dispatch raw ordinary]
  simp only [run, step, captured]
  split
  · rfl
  · rename_i absent
    split at absent
    · split at absent <;> cases absent
    · split at absent
      · split at absent <;> cases absent
      · cases absent

/-- Transport a completed raw unary call by equality of captured values.
Both calls retain the entire state and answer observation. -/
theorem raw_unary_capture_returns (program : Program) (first second : Subst)
    (before after : State) (head : String) (one two answer : Atom)
    (dispatch : (ioHead head || StdLib.known head ||
      program.equations.any (·.head == head)) = true)
    (raw : argumentIsRaw program head 0 = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (captured : applySubst first one = applySubst second two)
    (returned : PureReturns program first before (.expression [.symbol head, one]) after answer) :
    PureReturns program second before (.expression [.symbol head, two]) after answer := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program first before after _ _ returned
  have enough := completed_run_more_fuel program fuel 5 _ after [answer] [] [] completed
  rw [raw_unary_capture_run_eq program first second before head one two fuel
    dispatch raw ordinary captured] at enough
  exact completed_run_has_path program (fuel + 5) _ after [answer] [] [] enough

end Mettapedia.Languages.MeTTa.PeTTa.Eval

/-! ## Input and output framing

Syntactic closure excludes I/O and explicit code evaluation from the invoked
fragment. It constrains code and suspended continuations; captured values and
native stores remain arbitrary. Existing computation paths then preserve an
unread input suffix and prior output without changing their state or answers.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval.InputOutput

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open SpaceSemantics (Program patternHeads)

def blocked (excluded : List String) (head : String) : Bool := ioHead head || excluded.contains head

def codeSafe (excluded : List String) (expression : Atom) : Bool :=
  (patternHeads expression).all fun head => !blocked excluded head

private theorem symbol_safe (excluded : List String) (name : String) :
    codeSafe excluded (.symbol name) = true := by simp [codeSafe, patternHeads]

def targetSafe (excluded : List String) : Target → Bool
  | .data => true
  | .function head => !blocked excluded head

def controlSafe (excluded : List String) : Control → Bool
  | .evaluate _ expression => codeSafe excluded expression
  | .arguments _ target pending _ _ => targetSafe excluded target && pending.all (codeSafe excluded)
  | .sequence pending _ => controlsSafe excluded pending
  | .returned _ | .fault _ => true
termination_by control => sizeOf control
where
  controlsSafe (excluded : List String) : List Control → Bool
    | [] => true
    | first :: rest => controlSafe excluded first && controlsSafe excluded rest
  termination_by pending => sizeOf pending

def frameSafe (excluded : List String) : Frame → Bool
  | .collect => true
  | .bind _ _ body => codeSafe excluded body
  | .select _ cases => cases.all fun row => codeSafe excluded row.2
  | .branch _ yes no => codeSafe excluded yes && codeSafe excluded no
  | .argument _ target pending _ _ => targetSafe excluded target && pending.all (codeSafe excluded)
  | .sequence pending _ => controlSafe.controlsSafe excluded pending

def configurationSafe (excluded : List String) (configuration : Configuration) : Prop :=
  controlSafe excluded configuration.control = true ∧
    configuration.frames.all (frameSafe excluded) = true

def Closed (program : Program) (excluded : List String) : Prop :=
  ∀ equation ∈ program.equations, blocked excluded equation.head = false → codeSafe excluded equation.body = true

def withIO (configuration : Configuration) (input output : List Atom) : Configuration :=
  { configuration with input, output }

theorem step_with_io (program : Program) (excluded : List String) (source : Configuration)
    (input output : List Atom) (safe : controlSafe excluded source.control = true) :
    step program (withIO source input output) =
      (step program source).map (fun target => withIO target input output) := by
  cases source with
  | mk state control frames oldInput oldOutput =>
      cases control with
      | arguments bindings target pending values index =>
          cases target with
          | function head =>
              have ordinary : ioHead head = false := by
                cases observed : ioHead head
                · rfl
                · simp [controlSafe, targetSafe, blocked, observed] at safe
              cases pending <;> simp only [withIO, step, ordinary, Bool.false_eq_true, ↓reduceIte]
              all_goals repeat' first | rfl | split
          | data =>
              cases pending <;> rfl
      | returned answers =>
          cases frames with
          | nil => rfl
          | cons frame rest => cases frame <;> rfl
      | sequence pending answers => cases pending <;> rfl
      | fault reason => rfl
      | evaluate bindings expression =>
          cases expression <;> simp only [withIO, step]
          all_goals repeat' first | rfl | split

private theorem nested_safe (excluded : List String) (items : List Atom) :
    (patternHeads.nested items).all (fun head => !blocked excluded head) =
      items.all (codeSafe excluded) := by
  induction items with
  | nil => simp [patternHeads.nested]
  | cons first rest ih => simp [patternHeads.nested, List.all_append, codeSafe, ih]

theorem expression_safe (excluded : List String) (items : List Atom) :
    codeSafe excluded (.expression items) =
      ((match items with
      | .symbol head :: _ => !blocked excluded head
      | _ => true) && items.all (codeSafe excluded)) := by
  cases items with
  | nil => simp [codeSafe, patternHeads, patternHeads.nested]
  | cons first rest => cases first <;> simp [codeSafe, patternHeads, nested_safe]

private theorem controls_safe_iff (excluded : List String) (pending : List Control) :
    controlSafe.controlsSafe excluded pending = true ↔
      ∀ control ∈ pending, controlSafe excluded control = true := by
  induction pending with
  | nil => simp [controlSafe.controlsSafe]
  | cons first rest ih => simp [controlSafe.controlsSafe, ih]

private theorem clauses_safe (program : Program) (excluded : List String) (head : String)
    (values : List Atom) (closed : Closed program excluded) (allowed : blocked excluded head = false) :
    controlSafe.controlsSafe excluded (clauses program head values) = true := by
  apply (controls_safe_iff _ _).mpr
  intro control member
  obtain ⟨equation, eqMember, produced⟩ := List.mem_filterMap.mp (show control ∈ _ by simpa only [clauses] using member)
  split at produced
  · rename_i same
    cases matched : SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values) with
    | none => simp [matched] at produced
    | some bindings =>
        simp only [matched, Option.map_some, Option.some.injEq] at produced
        subst control
        simpa only [controlSafe] using closed equation eqMember (same ▸ allowed)
  · cases produced

private theorem nested_lets_safe (excluded : List String) (pairs : List Atom) (body nested : Atom)
    (pairsSafe : pairs.all (codeSafe excluded) = true) (bodySafe : codeSafe excluded body = true)
    (expanded : nestedLets pairs body = some nested)
    (letSafe : blocked excluded "let" = false) : codeSafe excluded nested = true := by
  induction pairs generalizing nested with
  | nil =>
      simp only [nestedLets, Option.some.injEq] at expanded
      subst nested
      exact bodySafe
  | cons first rest ih =>
      cases first with
      | var | symbol | grounded => simp [nestedLets] at expanded
      | expression items =>
          rcases items with _ | ⟨pattern, _ | ⟨value, _ | ⟨extra, tail⟩⟩⟩
          all_goals try solve | simp [nestedLets] at expanded
          simp only [List.all_cons, Bool.and_eq_true] at pairsSafe
          have firstSafe := pairsSafe.1
          have restSafe := pairsSafe.2
          have childSafe : [pattern, value].all (codeSafe excluded) = true := by
            rw [expression_safe] at firstSafe
            simp only [Bool.and_eq_true] at firstSafe
            exact firstSafe.2
          simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at childSafe
          cases tailExpanded : nestedLets rest body with
          | none => simp [nestedLets, tailExpanded] at expanded
          | some suffix =>
              simp [nestedLets, tailExpanded] at expanded
              subst nested
              rw [expression_safe]
              simp only [List.all_cons, List.all_nil, symbol_safe, letSafe, Bool.not_false,
                childSafe.1, childSafe.2, ih _ restSafe tailExpanded, Bool.and_self]

private theorem read_cases_safe (excluded : List String) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (safe : rows.all (codeSafe excluded) = true) (parsed : readCases rows = some cases) :
    cases.all (fun row => codeSafe excluded row.2) = true := by
  induction rows generalizing cases with
  | nil =>
      simp only [readCases, Option.some.injEq] at parsed
      subst cases
      rfl
  | cons first rest ih =>
      cases first with
      | var | symbol | grounded => simp [readCases] at parsed
      | expression items =>
          rcases items with _ | ⟨pattern, _ | ⟨body, _ | ⟨extra, tail⟩⟩⟩
          all_goals try solve | simp [readCases] at parsed
          simp only [List.all_cons, Bool.and_eq_true] at safe
          have bodySafe : codeSafe excluded body = true := by
            have firstSafe := safe.1
            rw [expression_safe] at firstSafe
            simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at firstSafe
            exact firstSafe.2.2
          cases tailParsed : readCases rest with
          | none => simp [readCases, tailParsed] at parsed
          | some suffix =>
              simp [readCases, tailParsed] at parsed
              subst cases
              simp [bodySafe, ih _ safe.2 tailParsed]

private theorem selected_body_safe (excluded : List String) (bindings : MORK.Subst)
    (value : Atom) (cases : SpaceSemantics.Cases) (bound : MORK.Subst) (body : Atom)
    (safe : cases.all (fun row => codeSafe excluded row.2) = true)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body)) :
    codeSafe excluded body = true := by
  induction cases with
  | nil => simp [SpaceSemantics.selectCase] at selected
  | cons row rest ih =>
      rcases row with ⟨pattern, candidate⟩
      simp only [List.all_cons, Bool.and_eq_true] at safe
      simp only [SpaceSemantics.selectCase] at selected
      split at selected
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj selected)
        exact safe.1
      · exact ih safe.2 selected

theorem transition_safe (program : Program) (excluded : List String)
    (closed : Closed program excluded) (letSafe : blocked excluded "let" = false)
    (source target : Configuration) (safe : configurationSafe excluded source)
    (transition : DeclarativeSpec.Transition program source target) : configurationSafe excluded target := by
  cases transition
  all_goals simp_all only [configurationSafe, controlSafe, frameSafe, targetSafe,
    expression_safe, List.all_cons, List.all_nil, controlSafe.controlsSafe,
    Bool.and_true, Bool.true_and, Bool.and_eq_true, and_true, true_and]
  all_goals try solve | simp_all [blocked, ioHead]
  case equations =>
    apply clauses_safe program excluded _ _ closed
    simpa using safe.1
  case let_star =>
    rename_i bindings pairs body nested control expanded
    exact nested_lets_safe excluded pairs body nested (by tauto) (by tauto) expanded letSafe
  case case_enter =>
    rename_i bindings value rows cases control parsed
    exact read_cases_safe excluded rows cases (by tauto) parsed
  case superpose_enter =>
    apply (controls_safe_iff _ _).mpr
    intro control member
    obtain ⟨value, belongs, rfl⟩ := List.mem_map.mp member
    simpa only [controlSafe] using (List.all_eq_true.mp (show _ = true by tauto)) value belongs
  case argument_return =>
    apply (controls_safe_iff _ _).mpr
    intro control member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    simpa only [controlSafe, targetSafe, Bool.and_eq_true] using safe.1
  case binding_return =>
    rename_i answers bindings pattern body rest control frames
    apply (controls_safe_iff _ _).mpr
    intro control member
    obtain ⟨value, _, produced⟩ := List.mem_filterMap.mp member
    cases selected : SpaceSemantics.matchBinding bindings pattern value with
    | none => simp [selected] at produced
    | some bound =>
        simp only [selected, Option.map_some, Option.some.injEq] at produced
        subst control
        simpa only [controlSafe] using safe.1
  case case_return =>
    rename_i answers bindings cases rest control frames
    apply (controls_safe_iff _ _).mpr
    intro control member
    obtain ⟨value, _, produced⟩ := List.mem_filterMap.mp member
    cases selected : SpaceSemantics.selectCase bindings value cases with
    | none => simp [selected] at produced
    | some row =>
        rcases row with ⟨bound, body⟩
        simp only [selected, Option.map_some, Option.some.injEq] at produced
        subst control
        simpa only [controlSafe] using selected_body_safe excluded bindings value cases bound body safe.1 selected
  case if_return =>
    apply (controls_safe_iff _ _).mpr
    intro control member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    simp only [controlSafe]
    split <;> tauto

theorem path_with_io (program : Program) (excluded : List String)
    (closed : Closed program excluded) (letSafe : blocked excluded "let" = false)
    (input output : List Atom) :
    {source target : Configuration} → (theory program).MultiStep source target →
      configurationSafe excluded source →
      (theory program).MultiStep (withIO source input output) (withIO target input output)
  | _, _, .refl _, _ => .refl _
  | source, _, .step transition rest, safe => by
      refine .step (step_transition ?_)
        (path_with_io program excluded closed letSafe input output rest
          (transition_safe program excluded closed letSafe _ _ safe transition))
      rw [step_with_io program excluded source input output safe.1, transition_step transition]
      rfl

theorem returns_with_io (program : Program) (excluded : List String)
    (closed : Closed program excluded) (letSafe : blocked excluded "let" = false)
    (bindings : MORK.Subst) (before after : Effects.State) (expression : Atom) (answers input output : List Atom)
    (safe : codeSafe excluded expression = true)
    (returned : Returns program bindings before expression after answers) :
    (theory program).MultiStep
      { state := before, control := .evaluate bindings expression, input, output }
      (finished after answers input output) := by
  simpa only [withIO, finished] using path_with_io program excluded closed letSafe input output returned
    (show configurationSafe excluded { state := before, control := .evaluate bindings expression } from
      ⟨by simpa only [controlSafe] using safe, rfl⟩)

end Mettapedia.Languages.MeTTa.PeTTa.Eval.InputOutput

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval.InputOutput

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State)

/-- Existing computation paths with explicit before/after I/O observations. -/
abbrev ReturnsIO (program : Program) (bindings : Subst) (before : State) (expression : Atom)
    (after : State) (answers : List Atom) (input output remaining printed : List Atom) : Prop :=
  (theory program).MultiStep { state := before, control := .evaluate bindings expression, input, output }
    (finished after answers remaining printed)

abbrev PureReturnsIO (program : Program) (bindings : Subst) (before : State) (expression : Atom)
    (after : State) (answer : Atom) (input output remaining printed : List Atom) : Prop :=
  ReturnsIO program bindings before expression after [answer] input output remaining printed

theorem single_sequence_io (program : Program) (before after : State) (control : Control)
    (collected answers input output remaining printed : List Atom)
    (returned : (theory program).MultiStep { state := before, control, input, output }
      (finished after answers remaining printed)) :
    (theory program).MultiStep { state := before, control := .sequence [control] collected, input, output }
      (finished after (collected ++ answers) remaining printed) := by
  refine .step (step_transition rfl) ?_
  have nested := path_with_caller_frames program [.sequence [] collected] returned
  apply path_trans nested
  exact .step (step_transition rfl) (.step (step_transition rfl) (.refl _))

theorem let_io_returns (program : Program) (bindings bound : Subst)
    (before middle after : State) (pattern expression body value answer : Atom)
    (input output middleInput middleOutput remaining printed : List Atom)
    (first : PureReturnsIO program bindings before expression middle value input output middleInput middleOutput)
    (matched : SpaceSemantics.matchBinding bindings pattern value = some bound)
    (second : PureReturnsIO program bound middle body after answer middleInput middleOutput remaining printed) :
    PureReturnsIO program bindings before (.expression [.symbol "let", pattern, expression, body])
      after answer input output remaining printed := by
  refine .step (step_transition rfl) ?_
  have nested := path_with_caller_frames program [.bind bindings pattern body] first
  apply path_trans nested
  refine .step (step_transition ?_) (single_sequence_io program middle after (.evaluate bound body)
    [] [answer] middleInput middleOutput remaining printed second)
  simp [withFrames, finished, step, matched]

theorem case_io_returns (program : Program) (bindings bound : Subst)
    (before middle after : State) (expression value body answer : Atom) (rows : List Atom) (cases : Cases)
    (input output middleInput middleOutput remaining printed : List Atom)
    (parsed : readCases rows = some cases)
    (first : PureReturnsIO program bindings before expression middle value input output middleInput middleOutput)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (second : PureReturnsIO program bound middle body after answer middleInput middleOutput remaining printed) :
    PureReturnsIO program bindings before (.expression [.symbol "case", expression, .expression rows])
      after answer input output remaining printed := by
  have nested := path_with_caller_frames program [.select bindings cases] first
  refine .step (step_transition ?_) (path_trans nested ?_)
  · simp [step, parsed, withFrames]
  · refine .step (step_transition ?_) (single_sequence_io program middle after (.evaluate bound body)
      [] [answer] middleInput middleOutput remaining printed second)
    simp [withFrames, finished, step, selected]

theorem variable_io_returns (program : Program) (bindings : Subst) (state : State)
    (name : String) (input output : List Atom) :
    PureReturnsIO program bindings state (.var name) state (applySubst bindings (.var name)) input output input output :=
  .step (step_transition rfl) (.refl _)

theorem symbol_io_returns (program : Program) (bindings : Subst) (state : State)
    (name : String) (input output : List Atom) :
    PureReturnsIO program bindings state (.symbol name) state (.symbol name) input output input output :=
  .step (step_transition rfl) (.refl _)

theorem call_io_returns (program : Program) (bindings : Subst) (before after : State)
    (head : String) (arguments : List Atom) (answer : Atom) (input output remaining printed : List Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) arguments [] 0, input, output }
      (finished after [answer] remaining printed)) :
    PureReturnsIO program bindings before (.expression (.symbol head :: arguments)) after answer
      input output remaining printed := by
  refine .step (step_transition ?_) computed
  simp at ordinary
  rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
  simp only [step]
  split <;> simp_all <;> grind

theorem variable_argument_io_returns (program : Program) (bindings : Subst) (before after : State)
    (head name : String) (value answer : Atom) (input output remaining printed : List Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (demanded : argumentIsRaw program head 0 = false) (captured : applySubst bindings (.var name) = value)
    (computed : (theory program).MultiStep
      { state := before, control := .arguments bindings (.function head) [] [value] 1, input, output }
      (finished after [answer] remaining printed)) :
    PureReturnsIO program bindings before (.expression [.symbol head, .var name]) after answer
      input output remaining printed := by
  apply call_io_returns program bindings before after head [.var name] answer input output remaining printed dispatch ordinary
  have enter : step program
      { state := before, control := .arguments bindings (.function head) [.var name] [] 0, input, output } =
      some { state := before, control := .evaluate bindings (.var name), frames := [.argument bindings (.function head) [] [] 0], input, output } := by simp [step, demanded]
  have capture : step program
      { state := before, control := .evaluate bindings (.var name), frames := [.argument bindings (.function head) [] [] 0], input, output } =
      some { state := before, control := .returned [value], frames := [.argument bindings (.function head) [] [] 0], input, output } := by simp [step, captured]
  have resume : step program
      { state := before, control := .returned [value], frames := [.argument bindings (.function head) [] [] 0], input, output } =
      some { state := before, control := .sequence [.arguments bindings (.function head) [] [value] 1] [], input, output } := by
        simp [step]
  exact .step (step_transition enter) (.step (step_transition capture) (.step (step_transition resume)
    (single_sequence_io program before after (.arguments bindings (.function head) [] [value] 1)
      [] [answer] input output remaining printed computed)))

theorem read_line_io_returns (program : Program) (bindings : Subst) (state : State)
    (request : Atom) (remaining output : List Atom) :
    PureReturnsIO program bindings state (.expression [.symbol "readln!"]) state request
      (request :: remaining) output remaining output := by
  apply call_io_returns program bindings state state "readln!" [] request _ _ _ _ (by simp [ioHead]) (by decide)
  exact .step (step_transition rfl) (.refl _)

theorem read_end_io_returns (program : Program) (bindings : Subst) (state : State) (output : List Atom) :
    PureReturnsIO program bindings state (.expression [.symbol "readln!"]) state (.symbol "end_of_file")
      [] output [] output := by
  apply call_io_returns program bindings state state "readln!" [] (.symbol "end_of_file") _ _ _ _ (by simp [ioHead]) (by decide)
  exact .step (step_transition rfl) (.refl _)

theorem eval_variable_io_returns (program : Program) (bindings : Subst) (before after : State)
    (name : String) (code answer : Atom) (input output remaining printed : List Atom)
    (demanded : argumentIsRaw program "eval" 0 = false)
    (captured : applySubst bindings (.var name) = code)
    (computed : PureReturnsIO program [] before code after answer input output remaining printed) :
    PureReturnsIO program bindings before (.expression [.symbol "eval", .var name]) after answer
      input output remaining printed := by
  apply variable_argument_io_returns program bindings before after "eval" name code answer
    input output remaining printed (by simp [ioHead]) (by decide) demanded captured
  exact .step (step_transition rfl) computed

theorem println_variable_io_returns (program : Program) (bindings : Subst) (state : State)
    (name : String) (value : Atom) (input output : List Atom)
    (demanded : argumentIsRaw program "println!" 0 = false)
    (captured : applySubst bindings (.var name) = value) :
    PureReturnsIO program bindings state (.expression [.symbol "println!", .var name]) state (Effects.boolean true)
      input output input (output ++ [value]) := by
  apply variable_argument_io_returns program bindings state state "println!" name value (Effects.boolean true)
    input output input (output ++ [value]) (by simp [ioHead]) (by decide) demanded captured
  exact .step (step_transition rfl) (.refl _)

/-- A dispatched nullary call drops its caller's environment before its
body or primitive executes, retaining the actual I/O observation. -/
theorem nullary_capture_run_eq (program : SpaceSemantics.Program) (first second : Subst)
    (state : State) (head : String) (fuel : Nat) (input output : List Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    run program (fuel + 2)
      { state, control := .evaluate first (.expression [.symbol head]), input, output } =
    run program (fuel + 2)
      { state, control := .evaluate second (.expression [.symbol head]), input, output } := by
  have enter (bindings : Subst) : step program
      { state, control := .evaluate bindings (.expression [.symbol head]), input, output } =
      some { state, control := .arguments bindings (.function head) [] [] 0, input, output } := by
    simp at ordinary
    rcases ordinary with ⟨notLet, notLetStar, notCase, notIf, notCollapse⟩
    simp only [step]
    split <;> simp_all <;> grind
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    run_succ_of_step program _ _ _ (enter first),
    run_succ_of_step program _ _ _ (enter second)]
  simp only [run, step]
  split
  · rfl
  · rename_i absent
    split at absent
    · split at absent <;> first | cases absent | (cases input <;> cases absent)
    · split at absent
      · split at absent <;> cases absent
      · cases absent

theorem nullary_capture_io_returns (program : SpaceSemantics.Program) (first second : Subst)
    (before after : State) (head : String) (answer : Atom) (input output remaining printed : List Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (returned : PureReturnsIO program first before (.expression [.symbol head]) after answer
      input output remaining printed) :
    PureReturnsIO program second before (.expression [.symbol head]) after answer input output remaining printed := by
  obtain ⟨fuel, completed⟩ := path_has_sufficient_fuel program _ after [answer] remaining printed returned
  have enough := completed_run_more_fuel program fuel 2 _ after [answer] remaining printed completed
  rw [nullary_capture_run_eq program first second before head fuel input output dispatch ordinary] at enough
  exact completed_run_has_path program (fuel + 2) _ after [answer] remaining printed enough


end Mettapedia.Languages.MeTTa.PeTTa.Eval.InputOutput
