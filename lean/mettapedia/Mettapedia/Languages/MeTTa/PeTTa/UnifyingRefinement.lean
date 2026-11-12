import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSound
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Branch substitution refinement through the source machine

The statements concern the existing `Unifying` machine and its actual
substitution-bearing answers. Refinement is carried through calls and saved
continuations, not assumed of a value-only call service.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem unifyLists_refines (unifier : Subst → Atom → Atom → Unified)
    (sound : ∀ bindings bound left right, Idempotent bindings →
      unifier bindings left right = .ok bound → Idempotent bound ∧ Refines bindings bound) :
    ∀ (left right : List Atom) (bindings bound : Subst), Idempotent bindings →
      unifyLists unifier bindings left right = .ok bound →
        Idempotent bound ∧ Refines bindings bound := by
  intro left
  induction left with
  | nil =>
      intro right bindings bound valid unified
      cases right with
      | nil =>
          cases unified
          exact ⟨valid, Refines.refl valid⟩
      | cons => cases unified
  | cons first rest ih =>
      intro right bindings bound valid unified
      cases right with
      | nil => cases unified
      | cons other others =>
          simp only [unifyLists] at unified
          cases head : unifier bindings first other with
          | clash => simp [head] at unified
          | exhausted => simp [head] at unified
          | ok middle =>
              rw [head, Unified.ok_andThen] at unified
              obtain ⟨middleValid, firstRefines⟩ := sound bindings middle first other valid head
              obtain ⟨boundValid, secondRefines⟩ := ih others middle bound middleValid unified
              exact ⟨boundValid, firstRefines.trans secondRefines⟩

theorem unifyPattern_refines (fuel : Nat) :
    ∀ (bindings bound : Subst) (pattern value : Atom), Idempotent bindings →
      unifyPattern fuel bindings pattern value = .ok bound →
        Idempotent bound ∧ Refines bindings bound := by
  induction fuel with
  | zero => intro bindings bound pattern value valid unified; cases unified
  | succ fuel ih =>
      intro bindings bound pattern value valid unified
      simp only [unifyPattern] at unified
      split at unified
      · rename_i _ _ first rest head tail _
        cases firstRun : unifyPattern fuel bindings first head with
        | clash => simp [firstRun] at unified
        | exhausted => simp [firstRun] at unified
        | ok middle =>
            rw [firstRun, Unified.ok_andThen] at unified
            obtain ⟨middleValid, firstRefines⟩ := ih bindings middle first head valid firstRun
            obtain ⟨boundValid, secondRefines⟩ := ih middle bound rest (.expression tail) middleValid unified
            exact ⟨boundValid, firstRefines.trans secondRefines⟩
      · exact ⟨(unifyTerms_sound fuel bindings bound _ value valid unified).1,
          (unifyTerms_sound fuel bindings bound _ value valid unified).2.1⟩
      · cases unified
      · exact unifyLists_refines (unifyPattern fuel) ih _ _ bindings bound valid unified
      · exact ⟨(unifyTerms_sound fuel bindings bound _ value valid unified).1,
          (unifyTerms_sound fuel bindings bound _ value valid unified).2.1⟩
      · cases unified
      · exact ⟨(unifyTerms_sound fuel bindings bound _ value valid unified).1,
          (unifyTerms_sound fuel bindings bound _ value valid unified).2.1⟩

theorem unifyBinding_refines (bindings bound : Subst) (pattern value : Atom)
    (valid : Idempotent bindings) (unified : unifyBinding bindings pattern value = .ok bound) :
    Idempotent bound ∧ Refines bindings bound := by
  unfold unifyBinding at unified
  split at unified
  · exact ⟨(unifyTerms_sound _ bindings bound _ value valid unified).1,
      (unifyTerms_sound _ bindings bound _ value valid unified).2.1⟩
  · exact unifyPattern_refines _ bindings bound _ value valid unified

/-- A branch record retains the initial caller's equations and is still
idempotent, as required by every subsequent source unification. -/
def BindingRefines (initial bindings : Subst) : Prop :=
  Idempotent bindings ∧ Refines initial bindings

theorem BindingRefines.pattern {initial bindings bound : Subst} (good : BindingRefines initial bindings)
    (pattern value : Atom) (fuel : Nat) (unified : unifyPattern fuel bindings pattern value = .ok bound) :
    BindingRefines initial bound := by
  obtain ⟨valid, refined⟩ := unifyPattern_refines fuel bindings bound pattern value good.1 unified
  exact ⟨valid, good.2.trans refined⟩

theorem BindingRefines.terms {initial bindings bound : Subst} (good : BindingRefines initial bindings)
    (left right : Atom) (unified : unify bindings left right = .ok bound) :
    BindingRefines initial bound := by
  obtain ⟨valid, refined, _⟩ := unifyTerms_sound _ bindings bound left right good.1 unified
  exact ⟨valid, good.2.trans refined⟩

theorem BindingRefines.binding {initial bindings bound : Subst} (good : BindingRefines initial bindings)
    (pattern value : Atom) (unified : unifyBinding bindings pattern value = .ok bound) :
    BindingRefines initial bound := by
  obtain ⟨valid, refined⟩ := unifyBinding_refines bindings bound pattern value good.1 unified
  exact ⟨valid, good.2.trans refined⟩

theorem BindingRefines.arguments {initial bindings bound : Subst} (good : BindingRefines initial bindings)
    (patterns values : List Atom) (unified : unifyArguments bindings patterns values = .ok bound) :
    BindingRefines initial bound := by
  obtain ⟨valid, refined⟩ := unifyLists_refines _ (unifyPattern_refines _) patterns values
    bindings bound good.1 unified
  exact ⟨valid, good.2.trans refined⟩

def ControlRefines (initial : Subst) : Control → Prop
  | .evaluate bindings _ => BindingRefines initial bindings
  | .dynamic bindings _ _ => BindingRefines initial bindings
  | .arguments bindings _ _ _ _ => BindingRefines initial bindings
  | .sequence pending answers =>
      (∀ control ∈ pending, ControlRefines initial control) ∧
        (∀ answer ∈ answers, BindingRefines initial answer.bindings)
  | .returned answers => ∀ answer ∈ answers, BindingRefines initial answer.bindings
  | .fault _ => True

def FrameRefines (initial : Subst) : Frame → Prop
  | .collect bindings => BindingRefines initial bindings
  | .sequence pending answers =>
      (∀ control ∈ pending, ControlRefines initial control) ∧
        (∀ answer ∈ answers, BindingRefines initial answer.bindings)
  | _ => True

def ConfigurationRefines (initial : Subst) (configuration : Configuration) : Prop :=
  ControlRefines initial configuration.control ∧
    ∀ frame ∈ configuration.frames, FrameRefines initial frame

theorem dispatchAnswer_refines {initial : Subst} (answer : Answer)
    (good : BindingRefines initial answer.bindings) : ControlRefines initial (dispatchAnswer answer) := by
  rcases answer with ⟨value, bindings⟩
  cases value with
  | symbol name => simpa [dispatchAnswer, ControlRefines] using good
  | var name => simpa [dispatchAnswer, ControlRefines] using good
  | grounded value => simpa [dispatchAnswer, ControlRefines] using good
  | expression items =>
      cases items <;> simpa [dispatchAnswer, ControlRefines] using good

theorem recovered_frames_refine {initial : Subst} (earned : List Answer) (frames : List Frame)
    (earnedGood : ∀ answer ∈ earned, BindingRefines initial answer.bindings)
    (framesGood : ∀ frame ∈ frames, FrameRefines initial frame)
    (answers : List Answer) (remaining : List Frame)
    (recovered : recoverDynamic earned frames = some (answers, remaining)) :
    (∀ answer ∈ answers, BindingRefines initial answer.bindings) ∧
      (∀ frame ∈ remaining, FrameRefines initial frame) := by
  induction frames generalizing earned with
  | nil => cases recovered
  | cons frame rest ih =>
      have headGood := framesGood frame (by simp)
      have tailGood : ∀ frame ∈ rest, FrameRefines initial frame :=
        fun frame member => framesGood frame (List.mem_cons_of_mem _ member)
      cases frame with
      | dynamicCall =>
          simp only [recoverDynamic, Option.some.injEq, Prod.mk.injEq] at recovered
          rcases recovered with ⟨rfl, rfl⟩
          exact ⟨earnedGood, tailGood⟩
      | sequence pending completed =>
          apply ih (completed ++ earned) ?_ tailGood recovered
          intro answer member
          exact (List.mem_append.mp member).elim (headGood.2 answer) (earnedGood answer)
      | _ => exact ih [] (by simp) tailGood recovered

theorem selections_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (values : List Atom) : ∀ use equations selected,
    selections bindings values use equations = some selected →
      ∀ control ∈ selected, ControlRefines initial control := by
  intro use equations
  induction equations generalizing use with
  | nil =>
      intro selected chosen
      simp only [selections, Option.some.injEq] at chosen
      subst selected
      simp
  | cons equation rest ih =>
      intro selected chosen
      simp only [selections] at chosen
      cases tailRun : selections bindings values (use + 1) rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases unified : unifyArguments bindings (equation.arguments.map (rename use)) values with
          | exhausted => simp [unified] at chosen
          | clash =>
              simp [unified] at chosen
              subst selected
              exact ih _ _ tailRun
          | ok bound =>
              simp [unified] at chosen
              subst selected
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · simpa only [ControlRefines] using good.arguments _ _ unified
              · exact ih _ _ tailRun control present

theorem application_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (registry : SpaceSemantics.Program) (live : List SpaceSemantics.Equation) (head : String)
    (values : List Atom) (use : Nat) (control : Control) (used : Nat)
    (chosen : application registry live head values bindings use = some (control, used)) :
    ControlRefines initial control := by
  unfold application at chosen
  split at chosen
  · cases found : selections bindings values use (candidates live head values.length) with
    | none => simp [found] at chosen
    | some selected =>
        simp [found] at chosen
        obtain ⟨rfl, rfl⟩ := chosen
        simpa only [ControlRefines, List.not_mem_nil, false_implies, implies_true, and_true] using
          selections_refines good values use _ selected found
  · split at chosen
    · cases chosen; simp [ControlRefines]
    · cases chosen
      simpa [ControlRefines] using good

theorem bindAnswers_refines {initial : Subst} (pattern body : Atom) :
    ∀ answers continued, (∀ answer ∈ answers, BindingRefines initial answer.bindings) →
      bindAnswers pattern body answers = some continued →
        ∀ control ∈ continued, ControlRefines initial control := by
  intro answers
  induction answers with
  | nil =>
      intro continued good bound
      simp only [bindAnswers, Option.some.injEq] at bound
      subst continued
      simp
  | cons answer rest ih =>
      intro continued good bound
      simp only [bindAnswers] at bound
      cases tailRun : bindAnswers pattern body rest with
      | none => simp [tailRun] at bound
      | some tail =>
          simp only [tailRun] at bound
          cases unified : unifyBinding answer.bindings pattern answer.value with
          | exhausted => simp [unified] at bound
          | clash =>
              simp [unified] at bound
              subst continued
              exact ih tail (fun answer present => good answer (by simp [present])) tailRun
          | ok bindings =>
              simp [unified] at bound
              subst continued
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · simpa only [ControlRefines] using (good answer (by simp)).binding pattern answer.value unified
              · exact ih tail (fun answer present => good answer (by simp [present])) tailRun control present

theorem selectCase_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (value : Atom) : ∀ cases bound body,
    selectCase bindings value cases = some (some (bound, body)) → BindingRefines initial bound := by
  intro cases
  induction cases with
  | nil => intro bound body chosen; cases chosen
  | cons first rest ih =>
      intro bound body chosen
      simp only [selectCase] at chosen
      cases unified : unifyAsPattern bindings first.1 value with
      | exhausted => simp [unified] at chosen
      | clash => simp only [unified] at chosen; exact ih bound body chosen
      | ok next =>
          simp [unified] at chosen
          obtain ⟨rfl, rfl⟩ := chosen
          exact good.pattern _ _ _ unified

theorem selectAnswers_refines {initial : Subst} (cases : SpaceSemantics.Cases) :
    ∀ answers continued, (∀ answer ∈ answers, BindingRefines initial answer.bindings) →
      selectAnswers cases answers = some continued →
        ∀ control ∈ continued, ControlRefines initial control := by
  intro answers
  induction answers with
  | nil =>
      intro continued good chosen
      simp only [selectAnswers, Option.some.injEq] at chosen
      subst continued
      simp
  | cons answer rest ih =>
      intro continued good chosen
      simp only [selectAnswers] at chosen
      cases tailRun : selectAnswers cases rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases selected : selectCase answer.bindings answer.value cases with
          | none => simp [selected] at chosen
          | some selection =>
              cases selection with
              | none =>
                  simp [selected] at chosen
                  subst continued
                  exact ih tail (fun answer present => good answer (by simp [present])) tailRun
              | some pair =>
                  obtain ⟨bindings, body⟩ := pair
                  simp [selected] at chosen
                  subst continued
                  intro control member
                  rcases List.mem_cons.mp member with rfl | present
                  · simpa only [ControlRefines] using selectCase_refines (good answer (by simp)) _ _ _ _ selected
                  · exact ih tail (fun answer present => good answer (by simp [present])) tailRun control present

theorem queryBodies_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (pattern body : Atom) : ∀ use rows continued,
    queryBodies bindings pattern body use rows = some continued →
      ∀ control ∈ continued, ControlRefines initial control := by
  intro use rows
  induction rows generalizing use with
  | nil =>
      intro continued queried
      simp only [queryBodies, Option.some.injEq] at queried
      subst continued
      simp
  | cons row rest ih =>
      intro continued queried
      simp only [queryBodies] at queried
      cases tailRun : queryBodies bindings pattern body (use + 1) rest with
      | none => simp [tailRun] at queried
      | some tail =>
          simp only [tailRun] at queried
          cases unified : unify bindings pattern (rename use row) with
          | exhausted => simp [unified] at queried
          | clash =>
              simp [unified] at queried
              subst continued
              exact ih _ _ tailRun
          | ok bound =>
              simp [unified] at queried
              subst continued
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · simpa only [ControlRefines] using good.terms _ _ unified
              · exact ih _ _ tailRun control present

theorem matchAnswers_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (pattern template : Atom) : ∀ use rows answers,
    matchAnswers bindings pattern template use rows = some answers →
      ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
  intro use rows
  induction rows generalizing use with
  | nil =>
      intro answers queried
      cases queried
      simp
  | cons row rest ih =>
      intro answers queried
      simp only [matchAnswers] at queried
      cases tailRun : matchAnswers bindings pattern template (use + 1) rest with
      | none => simp [tailRun] at queried
      | some tail =>
          simp only [tailRun] at queried
          cases unified : unify bindings pattern (rename use row) with
          | exhausted => simp [unified] at queried
          | clash =>
              simp [unified] at queried
              subst answers
              exact ih _ _ tailRun
          | ok bound =>
              simp [unified] at queried
              subst answers
              intro answer member
              rcases List.mem_cons.mp member with rfl | present
              · exact good.terms _ _ unified
              · exact ih _ _ tailRun answer present

theorem matchCall_refines {initial bindings : Subst} (good : BindingRefines initial bindings)
    (state : Effects.State) (use : Nat) (values : List Atom) (answers : List Answer) (used : Nat)
    (queried : matchCall state bindings use values = some (.ok (answers,used))) :
    ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
  unfold matchCall at queried
  split at queried
  · split at queried
    · cases queried
    · obtain ⟨returned,source,same⟩ := Option.map_eq_some_iff.mp queried
      cases same
      exact matchAnswers_refines good _ _ _ _ _ source
  · cases queried

theorem queries_refines {initial : Subst} (state : Effects.State) (pattern body : Atom) :
    ∀ use answers continued used, (∀ answer ∈ answers, BindingRefines initial answer.bindings) →
      queries state pattern body use answers = some (continued, used) →
        ∀ control ∈ continued, ControlRefines initial control := by
  intro use answers
  induction answers generalizing use with
  | nil =>
      intro continued used good queried
      simp only [queries, Option.some.injEq, Prod.mk.injEq] at queried
      obtain ⟨rfl, rfl⟩ := queried
      simp
  | cons answer rest ih =>
      intro continued used good queried
      simp only [queries] at queried
      split at queried
      · rename_i rows read
        cases here : queryBodies answer.bindings pattern body use rows with
        | none => simp [here] at queried
        | some controls =>
            cases there : queries state pattern body (use + rows.length) rest with
            | none => simp [here, there] at queried
            | some tail =>
                obtain ⟨others, count⟩ := tail
                simp [here, there] at queried
                obtain ⟨rfl, rfl⟩ := queried
                intro control member
                rcases List.mem_append.mp member with present | present
                · exact queryBodies_refines (good answer (by simp)) _ _ _ _ _ here control present
                · exact ih _ _ _ (fun answer present => good answer (by simp [present])) there control present
      · cases there : queries state pattern body use rest with
        | none => simp [there] at queried
        | some tail =>
            obtain ⟨others, count⟩ := tail
            simp [there] at queried
            obtain ⟨rfl, rfl⟩ := queried
            intro control member
            rcases List.mem_cons.mp member with rfl | present
            · simp [ControlRefines]
            · exact ih _ _ _ (fun answer present => good answer (by simp [present])) there control present

theorem transition_refines {registry : SpaceSemantics.Program} {initial : Subst}
    {source target : Configuration} (transition : Transition registry source target)
    (good : ConfigurationRefines initial source) : ConfigurationRefines initial target := by
  obtain ⟨controlGood, framesGood⟩ := good
  cases transition
  all_goals try solve | simp_all [ConfigurationRefines, ControlRefines, FrameRefines]
  case sequence_return answers collected pending rest control frames =>
    have incoming : ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
      simpa only [control, ControlRefines] using controlGood
    simp only [frames, List.mem_cons, forall_eq_or_imp, FrameRefines] at framesGood
    refine ⟨?_, framesGood.2⟩
    simp only [ControlRefines]
    refine ⟨framesGood.1.1, ?_⟩
    intro answer member
    rcases List.mem_append.mp member with old | new
    · exact framesGood.1.2 answer old
    · exact incoming answer new
  case equations bindings head index held selected used control ordinary notRemove notNative chosen =>
    refine ⟨application_refines ?_ _ _ _ _ _ _ _ chosen, framesGood⟩
    simpa only [control, ControlRefines] using controlGood
  case native_query bindings index held answers used control queried =>
    refine ⟨?_,framesGood⟩
    simpa only [ControlRefines] using
      matchCall_refines (by simpa only [control,ControlRefines] using controlGood) _ _ _ _ _ queried
  case dynamic_equations bindings callee supplied head selected used control resolved notNative registered chosen =>
    refine ⟨application_refines ?_ _ _ _ _ _ _ _ chosen, ?_⟩
    · simpa only [control, ControlRefines] using controlGood
    · cases selected <;> simpa only [invocationFrames, List.mem_cons, forall_eq_or_imp,
        FrameRefines, true_and] using framesGood
  case fault_caught reason earned rest control recovered =>
    simpa only [ConfigurationRefines, ControlRefines] using
      recovered_frames_refine [] source.frames (by simp) framesGood earned rest recovered
  case dispatch_return answers rest control frames =>
    have incoming : ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
      simpa only [control, ControlRefines] using controlGood
    refine ⟨?_, ?_⟩
    · simp only [ControlRefines, List.not_mem_nil, false_implies, implies_true, and_true]
      intro pending member
      rcases List.mem_map.mp member with ⟨answer, sourceMember, rfl⟩
      exact dispatchAnswer_refines answer (incoming answer sourceMember)
    · intro frame member
      exact framesGood frame (by rw [frames]; exact List.mem_cons_of_mem _ member)
  case binding_return answers pattern body rest continued control frames bound =>
    have all := bindAnswers_refines (initial := initial) pattern body answers continued
      (by simpa only [control, ControlRefines] using controlGood) bound
    simpa only [ConfigurationRefines, ControlRefines, frames, FrameRefines, List.mem_cons,
      forall_eq_or_imp, true_and, List.not_mem_nil, false_implies, implies_true, and_true] using
      And.intro all framesGood
  case case_return answers cases rest continued control frames selected =>
    have all := selectAnswers_refines (initial := initial) cases answers continued
      (by simpa only [control, ControlRefines] using controlGood) selected
    simpa only [ConfigurationRefines, ControlRefines, frames, FrameRefines, List.mem_cons,
      forall_eq_or_imp, true_and, List.not_mem_nil, false_implies, implies_true, and_true] using
      And.intro all framesGood
  case query_return answers pattern body rest continued used control frames queried =>
    have all := queries_refines (initial := initial) source.state pattern body source.uses answers continued used
      (by simpa only [control, ControlRefines] using controlGood) queried
    simpa only [ConfigurationRefines, ControlRefines, frames, FrameRefines, List.mem_cons,
      forall_eq_or_imp, true_and, List.not_mem_nil, false_implies, implies_true, and_true] using
      And.intro all framesGood

theorem step_refines {registry : SpaceSemantics.Program} {initial : Subst}
    {source target : Configuration} (stepTaken : step registry source = some target)
    (good : ConfigurationRefines initial source) : ConfigurationRefines initial target :=
  transition_refines ((step_iff_transition registry source target).mp stepTaken) good

theorem steps_refine {registry : SpaceSemantics.Program} {initial : Subst}
    {source target : Configuration} (steps : Relation.ReflTransGen (Transition registry) source target)
    (good : ConfigurationRefines initial source) : ConfigurationRefines initial target := by
  induction steps with
  | refl => exact good
  | tail previous stepTaken ih => exact transition_refines stepTaken ih

/-- An actual reached return exposes each branch's refinement certificate;
no property of a supplied helper oracle is assumed. -/
theorem reached_answers_refine {registry : SpaceSemantics.Program} {initial : Subst}
    {source target : Configuration} (steps : Relation.ReflTransGen (Transition registry) source target)
    (good : ConfigurationRefines initial source) (answers : List Answer)
    (returned : target.control = .returned answers) :
    ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
  have final := (steps_refine steps good).1
  simpa only [returned, ControlRefines] using final

theorem evaluation_entry_refines (bindings : Subst) (valid : Idempotent bindings)
    (state : Effects.State) (expression : Atom) (input output : List Atom) (use : Nat) :
    ConfigurationRefines bindings
      { state, control := .evaluate bindings expression, input, output, uses := use } := by
  simp only [ConfigurationRefines, ControlRefines, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨valid, Refines.refl valid⟩

/-- A completed derivation has an actual returned-answer endpoint. Keeping
that endpoint prevents an existential list of fabricated answers from
standing in for the substitutions the source execution produced. -/
theorem Runs.completed_endpoint {registry : SpaceSemantics.Program} {source : Configuration}
    {state : Effects.State} {values input output : List Atom}
    (derivation : Runs registry source (.complete state values input output)) :
    ∃ final answers, Relation.ReflTransGen (Transition registry) source final ∧
      final.control = .returned answers ∧ final.frames = [] ∧
      final.state = state ∧ final.input = input ∧ final.output = output ∧
      values = answers.map (fun answer => resolve answer.bindings answer.value) := by
  generalize resultEq : Outcome.complete state values input output = result at derivation
  induction derivation with
  | completed control frames =>
      cases resultEq
      exact ⟨_, _, .refl, control, frames, rfl, rfl, rfl, rfl⟩
  | fault => cases resultEq
  | next transition rest ih =>
      obtain ⟨final, answers, steps, properties⟩ := ih resultEq
      exact ⟨final, answers, steps.head transition, properties⟩

/-- Completed source calls preserve the original caller equations in each
actual branch packet. The list equality preserves answer order and repeats. -/
theorem completed_run_refines {registry : SpaceSemantics.Program} {initial : Subst}
    {source : Configuration} (good : ConfigurationRefines initial source)
    {fuel : Nat} {state : Effects.State} {values input output : List Atom}
    (completed : run registry fuel source = .complete state values input output) :
    ∃ final answers, Relation.ReflTransGen (Transition registry) source final ∧
      final.control = .returned answers ∧ final.frames = [] ∧
      final.state = state ∧ final.input = input ∧ final.output = output ∧
      values = answers.map (fun answer => resolve answer.bindings answer.value) ∧
      ∀ answer ∈ answers, BindingRefines initial answer.bindings := by
  have derivation := (completed_run_iff_derivation registry source state values input output).mp ⟨fuel, completed⟩
  obtain ⟨final, answers, steps, returned, frames, finalState, finalInput, finalOutput, results⟩ :=
    derivation.completed_endpoint
  exact ⟨final, answers, steps, returned, frames, finalState, finalInput, finalOutput, results,
    reached_answers_refine steps good answers returned⟩

namespace RefinementControls

def emptyRegistry : SpaceSemantics.Program := { equations := [], declarations := [] }

theorem actual_control_forms (value : Atom) :
    sourceControlForm (.expression [.symbol "let", .var "x", value, .var "x"]) = true ∧
    sourceControlForm (.expression [.symbol "let*", .expression [], value]) = true ∧
    sourceControlForm (.expression [.symbol "case", value, .expression []]) = true ∧
    sourceControlForm (.expression [.symbol "if", value, value, value]) = true ∧
    sourceControlForm (.expression [.symbol "collapse", value]) = true ∧
    sourceControlForm (.expression [.symbol "superpose", .expression [value]]) = true ∧
    sourceControlForm (.expression [.symbol "empty"]) = true ∧
    sourceControlForm (.expression [.symbol "quote", value]) = true ∧
    sourceControlForm (.expression [.symbol "match", .symbol "&self", .var "x", value]) = true := by
  simp only [sourceControlForm, and_self]

theorem unique_is_ordinary_in_this_profile (value : Atom) :
    sourceControlForm (.expression [.symbol "unique", value]) = false := rfl

theorem unique_dispatches_as_data (value : Atom) :
    step emptyRegistry { state := Effects.empty, control := .evaluate [] (.expression [.symbol "unique", value]) } =
      some { state := Effects.empty, control := .arguments [] .data [.symbol "unique", value] [] 0 } := by
  rfl

end RefinementControls

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
