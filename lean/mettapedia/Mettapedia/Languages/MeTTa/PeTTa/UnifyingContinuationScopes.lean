import Mettapedia.Languages.MeTTa.PeTTa.UnifyingFrontierScopes

/-!
# Variable support through the actual binding and selection continuations

The source helpers retain branch substitutions and saved bodies. Their support
laws quantify over open terms and arbitrary pending alternatives; unification
failure or exhaustion is never changed into an artificial successful branch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem bindAnswers_supported (allowed : String → Prop) (pattern body : Atom)
    (patternGood : Supported allowed pattern) (bodyGood : Supported allowed body) :
    ∀ answers continued, (∀ answer ∈ answers, AnswerSupported allowed answer) →
      bindAnswers pattern body answers = some continued →
      ∀ control ∈ continued, ControlSupported allowed control := by
  intro answers
  induction answers with
  | nil => intro continued _ bound; cases bound; simp
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
              exact ih _ (fun item member => good item (by simp [member])) tailRun
          | ok bindings =>
              simp [unified] at bound
              subst continued
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · simp only [ControlSupported]
                exact ⟨unifyBinding_supported allowed _ _ _ _ (good answer (by simp)).2
                  patternGood (good answer (by simp)).1 unified,bodyGood⟩
              · exact ih _ (fun item member => good item (by simp [member])) tailRun control present

theorem selectCase_supported (allowed : String → Prop) (bindings : Subst) (value : Atom)
    (good : SupportedBindings allowed bindings) (valueGood : Supported allowed value) :
    ∀ cases bound body, (∀ branch ∈ cases, Supported allowed branch.1 ∧ Supported allowed branch.2) →
      selectCase bindings value cases = some (some (bound,body)) →
      SupportedBindings allowed bound ∧ Supported allowed body := by
  intro cases
  induction cases with
  | nil => intro _ _ _ selected; cases selected
  | cons branch rest ih =>
      obtain ⟨pattern,body⟩ := branch
      intro bound chosen casesGood selected
      simp only [selectCase] at selected
      cases unified : unifyAsPattern bindings pattern value with
      | exhausted => simp [unified] at selected
      | clash =>
          rw [unified] at selected
          exact ih _ _ (fun branch member => casesGood branch (by simp [member])) selected
      | ok middle =>
          rw [unified] at selected
          cases selected
          change unifyPattern (fuelFor bindings pattern value) bindings pattern value = .ok bound at unified
          exact ⟨unifyPattern_supported allowed _ _ _ pattern value good
            (casesGood (pattern,body) (by simp)).1 valueGood unified,
            (casesGood (pattern,body) (by simp)).2⟩

theorem selectAnswers_supported (allowed : String → Prop) (cases : SpaceSemantics.Cases)
    (casesGood : ∀ branch ∈ cases, Supported allowed branch.1 ∧ Supported allowed branch.2) :
    ∀ answers continued, (∀ answer ∈ answers, AnswerSupported allowed answer) →
      selectAnswers cases answers = some continued →
      ∀ control ∈ continued, ControlSupported allowed control := by
  intro answers
  induction answers with
  | nil => intro continued _ selected; cases selected; simp
  | cons answer rest ih =>
      intro continued good selected
      simp only [selectAnswers] at selected
      cases tailRun : selectAnswers cases rest with
      | none => simp [tailRun] at selected
      | some tail =>
          simp only [tailRun] at selected
          cases chosen : selectCase answer.bindings answer.value cases with
          | none => simp [chosen] at selected
          | some selection =>
              cases selection with
              | none =>
                  simp [chosen] at selected
                  subst continued
                  exact ih _ (fun item member => good item (by simp [member])) tailRun
              | some pair =>
                  obtain ⟨bindings,body⟩ := pair
                  simp [chosen] at selected
                  subst continued
                  intro control member
                  rcases List.mem_cons.mp member with rfl | present
                  · simpa only [ControlSupported] using selectCase_supported allowed _ _
                      (good answer (by simp)).2 (good answer (by simp)).1 _ _ _ casesGood chosen
                  · exact ih _ (fun item member => good item (by simp [member])) tailRun control present

theorem readCases_supported (allowed : String → Prop) :
    ∀ rows cases, (∀ row ∈ rows, Supported allowed row) → Eval.readCases rows = some cases →
      ∀ branch ∈ cases, Supported allowed branch.1 ∧ Supported allowed branch.2 := by
  intro rows
  induction rows with
  | nil => intro cases _ read; cases read; simp
  | cons row rest ih =>
      intro cases good read
      cases row with
      | var | symbol | grounded => cases read
      | expression items =>
          cases items with
          | nil => cases read
          | cons pattern items =>
              cases items with
              | nil => cases read
              | cons body items =>
                  cases items with
                  | cons => cases read
                  | nil =>
                      simp only [Eval.readCases] at read
                      obtain ⟨tail,tailRead,same⟩ := Option.map_eq_some_iff.mp read
                      cases same
                      intro branch member
                      rcases List.mem_cons.mp member with rfl | present
                      · simpa [supported_expression] using good (.expression [pattern,body]) (by simp)
                      · exact ih _ (fun row member => good row (by simp [member])) tailRead branch present

theorem nestedLets_supported (allowed : String → Prop) (body : Atom) (bodyGood : Supported allowed body) :
    ∀ pairs nested, (∀ pair ∈ pairs, Supported allowed pair) → Eval.nestedLets pairs body = some nested →
      Supported allowed nested := by
  intro pairs
  induction pairs with
  | nil => intro nested _ built; cases built; exact bodyGood
  | cons pair rest ih =>
      intro nested good built
      cases pair with
      | var | symbol | grounded => cases built
      | expression items =>
          cases items with
          | nil => cases built
          | cons pattern items =>
              cases items with
              | nil => cases built
              | cons value items =>
                  cases items with
                  | cons => cases built
                  | nil =>
                      simp only [Eval.nestedLets] at built
                      obtain ⟨tail,tailBuilt,same⟩ := Option.map_eq_some_iff.mp built
                      cases same
                      have pairGood : Supported allowed pattern ∧ Supported allowed value := by
                        simpa [supported_expression] using good (.expression [pattern,value]) (by simp)
                      have tailGood := ih _ (fun pair member => good pair (by simp [member])) tailBuilt
                      simpa [supported_expression] using And.intro pairGood.1 (And.intro pairGood.2 tailGood)

theorem resolved_values_supported (allowed : String → Prop) (bindings : Subst) (values : List Atom)
    (good : SupportedBindings allowed bindings) (valuesGood : ∀ value ∈ values, Supported allowed value) :
    ∀ value ∈ values.map (resolve bindings), Supported allowed value := by
  intro value member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact supported_resolve good original (valuesGood original present)

theorem partial_captures_supported (allowed : String → Prop) (value : Atom)
    (head : String) (captured : List Atom) (good : Supported allowed value)
    (recognized : partial? value = some (head,captured)) :
    ∀ value ∈ captured, Supported allowed value := by
  have same := (partial?_some value head captured).mp recognized
  rw [same] at good
  simpa [Eval.partialValue,Eval.partialTag,supported_expression] using good

theorem dispatchAnswer_supported (allowed : String → Prop) (answer : Answer)
    (good : AnswerSupported allowed answer) : ControlSupported allowed (dispatchAnswer answer) := by
  unfold dispatchAnswer
  split
  · rename_i head values same
    have valueGood := good.1
    rw [same] at valueGood
    have parts := (supported_expression_cons allowed head values).mp valueGood
    simpa only [ControlSupported,supported_expression] using And.intro good.2 parts
  · simpa only [ControlSupported,List.mem_singleton,forall_eq] using good

theorem invocationFrames_supported (allowed : String → Prop) (control : Control) (frames : List Frame)
    (good : ∀ frame ∈ frames, FrameSupported allowed frame) :
    ∀ frame ∈ invocationFrames control frames, FrameSupported allowed frame := by
  cases control <;> simpa only [invocationFrames,List.mem_cons,forall_eq_or_imp,FrameSupported,true_and] using good

theorem recoverDynamic_supported (allowed : String → Prop) (frames : List Frame) :
    ∀ earned answers rest, (∀ answer ∈ earned, AnswerSupported allowed answer) →
      (∀ frame ∈ frames, FrameSupported allowed frame) →
      recoverDynamic earned frames = some (answers,rest) →
      (∀ answer ∈ answers, AnswerSupported allowed answer) ∧ ∀ frame ∈ rest, FrameSupported allowed frame := by
  induction frames with
  | nil => intro _ _ _ _ _ recovered; cases recovered
  | cons frame tail ih =>
      intro earned answers rest earnedGood framesGood recovered
      have first := framesGood frame (by simp)
      have remaining : ∀ frame ∈ tail, FrameSupported allowed frame :=
        fun frame member => framesGood frame (by simp [member])
      cases frame with
      | dynamicCall => cases recovered; exact ⟨earnedGood,remaining⟩
      | sequence pending completed =>
          apply ih (completed ++ earned) answers rest ?_ remaining recovered
          intro answer member
          exact (List.mem_append.mp member).elim (first.2 answer) (earnedGood answer)
      | _ => exact ih [] answers rest (by simp) remaining recovered

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
