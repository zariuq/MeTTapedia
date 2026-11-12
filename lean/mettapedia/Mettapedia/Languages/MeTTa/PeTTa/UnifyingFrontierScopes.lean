import Mettapedia.Languages.MeTTa.PeTTa.UnifyingScopeInvariant

/-!
# Allocated support through actual clause and row frontiers

The computed frontier determines the range of activation numbers. Fresh row
and clause copies are supported below that range's endpoint; the executable
unifiers preserve the support of each branch. No matching service or proposed
frontier is assumed to satisfy the conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.ScopedString (Before)

theorem renamed_supported_before (ceiling use : Nat) (fits : use < ceiling) (term : Atom) :
    Supported (Before ceiling) (rename use term) :=
  Supported.mono (fun _ old => Mettapedia.ScopedString.before_mono (by omega) old)
    (ScopedSource.renamed_allocated use term)

theorem selections_supported (ceiling : Nat) (bindings : Subst) (values : List Atom)
    (good : SupportedBindings (Before ceiling) bindings)
    (valuesGood : ∀ value ∈ values, Supported (Before ceiling) value) :
    ∀ use equations selected, use + equations.length ≤ ceiling →
      selections bindings values use equations = some selected →
      ∀ control ∈ selected, ControlSupported (Before ceiling) control := by
  intro use equations
  induction equations generalizing use with
  | nil => intro selected _ chosen; cases chosen; simp
  | cons equation rest ih =>
      intro selected fits chosen
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
              exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun
          | ok bound =>
              simp [unified] at chosen
              subst selected
              intro control member
              rcases List.mem_cons.mp member with rfl | member
              · simp only [ControlSupported]
                refine ⟨unifyArguments_supported _ _ _ _ _ good ?_ valuesGood unified,?_⟩
                · intro term present
                  obtain ⟨original,_,rfl⟩ := List.mem_map.mp present
                  exact renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) original
                · exact renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) equation.body
              · exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun control member

theorem queryBodies_supported (ceiling : Nat) (bindings : Subst) (pattern body : Atom)
    (good : SupportedBindings (Before ceiling) bindings)
    (patternGood : Supported (Before ceiling) pattern) (bodyGood : Supported (Before ceiling) body) :
    ∀ use rows selected, use + rows.length ≤ ceiling →
      queryBodies bindings pattern body use rows = some selected →
      ∀ control ∈ selected, ControlSupported (Before ceiling) control := by
  intro use rows
  induction rows generalizing use with
  | nil => intro selected _ chosen; cases chosen; simp
  | cons row rest ih =>
      intro selected fits chosen
      simp only [queryBodies] at chosen
      cases tailRun : queryBodies bindings pattern body (use + 1) rest with
      | none => simp [tailRun] at chosen
      | some tail =>
          simp only [tailRun] at chosen
          cases unified : unify bindings pattern (rename use row) with
          | exhausted => simp [unified] at chosen
          | clash =>
              simp [unified] at chosen
              subst selected
              exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun
          | ok bound =>
              simp [unified] at chosen
              subst selected
              intro control member
              rcases List.mem_cons.mp member with rfl | member
              · simp only [ControlSupported]
                exact ⟨unifyTerms_supported _ _ _ _ _ _ good patternGood
                  (renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) row)
                  unified,bodyGood⟩
              · exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun control member

theorem matchAnswers_supported (ceiling : Nat) (bindings : Subst) (pattern template : Atom)
    (good : SupportedBindings (Before ceiling) bindings)
    (patternGood : Supported (Before ceiling) pattern) (templateGood : Supported (Before ceiling) template) :
    ∀ use rows answers, use + rows.length ≤ ceiling →
      matchAnswers bindings pattern template use rows = some answers →
      ∀ answer ∈ answers, AnswerSupported (Before ceiling) answer := by
  intro use rows
  induction rows generalizing use with
  | nil => intro answers _ queried; cases queried; simp
  | cons row rest ih =>
      intro answers fits queried
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
              exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun
          | ok bound =>
              simp [unified] at queried
              subst answers
              have boundGood := unifyTerms_supported _ _ _ _ _ _ good patternGood
                (renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) row) unified
              intro answer member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨supported_resolve boundGood template templateGood,boundGood⟩
              · exact ih _ _ (by simp only [List.length_cons] at fits; omega) tailRun answer member

theorem matchCall_supported (ceiling : Nat) (state : Effects.State) (bindings : Subst)
    (use : Nat) (values : List Atom) (answers : List Answer) (used : Nat)
    (good : SupportedBindings (Before ceiling) bindings)
    (valuesGood : ∀ value ∈ values, Supported (Before ceiling) value)
    (fits : use + used ≤ ceiling)
    (queried : matchCall state bindings use values = some (.ok (answers,used))) :
    ∀ answer ∈ answers, AnswerSupported (Before ceiling) answer := by
  unfold matchCall at queried
  split at queried
  · rename_i location pattern template
    split at queried
    · cases queried
    · obtain ⟨returned,source,same⟩ := Option.map_eq_some_iff.mp queried
      cases same
      exact matchAnswers_supported ceiling bindings pattern template good
        (valuesGood pattern (by simp)) (valuesGood template (by simp)) _ _ _ fits source
  · cases queried

theorem application_supported (ceiling : Nat) (registry : SpaceSemantics.Program)
    (live : List SpaceSemantics.Equation) (head : String) (values : List Atom) (bindings : Subst)
    (use : Nat) (selected : Control) (used : Nat)
    (good : SupportedBindings (Before ceiling) bindings)
    (valuesGood : ∀ value ∈ values, Supported (Before ceiling) value)
    (fits : use + used ≤ ceiling)
    (chosen : application registry live head values bindings use = some (selected,used)) :
    ControlSupported (Before ceiling) selected := by
  unfold application at chosen
  split at chosen
  · obtain ⟨controls,selectedRun,same⟩ := Option.map_eq_some_iff.mp chosen
    cases same
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    exact selections_supported ceiling bindings values good valuesGood _ _ _ fits selectedRun
  · split at chosen
    · cases chosen
      simp only [ControlSupported]
    · cases chosen
      simp only [ControlSupported,List.mem_singleton]
      intro answer same
      subst answer
      refine ⟨?_,good⟩
      simpa [Eval.partialValue,Eval.partialTag,supported_expression] using valuesGood

theorem queries_supported (ceiling : Nat) (state : Effects.State) (pattern body : Atom)
    (patternGood : Supported (Before ceiling) pattern) (bodyGood : Supported (Before ceiling) body) :
    ∀ use answers continued used,
      (∀ answer ∈ answers, AnswerSupported (Before ceiling) answer) →
      use + used ≤ ceiling → queries state pattern body use answers = some (continued,used) →
      ∀ control ∈ continued, ControlSupported (Before ceiling) control := by
  intro use answers
  induction answers generalizing use with
  | nil => intro continued used _ _ queried; cases queried; simp
  | cons answer rest ih =>
      intro continued used good fits queried
      simp only [queries] at queried
      cases read : Effects.readHandle answer.value >>= state.read with
      | none =>
          simp only [read] at queried
          cases tailRun : queries state pattern body use rest with
          | none => simp [tailRun] at queried
          | some pair =>
              obtain ⟨tail,usedTail⟩ := pair
              simp [tailRun] at queried
              obtain ⟨rfl,rfl⟩ := queried
              intro control member
              rcases List.mem_cons.mp member with rfl | present
              · simp only [ControlSupported]
              · exact ih _ _ _ (fun item member => good item (by simp [member])) fits tailRun control present
      | some rows =>
          simp only [read] at queried
          cases here : queryBodies answer.bindings pattern body use rows with
          | none => simp [here] at queried
          | some headControls =>
              simp only [here] at queried
              cases tailRun : queries state pattern body (use + rows.length) rest with
              | none => simp [tailRun] at queried
              | some pair =>
                  obtain ⟨tail,usedTail⟩ := pair
                  simp [tailRun] at queried
                  obtain ⟨rfl,rfl⟩ := queried
                  intro control member
                  rcases List.mem_append.mp member with present | present
                  · exact queryBodies_supported ceiling answer.bindings pattern body
                      (good answer (by simp)).2 patternGood bodyGood _ _ _ (by omega) here control present
                  · exact ih _ _ _ (fun item member => good item (by simp [member]))
                      (by omega) tailRun control present

theorem copyTerms_supported (ceiling : Nat) : ∀ use terms,
    use + terms.length ≤ ceiling → ∀ term ∈ copyTerms use terms, Supported (Before ceiling) term := by
  intro use terms
  induction terms generalizing use with
  | nil => intro _ term present; cases present
  | cons first rest ih =>
      intro fits term present
      simp only [copyTerms,List.mem_cons] at present
      rcases present with rfl | present
      · exact renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) first
      · exact ih (use + 1) (by simp only [List.length_cons] at fits; omega) term present

theorem copies_supported (ceiling : Nat) : ∀ use answers,
    use + answers.length ≤ ceiling → ∀ term ∈ copies use answers, Supported (Before ceiling) term := by
  intro use answers
  induction answers generalizing use with
  | nil => intro _ term present; cases present
  | cons answer rest ih =>
      intro fits term present
      simp only [copies,List.mem_cons] at present
      rcases present with rfl | present
      · exact renamed_supported_before ceiling use (by simp only [List.length_cons] at fits; omega) _
      · exact ih (use + 1) (by simp only [List.length_cons] at fits; omega) term present

/-- The runtime query's real transition retains a well-scoped caller world
and continuation. Its output support is proved from row copying and actual
unification, rather than required as a condition of native admission. -/
theorem native_query_scoped_step (registry : SpaceSemantics.Program) (source : Configuration)
    (bindings : Subst) (held : List Atom) (index : Nat) (answers : List Answer) (used : Nat)
    (well : WellScoped source)
    (control : source.control = .arguments bindings (.function "match") [] held index)
    (queried : matchCall source.state bindings source.uses (held.map (resolve bindings)) =
      some (.ok (answers,used))) :
    step registry source = some {source with control := .returned answers, uses := source.uses + used} ∧
      WellScoped {source with control := .returned answers, uses := source.uses + used} := by
  refine ⟨transition_step (.native_query control queried),?_⟩
  have included : ∀ key, Before source.uses key → Before (source.uses + used) key :=
    fun _ old => Mettapedia.ScopedString.before_mono (by omega) old
  have caller := well
  unfold WellScoped at caller
  have later := caller.mono included
  have inputs : SupportedBindings (Before (source.uses + used)) bindings ∧
      (∀ term ∈ held, Supported (Before (source.uses + used)) term) := by
    simpa only [control,ControlSupported,List.not_mem_nil,false_implies,implies_true,true_and] using later.1
  refine ⟨?_,later.2.1,later.2.2.1,later.2.2.2⟩
  simp only [ControlSupported]
  apply matchCall_supported _ _ _ _ _ _ _ inputs.1 _ (Nat.le_refl _) queried
  intro term present
  obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
  exact supported_resolve inputs.1 original (inputs.2 original member)

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
