import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.BoundVariables

/-!
# HE drops an error answer when another alternative succeeds: a named difference from PeTTa

HE's evaluation publishes the successful answers of an expression when there are any, and its
errors only when every answer is an error. The tree's HE machine has this filter: the publication
of a call's batch is `Machines.OrderedProtocol.Completion.SuccessPriorityRel` over the batch, which
keeps the non-error answers if one exists and every answer otherwise. PeTTa publishes every answer.

On `{(= (g) 1), (= (g) (Error foo bar))}`, the call `(g)`:

* `equations_steps_mixed`: HE's equation loop when a body is evaluated or, being an error or
  `Empty`, returned as it is (`returnStopped`);
* `mixed_run`: a complete run of HE's machine exists, publishing `1`;
* `mixed_source`: every derivation of HE's completed relation for `(g)` publishes exactly `1`: the
  body `1` answers `1`, the body `(Error foo bar)` is returned as it is, and success priority drops
  the error;
* `error_dropped_every_run`: a complete run exists and every complete run publishes `[1]`; PeTTa's
  run yields `1` and `(Error foo bar)`.
* `not_union`: HE's answers are not the union over the alternatives: with only `(= (g) 1)` every
  complete run publishes `1`, with only `(= (g) (Error foo bar))` it publishes `(Error foo bar)`,
  and with both it publishes `1` alone. Adding an equation removed an answer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace ErrorAlternatives

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables

/-- **A body HE returns as it is**: closed, no function, and an error or `Empty`. -/
structure StoppedBody (t : Atom) : Prop where
  closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs t name
  notFunction : ∀ policy : Policy, ¬ Completed.FunctionPending policy (Entry.Value.ofAtom t)
  stopped : IsEmptyOrErrorRel t

section Loop

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **The equation loop when each body is evaluated or returned as it is.** Each work's body is
read as its instance under its unifier's frame; an instance meeting `BodyFacts` is evaluated, a
stopped one is returned as it is; the batches are concatenated in work order. -/
theorem equations_steps_mixed {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
        ((HEEvaluates dispatch lookup policy atoms i L ∧ BodyFacts i) ∨
          (StoppedBody i ∧ L = [i]))) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HERuns.HESteps dispatch lookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
              works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (.internal .equationsNil)⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨i, readsAs, kind⟩ := here
          rcases kind with ⟨evaluates, facts⟩ | ⟨stoppedBody, rfl⟩
          · obtain ⟨R, eraseR, pathR⟩ := evaluates live scope output
              (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
                .append (.equations live scope original Atom.undefinedType activation works) :: stack)
              emitted
            obtain ⟨R', eraseR', pathR'⟩ := equations_steps_mixed works Ls'
              (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
              (.prepend (R ++ []) :: stack) emitted
            refine ⟨(R ++ []) ++ R', ?_, ?_⟩
            · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
            · refine .head (.internal (.equationsCons sameBindings unified)) ?_
              rw [readsAs output sameBindings]
              refine .head (.internal (.boundaryProducerRaw (facts.notFunction policy))) ?_
              refine .head (.internal .boundaryBatch) ?_
              refine .head (.internal .boundaryBatchCons) ?_
              refine .head (.internal .boundaryReturned) ?_
              refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
              · rw [Entry.Value.erase_ofAtom]
                exact facts.notRefused
              · rw [Entry.Value.erase_ofAtom]
                exact facts.notStopped
              refine .trans pathR ?_
              refine .head (.internal .append) ?_
              refine .head (.internal .boundaryBatchNil) ?_
              refine .head (.internal .prepend) ?_
              refine .head (.internal .append) ?_
              refine .trans pathR' ?_
              exact .single (.internal .prepend)
          · obtain ⟨R', eraseR', pathR'⟩ := equations_steps_mixed works Ls'
              (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
              (.prepend ([(Entry.Value.ofAtom i, output)] ++ []) :: stack) emitted
            refine ⟨([(Entry.Value.ofAtom i, output)] ++ []) ++ R', ?_, ?_⟩
            · rw [List.append_nil, List.map_append, eraseR', List.flatten_cons]
              simp
            · refine .head (.internal (.equationsCons sameBindings unified)) ?_
              rw [readsAs output sameBindings]
              refine .head (.internal (.boundaryProducerRaw (stoppedBody.notFunction policy))) ?_
              refine .head (.internal .boundaryBatch) ?_
              refine .head (.internal .boundaryBatchCons) ?_
              refine .head (.internal .boundaryReturned) ?_
              refine .head (.internal (.returnStopped ?_)) ?_
              · rw [Entry.Value.erase_ofAtom]
                exact stoppedBody.stopped
              refine .head (.internal .append) ?_
              refine .head (.internal .boundaryBatchNil) ?_
              refine .head (.internal .prepend) ?_
              refine .head (.internal .append) ?_
              refine .trans pathR' ?_
              exact .single (.internal .prepend)

end Loop

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open WholeRunWords.Double (noHost)

/-- `1`. -/
abbrev one : Atom := .grounded (.int 1)

/-- `(Error foo bar)`. -/
abbrev fooBar : Atom := Atom.error (sym "foo") (sym "bar")

/-- `{(= (g) 1), (= (g) (Error foo bar))}`. -/
abbrev mixedRows : List Atom := [rule (app "g" []) one, rule (app "g" []) fooBar]

/-- `{(= (g) 1)}`. -/
abbrev successRows : List Atom := [rule (app "g" []) one]

/-- `{(= (g) (Error foo bar))}`. -/
abbrev errorRows : List Atom := [rule (app "g" []) fooBar]

theorem one_data : DataAtom one := .grounded _

theorem fooBar_closed :
    ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs fooBar name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> cases inner

theorem fooBar_stopped : StoppedBody fooBar where
  closed := fooBar_closed
  notFunction := fun policy pending => by
    obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp [fooBar, Atom.error] at same
  stopped := Or.inr ⟨[sym "foo", sym "bar"], rfl⟩

theorem fooBar_isError : isErrorAtom fooBar = true := rfl

/-- A one-row or two-row program of `(g)`'s equations. -/
theorem rows_consFree {atoms : List Atom} (rows : ∀ row ∈ atoms, row = rule (app "g" []) one ∨
    row = rule (app "g" []) fooBar) :
    ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  rcases rows row member with rfl | rfl <;>
    exact rule_consFree (fun a member => by cases member)

theorem rows_scoped {atoms : List Atom} (rows : ∀ row ∈ atoms, row = rule (app "g" []) one ∨
    row = rule (app "g" []) fooBar) : ScopedProgram atoms := by
  intro row member
  refine ⟨rows_consFree rows row member, ?_⟩
  rcases rows row member with rfl | rfl
  · intro lhs rhs same
    cases same
    decide
  · intro lhs rhs same
    cases same
    decide

theorem mixed_rows : ∀ row ∈ mixedRows, row = rule (app "g" []) one ∨ row = rule (app "g" []) fooBar := by
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem g_ordinary : Ordinary noHost mixedRows "g" [] :=
  ⟨.symbol (by decide) (by decide), by simp, by decide +kernel, fun impossible => impossible,
    by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩

theorem mixed_instances : regionInstances mixedRows "g" [] = [one, fooBar] := by
  decide +kernel

theorem mixed_bodies : regionBodies mixedRows "g" [] = [one, fooBar] := by
  decide +kernel

/-- **A complete run of HE on `(g)` publishes `1`.** -/
theorem mixed_run (policy : Policy) :
    ∃ emitted : List Result, emitted.map (fun r => r.1.erase) = [one] ∧
      HERuns.HESteps noHost Completed.rawLookup policy
        (load (Space.ofList mixedRows) (app "g" []) Atom.undefinedType)
        ⟨Space.ofList mixedRows, .returning [], [], emitted⟩ := by
  have items : ∀ a ∈ Atom.symbol "g" :: ([] : List Atom), DataAtom a := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact .symbol (by decide) (by decide)
  have untyped : (Space.ofList mixedRows).atoms.filter (typeRegion (.symbol "g")) = [] := by
    decide +kernel
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList mixedRows) (Atom.undefinedType :: [])
    (.expression [.symbol "g"]) Completed.Frame.empty.bindings
  have instances := works_instances (policy := policy) (args := [])
    (fun a member => by cases member) (rows_scoped mixed_rows)
    Completed.Frame.empty.certified.satisfiable frontier
  rw [mixed_instances] at instances
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    cases instances
  have frontier' : EquationFrontierRel (Space.ofList mixedRows) (Atom.undefinedType :: [])
      (callValue "g" []).erase Completed.Frame.empty.bindings works := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding Completed.Frame.empty.environment (callValue "g" [])
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have bodies : List.Forall₂ (fun i L => (HEEvaluates noHost Completed.rawLookup policy mixedRows i L ∧
      BodyFacts i) ∨ (StoppedBody i ∧ L = [i])) [one, fooBar] [[one], [fooBar]] :=
    .cons (Or.inl ⟨HERuns.he_data raw_answers mixedRows one_data,
        settles_facts (Settles.data (dispatch := noHost) (atoms := mixedRows) one_data (by decide))⟩)
      (.cons (Or.inr ⟨fooBar_stopped, rfl⟩) .nil)
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
      ((HEEvaluates noHost Completed.rawLookup policy mixedRows i L ∧ BodyFacts i) ∨
        (StoppedBody i ∧ L = [i]))) works [[one], [fooBar]] :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, kind⟩ := both
      exact ⟨i, reads, kind⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_mixed (dispatch := noHost) (lookup := Completed.rawLookup)
    (policy := policy) (atoms := mixedRows) (live := []) (scope := []) (original := callValue "g" [])
    (activation := Completed.Frame.empty) works [[one], [fooBar]] unifiers related
    (.append (.calls [] [] Atom.undefinedType []) :: .publish (app "g" []) :: []) []
  simp only [List.flatten_cons, List.flatten_nil, List.singleton_append, List.append_nil] at eraseR
  obtain ⟨r₁, r₂, rfl, first, second⟩ : ∃ r₁ r₂ : Result, R = [r₁, r₂] ∧ r₁.1.erase = one ∧
      r₂.1.erase = fooBar := by
    rcases R with _ | ⟨r₁, _ | ⟨r₂, _ | ⟨r₃, rest⟩⟩⟩ <;> simp at eraseR
    exact ⟨r₁, r₂, rfl, eraseR.1, eraseR.2⟩
  have closed : ∀ r ∈ [r₁, r₂], ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs r.1.erase name := by
    intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [first]
      exact (answerable_of_data one_data).closed
    · rw [second]
      exact fooBar_closed
  have unchanged : ([r₁, r₂] ++ []).map (Completed.readResult policy) = [r₁, r₂] := by
    rw [List.append_nil]
    exact map_fixed fun r member => HERuns.readResult_closed policy r (closed r member)
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      (([r₁, r₂] ++ []).map (Completed.readResult policy)) [r₁] := by
    rw [unchanged]
    have chosen := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
      (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [r₁, r₂])
      ⟨r₁, List.mem_cons_self, by rw [first]; rfl⟩
    have filtered : [r₁, r₂].filter (fun r : Result => !isErrorAtom r.1.erase) = [r₁] := by
      simp [List.filter, first, second, fooBar_isError]
      rfl
    rwa [filtered] at chosen
  refine ⟨[] ++ [r₁].map (Completed.publishResult policy (app "g" [])), ?_, ?_⟩
  · simp [Completed.publishResult, first]
  · refine .trans (HERuns.call_entry_steps raw_answers items untyped [] [] Completed.Frame.empty [] [])
      ?_
    refine .head (.internal (.callEquations (HERuns.value_not_error g_ordinary.head
      (callValue_erase "g" [])) (HERuns.value_nonGrounded g_ordinary.notHost
        (g_ordinary.notInstruction) (callValue_erase "g" [])) frontier' worksNonempty)) ?_
    refine .trans pathR ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .callsNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal (.publish selected)) ?_
    exact HERuns.publish_all _ _ []

/-- **Every derivation of HE's completed relation for `(g)` publishes `1`.** The body `1` answers
`1`; the body `(Error foo bar)` is returned as it is; success priority keeps `1` alone. -/
theorem mixed_source (policy : Policy) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList mixedRows) noHost Completed.rawLookup [] []
      (Entry.Value.ofAtom (app "g" [])) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [one] := by
  have fixed : ∀ b ∈ regionBodies mixedRows "g" [], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [mixed_bodies]
    intro b member rename
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars, fooBar,
        Atom.error]
  obtain ⟨after, children, selected, called, chosen, erased⟩ :=
    call_source raw_contract g_ordinary derived
  rcases callRel_source (rows_consFree mixed_rows) g_ordinary fixed called with
    ⟨_, empty⟩ | ⟨works, _, bodies, equations⟩
  · rw [mixed_bodies] at empty
    cases empty
  · rw [mixed_bodies] at bodies
    obtain ⟨w₁, w₂, rfl, body₁, body₂⟩ : ∃ w₁ w₂ : EquationWork, works = [w₁, w₂] ∧
        w₁.body = one ∧ w₂.body = fooBar := by
      rcases works with _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, rest⟩⟩⟩ <;> simp at bodies
      exact ⟨w₁, w₂, rfl, bodies.1, bodies.2⟩
    cases equations with
    | cons _ _ boundary₁ batch₁ later₁ =>
        rw [body₁, HERuns.read_closed policy _ (answerable_of_data one_data).closed] at boundary₁
        cases later₁ with
        | cons _ _ boundary₂ batch₂ later₂ =>
            cases later₂
            rw [body₂, HERuns.read_closed policy _ fooBar_closed] at boundary₂
            cases boundary₁ with
            | producerFunction pending _ =>
                obtain ⟨⟨_, same⟩, _⟩ := pending
                rw [Entry.Value.erase_ofAtom] at same
                cases same
            | producerRaw _ =>
                cases batch₁ with
                | cons returned₁ tail₁ =>
                    cases tail₁
                    cases returned₁ with
                    | returned answered₁ =>
                        cases answered₁ with
                        | notReducible same =>
                            rw [Entry.Value.erase_ofAtom] at same
                            cases same
                        | stopped stopped =>
                            exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped)
                              one_data.not_stopped
                        | evaluate _ _ evaluated =>
                            obtain ⟨after₁, rfl⟩ := data_source raw_contract one_data evaluated
                            cases boundary₂ with
                            | producerFunction pending _ =>
                                exact absurd pending (fooBar_stopped.notFunction policy)
                            | producerRaw _ =>
                                cases batch₂ with
                                | cons returned₂ tail₂ =>
                                    cases tail₂
                                    cases returned₂ with
                                    | returned answered₂ =>
                                        cases answered₂ with
                                        | notReducible same =>
                                            rw [Entry.Value.erase_ofAtom] at same
                                            cases same
                                        | evaluate _ notStopped _ =>
                                            exact absurd (by
                                              rw [Entry.Value.erase_ofAtom]
                                              exact fooBar_stopped.stopped) notStopped
                                        | stopped _ =>
                                            simp only [List.append_nil, List.singleton_append] at chosen
                                            rw [map_fixed fun r member => HERuns.readResult_closed policy r
                                              (by
                                                simp only [List.mem_cons, List.not_mem_nil,
                                                  or_false] at member
                                                rcases member with rfl | rfl
                                                · simpa using (answerable_of_data one_data).closed
                                                · simpa using fooBar_closed)] at chosen
                                            have filtered :=
                                              Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
                                                chosen
                                                (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
                                                  ⟨(Entry.Value.ofAtom one, after₁), List.mem_cons_self,
                                                    by simp [isErrorAtom]⟩)
                                            rw [erased, filtered]
                                            simp [isErrorAtom, fooBar, Atom.error]

theorem error_rows : ∀ row ∈ errorRows, row = rule (app "g" []) one ∨ row = rule (app "g" []) fooBar := by
  intro row member
  simp only [List.mem_singleton] at member
  exact Or.inr member

theorem error_ordinary : Ordinary noHost errorRows "g" [] :=
  ⟨.symbol (by decide) (by decide), by simp, by decide +kernel, fun impossible => impossible,
    by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩

theorem error_instances : regionInstances errorRows "g" [] = [fooBar] := by
  decide +kernel

theorem error_bodies : regionBodies errorRows "g" [] = [fooBar] := by
  decide +kernel

/-- **A complete run of HE on `(g)` with only the error row publishes the error.** -/
theorem error_only_run (policy : Policy) :
    ∃ emitted : List Result, emitted.map (fun r => r.1.erase) = [fooBar] ∧
      HERuns.HESteps noHost Completed.rawLookup policy
        (load (Space.ofList errorRows) (app "g" []) Atom.undefinedType)
        ⟨Space.ofList errorRows, .returning [], [], emitted⟩ := by
  have items : ∀ a ∈ Atom.symbol "g" :: ([] : List Atom), DataAtom a := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact .symbol (by decide) (by decide)
  have untyped : (Space.ofList errorRows).atoms.filter (typeRegion (.symbol "g")) = [] := by
    decide +kernel
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList errorRows) (Atom.undefinedType :: [])
    (.expression [.symbol "g"]) Completed.Frame.empty.bindings
  have instances := works_instances (policy := policy) (args := [])
    (fun a member => by cases member) (rows_scoped error_rows)
    Completed.Frame.empty.certified.satisfiable frontier
  rw [error_instances] at instances
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    cases instances
  have frontier' : EquationFrontierRel (Space.ofList errorRows) (Atom.undefinedType :: [])
      (callValue "g" []).erase Completed.Frame.empty.bindings works := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding Completed.Frame.empty.environment (callValue "g" [])
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have bodies : List.Forall₂ (fun i L => (HEEvaluates noHost Completed.rawLookup policy errorRows i L ∧
      BodyFacts i) ∨ (StoppedBody i ∧ L = [i])) [fooBar] [[fooBar]] :=
    .cons (Or.inr ⟨fooBar_stopped, rfl⟩) .nil
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
      ((HEEvaluates noHost Completed.rawLookup policy errorRows i L ∧ BodyFacts i) ∨
        (StoppedBody i ∧ L = [i]))) works [[fooBar]] :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, kind⟩ := both
      exact ⟨i, reads, kind⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_mixed (dispatch := noHost) (lookup := Completed.rawLookup)
    (policy := policy) (atoms := errorRows) (live := []) (scope := []) (original := callValue "g" [])
    (activation := Completed.Frame.empty) works [[fooBar]] unifiers related
    (.append (.calls [] [] Atom.undefinedType []) :: .publish (app "g" []) :: []) []
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at eraseR
  obtain ⟨r, rfl, only⟩ : ∃ r : Result, R = [r] ∧ r.1.erase = fooBar := by
    rcases R with _ | ⟨r, _ | ⟨r₂, rest⟩⟩ <;> simp at eraseR
    exact ⟨r, rfl, eraseR⟩
  have unchanged : ([r] ++ []).map (Completed.readResult policy) = [r] := by
    rw [List.append_nil, List.map_singleton, HERuns.readResult_closed policy r
      (by rw [only]; exact fooBar_closed)]
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      (([r] ++ []).map (Completed.readResult policy)) [r] := by
    rw [unchanged]
    exact .allErrors fun x member => by
      rw [List.mem_singleton] at member
      subst member
      rw [only]
      rfl
  refine ⟨[] ++ [r].map (Completed.publishResult policy (app "g" [])), ?_, ?_⟩
  · simp [Completed.publishResult, only]
  · refine .trans (HERuns.call_entry_steps raw_answers items untyped [] [] Completed.Frame.empty [] [])
      ?_
    refine .head (.internal (.callEquations (HERuns.value_not_error error_ordinary.head
      (callValue_erase "g" [])) (HERuns.value_nonGrounded error_ordinary.notHost
        (error_ordinary.notInstruction) (callValue_erase "g" [])) frontier' worksNonempty)) ?_
    refine .trans pathR ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .callsNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal (.publish selected)) ?_
    exact HERuns.publish_all _ _ []

/-- **Every derivation for `(g)` with only the error row publishes the error.** -/
theorem error_only_source (policy : Policy) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList errorRows) noHost Completed.rawLookup [] []
      (Entry.Value.ofAtom (app "g" [])) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [fooBar] := by
  have fixed : ∀ b ∈ regionBodies errorRows "g" [], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [error_bodies]
    intro b member rename
    simp only [List.mem_singleton] at member
    subst member
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars, fooBar,
      Atom.error]
  obtain ⟨after, children, selected, called, chosen, erased⟩ :=
    call_source raw_contract error_ordinary derived
  rcases callRel_source (rows_consFree error_rows) error_ordinary fixed called with
    ⟨_, empty⟩ | ⟨works, _, bodies, equations⟩
  · rw [error_bodies] at empty
    cases empty
  · rw [error_bodies] at bodies
    obtain ⟨w, rfl, body⟩ : ∃ w : EquationWork, works = [w] ∧ w.body = fooBar := by
      rcases works with _ | ⟨w, _ | ⟨w₂, rest⟩⟩ <;> simp at bodies
      exact ⟨w, rfl, bodies⟩
    cases equations with
    | cons _ _ boundary batch later =>
        cases later
        rw [body, HERuns.read_closed policy _ fooBar_closed] at boundary
        cases boundary with
        | producerFunction pending _ => exact absurd pending (fooBar_stopped.notFunction policy)
        | producerRaw _ =>
            cases batch with
            | cons returned tail =>
                cases tail
                cases returned with
                | returned answered =>
                    cases answered with
                    | notReducible same =>
                        rw [Entry.Value.erase_ofAtom] at same
                        cases same
                    | evaluate _ notStopped _ =>
                        exact absurd (by
                          rw [Entry.Value.erase_ofAtom]
                          exact fooBar_stopped.stopped) notStopped
                    | stopped _ =>
                        simp only [List.append_nil] at chosen
                        rw [map_fixed fun r member => HERuns.readResult_closed policy r (by
                          rw [List.mem_singleton] at member
                          subst member
                          simpa using fooBar_closed)] at chosen
                        have same :=
                          Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
                            chosen
                            (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.allErrors
                              fun x member => by
                                rw [List.mem_singleton] at member
                                subst member
                                simp [isErrorAtom, fooBar, Atom.error])
                        rw [erased, same]
                        simp

/-- `(g)` with only `(= (g) 1)` settles. -/
theorem success_settles : Settles noHost successRows (app "g" []) := by
  have ordinary : Ordinary noHost successRows "g" [] :=
    ⟨.symbol (by decide) (by decide), by simp, by decide +kernel, fun impossible => impossible,
      by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩
  have bodies : regionBodies successRows "g" [] = [one] := by decide +kernel
  refine .call ordinary (by rw [bodies]; simp) ?_
  rw [bodies]
  intro b member
  rw [List.mem_singleton] at member
  subst member
  exact .data one_data (by decide)

/-- **HE's answers are not the union over the alternatives.** A complete run exists for each of the
three programs, and every complete run of `(g)` publishes: `1` with only `(= (g) 1)`;
`(Error foo bar)` with only `(= (g) (Error foo bar))`; and `1` alone with both equations, a bag that
is not the union of the two one-equation bags. -/
theorem not_union (policy : Policy) :
    ((∃ heAnswers : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList successRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList successRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList successRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList successRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [one]) ∧
    ((∃ heAnswers : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList errorRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList errorRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList errorRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList errorRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [fooBar]) ∧
    ((∃ heAnswers : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList mixedRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList mixedRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList mixedRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList mixedRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [one]) ∧
    (([one] : List Atom) : Multiset Atom) ≠
      (([one] : List Atom) : Multiset Atom) + (([fooBar] : List Atom) : Multiset Atom) := by
  have program : ∀ row ∈ successRows, RegionsWithVariables.ConsFreeHeads row :=
    rows_consFree fun row member => by
      simp only [List.mem_singleton] at member
      exact Or.inl member
  have computed : Streaming.values (Streaming.advance (translate successRows) 20
      (Streaming.enter { state := store successRows } (app "g" []))) = [one] := by
    decide +kernel
  have finished : (Streaming.advance (translate successRows) 20
      (Streaming.enter { state := store successRows } (app "g" []))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨successAnswers, successPath, _⟩, _⟩ :=
    answer_bags_every_run noHost policy program success_settles
  obtain ⟨N, every⟩ := every_complete_run noHost policy program success_settles
  obtain ⟨errorAnswers, _, errorPath⟩ := error_only_run policy
  obtain ⟨mixedAnswers, _, mixedPath⟩ := mixed_run policy
  refine ⟨⟨⟨successAnswers, successPath⟩, fun emitted run => ?_⟩,
    ⟨⟨errorAnswers, errorPath⟩, fun emitted run => error_only_source policy (complete_source run)⟩,
    ⟨⟨mixedAnswers, mixedPath⟩, fun emitted run => mixed_source policy (complete_source run)⟩, ?_⟩
  · have bag := every (max N 20) (le_max_left _ _) emitted run
    rw [advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 20) (le_max_right _ _),
      computed] at bag
    exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp bag.symm)
  · intro same
    have cards := congrArg Multiset.card same
    simp at cards

/-- **HE drops the error answer on every run; PeTTa keeps it.** On
`{(= (g) 1), (= (g) (Error foo bar))}`: a complete run of HE from the entry of `(g)` exists, every
complete run publishes exactly `1`, and PeTTa's run yields `1` and `(Error foo bar)`. -/
theorem error_dropped_every_run (policy : Policy) :
    (∃ heAnswers : List Result,
      HERuns.HESteps noHost Completed.rawLookup policy
        (load (Space.ofList mixedRows) (app "g" []) Atom.undefinedType)
        ⟨Space.ofList mixedRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        HERuns.HESteps noHost Completed.rawLookup policy
          (load (Space.ofList mixedRows) (app "g" []) Atom.undefinedType)
          ⟨Space.ofList mixedRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [one]) ∧
      Streaming.values (Streaming.advance (translate mixedRows) 20
        (Streaming.enter { state := store mixedRows } (app "g" []))) = [one, fooBar] := by
  obtain ⟨emitted, _, path⟩ := mixed_run policy
  exact ⟨⟨emitted, path⟩, fun emitted run => mixed_source policy (complete_source run),
    by decide +kernel⟩

end Controls

#print axioms equations_steps_mixed
#print axioms Controls.fooBar_stopped
#print axioms Controls.mixed_run
#print axioms Controls.mixed_source
#print axioms Controls.error_dropped_every_run
#print axioms Controls.error_only_run
#print axioms Controls.error_only_source
#print axioms Controls.not_union

end ErrorAlternatives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
