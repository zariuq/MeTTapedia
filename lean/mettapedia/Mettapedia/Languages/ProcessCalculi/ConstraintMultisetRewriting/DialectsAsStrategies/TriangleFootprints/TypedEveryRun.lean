import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredEveryRun

/-!
# The well-typed declared path on every run

`DeclaredHeads.typed_agrees` gives one complete run of HE's machine on
`{(: f (-> Number Number)), (: b Bool), (= (f $x) yes)}` in which the well-typed call `(f 4)` takes
HE's function path and answers `yes`, as PeTTa does. Here **every** complete run is covered, through
HE's completed relation (`EveryRun.complete_source`), by inverting each part of the function path:

* `typed_selection`: every admission of `(f 4)` selects `f`'s arrow with exactly one activation (the
  argument check of `4` against `Number` and the return check both accept, whatever frame renewal
  they choose); the tuple entry, the fallback and the failed selection are impossible;
* `typed_cast_source`: every cast of an atom with one stored type that the demand accepts returns the
  atom, at some frame (the operator `f` against its arrow, `4` against `Number`, `yes` against
  `Number`);
* `typed_call_source`: every derivation of the typed query of `(f 4)` under return demand `Number`
  returns `yes`;
* `typed_source`: every derivation for `(f 4)` publishes `yes`.

`typed_every_run`: a complete run exists, every complete run publishes `yes`, and PeTTa's run gives
`yes`. With `DeclaredEveryRun.declared_every_run` (`(f b)`: every run publishes the type error), the
declared head's guard is now settled on every run in both directions on this program.

## Controls

* `typed_every_run` (positive) and `DeclaredEveryRun.declared_every_run` (negative, same program).
* `Controls.no_tuple_entry`: the tuple entry is not available to a declared head (every derivation
  through it is impossible), so the function path is the only one.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace TypedEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom mkError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun DeclaredHeads DeclaredEveryRun
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Casts under a typed demand -/

/-- **Every cast of a data atom whose one stored type the demand accepts returns the atom**, at some
frame. -/
theorem typed_cast_source {space : Space} {live : List Atom} {scope : List String}
    {a expected actual : Atom} (data : DataAtom a)
    (entry : Entry.Rel policy.reentry .active a expected .cast)
    (stored : StorageTypesRel space a [actual])
    (accepts : ∀ frame : Frame, ∃ output, policy.matching.Rel expected actual frame.bindings output)
    {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel space dispatch Completed.rawLookup live scope
      (Entry.Value.ofAtom a) expected frame results (policy := policy)) :
    ∃ after : Frame, results = [(Entry.Value.ofAtom a, after)] := by
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase expected .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  cases derived with
  | delivered entered => cases Entry.functional entered entry'
  | cast _ batch related =>
      rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
      cases batch with
      | success _ _ _ _ =>
          obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
          obtain rfl := List.forall₂_nil_left_iff.mp rest
          have value : r.1 = Entry.Value.ofAtom a := by
            have payload := first.payload
            split at payload <;> exact payload
          exact ⟨r.2, by rw [← value]⟩
      | failure queried rejected =>
          have same := StorageTypesRel.unique (show StorageTypesRel space a _ from queried) stored
          subst same
          obtain ⟨output, matched⟩ := accepts frame
          exact (rejected actual List.mem_cons_self output matched).elim
  | tuple entered => cases Entry.functional entered entry'
  | function entered => cases Entry.functional entered entry'
  | fallback entered => cases Entry.functional entered entry'
  | selectionFailed entered => cases Entry.functional entered entry'

theorem symbol_cast_entry {name : String} (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    {expected : Atom}
    (notRaw : ¬(expected = Atom.atomType ∨ expected = Atom.symbolType ∨
      Atom.symbolType = Atom.variableType)) :
    Entry.Rel policy.reentry .active (.symbol name) expected .cast :=
  .cast (DataAtom.symbol notEmpty notError).not_stopped (.symbol _) notRaw (Or.inl ⟨_, rfl⟩)
    (fun _ => Or.inr rfl)

/-! ## Admission of `(f 4)` -/

theorem number_accepts (frame : Frame) :
    ∃ output, policy.matching.Rel (sym "Number") (sym "Number") frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (number_matches _)⟩

theorem undefined_accepts (actual : Atom) (frame : Frame) :
    ∃ output, policy.matching.Rel Atom.undefinedType actual frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (.undefinedLeft _ _)⟩

theorem number_meets_undefined (frame : Frame) :
    ∃ output, policy.matching.Rel (sym "Number") Atom.undefinedType frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (.undefinedRight _ _)⟩

/-- A type check whose demand accepts the type keeps exactly one frame. -/
theorem check_accepts {expected actual : Atom} {before : Frame} {check : Sum Atom Frame}
    (accepts : ∃ output, policy.matching.Rel expected actual before.bindings output)
    (checked : Completed.TypeCheckRel policy expected before actual check) :
    ∃ after, check = .inr after := by
  cases checked with
  | accepted _ => exact ⟨_, rfl⟩
  | rejected rejectedAll =>
      obtain ⟨output, matched⟩ := accepts
      exact (rejectedAll output matched).elim

/-- The projections of a selected arrow `(-> Number Number)`. -/
theorem projections_of {signature : SelectedTypePolicy}
    (functionType : signature.functionType = DeclaredEveryRun.arrowType) :
    signature.argumentTypes = [sym "Number"] ∧ signature.returnType = sym "Number" :=
  arrow_projections (functionType ▸ signature.isFunction)

/-- **Every application check of `(f 4)` against an arrow `(-> Number Number)` keeps exactly one
activation.** -/
theorem typed_checks {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    (functionType : signature.functionType = DeclaredEveryRun.arrowType)
    (checks : Completed.ApplicationChecksRel (Space.ofList declaredRows)
      (rawTypeLookupRel (Space.ofList declaredRows)) policy typedCall Atom.undefinedType
      signature Completed.Frame.empty frames errors) :
    ∃ after, frames = [after] := by
  have projections := arrow_projections (functionType ▸ signature.isFunction)
  cases checks with
  | wrongArity shaped arity =>
      simp only [typedCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [typedCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      cases arguments with
      | cons head rest =>
          cases rest
          cases head with
          | cons queried paired restChecks =>
              cases restChecks
              have same := StorageTypesRel.unique
                (show StorageTypesRel (Space.ofList declaredRows) (.grounded (.int 4)) _ from queried)
                four_types
              subst same
              obtain ⟨check, checks', checked, nilChecks, rfl⟩ := List.forall₂_cons_left_iff.mp paired
              obtain rfl := List.forall₂_nil_left_iff.mp nilChecks
              obtain ⟨after, rfl⟩ := check_accepts (number_accepts Completed.Frame.empty) checked
              simp only [Completed.checkedFrames, List.filterMap_cons, List.filterMap_nil,
                List.append_nil] at returned
              obtain ⟨returnCheck, rest', returnChecked, nilReturn, rfl⟩ :=
                List.forall₂_cons_left_iff.mp returned
              obtain rfl := List.forall₂_nil_left_iff.mp nilReturn
              obtain ⟨after', rfl⟩ := check_accepts (undefined_accepts _ after) returnChecked
              exact ⟨after', rfl⟩

/-- **Every admission of `(f 4)` selects `f`'s arrow with one activation.** -/
theorem typed_selection {outcome : Completed.InvocationSelection}
    (chosen : Completed.InvocationSelectionRel (Space.ofList declaredRows) Completed.rawLookup
      policy [] [] typedCall (.symbol "f") Atom.undefinedType Completed.Frame.empty outcome) :
    ∃ (signature : SelectedTypePolicy) (after : Frame),
      signature.functionType = DeclaredEveryRun.arrowType ∧
      outcome = .selected signature [after] := by
  obtain ⟨candidates, queried, scanned⟩ := chosen
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList declaredRows) (.symbol "f") candidates from queried) f_types
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨[sym "Number"], sym "Number", rfl⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, rfl⟩ := typed_checks functionType checks
      exact ⟨_, after, functionType, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible⟩ := typed_checks functionType checks
      cases impossible

/-! ## The typed query of `(f 4)` -/

theorem declared_program : ∀ row ∈ declaredRows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro lhs rhs same
    simp at same
  · intro lhs rhs same
    simp at same
  · exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .var _

/-- **Every derivation of the typed query of `(f 4)` under return demand `Number` returns `yes`.** -/
theorem typed_call_source {live : List Atom} {scope : List String} {value : Entry.Value}
    {frame : Frame} {children : List Result} (erased : value.erase = typedCall)
    (called : Completed.CallRel (Space.ofList declaredRows) dispatch Completed.rawLookup live scope
      value (sym "Number") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [sym "yes"] := by
  have bodies : regionBodies declaredRows "f" [.grounded (.int 4)] = [sym "yes"] := by decide +kernel
  have fixed : ∀ b ∈ regionBodies declaredRows "f" [.grounded (.int 4)], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [bodies]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  have ground : ∀ v ∈ [Atom.grounded (.int 4)],
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] := by
    intro v member
    simp only [List.mem_singleton] at member
    subst member
    rfl
  have yesData : DataAtom (sym "yes") := .symbol (by decide) (by decide)
  cases called with
  | error failed =>
      rw [erased] at failed
      obtain ⟨tail, same⟩ := failed
      simp at same
  | embedded _ _ instruction _ _ =>
      rw [erased] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have bodiesEq := HERuns.frontier_bodies ground frame.certified.satisfiable declared_program
        fixed frontier
      rw [bodies] at bodiesEq
      simp at bodiesEq
  | equations _ _ frontier nonempty equations =>
      rw [erased] at frontier
      have bodiesEq := HERuns.frontier_bodies ground frame.certified.satisfiable declared_program
        fixed frontier
      rw [bodies] at bodiesEq
      obtain ⟨work, rest, worksEq⟩ := List.exists_cons_of_ne_nil nonempty
      subst worksEq
      have restNil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at bodiesEq
      subst restNil
      have body : work.body = sym "yes" := by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
        exact bodiesEq
      cases equations with
      | cons _ _ boundary batch later =>
          cases later
          rw [body, HERuns.read_closed policy _ (answerable_of_data yesData).closed] at boundary
          cases boundary with
          | producerFunction pending _ =>
              obtain ⟨⟨inner, same⟩, _⟩ := pending
              rw [Entry.Value.erase_ofAtom] at same
              cases same
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [Entry.Value.erase_ofAtom] at same
                          simp [Atom.notReducible] at same
                      | stopped stopped =>
                          rw [Entry.Value.erase_ofAtom] at stopped
                          exact absurd stopped yesData.not_stopped
                      | evaluate _ _ evaluated =>
                          obtain ⟨after, rfl⟩ := typed_cast_source yesData
                            (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) yes_types
                            number_meets_undefined evaluated
                          simp

/-- A batch of answerable results is published whole, under every selection by success priority. -/
theorem publish_answers {raw selected : List Result} {original : Atom} {L : List Atom}
    (erased : raw.map (fun r => r.1.erase) = L) (clean : ∀ a ∈ L, Answerable a)
    (chosen : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (raw.map (Completed.readResult policy))
      selected) :
    (selected.map (Completed.publishResult policy original)).map (fun r => r.1.erase) = L := by
  have cleanRaw := NestedArguments.HENested.clean_of_erase erased clean
  have unchanged : raw.map (Completed.readResult policy) = raw :=
    map_fixed fun r member => HERuns.readResult_closed policy r (cleanRaw r member).closed
  rw [unchanged] at chosen
  have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
    chosen (HERuns.success_all raw fun r member => (cleanRaw r member).notError)
  have published : (selected.map (Completed.publishResult policy original)).map
      (fun r => r.1.erase) = selected.map (fun r => r.1.erase) := by
    simp [Completed.publishResult]
  rw [published, same, erased]

/-! ## Every derivation for `(f 4)` -/

theorem f_data : DataAtom (.symbol "f") := .symbol (by decide) (by decide)

theorem four_data : DataAtom (.grounded (.int 4)) := .grounded _

/-- **Every derivation of HE's completed relation for `(f 4)` publishes `yes`.** -/
theorem typed_source {results : List Result}
    (derived : Completed.AtomRel (Space.ofList declaredRows) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom typedCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [sym "yes"] := by
  have entry := call_entry policy f_data [.grounded (.int 4)]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom typedCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "f") ::
        [Atom.grounded (.int 4)].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [typedCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList declaredRows) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom typedCall)).erase
        (Entry.Value.ofAtom (.symbol "f")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame),
        signature.functionType = DeclaredEveryRun.arrowType ∧
        result = .selected signature [after] := by
    intro result chosen
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
    exact typed_selection chosen
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        f_types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosen _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible⟩ := outcome chosen
      cases impossible
  | selectionFailed _ shaped chosen _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible⟩ := outcome chosen
      cases impossible
  | function _ shaped chosen invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, selected⟩ := outcome chosen
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := projections_of functionType
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = sym "Number" →
          Completed.invocationReturnType s = sym "Number" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branches =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source f_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) f_types
                (fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame
                  (arrow_matches _)⟩) operatorRel
              rw [projections.1] at branches
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branches
              cases branches with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped f_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons argumentRel argumentBranches =>
                      obtain ⟨fr4, rfl⟩ := typed_cast_source four_data
                        (.cast four_data.not_stopped (.grounded _) (by decide +kernel)
                          (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)) four_types
                        number_accepts argumentRel
                      cases argumentBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedFour, _⟩ := stopped
                          rw [Entry.Value.erase_ofAtom] at stoppedFour
                          exact absurd stoppedFour four_data.not_stopped
                      | continuing _ packets restArguments =>
                          cases restArguments
                          cases packets
                          rw [returnType] at calls
                          simp only [List.map_cons, List.map_nil, List.append_nil,
                            Completed.argumentPrepend_packet] at calls
                          cases calls with
                          | cons callRel restCalls =>
                              cases restCalls
                              have assembled : (Completed.functionAssemble
                                  (Entry.Value.ofAtom (.symbol "f"))
                                  (Entry.Value.argumentPacket [Entry.Value.ofAtom (.grounded (.int 4))],
                                    fr4)).1.erase = typedCall := by
                                simp [Completed.functionAssemble, Entry.Value.erase, typedCall, app]
                              have answered := typed_call_source assembled callRel
                              exact publish_answers (by simp only [List.append_nil]; exact answered)
                                (fun a member => by
                                  rw [List.mem_singleton] at member
                                  subst member
                                  exact answerable_of_data (.symbol (by decide) (by decide)))
                                priority

/-! ## Every complete run -/

/-- **The well-typed declared path on every run.** On `{(: f (-> Number Number)), (: b Bool),
(= (f $x) yes)}`, with HE's historical lookup, any policy and any dispatch that does not execute `f`:
a complete run of HE from the entry of `(f 4)` exists, every complete run publishes exactly `yes`,
and PeTTa's run yields `yes` from fuel `40` on. -/
theorem typed_every_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "f"))
    (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
            ⟨Space.ofList declaredRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      ∀ n, 40 ≤ n → Streaming.values (Streaming.advance (translate declaredRows) n
        (Streaming.enter { state := store declaredRows } typedCall)) = [sym "yes"] := by
  obtain ⟨⟨heAnswers, path, _⟩, computed, finished⟩ := typed_agrees dispatch notHost policy
  refine ⟨⟨heAnswers, path⟩, fun emitted run => typed_source (complete_source run),
    fun n bigger => ?_⟩
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) n bigger]
  exact computed

/-! ## Controls -/

namespace Controls

/-- **The tuple entry is not available to a declared head**: `f`'s type collection is not
`%Undefined%` alone, so no derivation of `(f 4)` goes through HE's tuple entry. -/
theorem no_tuple_entry :
    ¬ Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList declaredRows).atoms : Multiset Atom) (.symbol "f") {Atom.undefinedType} :=
  (well_typed_takes_function (dispatch := WholeRunWords.Double.noHost) Policy.ready).2

/-- **The same program, both directions on every run**: the well-typed `(f 4)` answers `yes` on every
complete HE run as in PeTTa, while the ill-typed `(f b)` answers HE's type error on every complete
run where PeTTa answers `yes`. -/
theorem guard_both_ways (policy : Policy) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep WholeRunWords.Double.noHost Completed.rawLookup policy)
          (load (Space.ofList declaredRows) typedCall Atom.undefinedType)
          ⟨Space.ofList declaredRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep WholeRunWords.Double.noHost Completed.rawLookup policy)
            (load (Space.ofList declaredRows) declaredCall Atom.undefinedType)
            ⟨Space.ofList declaredRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [badArgument]) :=
  ⟨(typed_every_run WholeRunWords.Double.noHost (fun impossible => impossible) policy).2.1,
    (declared_every_run WholeRunWords.Double.noHost policy).1⟩

end Controls

#print axioms typed_cast_source
#print axioms typed_checks
#print axioms typed_selection
#print axioms typed_call_source
#print axioms typed_source
#print axioms typed_every_run
#print axioms Controls.no_tuple_entry
#print axioms Controls.guard_both_ways

end TypedEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
