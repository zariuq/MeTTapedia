import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.WholeRunWords

/-!
# The complete run of `(double 4)`: the whole-run triangle on H2's tied instance

`WholeRunWords` compared HE's run from its entry through the equation query with PeTTa's request
word. Here HE's run of H2's tied instance is followed to its end: from
`ExpressionTriangle.entry program (double 4)` on `{(p a), (= (double 4) 8)}`, HE's machine fires the
query, unifies the call with the equation's fresh pattern (the tree's
`Entry.Value.UnifyRel.equation_frontier`), evaluates the right-hand side `8` again under
`%Undefined%` (it is cast, and reads no row), and publishes. Every firing carries its declared
region (`EntryToQuery.Traced`).

## Results

* `double_complete_run`: HE's machine runs from the entry configuration to a completed phase that
  publishes one answer, whose atom is `8`, in 33 firings. Over the complete run the positioned rows
  read are exactly `(= (double 4) 8)` at position `1`: the query reads it and no other firing reads
  a row. PeTTa's run of the translation is the one request reading that row, and it answers `8`.
  So on this instance the whole-run triangle holds for rows read and for the answer, and the words
  differ exactly by HE's absence guards over declarations (`WholeRunWords.whole_run_guards`).

## Controls

* `Controls.declared_double_spoils`: `(: double Number)` falls in the guard of the run's first
  firing (`WholeRunWords.Double.double_declaration_race` makes the race exact).
* `Controls.eight_cast_reads_nothing`: the cast of the answer `8` has a vacuous region: a grounded
  value has an intrinsic type.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace CompleteRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeCastBatchRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery WholeRunWords

/-! ## Data atoms under any activation -/

/-- A data atom reads as itself under every activation. -/
theorem read_data (policy : Policy) (frame : Frame) {atom : Atom} (data : DataAtom atom) :
    frame.read policy (Entry.Value.ofAtom atom) = Entry.Value.ofAtom atom := by
  unfold Completed.Frame.read
  apply Entry.Value.substitute_variable_free
  intro name occurs
  rw [Entry.Value.erase_ofAtom] at occurs
  cases data <;> cases occurs

variable {dispatch : GroundedDispatch}

/-- **A data atom's cast under any activation** returns the atom with that activation. -/
theorem cast_step_frame {policy : Policy} {lookup : CastLookup} (answers : AnswersUndefined lookup)
    (space : Space) {atom : Atom} (data : DataAtom atom) (frame : Frame) (live : List Atom)
    (scope : List String) (stack : List Continuation) (emitted : List Result) :
    HEStep dispatch lookup policy
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom atom) Atom.undefinedType frame), stack,
        emitted⟩
      ⟨space, .returning [(Entry.Value.ofAtom atom, frame)], stack, emitted⟩ := by
  obtain ⟨type, rest, queried⟩ := answers
    (invocationTypeScope scope live atom Atom.undefinedType frame.bindings) space frame.bindings atom
  refine .internal (LocalStepWith.cast (raw := [(atom, frame.bindings)]) ?_ ?_ ?_)
  · simp only [read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  · simp only [read_data policy frame data, Entry.Value.erase_ofAtom]
    exact TypeCastBatchRel.success (earlierTypes := []) queried rfl
      (fun _ member => by simp at member) (undefined_matches policy.matching type frame)
  · simp only [read_data policy frame data, Entry.Value.erase_ofAtom]
    exact .cons ⟨by simp [Completed.rawResult], .same _, by simp⟩ .nil

/-- The cast reads the lookup's region of the atom, under any activation. -/
theorem cast_region_frame {policy : Policy} (D : DeclaredLookup) {atom : Atom} (data : DataAtom atom)
    (frame : Frame) (live : List Atom) (scope : List String) (after : Control) :
    heRegionD D policy (.work (.atom live scope (Entry.Value.ofAtom atom) Atom.undefinedType frame))
      after = D.region atom := by
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom atom)).status
      (frame.read policy (Entry.Value.ofAtom atom)).erase Atom.undefinedType .cast := by
    simp only [read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  rw [heRegionD_cast entry, read_data policy frame data, Entry.Value.erase_ofAtom]

/-- A successful singleton batch publishes itself. -/
theorem success_singleton {α : Type} {isError : α → Bool} {item : α} (fine : isError item = false) :
    Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel isError [item] [item] := by
  have chosen := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
    (isError := isError) (raw := [item]) ⟨item, List.mem_singleton_self item, fine⟩
  simpa [fine] using chosen

/-! ## The instance -/

open Instance (doubleFour eight doubleEight program registry store)

/-- The work of HE's query `(double 4)`: the row `(= (double 4) 8)` at position `1`, which is its own
fresh variant, with no bindings. -/
def doubleWork : EquationWork := ⟨1, doubleFour, eight, doubleFour, eight, Bindings.empty⟩

theorem eight_data : DataAtom eight := .grounded _

/-- **The frontier of HE's query `(double 4)` on the program**: `(p a)` contributes nothing, the
equation contributes its one work. -/
theorem double_frontier :
    EquationFrontierRel (Space.ofList program) [Atom.undefinedType] doubleFour Bindings.empty
      [doubleWork] := by
  have rows : (Space.ofList program).atoms.zipIdx =
      [(RunsAsFirings.Controls.p RunsAsFirings.Controls.a, 0), (doubleEight, 1)] := rfl
  have covered : List.Forall₂ (fun row block =>
      EquationRowResultsRel [Atom.undefinedType] doubleFour Bindings.empty row.2 row.1 block)
      (Space.ofList program).atoms.zipIdx [[], [doubleWork]] := by
    rw [rows]
    refine .cons (.irrelevant 0 _ fun left right same => by
      simp [RunsAsFirings.Controls.p] at same) (.cons ?_ .nil)
    exact .hit 1 doubleFour eight doubleFour eight Bindings.empty Bindings.empty
      (Tied.doubleEight_alpha [Atom.undefinedType] Bindings.empty) Instance.doubleFour_matches
      Controls.mergeEmpty
  exact .completed covered

theorem body_read (policy : Policy) (output : Frame) :
    output.read policy (Entry.Value.ofAtom doubleWork.body) = Entry.Value.ofAtom eight :=
  read_data policy output eight_data

theorem eight_not_function (policy : Policy) :
    ¬ Completed.FunctionPending policy (Entry.Value.ofAtom eight) := by
  rintro ⟨⟨body, same⟩, _⟩
  rw [Entry.Value.erase_ofAtom] at same
  simp [Instance.eight] at same

/-- The declared regions of the run after the query: the cast of the answer `8` reads the lookup's
region of `8`; every other move reads nothing. -/
def postWord : List (Atom → Bool) :=
  [nothing, nothing, nothing, nothing, nothing, nothing, rawDeclared.region eight,
    nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing]

/-- **The declared word of HE's complete run of `(double 4)`.** -/
def completeWord : List (Atom → Bool) :=
  entryWord rawDeclared "double" [.grounded (.int 4)] ++
    (eqRegion [Atom.undefinedType] doubleFour Bindings.empty :: postWord)

/-- **The whole-run triangle on H2's tied instance.** From `ExpressionTriangle.entry` of `(double 4)`
on `{(p a), (= (double 4) 8)}`, with HE's raw lookup, any policy and a dispatch for which `double`
is no host operation, HE's machine runs, with the declared region of every firing, to a completed
phase publishing one answer whose atom is `8`. The complete run has 33 firings; the rows they read
are exactly `(= (double 4) 8)` at position `1`. PeTTa's run of the translation is the one request
reading that row, and it answers `8`. -/
theorem double_complete_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "double")) (policy : Policy) :
    ∃ answer : Result,
      Traced rawDeclared dispatch policy (entry program doubleFour)
          ⟨Space.ofList program, .returning [], [], [answer]⟩ completeWord ∧
        answer.1.erase = eight ∧
        observe ⟨Space.ofList program, .returning [], [], [answer]⟩ = some [answer] ∧
        (completeWord.map fun ρ => regionRows ρ program).flatten = [(doubleEight, 1)] ∧
        completeWord.length = 33 ∧
        (pettaWord registry program doubleFour 30).map RunsAsFirings.Controls.shape =
          [([], [⟨1, .self, doubleEight⟩], [])] ∧
        Streaming.values (Streaming.advance registry 30
          (Streaming.enter { state := store } doubleFour)) = [eight] := by
  have untyped : (Space.ofList program).atoms.filter (typeRegion (.symbol "double")) = [] := by
    decide +kernel
  have notInstruction :
      Minimal.embeddedInstruction (.expression [.symbol "double", .grounded (.int 4)]) = false := by
    decide +kernel
  have headData : DataAtom (.symbol "double") := Double.double_data _ List.mem_cons_self
  have toCall := entry_traced (dispatch := dispatch) (policy := policy) rawDeclared raw_answers
    Double.double_data untyped
  have frontier' : EquationFrontierRel (Space.ofList program) [Atom.undefinedType]
      (callValue "double" [.grounded (.int 4)]).erase Completed.Frame.empty.bindings [doubleWork] := by
    rw [callValue_erase]
    exact double_frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
  cases paired with
  | cons here _ =>
      let output : Frame := ⟨doubleWork.bindings, _, here.2⟩
      have entryEmpty : ((entryWord rawDeclared "double" [.grounded (.int 4)]).map
          fun ρ => regionRows ρ program).flatten = [] := by
        apply List.flatten_eq_nil_iff.mpr
        intro rows member
        obtain ⟨ρ, inWord, rfl⟩ := List.mem_map.mp member
        exact entry_rows_empty Double.double_undeclared ρ inWord
      have queryRows : regionRows (eqRegion [Atom.undefinedType] doubleFour Bindings.empty) program =
          [(doubleEight, 1)] :=
        Tied.region_rows_any [Atom.undefinedType] Completed.Frame.empty
      have postEmpty : (postWord.map fun ρ => regionRows ρ program).flatten = [] := by
        decide +kernel
      refine ⟨Completed.publishResult policy (.expression [.symbol "double", .grounded (.int 4)])
        (Entry.Value.ofAtom eight, output), ?_, ?_, rfl, ?_, ?_,
        (Tied.double_expression_triangle (dispatch := dispatch) (lookup := Completed.rawLookup)
          (policy := policy)).2.1, (Instance.triangle_double []).2.2.2.1⟩
      · refine Traced.trans toCall ?_
        refine .cons (query_fires headData notHost notInstruction double_frontier)
          (query_region rawDeclared headData [doubleWork]) ?_
        refine .cons (.internal (.equationsCons (output := output) rfl here.1)) rfl ?_
        rw [body_read policy output]
        refine .cons (.internal (.boundaryProducerRaw (eight_not_function policy))) rfl ?_
        refine .cons (.internal .boundaryBatch) rfl ?_
        refine .cons (.internal .boundaryBatchCons) rfl ?_
        refine .cons (.internal .boundaryReturned) rfl ?_
        refine .cons (.internal (.returnEvaluate ?_ ?_)) rfl ?_
        · simp [Instance.eight, Atom.notReducible]
        · simpa using eight_data.not_stopped
        refine .cons (cast_step_frame raw_answers _ eight_data output _ _ _ _)
          (cast_region_frame rawDeclared eight_data output _ _ _) ?_
        refine .cons (.internal .append) rfl ?_
        refine .cons (.internal .boundaryBatchNil) rfl ?_
        refine .cons (.internal .prepend) rfl ?_
        refine .cons (.internal .append) rfl ?_
        refine .cons (.internal .equationsNil) rfl ?_
        refine .cons (.internal .prepend) rfl ?_
        refine .cons (.internal .append) rfl ?_
        refine .cons (.internal .callsNil) rfl ?_
        refine .cons (.internal .prepend) rfl ?_
        refine .cons (.internal (.publish (selected := [(Entry.Value.ofAtom eight, output)]) ?_))
          rfl ?_
        · simp only [List.append_nil, List.map_cons, List.map_nil, Completed.readResult,
            read_data policy output eight_data]
          exact success_singleton (by simp [Instance.eight, isErrorAtom])
        refine .cons .publish rfl ?_
        exact .refl _
      · have published := congrArg Prod.fst (Completed.publishResult_source policy
          (.expression [.symbol "double", .grounded (.int 4)]) (Entry.Value.ofAtom eight, output))
        simp only [Completed.sourceResult, Entry.Value.erase_ofAtom] at published
        exact published
      · simp only [completeWord, List.map_append, List.map_cons, List.flatten_append,
          List.flatten_cons, entryEmpty, queryRows, postEmpty, List.nil_append, List.append_nil]
      · simp [completeWord, entryWord_length, postWord]

/-! ## Controls -/

namespace Controls

/-- **The run's first firing guards `(: double Number)`**: the declaration is in the region of the
entry of `(double 4)`, the first region of the complete word. -/
theorem declared_double_spoils :
    completeWord.head? = some (interpretRegion rawDeclared doubleFour) ∧
      interpretRegion rawDeclared doubleFour Double.declareDouble = true := by
  refine ⟨rfl, (whole_run_guards "double" [.grounded (.int 4)]).2.2 _⟩

/-- **The cast of the answer reads nothing**: a grounded value has an intrinsic type, so the
region of its cast holds no row at all. -/
theorem eight_cast_reads_nothing : ∀ row, rawDeclared.region eight row = false := fun _ => rfl

end Controls

#print axioms read_data
#print axioms cast_step_frame
#print axioms double_frontier
#print axioms double_complete_run
#print axioms Controls.declared_double_spoils
#print axioms Controls.eight_cast_reads_nothing

end CompleteRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
