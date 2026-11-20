import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedDifferences

/-!
# Primitive names: an equation for a name in PeTTa's table, and an equation for HE's own operation

PeTTa applies its primitive table (`StdLib.known`: `+ - * % < <= > >= == and or not cons
size-atom …`) to every call of a primitive's name, in place of the program's equations: in
`Unifying.step`, the `StdLib.known` branch comes before the equations' application. HE's grounded
operations are its own table (`GroundedTables.measuredDispatch`); on a name that table does not
execute, HE queries the program's equations.

* `HEHead`: HE's side of a call's head (undeclared, no host operation, no instruction), without
  PeTTa's conditions.
* `he_query_head`, `query_head_determined`: HE's query of a call of data atoms with open bodies, and
  its determinacy, for such a head.
* `Controls.cons_every_run`: on `{(= (cons Yes No) Both)}`, `cons` is a name in PeTTa's table and no
  operation of HE's: every complete run of HE publishes `Both`, through the equation; PeTTa's machine
  applies its `cons` primitive to the symbols `Yes` and `No` and stops at the `invalidArguments`
  fault, with no value.
* `Controls.not_declines_every_run`: on `{(= (not Yes) No)}`, `not` is an operation of HE's table as
  well. It declines the symbol `Yes`, so every complete run of HE's world machine publishes the call
  `(not Yes)` itself; the equation, whose region holds `No`, is never consulted
  (`GroundedDifferences.declined_source_of`, the grounded-head rule). PeTTa's machine stops at the
  `invalidArguments` fault. Neither dialect answers `No`.
* `Controls.neg_every_run` (positive): the same one-row program under the name `neg`, in neither
  table, gets `No` on every complete HE run and in PeTTa.

The PeTTa hosts refuse both programs when they load them (the equation would redefine a built-in);
the PeTTa machine of the tree loads them and faults at the call. Both give no value.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace PrimitiveNames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe WorldSteps)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun GroundedTables

/-- **HE's side of a call's head**: undeclared, no host operation, no instruction. -/
structure HEHead (dispatch : GroundedDispatch) (atoms : List Atom) (f : String) : Prop where
  head : DataAtom (.symbol f)
  untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []
  notHost : ¬ dispatch.executable (.symbol f)
  notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false

theorem HEHead.instruction {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}
    (head : HEHead dispatch atoms f) (items : List Atom) :
    Minimal.embeddedInstruction (.expression (.symbol f :: items)) = false :=
  head.notInstruction

section HE

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **HE's query of a call of data atoms with open bodies**, for a head with HE's conditions only:
each work's body is read as its instance and evaluated, and the batches come back in row order. -/
theorem he_query_head {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {args : List Atom} (head : HEHead dispatch atoms f) (argsData : ∀ a ∈ args, DataAtom a)
    (nonempty : regionInstances atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluates dispatch lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionInstances atoms f args) Ls) :
    HEQuery dispatch lookup policy atoms f args Ls.flatten := by
  intro live scope activation value erased stack emitted
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances (policy := policy) argsData program
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment value
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
      HEEvaluates dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts, _⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_open works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (.internal (.callEquations (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction args) erased) frontier'
    worksNonempty)) pathR⟩

end HE

/-- **HE's query of a call of data atoms with open bodies is determined**, for a head with HE's
conditions only. -/
theorem query_head_determined {dispatch : GroundedDispatch} {policy : Policy} {atoms : List Atom}
    (program : ScopedProgram atoms) {f : String} {vals : List Atom} (head : HEHead dispatch atoms f)
    (valsData : ∀ v ∈ vals, DataAtom v) (nonempty : regionInstances atoms f vals ≠ [])
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => Determined dispatch policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    QueryDetermined dispatch policy atoms f vals Ls.flatten := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (valsData v member))
  intro live scope value frame children erased called
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head.head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, head.instruction vals] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have sidesEq := frontier_sides ground frame.certified.satisfiable (scoped_consFree program)
        frontier
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      have instances := works_instances (policy := policy) valsData program
        frame.certified.satisfiable frontier
      have onWorks : List.Forall₂ (fun (w : EquationWork) L => ∃ i, (∀ output : Frame,
            output.bindings = w.bindings →
              output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
          DeterminedUnder dispatch Completed.rawLookup policy atoms i L ∧ BodyFacts i) _ Ls :=
        (forall₂_comp instances bodies).imp fun _ _ both => by
          obtain ⟨i, ⟨_, reads⟩, determined, facts⟩ := both
          exact ⟨i, reads, determined, facts⟩
      exact bodies_source_open _ Ls onWorks equations

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (sym_data)
open WholeRunWords.Double (noHost)
open NestedCalls.Controls (one_consFree yes_data no_data one_data)
open GroundedDifferences.Controls (measuredServices executable_of outcome_eq)

/-! ### `cons`: a name in PeTTa's table, no operation of HE's -/

/-- A program that gives an equation to `cons`, a name in PeTTa's primitive table. -/
def consRows : List Atom := [rule (app "cons" [sym "Yes", sym "No"]) (sym "Both")]

/-- `cons` is a PeTTa primitive. -/
theorem cons_primitive : StdLib.known "cons" = true := by decide

theorem both_data : DataAtom (sym "Both") := sym_data "Both" (by decide) (by decide)

theorem two_data : ∀ v ∈ [sym "Yes", sym "No"], DataAtom v := by
  intro v member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact yes_data
  · exact no_data

theorem cons_head : HEHead measuredDispatch consRows "cons" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, cons_not_measured, by decide⟩

theorem cons_scoped : ScopedProgram consRows := by
  intro row member
  simp only [consRows, List.mem_singleton] at member
  subst member
  exact ⟨rule_consFree (fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .symbol _), fun lhs rhs same => by
    cases same
    decide⟩

theorem cons_instances : regionInstances consRows "cons" [sym "Yes", sym "No"] = [sym "Both"] := by
  decide +kernel

theorem cons_closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
    (app "cons" [sym "Yes", sym "No"]) name :=
  (call_answerable cons_head.head two_data).closed

theorem both_answerable : ∀ a ∈ [sym "Both"], Answerable a := by
  intro a member
  rw [List.mem_singleton] at member
  subst member
  exact answerable_of_data both_data

/-- HE evaluates `(cons Yes No)` to `Both`, through the program's equation. -/
theorem cons_evaluates {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    HEEvaluates measuredDispatch lookup policy consRows (app "cons" [sym "Yes", sym "No"])
      [sym "Both"] := by
  have only : combos [[sym "Yes"], [sym "No"]] = [[sym "Yes", sym "No"]] := rfl
  have evaluates := HENested.he_nested answers cons_head.head cons_head.untyped cons_closed
    (Ls := [[sym "Yes"], [sym "No"]])
    (.cons ⟨HERuns.he_data answers consRows yes_data, fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data yes_data⟩
      (.cons ⟨HERuns.he_data answers consRows no_data, fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data no_data⟩ .nil))
    (fun _ => [sym "Both"]) (fun vals member => by
      rw [only, List.mem_singleton] at member
      subst member
      have query := he_query_head (policy := policy) cons_scoped cons_head two_data
        (by rw [cons_instances]; simp) (Ls := [[sym "Both"]])
        (by
          rw [cons_instances]
          exact .cons ⟨HERuns.he_data answers consRows both_data,
            settles_facts (Settles.data (dispatch := measuredDispatch) (atoms := consRows) both_data
              (by decide)),
            both_answerable⟩ .nil)
      exact ⟨by simpa using query, both_answerable⟩)
  rw [only] at evaluates
  simpa using evaluates

/-- HE's source semantics determines `(cons Yes No)`'s answer, `Both` (historical lookup). -/
theorem cons_determined (policy : Policy) :
    Determined measuredDispatch policy consRows (app "cons" [sym "Yes", sym "No"]) [sym "Both"] := by
  have only : combos [[sym "Yes"], [sym "No"]] = [[sym "Yes", sym "No"]] := rfl
  have determined := nested_determined (dispatch := measuredDispatch) (policy := policy)
    cons_head.head cons_head.untyped cons_closed (Ls := [[sym "Yes"], [sym "No"]])
    (.cons (data_settled yes_data) (.cons (data_settled no_data) .nil))
    (fun _ => [sym "Both"]) (fun vals member => by
      rw [only, List.mem_singleton] at member
      subst member
      have query := query_head_determined (policy := policy) cons_scoped cons_head two_data
        (by rw [cons_instances]; simp) (Ls := [[sym "Both"]])
        (by
          rw [cons_instances]
          exact .cons ⟨(data_settled both_data).2,
            settles_facts (Settles.data (dispatch := measuredDispatch) (atoms := consRows) both_data
              (by decide))⟩ .nil)
      exact ⟨both_answerable, by simpa using query⟩)
  rw [only] at determined
  simpa using determined.2

/-- **A name in PeTTa's table hides the program's equation from PeTTa.** On
`{(= (cons Yes No) Both)}`, with HE's table as the dispatch (it has no `cons`): a complete run of HE
exists, and every complete run publishes `Both`, through the equation; PeTTa's machine applies its
`cons` primitive to the symbols `Yes` and `No` and stops at the `invalidArguments` fault, with no
value. -/
theorem cons_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen
        (HEStep measuredDispatch Completed.rawLookup policy)
        (load (Space.ofList consRows) (app "cons" [sym "Yes", sym "No"]) Atom.undefinedType)
        ⟨Space.ofList consRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen
          (HEStep measuredDispatch Completed.rawLookup policy)
          (load (Space.ofList consRows) (app "cons" [sym "Yes", sym "No"]) Atom.undefinedType)
          ⟨Space.ofList consRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "Both"]) ∧
      GroundedDifferences.stoppedAt (Streaming.advance (translate consRows) 20
        (Streaming.enter { state := store consRows } (app "cons" [sym "Yes", sym "No"]))).agenda =
          some (.invalidArguments "cons") ∧
      Streaming.values (Streaming.advance (translate consRows) 20
        (Streaming.enter { state := store consRows } (app "cons" [sym "Yes", sym "No"]))) = [] := by
  obtain ⟨R, _, path, _⟩ := he_complete (cons_evaluates raw_answers policy)
  exact ⟨⟨⟨R, path⟩, fun emitted run => cons_determined policy _ _ _ _ (complete_source run)⟩,
    by decide +kernel, by decide +kernel⟩

/-! ### `not`: an operation of both tables -/

/-- A program that gives an equation to `not`, an operation of HE's table and of PeTTa's. -/
def notRows : List Atom := [rule (app "not" [sym "Yes"]) (sym "No")]

/-- `not` is a PeTTa primitive. -/
theorem not_primitive : StdLib.known "not" = true := by decide

/-- The program's equation matches `(not Yes)`: its region holds `No`. -/
theorem not_instances : regionInstances notRows "not" [sym "Yes"] = [sym "No"] := by
  decide +kernel

/-- **HE's grounded `not` declines a symbol, and the equation is not consulted.** On
`{(= (not Yes) No)}`, whose equation matches the call (`not_instances`), the call is in HE's typed
region (`Yes` has no declared type), and with HE's table: a complete run of HE's world machine
exists, and every complete run publishes the call `(not Yes)` itself;
PeTTa's machine applies its `not` primitive to the symbol `Yes` and stops at the `invalidArguments`
fault, with no value. Neither publishes `No`. -/
theorem not_declines_every_run (minimal : Minimal.Services) (policy : Policy) :
    TypedRegion notRows "not" [sym "Yes"] ∧
    regionInstances notRows "not" [sym "Yes"] = [sym "No"] ∧
      ((∃ heAnswers : List Result,
          WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
            Completed.rawLookup policy
            (WorldConfiguration.ofReadOnly
              (load (Space.ofList notRows) (app "not" [sym "Yes"]) Atom.undefinedType))
            (WorldConfiguration.ofReadOnly ⟨Space.ofList notRows, .returning [], [], heAnswers⟩)) ∧
        ∀ emitted : List Result,
          WorldSteps (fun (_ : Unit) => id) (measuredServices minimal) measuredDispatch
            Completed.rawLookup policy
            (WorldConfiguration.ofReadOnly
              (load (Space.ofList notRows) (app "not" [sym "Yes"]) Atom.undefinedType))
            (WorldConfiguration.ofReadOnly ⟨Space.ofList notRows, .returning [], [], emitted⟩) →
          emitted.map (fun r => r.1.erase) = [app "not" [sym "Yes"]]) ∧
      GroundedDifferences.stoppedAt (Streaming.advance (translate notRows) 20
        (Streaming.enter { state := store notRows } (app "not" [sym "Yes"]))).agenda =
          some (.invalidArguments "not") ∧
      Streaming.values (Streaming.advance (translate notRows) 20
        (Streaming.enter { state := store notRows } (app "not" [sym "Yes"]))) = [] := by
  have head : DataAtom (.symbol "not") := .symbol (by decide) (by decide)
  have computed : measuredOutcome (.symbol "not") [sym "Yes"] = .incorrectArgument := rfl
  have untyped : (Space.ofList notRows).atoms.filter (typeRegion (.symbol "not")) = [] := by
    decide +kernel
  obtain ⟨R, _, path⟩ := GroundedDifferences.declined_steps (policy := policy)
    measuredDispatch_minimal minimal raw_answers (atoms := notRows) (executable_of "not" (by decide))
    head (one_data yes_data) computed.symm untyped
  exact ⟨by decide +kernel, not_instances, ⟨⟨R, path⟩, fun emitted run =>
    GroundedDifferences.declined_every_run raw_contract (executable_of "not" (by decide)) head
    (one_data yes_data) (outcome_eq computed) untyped emitted run⟩, by decide +kernel,
    by decide +kernel⟩

/-! ### `neg`: in neither table -/

/-- The same one-row program under a name outside PeTTa's table. -/
def negOnlyRows : List Atom := [rule (app "neg" [sym "Yes"]) (sym "No")]

theorem negOnly_program : NestedCalls.CallProgram negOnlyRows := by
  intro row member
  simp only [negOnlyRows, List.mem_singleton] at member
  subst member
  exact ⟨rule_consFree (one_consFree _ (.symbol _)), fun lhs rhs same => by
    cases same
    exact ⟨by decide, .item (.symbol _)⟩⟩

theorem negOnly_settles :
    NestedCalls.SettlesC noHost negOnlyRows (app "neg" [sym "Yes"]) [sym "No"] := by
  have instances : regionInstances negOnlyRows "neg" [sym "Yes"] = [sym "No"] := by decide +kernel
  have built := NestedCalls.flat_call (Lb := [[sym "No"]])
    (⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
      by decide, by decide, by decide⟩ : NestedCalls.NodeHead noHost negOnlyRows "neg")
    (by decide +kernel) (one_data yes_data) (fun v member => by
      rw [List.mem_singleton] at member
      subst member
      decide) (by rw [instances]; simp) (by rw [instances]; rfl)
    (by
      rw [instances]
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact .data no_data (by decide))
  simpa using built

/-- **Positive control: only the name separates them.** On `{(= (neg Yes) No)}`, the same program
under a name in neither table, every complete HE run publishes `No` and PeTTa's run gives `No`. -/
theorem neg_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList negOnlyRows) (app "neg" [sym "Yes"]) Atom.undefinedType)
        ⟨Space.ofList negOnlyRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList negOnlyRows) (app "neg" [sym "Yes"]) Atom.undefinedType)
          ⟨Space.ofList negOnlyRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "No"]) ∧
      Streaming.values (Streaming.advance (translate negOnlyRows) 20
        (Streaming.enter { state := store negOnlyRows } (app "neg" [sym "Yes"]))) = [sym "No"] := by
  obtain ⟨complete, N, every⟩ := NestedCalls.every_complete_run_c_single policy negOnly_program
    negOnly_settles
  exact ⟨⟨complete, (every N le_rfl).2⟩, by decide +kernel⟩

end Controls

#print axioms he_query_head
#print axioms query_head_determined
#print axioms Controls.cons_evaluates
#print axioms Controls.cons_determined
#print axioms Controls.cons_every_run
#print axioms Controls.not_declines_every_run
#print axioms Controls.neg_every_run

end PrimitiveNames

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
