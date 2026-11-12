import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedDifferences

/-!
# A primitive's name hides the program's equations from PeTTa

PeTTa applies its primitive table (`StdLib.known`: `+ - * % < <= > >= == and or not cons
size-atom …`) to every call of a primitive's name, in place of the program's equations: in
`Unifying.step`, the `StdLib.known` branch comes before the equations' application. HE's grounded
dispatch is its own table; on a name its dispatch does not execute, HE queries the program's
equations. The two tables differ (`GroundedTables`: HE's integer dispatch has no `not`), so a
program that gives equations to such a name is read by HE and not by PeTTa.

* `HEHead`: HE's side of a call's head (undeclared, no host operation, no instruction), without
  PeTTa's conditions.
* `he_query_head`, `query_head_determined`: HE's query of a call of data atoms with open bodies, and
  its determinacy, for such a head.
* `Controls.not_every_run`: on `{(= (not Yes) No)}`, every complete run of HE publishes `No`, while
  PeTTa applies its `not` primitive to the symbol `Yes` and stops at the `invalidArguments` fault,
  with no value.
* `Controls.neg_every_run` (positive): the same program under the name `neg` gets `No` on every
  complete HE run and in PeTTa; only the name separates the dialects.
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
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun

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

/-- A program that gives an equation to `not`, a name in PeTTa's primitive table. -/
def notRows : List Atom := [rule (app "not" [sym "Yes"]) (sym "No")]

/-- `not` is a PeTTa primitive. -/
theorem not_primitive : StdLib.known "not" = true := by decide

theorem not_head : HEHead noHost notRows "not" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide⟩

theorem not_scoped : ScopedProgram notRows := by
  intro row member
  simp only [notRows, List.mem_singleton] at member
  subst member
  exact ⟨rule_consFree (one_consFree _ (.symbol _)), fun lhs rhs same => by
    cases same
    decide⟩

theorem not_instances : regionInstances notRows "not" [sym "Yes"] = [sym "No"] := by
  decide +kernel

theorem not_closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
    (app "not" [sym "Yes"]) name :=
  (call_answerable not_head.head (one_data yes_data)).closed

theorem no_answerable : ∀ a ∈ [sym "No"], Answerable a := by
  intro a member
  rw [List.mem_singleton] at member
  subst member
  exact answerable_of_data no_data

/-- HE evaluates `(not Yes)` to `No`, through the program's equation. -/
theorem not_evaluates {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    HEEvaluates noHost lookup policy notRows (app "not" [sym "Yes"]) [sym "No"] := by
  have only : combos [[sym "Yes"]] = [[sym "Yes"]] := rfl
  have evaluates := HENested.he_nested answers not_head.head not_head.untyped not_closed
    (Ls := [[sym "Yes"]])
    (.cons ⟨HERuns.he_data answers notRows yes_data, fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data yes_data⟩ .nil)
    (fun _ => [sym "No"]) (fun vals member => by
      rw [only, List.mem_singleton] at member
      subst member
      have query := he_query_head (policy := policy) not_scoped not_head (one_data yes_data)
        (by rw [not_instances]; simp) (Ls := [[sym "No"]])
        (by
          rw [not_instances]
          exact .cons ⟨HERuns.he_data answers notRows no_data,
            settles_facts (Settles.data (dispatch := noHost) (atoms := notRows) no_data (by decide)),
            no_answerable⟩ .nil)
      exact ⟨by simpa using query, no_answerable⟩)
  rw [only] at evaluates
  simpa using evaluates

/-- HE's source semantics determines `(not Yes)`'s answer, `No` (historical lookup). -/
theorem not_determined (policy : Policy) :
    Determined noHost policy notRows (app "not" [sym "Yes"]) [sym "No"] := by
  have only : combos [[sym "Yes"]] = [[sym "Yes"]] := rfl
  have determined := nested_determined (dispatch := noHost) (policy := policy) not_head.head
    not_head.untyped not_closed (Ls := [[sym "Yes"]]) (.cons (data_settled yes_data) .nil)
    (fun _ => [sym "No"]) (fun vals member => by
      rw [only, List.mem_singleton] at member
      subst member
      have query := query_head_determined (policy := policy) not_scoped not_head
        (one_data yes_data) (by rw [not_instances]; simp) (Ls := [[sym "No"]])
        (by
          rw [not_instances]
          exact .cons ⟨(data_settled no_data).2,
            settles_facts (Settles.data (dispatch := noHost) (atoms := notRows) no_data (by decide))⟩
            .nil)
      exact ⟨no_answerable, by simpa using query⟩)
  rw [only] at determined
  simpa using determined.2

/-- **A primitive's name hides the program's equations from PeTTa.** On `{(= (not Yes) No)}`: a
complete run of HE exists, and every complete run publishes `No`, through the equation; PeTTa
applies its `not` primitive to the symbol `Yes` and stops at the `invalidArguments` fault, with no
value. -/
theorem not_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList notRows) (app "not" [sym "Yes"]) Atom.undefinedType)
        ⟨Space.ofList notRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList notRows) (app "not" [sym "Yes"]) Atom.undefinedType)
          ⟨Space.ofList notRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "No"]) ∧
      GroundedDifferences.stoppedAt (Streaming.advance (translate notRows) 20
        (Streaming.enter { state := store notRows } (app "not" [sym "Yes"]))).agenda =
          some (.invalidArguments "not") ∧
      Streaming.values (Streaming.advance (translate notRows) 20
        (Streaming.enter { state := store notRows } (app "not" [sym "Yes"]))) = [] := by
  obtain ⟨R, _, path, _⟩ := he_complete (not_evaluates raw_answers policy)
  exact ⟨⟨⟨R, path⟩, fun emitted run => not_determined policy _ _ _ _ (complete_source run)⟩,
    by decide +kernel, by decide +kernel⟩

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
under a name outside PeTTa's table, every complete HE run publishes `No` and PeTTa's run gives `No`. -/
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
  obtain ⟨complete, N, every⟩ := NestedCalls.every_complete_run_c policy negOnly_program
    negOnly_settles
  exact ⟨⟨complete, (every N le_rfl).2⟩, by decide +kernel⟩

end Controls

#print axioms he_query_head
#print axioms query_head_determined
#print axioms Controls.not_every_run
#print axioms Controls.neg_every_run

end PrimitiveNames

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
