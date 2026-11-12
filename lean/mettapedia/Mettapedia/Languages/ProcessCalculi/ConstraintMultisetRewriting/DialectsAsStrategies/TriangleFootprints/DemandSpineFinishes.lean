import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfFinishes

/-!
# Every run under a transparent demand finishes

`EveryRunFinishes` (H6) proves that every run of HE's machine on a settling term finishes, under the
demand `%Undefined%`: its logical relation `Fine` is carried by `FineRuns`, `FineEval` and `FineQuery`.
`DemandSpine` showed that a demand enters the evaluation of a settling term only along its spine. Here
the same holds for `Fine`:

* `FineRunsAt`, `FineEvalAt`, `FineQueryAt`: H6's relation with the demand `E` as a parameter;
* `fine_data_at`, `fine_held_at`, `fine_calls_at`, `fine_equations_at`, `fine_query_absent_at`,
  `fine_query_equations_at`, `fine_node_at`: the spine under `E`, the arguments by H6's theorems
  under `%Undefined%`;
* `fine_settlesK_at`: every run of every marked presentation of a settling term under a transparent
  demand that casts its data answers as they are finishes, with those answers.

`IfComputedFinishes` uses it for the condition of `if` under `Bool`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DemandSpineFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DemandSpine
  EveryRunFinishes IfFinishes

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The relation with the demand as a parameter -/

/-- **Every run from pending work on `v` under `E` finishes, with answers `L`.** -/
def FineRunsAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    (∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope v E activation), stack, emitted⟩

/-- **Every marked presentation of `t` runs finely under `E` to `L`.** -/
def FineEvalAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v → FineRunsAt dispatch policy atoms E v L

/-- **Every query of `(f vals)` under `E`, on every call value, runs finely to `A`.** -/
def FineQueryAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (f : String) (vals A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) →
    ∀ (stack : List Continuation) (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = A →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
        .work (.call live scope value E activation), stack, emitted⟩

/-! ## Leaves -/

/-- **A data answer under `E`**: every cast result is the atom. -/
theorem fine_data_at {atoms : List Atom} {E d : Atom} (casts : CastsAt atoms E d) :
    FineEvalAt dispatch policy atoms E d [d] := by
  intro v erased _ live scope activation stack emitted cont
  rw [value_of_data casts.data erased]
  obtain ⟨T, stored, keeps⟩ := casts.typed
  exact fine_data_cast casts.data (casts.entry _) stored (keeping_renewal (keeps _))
    ⟨_, Completed.Frame.preserved_type_match policy activation (keeps _)⟩
    (fun after => cont _ (by simp))

/-- **A held expression under reuse and a transparent demand is delivered**, the only step. -/
theorem fine_held_at (atoms : List Atom) {E : Atom} (transparent : Transparent E)
    {children : List Entry.Value} (reuses : policy.reentry = .reuse)
    (closed : ∀ name, ¬ AtomOccurs (.expression (children.map Entry.Value.erase)) name)
    (notStopped : ¬ IsEmptyOrErrorRel (.expression (children.map Entry.Value.erase))) :
    FineRunsAt dispatch policy atoms E (.expression .held children)
      [.expression (children.map Entry.Value.erase)] := by
  intro live scope activation stack emitted cont
  have eraseV : (Entry.Value.expression .held children).erase =
      .expression (children.map Entry.Value.erase) := by
    simp only [Entry.Value.erase]
  have readV := read_closed_value policy activation (v := .expression .held children)
    (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression .held children)).status
      (activation.read policy (.expression .held children)).erase E .deliver := by
    rw [readV, eraseV]
    exact .held notStopped transparent reuses rfl
  refine .step ⟨_, .internal (.delivered entry)⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered _ =>
          apply cont
          rw [readV]
          simp only [List.map_cons, List.map_nil, eraseV]
      | cast entered => cases Entry.functional entered entry
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-! ## The spine -/

/-- **The calls continuation under `E`**, for every successor. -/
theorem fine_calls_at (atoms : List Atom) {E : Atom} {live : List Atom} {scope : List String}
    {f : String} (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQueryAt dispatch policy atoms E f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) →
          Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
          .work (.calls live scope E rows), stack, emitted⟩
  | [], _, stack, emitted, cont => fine_calls_nil (cont [] rfl)
  | r :: rs, queries, stack, emitted, cont => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      apply fine_calls_cons
      apply query live scope r.2 r.1 erased (.append (.calls live scope E rs) :: stack) emitted
      intro Qr eraseQr
      apply fine_append
      apply fine_calls_at atoms Q rs (fun x member => queries x (List.mem_cons_of_mem _ member))
        (.prepend Qr :: stack) emitted
      intro Rs eraseRs
      apply fine_prepend
      apply cont
      rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
      rfl

/-- **The equation loop under `E`**, for every unifier output of every work. -/
theorem fine_equations_at (atoms : List Atom) {E : Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEvalAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = Ls.flatten →
          Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
          .work (.equations live scope original E activation works), stack, emitted⟩
  | [], Ls, _, related, stack, emitted, cont => by
      cases related
      exact fine_equations_nil (cont [] rfl)
  | work :: works, Ls, unifiers, related, stack, emitted, cont => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨i, readsAs, fineI, facts⟩ := here
          obtain ⟨output₀, sameBindings₀, unified₀⟩ := unifiers work List.mem_cons_self
          refine .step ⟨_, .internal (.equationsCons sameBindings₀ unified₀)⟩ ?_
          intro y step
          cases step with
          | internal l =>
              cases l with
              | equationsCons sameBindings _ =>
                  obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings
                  apply fine_boundary_producer (not_pending facts readErase)
                  apply fine_boundaryBatch_frame
                  apply fine_boundaryBatch_cons
                  apply fine_boundary_returned
                  apply fine_returned_evaluate (by rw [readErase]; exact facts.notRefused)
                    (by rw [readErase]; exact facts.notStopped)
                  refine fineI _ readErase readMarked _ _ _ _ _ ?_
                  intro Rb eraseRb
                  apply fine_append
                  apply fine_boundaryBatch_nil
                  apply fine_prepend
                  apply fine_append
                  apply fine_equations_at atoms works Ls'
                    (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
                    (.prepend (Rb ++ []) :: stack) emitted
                  intro Rs eraseRs
                  apply fine_prepend
                  apply cont
                  rw [List.append_nil, List.map_append, eraseRb, eraseRs, List.flatten_cons]

/-- **A query with an empty region under `E`**: `callAbsent` is the only step, returning the call. -/
theorem fine_query_absent_at {atoms : List Atom} {E : Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (empty : regionBodies atoms f vals = []) :
    FineQueryAt dispatch policy atoms E f vals [.expression (.symbol f :: vals)] := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  have noBodies : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [empty]
    intro b member
    cases member
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (E :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies := HERuns.frontier_bodies ground activation.certified.satisfiable program noBodies frontier
  rw [empty] at bodies
  have none : works = [] := List.map_eq_nil_iff.mp bodies
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (E :: live)
      value.erase activation.bindings [] := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callAbsent (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier')⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed (HERuns.value_not_error head.head erased)
      | callEmbedded _ _ instruction =>
          rw [erased, head.instruction vals] at instruction
          cases instruction
      | callAbsent _ _ _ =>
          apply cont
          simp [erased]
      | callEquations _ _ frontierW nonemptyW =>
          rw [erased] at frontierW
          have bodiesW := HERuns.frontier_bodies ground activation.certified.satisfiable program
            noBodies frontierW
          rw [empty] at bodiesW
          exact absurd (List.map_eq_nil_iff.mp bodiesW) nonemptyW

/-- **A query with a nonempty region under `E`**: every frontier fires, and each work's body is read
as a marked value of its instance and runs finely under `E`. -/
theorem fine_query_equations_at {atoms : List Atom} {E : Atom} (program : ScopedProgram atoms)
    {f : String} {vals : List Atom} (head : NodeHead dispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value dispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => FineEvalAt dispatch policy atoms E b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    FineQueryAt dispatch policy atoms E f vals Ls.flatten := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  have fromFrontier : ∀ (works : List EquationWork),
      EquationFrontierRel (Space.ofList atoms) (E :: live)
        (.expression (.symbol f :: vals)) activation.bindings works →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value E activation works), stack, emitted⟩ := by
    intro works frontier
    have instances := works_instances_K policy valsValues program activation.certified.satisfiable
      frontier
    have frontier' : EquationFrontierRel (Space.ofList atoms) (E :: live)
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
            (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
            Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        FineEvalAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls :=
      (forall₂_comp instances bodies).imp fun _ _ both => by
        obtain ⟨i, ⟨_, reads⟩, fineI, facts⟩ := both
        exact ⟨i, reads, fineI, facts⟩
    exact fine_equations_at atoms works Ls unifiers related stack emitted cont
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (E :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have instances := works_instances_K policy valsValues program activation.certified.satisfiable
    frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (E :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callEquations (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier'
    worksNonempty)⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed (HERuns.value_not_error head.head erased)
      | callEmbedded _ _ instruction =>
          rw [erased, head.instruction vals] at instruction
          cases instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have sidesEq := frontier_sides ground activation.certified.satisfiable
            (scoped_consFree program) frontierEmpty
          apply absurd _ nonempty
          rw [regionInstances_sides, ← sidesEq]
          rfl
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-- **A marked call whose root HE interprets, under `E`**: the tuple entry or the fallback, the
argument product under `%Undefined%`, the calls of each combination under `E`, the publication. -/
theorem fine_node_at {atoms : List Atom} {E : Atom} (transparent : Transparent E) {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    (headFine : FineRuns dispatch Completed.rawLookup policy atoms (.symbol f) [.symbol f])
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => FineRuns dispatch Completed.rawLookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, FineQueryAt dispatch policy atoms E f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    FineRunsAt dispatch policy atoms E (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  intro live scope activation stack emitted cont
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : activation.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy activation (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression readiness (.symbol f :: vs))).status
      (activation.read policy (.expression readiness (.symbol f :: vs))).erase
      E .interpret := by
    rw [readV, eraseV]
    exact .expression (call_not_stopped head) transparent interpreted
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol f).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences untyped
  have storage : StorageTypesRel (Space.ofList atoms) (.symbol f) [Atom.undefinedType] :=
    (StorageTypesRel.undefined_iff_occurrences _ _).mpr (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy live scope
        (activation.read policy (.expression readiness (.symbol f :: vs))).erase
        (.symbol f) E activation outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      raw_contract.undeclared _ _ _ _ _ storage queried
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol f :: ts)) :: stack, emitted⟩ := by
    intro R eraseR
    apply fine_publish (HENested.clean_of_erase eraseR answerableAll)
    apply cont
    rw [publish_erase, eraseR]
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, rest, emitted⟩) →
      ∀ rows : List Result, rows.map (fun r => r.1.erase) =
          (combos ([.symbol f] :: Ls)).map Atom.expression →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning rows,
          .calls live scope E :: rest, emitted⟩ := by
    intro rest restFine rows eraseRows
    rw [combos_head] at eraseRows
    apply fine_calls_frame
    have queries : ∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        FineQueryAt dispatch policy atoms E f vals (Q vals) := by
      intro r member
      have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
        rw [← eraseRows]
        exact List.mem_map.mpr ⟨r, member, rfl⟩
      rw [List.map_map] at inRows
      obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
      exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
    apply fine_calls_at atoms Q rows queries rest emitted
    intro R eraseR
    apply restFine
    rw [eraseR]
    have viaAtoms : rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (rows.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseRows, List.map_map, List.flatMap_map]
    rfl
  have argsAll : List.Forall₂ (fun v L => FineRuns dispatch Completed.rawLookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) (Entry.Value.symbol f :: vs) ([.symbol f] :: Ls) :=
    .cons ⟨headFine, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args
  refine .step ⟨_, .internal (LocalStepWith.atomTuple entry readV occurrences)⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped _ =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [published]
          exact fine_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _) argsAll
            _ scope activation _ emitted (afterRows _ afterPublish)
      | atomFunction _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          cases selectionExact chosen
      | atomFallback _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
          subst exhausted
          rw [published]
          refine fine_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _) argsAll
            _ scope activation _ emitted (afterRows _ ?_)
          intro R eraseR
          apply fine_diagnostics
          simp only [Completed.diagnosticResults, List.map_nil, List.append_nil]
          exact afterPublish R eraseR
      | atomSelectionFailed _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp at exhausted

/-! ## Every settling term under a transparent demand -/

/-- **Every run of a settling term under a transparent demand finishes**: if the demand casts each
data answer as it is, every marked presentation runs finely under `E` to the answers. The arguments
are H6's `fine_settlesK` under `%Undefined%`. -/
theorem fine_settlesK_at {atoms : List Atom} (program : CallProgram atoms) {E : Atom}
    (transparent : Transparent E) {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) :
    (∀ a ∈ L, DataAtom a → CastsAt atoms E a) → FineEvalAt dispatch policy atoms E t L := by
  induction settles with
  | @data d data _ =>
      intro casts
      exact fine_data_at (casts d List.mem_cons_self data)
  | @build f ts Ls head noEquation length settled _ =>
      intro _
      have whole := SettlesK.build head noEquation length settled
      have argsK : List.Forall₂ (fun t L => SettlesK dispatch atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => settled p member
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, settlesT⟩ := forall₂_right_exists argsK L member
        exact (settlesK_shape settlesT).1.answers a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRuns dispatch Completed.rawLookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK) fun w member L settlesW =>
          ⟨fine_settlesK raw_answers raw_contract program settlesW w rfl
              (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape settlesW).1.answers⟩
      have headFine : FineRuns dispatch Completed.rawLookup policy atoms (.symbol f) [.symbol f] :=
        fine_data raw_answers raw_contract atoms head.head (.symbol f)
          (by simp only [Entry.Value.erase]) (.symbol f)
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesK_value_self whole value]
        have runs := fine_held_at (dispatch := dispatch) atoms transparent reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rwa [eraseList] at runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact fine_node_at transparent head.head head.untyped closed headFine interpreted rfl args
          (fun vals => [.expression (.symbol f :: vals)])
          (fun vals member => ⟨fine_query_absent_at (scoped_consFree program.scoped) head
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation),
            fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  | @call f ts Ls R head defined length settled nonempty lengths bodies _ ihBodies =>
      intro casts
      have whole := SettlesK.call R head defined length settled nonempty lengths bodies
      have argsK : List.Forall₂ (fun t L => SettlesK dispatch atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => settled p member
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, settlesT⟩ := forall₂_right_exists argsK L member
        exact (settlesK_shape settlesT).2 a inside
      have bodyCasts : ∀ vals ∈ combos Ls, ∀ p ∈ (regionInstances atoms f vals).zip (R vals),
          ∀ a ∈ p.2, DataAtom a → CastsAt atoms E a := by
        intro vals member p inside a inA data
        apply casts a _ data
        apply List.mem_flatMap.mpr
        refine ⟨vals, member, List.mem_flatten.mpr ⟨p.2, (List.of_mem_zip inside).2, inA⟩⟩
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => FineRuns dispatch Completed.rawLookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK) fun w member L settlesW =>
          ⟨fine_settlesK raw_answers raw_contract program settlesW w rfl
              (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape settlesW).1.answers⟩
      have headFine : FineRuns dispatch Completed.rawLookup policy atoms (.symbol f) [.symbol f] :=
        fine_data raw_answers raw_contract atoms head.head (.symbol f)
          (by simp only [Entry.Value.erase]) (.symbol f)
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim
      | active =>
          exact fine_node_at transparent head.head head.untyped closed headFine (Or.inr rfl) rfl args
            (fun vals => (R vals).flatten)
            (fun vals member => ⟨fine_query_equations_at program.scoped head
                (combos_all allValues vals member) (nonempty vals member)
                (forall₂_of_zip (lengths vals member) fun p inside =>
                  ⟨ihBodies vals member p inside (bodyCasts vals member p inside),
                    settlesK_facts (bodies vals member p inside)⟩),
              fun a inside => by
                obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
                have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
                obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
                exact (settlesK_shape settlesB).1.answers a inner⟩)

#print axioms fine_data_at
#print axioms fine_held_at
#print axioms fine_calls_at
#print axioms fine_equations_at
#print axioms fine_query_absent_at
#print axioms fine_query_equations_at
#print axioms fine_node_at
#print axioms fine_settlesK_at

end DemandSpineFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
