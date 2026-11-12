import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfBranches

/-!
# HE's evaluation under any transparent demand

Every evaluation lemma of `MarkedValues` and `CompoundBindings` is stated under the demand
`%Undefined%`. HE's control forms ask for others: the condition of `if` is evaluated under `Bool`,
the branch it takes under `$t`. A demand enters HE's evaluation of a settling term only along its
**spine**: the call's `calls` continuation, the equation bodies the call returns, and the casts of the
data answers at the leaves. The elements of every tuple (the arguments) stay under `%Undefined%`.

* `Transparent E`: `E` is neither `Atom` nor `Expression`, so an expression under it is interpreted
  (or delivered when held and reused), exactly as under `%Undefined%`.
* `CastsAt atoms E d`: the data answer `d` enters `E` by a cast, has one stored type, and `E` matches
  that type keeping every binding, so the cast returns `d` at every frame (for instance `True` under
  `Bool`, an undeclared symbol under `$t`).
* `HERunsAt`, `HEEvaluatesAt`, `HEQueryAt`, `RunsDeterminedAt`, `DeterminedAt`,
  `QueryDeterminedAt`: `MarkedValues`'s statements with the demand as a parameter.
* `settlesK_at`: for every term that settles (`CompoundBindings.SettlesK`) whose data answers `E`
  casts as they are, HE's machine evaluates every marked presentation under `E` to the answers, and
  every derivation of HE's completed relation under `E` returns them. The arguments reuse the
  `%Undefined%` theorems; only the spine is new.

## Controls

The controls are in `IfComputed`, which instantiates the demands: `IfComputed.Controls.isZero_bool`
(positive: `(isZero 0)` under `Bool` on `{(= (isZero 0) True), (= (isZero 1) False), …}`, every
derivation returns `True` and a run exists), `IfComputed.Controls.number_not_bool` (negative: `5` is
no leaf `Bool` casts as it is), `IfComputed.Controls.transparency` (`%Undefined%`, `Bool` and `$t`
are transparent, `Atom` is not).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DemandSpine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  TypedEveryRun

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Demands and leaves -/

/-- **A transparent demand**: neither `Atom` nor `Expression`. An expression under it is
interpreted, or delivered when held and reused, exactly as under `%Undefined%`. -/
def Transparent (E : Atom) : Prop :=
  ¬(E = Atom.atomType ∨ E = Atom.expressionType ∨ Atom.expressionType = Atom.variableType)

theorem undefined_transparent : Transparent Atom.undefinedType := MarkedValues.undefined_not_raw

/-- **A data answer the demand `E` casts as it is**: it enters `E` by a cast, it has one stored type,
and `E` matches that type keeping every binding. -/
structure CastsAt (atoms : List Atom) (E : Atom) (d : Atom) : Prop where
  data : DataAtom d
  entry : ∀ reentry : Entry.ReentryPolicy, Entry.Rel reentry .active d E .cast
  typed : ∃ T, StorageTypesRel (Space.ofList atoms) d [T] ∧ ∀ b : Bindings, TypeMatchRel E T b b

/-! ## The statements, with the demand as a parameter -/

/-- **HE's machine runs `v` under the demand `E` to the answers `L`**, from any live list, scope,
activation, continuation stack and publication prefix. -/
def HERunsAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    ∃ results : List Result, results.map (fun result => result.1.erase) = L ∧
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
        ⟨Space.ofList atoms, .work (.atom live scope v E activation), stack, emitted⟩
        ⟨Space.ofList atoms, .returning results, stack, emitted⟩

/-- **HE's machine evaluates every marked presentation of `t` under `E` to `L`.** -/
def HEEvaluatesAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v → HERunsAt dispatch policy atoms E v L

/-- **HE's equation query of `(f vals)` under `E` returns `A`**, on every call value. -/
def HEQueryAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) → ∀ (stack : List Continuation)
      (emitted : List Result),
      ∃ results : List Result, results.map (fun result => result.1.erase) = A ∧
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          ⟨Space.ofList atoms, .work (.call live scope value E activation), stack, emitted⟩
          ⟨Space.ofList atoms, .returning results, stack, emitted⟩

/-- **Every derivation of HE's completed relation for `v` under `E` returns the atoms `L`.** -/
def RunsDeterminedAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (frame : Frame) (results : List Result),
    Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup live scope v E frame results
      (policy := policy) →
    results.map (fun r => r.1.erase) = L

/-- **Every marked presentation of `t` is determined under `E` to `L`.** -/
def DeterminedAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v →
    RunsDeterminedAt dispatch policy atoms E v L

/-- **HE's query of `(f vals)` under `E` is determined to `A`.** -/
def QueryDeterminedAt (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (E : Atom)
    (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (value : Entry.Value) (frame : Frame)
    (children : List Result), value.erase = .expression (.symbol f :: vals) →
    Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope value E frame
      children (policy := policy) →
    children.map (fun r => r.1.erase) = A

/-! ## HE's machine under `E` -/

/-- **A data answer under `E`**: the cast returns it at the same frame. -/
theorem he_data_at {atoms : List Atom} {E d : Atom} (casts : CastsAt atoms E d) :
    HEEvaluatesAt dispatch policy atoms E d [d] := by
  intro v erased _ live scope activation stack emitted
  rw [value_of_data casts.data erased]
  obtain ⟨T, stored, keeps⟩ := casts.typed
  exact ⟨[(Entry.Value.ofAtom d, activation)], by simp,
    .single (typed_cast dispatch policy (answerable_of_data casts.data).closed (casts.entry _)
      stored activation (keeps _) live scope stack emitted)⟩

/-- **A held expression under reuse is delivered under every transparent demand.** -/
theorem he_held_at (atoms : List Atom) {E : Atom} (transparent : Transparent E)
    {children : List Entry.Value} (reuses : policy.reentry = .reuse)
    (closed : ∀ name, ¬ AtomOccurs (.expression (children.map Entry.Value.erase)) name)
    (notStopped : ¬ IsEmptyOrErrorRel (.expression (children.map Entry.Value.erase))) :
    HERunsAt dispatch policy atoms E (.expression .held children)
      [.expression (children.map Entry.Value.erase)] := by
  intro live scope activation stack emitted
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
  refine ⟨[(activation.read policy (.expression .held children), activation)], ?_,
    .single (.internal (.delivered entry))⟩
  rw [readV]
  simp only [List.map_cons, List.map_nil, eraseV]

/-- **The calls continuation under `E`**: each row's call value is queried in turn. -/
theorem calls_loop_at (atoms : List Atom) {E : Atom} {live : List Atom} {scope : List String}
    {f : String} (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        HEQueryAt dispatch policy atoms E f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) = rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) ∧
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          ⟨Space.ofList atoms, .work (.calls live scope E rows), stack, emitted⟩
          ⟨Space.ofList atoms, .returning R, stack, emitted⟩
  | [], _, stack, emitted => ⟨[], rfl, .single (.internal .callsNil)⟩
  | r :: rs, queries, stack, emitted => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      obtain ⟨Qr, eraseQr, pathQr⟩ := query live scope r.2 r.1 erased
        (.append (.calls live scope E rs) :: stack) emitted
      obtain ⟨Rs, eraseRs, pathRs⟩ := calls_loop_at atoms Q rs
        (fun x member => queries x (List.mem_cons_of_mem _ member)) (.prepend Qr :: stack) emitted
      refine ⟨Qr ++ Rs, ?_, ?_⟩
      · rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
        rfl
      · refine .head (.internal .callsCons) ?_
        refine .trans pathQr ?_
        refine .head (.internal .append) ?_
        refine .trans pathRs ?_
        exact .single (.internal .prepend)

/-- **HE evaluates a marked call it interprets under `E`**: the argument product under
`%Undefined%`, then the query of `f` on each combination under `E`, then the publication. -/
theorem he_nested_at {atoms : List Atom} {E : Atom} (transparent : Transparent E) {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => HERunsTo dispatch Completed.rawLookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, HEQueryAt dispatch policy atoms E f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    HERunsAt dispatch policy atoms E (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  intro live scope activation stack emitted
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
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := Completed.rawLookup) (live := live) (scope := scope)
    (stack := stack) entry readV occurrences
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  rw [published] at step
  have headRuns : HERunsTo dispatch Completed.rawLookup policy atoms (.symbol f) [.symbol f] :=
    he_data_M raw_answers atoms head (.symbol f) (by simp only [Entry.Value.erase]) (.symbol f)
  obtain ⟨T, eraseT, _, pathT⟩ := tuple_product_M (dispatch := dispatch)
    (lookup := Completed.rawLookup) (policy := policy) atoms (.symbol f :: vs) ([.symbol f] :: Ls)
    (List.cons_ne_nil _ _)
    (.cons ⟨headRuns, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args) (E :: live) scope activation
    (.calls live scope E :: .publish (.expression (.symbol f :: ts)) :: stack) emitted
  rw [combos_head] at eraseT
  have rows : ∀ r ∈ T, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
      HEQueryAt dispatch policy atoms E f vals (Q vals) := by
    intro r member
    have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
      rw [← eraseT]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.map_map] at inRows
    obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
    exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
  obtain ⟨R, eraseR, pathR⟩ := calls_loop_at (dispatch := dispatch) (policy := policy) atoms
    (live := live) (scope := scope) Q T rows (.publish (.expression (.symbol f :: ts)) :: stack)
    emitted
  have totals : T.flatMap (fun r => Q (HENested.argsOf r.1.erase)) = (combos Ls).flatMap Q := by
    have viaAtoms : T.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (T.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseT, List.map_map, List.flatMap_map]
    rfl
  rw [totals] at eraseR
  have clean : ∀ r ∈ R, Answerable r.1.erase := by
    apply HENested.clean_of_erase eraseR
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  obtain ⟨final, eraseFinal, pathFinal⟩ := HENested.publish_step (dispatch := dispatch)
    (lookup := Completed.rawLookup) (policy := policy) (atoms := atoms)
    (.expression (.symbol f :: ts)) R clean stack emitted
  refine ⟨final, by rw [eraseFinal, eraseR], ?_⟩
  refine .head (.internal step) ?_
  refine .trans pathT ?_
  refine .head (.internal .calls) ?_
  exact pathR.trans pathFinal

/-- **A query with an empty region under `E` returns the call value.** -/
theorem he_query_absent_at {atoms : List Atom} {E : Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f)) (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (ground : ∀ v ∈ vals, TypeSubst.typeVars v = [])
    (empty : regionBodies atoms f vals = []) (live : List Atom) (scope : List String)
    (activation : Frame) (value : Entry.Value) (erased : value.erase = .expression (.symbol f :: vals))
    (stack : List Continuation) (emitted : List Result) :
    HERuns.HESteps dispatch Completed.rawLookup policy
      ⟨Space.ofList atoms, .work (.call live scope value E activation), stack, emitted⟩
      ⟨Space.ofList atoms, .returning [(value, activation)], stack, emitted⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (E :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies := HERuns.frontier_bodies ground activation.certified.satisfiable program
    (by rw [empty]; intro b member; cases member) frontier
  rw [empty] at bodies
  have none : works = [] := List.map_eq_nil_iff.mp bodies
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (E :: live)
      value.erase activation.bindings [] := by
    rw [erased]
    exact frontier
  exact .single (.internal (.callAbsent (HERuns.value_not_error head erased)
    (HERuns.value_nonGrounded notHost notInstruction erased) frontier'))

/-- **The equation loop under `E`**: each work's body is read as a marked value of its instance and
evaluated under `E`. -/
theorem equations_steps_at {atoms : List Atom} {E : Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        HEEvaluatesAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HERuns.HESteps dispatch Completed.rawLookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original E activation works), stack,
              emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (.internal .equationsNil)⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨i, readsAs, evaluates, facts⟩ := here
          obtain ⟨readErase, readMarked⟩ := readsAs output sameBindings
          obtain ⟨R, eraseR, pathR⟩ := evaluates _ readErase readMarked live scope output
            (.append (.boundaryBatch live scope none (.returned original E) []) ::
              .append (.equations live scope original E activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_at works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (.internal (.equationsCons sameBindings unified)) ?_
            refine .head (.internal (.boundaryProducerRaw (not_pending facts readErase))) ?_
            refine .head (.internal .boundaryBatch) ?_
            refine .head (.internal .boundaryBatchCons) ?_
            refine .head (.internal .boundaryReturned) ?_
            refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
            · rw [readErase]
              exact facts.notRefused
            · rw [readErase]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (.internal .append) ?_
            refine .head (.internal .boundaryBatchNil) ?_
            refine .head (.internal .prepend) ?_
            refine .head (.internal .append) ?_
            refine .trans pathR' ?_
            exact .single (.internal .prepend)

/-- **HE's equation query under `E`** on a call of values with a nonempty region. -/
theorem he_query_at {atoms : List Atom} {E : Atom} (program : ScopedProgram atoms) {f : String}
    {args : List Atom} (head : NodeHead dispatch atoms f)
    (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a)
    (nonempty : regionInstances atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluatesAt dispatch policy atoms E b L ∧ BodyFacts b)
      (regionInstances atoms f args) Ls) :
    HEQueryAt dispatch policy atoms E f args Ls.flatten := by
  intro live scope activation value erased stack emitted
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (E :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances_K policy argsValues program
    activation.certified.satisfiable frontier
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
      HEEvaluatesAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_at works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (.internal (.callEquations (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction args) erased) frontier'
    worksNonempty)) pathR⟩

/-! ## HE's completed relation under `E` -/

/-- **A data answer under `E`**: every derivation casts it to itself. -/
theorem data_determined_at {atoms : List Atom} {E d : Atom} (casts : CastsAt atoms E d) :
    DeterminedAt dispatch policy atoms E d [d] := by
  intro v erased _ live scope frame results derived
  rw [value_of_data casts.data erased] at derived
  obtain ⟨T, stored, keeps⟩ := casts.typed
  obtain ⟨after, rfl⟩ := typed_cast_source casts.data (casts.entry _) stored
    (fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame (keeps _)⟩) derived
  simp

/-- **The calls continuation under `E`, every derivation.** -/
theorem calls_rows_at {atoms : List Atom} {E : Atom} {live : List Atom} {scope : List String}
    {f : String} {Q : List Atom → List Atom} :
    ∀ (rows : List Result) (cs : List (List Atom)) (raw : List Result),
      List.Forall₂ (fun r vals => r.1.erase = .expression (.symbol f :: vals)) rows cs →
      (∀ vals ∈ cs, QueryDeterminedAt dispatch policy atoms E f vals (Q vals)) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope E rows raw
        (policy := policy) →
      raw.map (fun r => r.1.erase) = cs.flatMap Q
  | [], _, _, related, _, derived => by
      cases related
      cases derived
      rfl
  | _ :: rs, _, _, related, queries, derived => by
      obtain ⟨vals, cs', erased, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons called later =>
          rw [List.map_append, queries vals List.mem_cons_self _ _ _ _ _ erased called,
            calls_rows_at rs cs' _ rest (fun v member => queries v (List.mem_cons_of_mem _ member))
              later, List.flatMap_cons]

/-- **Marked calls under `E` are determined, compositionally.** -/
theorem nested_determined_at {atoms : List Atom} {E : Atom} (transparent : Transparent E)
    {f : String} {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value} (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
      RunsDetermined dispatch policy atoms v L) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      QueryDeterminedAt dispatch policy atoms E f vals (Q vals))
    (held : readiness = .held → policy.reentry = .reuse →
      (combos Ls).flatMap Q = [.expression (.symbol f :: ts)]) :
    RunsDeterminedAt dispatch policy atoms E (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).1 a inner
  intro live scope frame results derived
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : frame.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy frame (by rw [eraseV]; exact closed)
  have storage : StorageTypesRel (Space.ofList atoms) (.symbol f) [Atom.undefinedType] :=
    (StorageTypesRel.undefined_iff_occurrences _ _).mpr (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have batch : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.symbol f = operator → vs = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup
        (E :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
        E rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    have headDetermined : RunsDetermined dispatch policy atoms (.symbol f) [.symbol f] :=
      fun live' scope' frame' results' derived' =>
        data_determined_M (policy := policy) head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f) live' scope' frame' results' derived'
    have rowsShape := tuple_rows_M (Entry.Value.symbol f :: vs) ([Atom.symbol f] :: Ls)
      (.cons ⟨fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data head, headDetermined⟩ args)
      (List.cons_ne_nil _ _) _ _ _ tuples
    rw [combos_head, List.forall₂_map_right_iff] at rowsShape
    exact calls_rows_at _ _ _ (rowsShape.imp fun _ _ row => row.2.1)
      (fun vals member => (apps vals member).2) calls
  have publish : ∀ {raw selected : List Result},
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      selected.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro raw selected erasedRaw chosen
    have cleanRaw := HENested.clean_of_erase erasedRaw answerableAll
    have unchanged : raw.map (Completed.readResult policy) = raw :=
      map_fixed fun r member => HERuns.readResult_closed policy r (cleanRaw r member).closed
    rw [unchanged] at chosen
    have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
      chosen (HERuns.success_all raw fun r member => (cleanRaw r member).notError)
    rw [same, erasedRaw]
  by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
  · have entry : Entry.Rel policy.reentry
        (frame.read policy (.expression readiness (.symbol f :: vs))).status
        (frame.read policy (.expression readiness (.symbol f :: vs))).erase
        E .deliver := by
      rw [readV, eraseV]
      exact .held (call_not_stopped head) transparent reusedHeld.1 reusedHeld.2
    cases derived with
    | delivered _ =>
        rw [held reusedHeld.2 reusedHeld.1, readV]
        simp only [List.map_cons, List.map_nil, eraseV]
    | cast entered => cases Entry.functional entered entry
    | tuple entered => cases Entry.functional entered entry
    | function entered => cases Entry.functional entered entry
    | fallback entered => cases Entry.functional entered entry
    | selectionFailed entered => cases Entry.functional entered entry
  · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
      cases reentry : policy.reentry <;> cases readiness <;> simp_all
    have entry : Entry.Rel policy.reentry
        (frame.read policy (.expression readiness (.symbol f :: vs))).status
        (frame.read policy (.expression readiness (.symbol f :: vs))).erase
        E .interpret := by
      rw [readV, eraseV]
      exact .expression (call_not_stopped head) transparent interpreted
    cases derived with
    | delivered entered => cases Entry.functional entered entry
    | cast entered => cases Entry.functional entered entry
    | tuple _ shaped _ tuples calls chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, sameOperator, sameArguments⟩ := shaped
        rw [publish_erase]
        exact publish (batch sameOperator sameArguments tuples calls) chosen
    | function _ shaped chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, rfl, _⟩ := shaped
        rw [operatorErase] at chosen
        cases chosen.undefined_exact storage
    | fallback _ shaped chosen tuples calls selected =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, sameOperator, sameArguments⟩ := shaped
        rw [← sameOperator, operatorErase] at chosen
        have exhausted := chosen.undefined_exact storage
        simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
        subst exhausted
        have chosenRaw := selected
        simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
        rw [publish_erase]
        exact publish (batch sameOperator sameArguments tuples calls) chosenRaw
    | selectionFailed _ shaped chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, rfl, _⟩ := shaped
        rw [operatorErase] at chosen
        have exhausted := chosen.undefined_exact storage
        simp at exhausted

/-- **The equation bodies under `E`, read as marked values.** -/
theorem bodies_source_at {atoms : List Atom} {E : Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
        DeterminedAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result},
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
          original E frame works results (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, derived => by
      obtain ⟨L, Ls', ⟨i, readsAs, determined, facts⟩, rest, rfl⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons sameBindings _ boundary batch later =>
          obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings
          cases boundary with
          | producerFunction pending _ => exact absurd pending (not_pending facts readErase)
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [readErase] at same
                          exact absurd same facts.notRefused
                      | stopped stopped =>
                          rw [readErase] at stopped
                          exact absurd stopped facts.notStopped
                      | evaluate _ _ evaluated =>
                          rw [List.append_nil, List.map_append,
                            determined _ readErase readMarked _ _ _ _ evaluated,
                            bodies_source_at ws Ls' rest later, List.flatten_cons]

/-- **HE's query under `E` of a call of values with open bodies is determined.** -/
theorem query_determined_at {atoms : List Atom} {E : Atom} (program : ScopedProgram atoms)
    {f : String} {vals : List Atom} (head : NodeHead dispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value dispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => DeterminedAt dispatch policy atoms E b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    QueryDeterminedAt dispatch policy atoms E f vals Ls.flatten := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
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
      have instances := works_instances_K policy valsValues program frame.certified.satisfiable
        frontier
      have onWorks : List.Forall₂ (fun (w : EquationWork) (L : List Atom) => ∃ i, (∀ output : Frame,
            output.bindings = w.bindings →
              (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
              Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
          DeterminedAt dispatch policy atoms E i L ∧ BodyFacts i) _ Ls :=
        (forall₂_comp instances bodies).imp fun _ _ both => by
          obtain ⟨i, ⟨_, reads⟩, determined, facts⟩ := both
          exact ⟨i, reads, determined, facts⟩
      exact bodies_source_at _ Ls onWorks equations

/-- **A query with an empty region under `E` returns the call, every derivation.** -/
theorem query_absent_at {atoms : List Atom} {E : Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (valsClean : ∀ v ∈ vals, Answerable v) (empty : regionBodies atoms f vals = []) :
    QueryDeterminedAt dispatch policy atoms E f vals [.expression (.symbol f :: vals)] := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  intro live scope value frame children erased called
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      simp [erased]
  | equations _ _ frontier nonempty _ =>
      rw [erased] at frontier
      have bodies := HERuns.frontier_bodies ground frame.certified.satisfiable program
        (by rw [empty]; intro b member; cases member) frontier
      rw [empty] at bodies
      exact absurd (List.map_eq_nil_iff.mp bodies) nonempty

/-! ## Every settling term, under every transparent demand -/

/-- **HE evaluates every settling term under a transparent demand**: if the demand casts each data
answer as it is, HE's machine evaluates every marked presentation under `E` to the answers, and
every derivation of HE's completed relation under `E` returns them. The arguments are evaluated
under `%Undefined%` by `CompoundBindings.settlesK_agree` and `settlesK_determined`. -/
theorem settlesK_at {atoms : List Atom} (program : CallProgram atoms) {E : Atom}
    (transparent : Transparent E) {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) :
    (∀ a ∈ L, DataAtom a → CastsAt atoms E a) →
    HEEvaluatesAt dispatch policy atoms E t L ∧ DeterminedAt dispatch policy atoms E t L := by
  induction settles with
  | @data d data _ =>
      intro casts
      have here := casts d List.mem_cons_self data
      exact ⟨he_data_at here, data_determined_at here⟩
  | @build f ts Ls head noEquation length settled _ =>
      intro _
      have whole := SettlesK.build head noEquation length settled
      have argsK : List.Forall₂ (fun t L => SettlesK dispatch atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => settled p member
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, settlesT⟩ := forall₂_right_exists argsK L member
        exact (settlesK_shape settlesT).1.answers a inside
      have closed := (settlesK_shape whole).1.answerable.closed
      refine ⟨fun v erased marked => ?_, fun v erased marked => ?_⟩
      · obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
        subst vsErase
        have argRuns : List.Forall₂ (fun v L => HERunsTo dispatch Completed.rawLookup policy atoms
            v L ∧ ∀ a ∈ L, Answerable a) vs Ls :=
          forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK) fun w member L settlesW =>
            ⟨(settlesK_agree (lookup := Completed.rawLookup) (policy := policy) raw_answers program
                settlesW).1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
              (settlesK_shape settlesW).1.answers⟩
        have query : ∀ vals ∈ combos Ls, HEQueryAt dispatch policy atoms E f vals
            [.expression (.symbol f :: vals)] ∧
            ∀ a ∈ [Atom.expression (.symbol f :: vals)], Answerable a := by
          intro vals member
          have valsClean := combos_answerable allClean vals member
          refine ⟨fun live scope activation value erased stack emitted => ?_, fun a inside => ?_⟩
          · refine ⟨[(value, activation)], by simp [erased], ?_⟩
            exact he_query_absent_at (scoped_consFree program.scoped) head.head head.notHost
              (head.instruction vals) (fun v inside => HERuns.ground_typeVars (valsClean v inside))
              (regionBodies_nil_of_no_equation vals noEquation) live scope activation value erased
              stack emitted
          · rw [List.mem_singleton] at inside
            subst inside
            exact app_answerable head.head valsClean
        by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
        · obtain ⟨reuses, rfl⟩ := reusedHeld
          have value := marked.held_value
          have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
              .symbol f :: vs.map Entry.Value.erase := by
            simp only [List.map_cons, Entry.Value.erase]
          rw [eraseList] at value
          rw [settlesK_value_self whole value]
          have runs := he_held_at (dispatch := dispatch) atoms transparent reuses
            (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
            (by rw [eraseList]; exact call_not_stopped head.head)
          rwa [eraseList] at runs
        · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
            cases reentry : policy.reentry <;> cases readiness <;> simp_all
          exact he_nested_at transparent head.head head.untyped closed interpreted rfl argRuns _ query
      · obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
        subst vsErase
        have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
            RunsDetermined dispatch policy atoms v L) vs Ls :=
          forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK)
            fun w member L settlesW => ⟨(settlesK_shape settlesW).1.answers,
              (settlesK_determined (policy := policy) program settlesW) w rfl
                (marked.children w (List.mem_cons_of_mem _ member))⟩
        exact nested_determined_at transparent head.head head.untyped closed rfl args
          (fun vals => [.expression (.symbol f :: vals)])
          (fun vals member => ⟨fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member),
            query_absent_at (scoped_consFree program.scoped) head.head (head.instruction vals)
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation)⟩)
          (fun isHeld _ => by
            subst isHeld
            have value := marked.held_value
            simp only [List.map_cons, Entry.Value.erase] at value
            exact settlesK_value_self whole value)
  | @call f ts Ls R head defined length settled nonempty lengths bodies _ ihBodies =>
      intro casts
      have whole := SettlesK.call R head defined length settled nonempty lengths bodies
      have argsK : List.Forall₂ (fun t L => SettlesK dispatch atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => settled p member
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, settlesT⟩ := forall₂_right_exists argsK L member
        exact (settlesK_shape settlesT).2 a inside
      have valsValues : ∀ vals ∈ combos Ls, ∀ v ∈ vals, NestedValues.Value dispatch atoms v :=
        combos_all allValues
      have bodyCasts : ∀ vals ∈ combos Ls, ∀ p ∈ (regionInstances atoms f vals).zip (R vals),
          ∀ a ∈ p.2, DataAtom a → CastsAt atoms E a := by
        intro vals member p inside a inA data
        apply casts a _ data
        apply List.mem_flatMap.mpr
        refine ⟨vals, member, List.mem_flatten.mpr ⟨p.2, (List.of_mem_zip inside).2, inA⟩⟩
      have regions : ∀ vals ∈ combos Ls, List.Forall₂ (fun b L => SettlesK dispatch atoms b L ∧
          (HEEvaluatesAt dispatch policy atoms E b L ∧ DeterminedAt dispatch policy atoms E b L))
          (regionInstances atoms f vals) (R vals) :=
        fun vals member => forall₂_of_zip (lengths vals member) fun p inside =>
          ⟨bodies vals member p inside,
            ihBodies vals member p inside (bodyCasts vals member p inside)⟩
      have closed := (settlesK_shape whole).1.answerable.closed
      refine ⟨fun v erased marked => ?_, fun v erased marked => ?_⟩
      · have query : ∀ vals ∈ combos Ls, HEQueryAt dispatch policy atoms E f vals (R vals).flatten ∧
            ∀ a ∈ (R vals).flatten, Answerable a := by
          intro vals member
          refine ⟨he_query_at program.scoped head (valsValues vals member) (nonempty vals member)
              ((regions vals member).imp fun _ _ both => ⟨both.2.1, settlesK_facts both.1⟩),
            fun a inside => ?_⟩
          obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
          obtain ⟨b, both⟩ := forall₂_right_exists (regions vals member) L inR
          exact (settlesK_shape both.1).1.answers a inner
        obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
        subst vsErase
        have argRuns : List.Forall₂ (fun v L => HERunsTo dispatch Completed.rawLookup policy atoms
            v L ∧ ∀ a ∈ L, Answerable a) vs Ls :=
          forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK) fun w member L settlesW =>
            ⟨(settlesK_agree (lookup := Completed.rawLookup) (policy := policy) raw_answers program
                settlesW).1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
              (settlesK_shape settlesW).1.answers⟩
        cases readiness with
        | held =>
            have value := marked.held_value
            simp only [List.map_cons, Entry.Value.erase] at value
            exact (value_not_defined defined value).elim
        | active =>
            exact he_nested_at transparent head.head head.untyped closed (Or.inr rfl) rfl argRuns _
              query
      · obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
        subst vsErase
        have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
            RunsDetermined dispatch policy atoms v L) vs Ls :=
          forall₂_imp_mem (List.forall₂_map_left_iff.mp argsK)
            fun w member L settlesW => ⟨(settlesK_shape settlesW).1.answers,
              (settlesK_determined (policy := policy) program settlesW) w rfl
                (marked.children w (List.mem_cons_of_mem _ member))⟩
        exact nested_determined_at transparent head.head head.untyped closed rfl args
          (fun vals => (R vals).flatten)
          (fun vals member => ⟨fun a inside => by
              obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
              obtain ⟨b, both⟩ := forall₂_right_exists (regions vals member) L inR
              exact (settlesK_shape both.1).1.answers a inner,
            query_determined_at program.scoped head (valsValues vals member) (nonempty vals member)
              ((regions vals member).imp fun _ _ both => ⟨both.2.2, settlesK_facts both.1⟩)⟩)
          (fun isHeld _ => by
            subst isHeld
            have value := marked.held_value
            simp only [List.map_cons, Entry.Value.erase] at value
            exact (value_not_defined defined value).elim)

#print axioms he_data_at
#print axioms he_held_at
#print axioms calls_loop_at
#print axioms he_nested_at
#print axioms he_query_absent_at
#print axioms equations_steps_at
#print axioms he_query_at
#print axioms data_determined_at
#print axioms calls_rows_at
#print axioms nested_determined_at
#print axioms bodies_source_at
#print axioms query_determined_at
#print axioms query_absent_at
#print axioms settlesK_at

end DemandSpine

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
