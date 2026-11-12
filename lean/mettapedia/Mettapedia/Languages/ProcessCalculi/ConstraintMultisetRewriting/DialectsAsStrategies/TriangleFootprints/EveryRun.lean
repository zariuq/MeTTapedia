import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.FragmentDifferences
import Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

/-!
# Every complete run of HE publishes PeTTa's answers

`AnswerBags.answers_agree` builds one complete run of HE's machine and shows that it publishes the
answers of PeTTa's streaming run. HE's machine is a relation, and it does branch on the fragment:
from the entry of an undeclared call both the tuple entry and the tuple fallback fire
(`Controls.entry_branches`), and casts and equation queries may reach different activation frames.
Here every complete run is covered.

The route is through HE's own source semantics. `RecursiveCorrectness.Contextual.steps_source_back`
reads every machine path back into HE's completed (big-step) relations, so a complete run from
the entry yields a derivation of `Completed.AtomRel` for the loaded term with the published batch
(`complete_source`). On the fragment that relation determines the published atoms:

* `data_source`: a data atom under `%Undefined%` has exactly one result, itself;
* `tuple_source`: the tuple of a call of data atoms has exactly one row, the call;
* `call_source`, `callRel_source`: the entry of an ordinary call, by the tuple entry or by the
  fallback, publishes the call's batch, which is the call itself when its region is empty and the
  results of its equation bodies otherwise;
* `bodies_source`: each equation body's results are its own;
* `settles_determined`: by induction on `Settles`, every derivation for a settling term publishes
  the same atoms.

`every_complete_run_under`: for every type lookup meeting `LookupContract` (under `%Undefined%`
demand it never answers the empty list, and it answers `[%Undefined%]` for an atom stored with just
that type), every complete run from HE's entry configuration publishes, as a list and so as a bag,
the values of PeTTa's streaming run of the translation from some fuel on. Both of HE's lookups meet
the contract (`raw_contract`, `scoped_contract`, `every_complete_run_with_he_lookups`);
`answer_bags_every_run` adds that a complete run exists. The named differences of
`FragmentDifferences` hold on every run (`uncovered_every_run`, `refused_every_run`,
`arity_every_run`, `over_every_run`).

## Controls

* `Controls.entry_branches` (the theorem has content): HE's machine takes two different first
  steps from the entry of `(toss)`.
* `Controls.toss_every_run` (positive): every complete run of `(toss)` on the coin program
  publishes `heads`, `tails`, `edge`.
* `Controls.loose_lookup_two_bags` (negative, the lookup): a lookup that answers the type list
  `[%Undefined%]` and also the empty list meets `AnswersUndefined`, but under it HE's machine has a
  complete run of the data atom `a` publishing nothing, besides one publishing `a`, which PeTTa
  answers; it fails the contract (`Controls.loose_not_contract`). So the every-run statement needs
  a lookup whose answers are never empty, as HE's own are.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace EveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open EntryToQuery AnswerBags

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## What the theorem needs of a type lookup -/

/-- **The lookup contract of the every-run theorem**: under `%Undefined%` demand a query never
answers the empty type list, and an atom whose stored types are just `%Undefined%` is answered
`[%Undefined%]`. -/
structure LookupContract (lookup : CastLookup) : Prop where
  nonempty : ∀ (scope : List String) (space : Space) (bindings : Bindings) (subject : Atom)
    (types : List Atom), lookup scope space bindings subject Atom.undefinedType types → types ≠ []
  undeclared : ∀ (scope : List String) (space : Space) (bindings : Bindings) (subject : Atom)
    (types : List Atom),
    Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel space subject [Atom.undefinedType] →
    lookup scope space bindings subject Atom.undefinedType types → types = [Atom.undefinedType]

/-- **HE's historical list-storage lookup meets the contract.** -/
theorem raw_contract : LookupContract Completed.rawLookup :=
  ⟨fun _ space _ subject _ queried =>
      (show Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel space subject _ from
        queried).nonempty,
    fun _ space _ subject _ stored queried =>
      Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.unique
        (show Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel space subject _ from queried)
        stored⟩

/-- **HE's scoped lookup (fresh variants of the stored types) meets the contract.** -/
theorem scoped_contract : LookupContract Completed.scopedLookup := by
  refine ⟨fun scope space bindings subject types queried => ?_,
    fun scope space bindings subject types stored queried => ?_⟩
  · obtain ⟨raw, stored, variants⟩ := queried
    intro empty
    subst empty
    cases variants
    exact stored.nonempty rfl
  · obtain ⟨raw, storedRaw, variants⟩ := queried
    have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.unique storedRaw stored
    subst same
    cases variants with
    | cons variant rest =>
        cases rest
        obtain ⟨rename, _, renamed, _⟩ := variant
        rw [renamed]
        simp [Atom.undefinedType,
          Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]

/-! ## From complete runs to HE's source semantics -/

/-- **A complete run is a source derivation.** Every run of HE's machine from the entry
configuration of `c` to a completed phase with publication `E` gives HE's completed relation for
`c` with the result batch `E`. -/
theorem complete_source {lookup : CastLookup} {space : Space} {c : Atom} {E : List Result}
    (run : Relation.ReflTransGen (HEStep dispatch lookup policy)
      (load space c Atom.undefinedType) ⟨space, .returning [], [], E⟩) :
    Completed.AtomRel space dispatch lookup [] [] (Entry.Value.ofAtom c) Atom.undefinedType
      Completed.Frame.empty E (policy := policy) := by
  have final : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.SourceRel
      dispatch lookup policy ⟨space, .returning [], [], E⟩ E :=
    ⟨[], [], .returning [], .nil [], (List.append_nil E).symm⟩
  have initial := Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.steps_source_back
    run final
  exact (Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.initial_source_iff space
    dispatch lookup policy (.atom [] [] (Entry.Value.ofAtom c) Atom.undefinedType
      Completed.Frame.empty) E).mp initial

/-! ## HE's source semantics on the fragment -/

/-- **A data atom has one result, itself**, at some reached frame, under a lookup meeting the
contract. -/
theorem data_source {lookup : CastLookup} (contract : LookupContract lookup) {space : Space}
    {live : List Atom} {scope : List String} {d : Atom}
    (data : DataAtom d) {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel space dispatch lookup live scope
      (Entry.Value.ofAtom d) Atom.undefinedType frame results (policy := policy)) :
    ∃ after : Frame, results = [(Entry.Value.ofAtom d, after)] := by
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom d)).status
      (frame.read policy (Entry.Value.ofAtom d)).erase Atom.undefinedType .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast _ batch related =>
      rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
      cases batch with
      | success _ _ _ _ =>
          obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
          obtain rfl := List.forall₂_nil_left_iff.mp rest
          have value : r.1 = Entry.Value.ofAtom d := by
            have payload := first.payload
            split at payload <;> exact payload
          exact ⟨r.2, by rw [← value]⟩
      | failure queried rejected =>
          obtain ⟨type, member⟩ := List.exists_mem_of_ne_nil _
            (contract.nonempty _ _ _ _ _ queried)
          exact (rejected type member frame.bindings
            (undefined_matches policy.matching type frame)).elim
  | tuple entered => cases Entry.functional entered entry
  | function entered => cases Entry.functional entered entry
  | fallback entered => cases Entry.functional entered entry
  | selectionFailed entered => cases Entry.functional entered entry

/-- **The tuple of data atoms has one row**, the tuple itself, at some reached frame. -/
theorem tuple_source {lookup : CastLookup} (contract : LookupContract lookup) {space : Space}
    {scope : List String} :
    ∀ (values : List Atom), values ≠ [] → (∀ v ∈ values, DataAtom v) →
      ∀ (live : List Atom) (frame : Frame) (results : List Result),
        Completed.TupleRel space dispatch lookup live scope
          (values.map Entry.Value.ofAtom) frame results (policy := policy) →
        ∃ after : Frame,
          results = [(.expression .active (values.map Entry.Value.ofAtom), after)]
  | [], nonempty, _ => absurd rfl nonempty
  | [v], _, data => by
      intro live frame results derived
      have here := data v List.mem_cons_self
      simp only [List.map_cons, List.map_nil] at derived
      cases derived with
      | singleton heads =>
          obtain ⟨after, rfl⟩ := data_source contract here heads
          refine ⟨after, ?_⟩
          rw [List.map_singleton, tupleSingleton_data here]
          rfl
  | v :: next :: rest, _, data => by
      intro live frame results derived
      have here := data v List.mem_cons_self
      have later : ∀ w ∈ next :: rest, DataAtom w := fun w member =>
        data w (List.mem_cons_of_mem _ member)
      simp only [List.map_cons] at derived
      cases derived with
      | cons heads branches =>
          obtain ⟨after, rfl⟩ := data_source contract here heads
          cases branches with
          | stopped stopped _ =>
              exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped) here.not_stopped
          | continuing _ children tail =>
              cases tail
              obtain ⟨after', rfl⟩ := tuple_source contract (next :: rest) (List.cons_ne_nil _ _)
                later _ _ _ children
              refine ⟨after', ?_⟩
              rw [List.map_singleton, List.append_nil,
                tuplePrepend_data (later next List.mem_cons_self) rest]
              rfl

/-- **The entry of an ordinary call**, by the tuple entry or by the fallback: the published atoms
are those of the batch the call's `CallRel` returns, selected by success priority. -/
theorem call_source {lookup : CastLookup} (contract : LookupContract lookup) {atoms : List Atom}
    {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) {live : List Atom} {scope : List String}
    {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch lookup live scope
      (Entry.Value.ofAtom (.expression (.symbol f :: args))) Atom.undefinedType frame results
      (policy := policy)) :
    ∃ (after : Frame) (children selected : List Result),
      Completed.CallRel (Space.ofList atoms) dispatch lookup live scope
        (callValue f args) Atom.undefinedType after children (policy := policy) ∧
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (children.map (Completed.readResult policy)) selected ∧
      results.map (fun r => r.1.erase) = selected.map (fun r => r.1.erase) := by
  have closed := (call_answerable ordinary.head ordinary.arguments).closed
  have readCall := HERuns.read_closed policy frame closed
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).status
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy ordinary.head args
    rw [Completed.Frame.read_empty] at base
    rw [readCall]
    exact base
  have shape : frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: args.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences ordinary.untyped)
  have data := HERuns.ordinary_data ordinary
  -- the tuple and its calls, shared by the tuple entry and the fallback
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
        (.symbol f) Atom.undefinedType frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have rows : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.ofAtom (.symbol f) = operator → args.map Entry.Value.ofAtom = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch lookup
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch lookup live scope
        Atom.undefinedType rows raw (policy := policy) →
      ∃ after : Frame, Completed.CallRel (Space.ofList atoms) dispatch lookup live
        scope (callValue f args) Atom.undefinedType after raw (policy := policy) := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    obtain ⟨after, rfl⟩ := tuple_source contract (Atom.symbol f :: args) (List.cons_ne_nil _ _)
      data _ _ _ tuples
    cases calls with
    | cons called rest =>
        cases rest
        rw [List.append_nil]
        exact ⟨after, called⟩
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped _ tuples calls chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      obtain ⟨after, called⟩ := rows sameOperator sameArguments tuples calls
      exact ⟨after, _, _, called, chosen, by simp [Completed.publishResult]⟩
  | function _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      cases selectionExact chosen
  | fallback _ shaped chosen tuples calls selected =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      have operatorErase := congrArg Entry.Value.erase sameOperator
      rw [Entry.Value.erase_ofAtom] at operatorErase
      rw [← operatorErase] at chosen
      have exhausted := selectionExact chosen
      simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
      subst exhausted
      obtain ⟨after, called⟩ := rows sameOperator sameArguments tuples calls
      have chosenRaw := selected
      simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
      exact ⟨after, _, _, called, chosenRaw, by simp [Completed.publishResult]⟩
  | selectionFailed _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      have exhausted := selectionExact chosen
      simp at exhausted

/-- **The batch of an ordinary call**: the call itself when its region is empty, the results of
its equation bodies (one work per row of the region, in row order) otherwise. -/
theorem callRel_source {lookup : CastLookup} {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b)
    {live : List Atom} {scope : List String} {after : Frame} {children : List Result}
    (called : Completed.CallRel (Space.ofList atoms) dispatch lookup live scope
      (callValue f args) Atom.undefinedType after children (policy := policy)) :
    (children = [(callValue f args, after)] ∧ regionBodies atoms f args = []) ∨
      ∃ works : List EquationWork, works ≠ [] ∧
        works.map EquationWork.body = regionBodies atoms f args ∧
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch lookup live scope
          (callValue f args) Atom.undefinedType after works children (policy := policy) := by
  have ground : ∀ v ∈ args,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member))
  cases called with
  | error failed => exact absurd failed (call_not_error ordinary.head args)
  | embedded _ _ instruction _ _ =>
      rw [callValue_erase, ordinary.notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [callValue_erase] at frontier
      have bodies := HERuns.frontier_bodies ground after.certified.satisfiable program fixed frontier
      exact Or.inl ⟨rfl, bodies.symm⟩
  | equations _ _ frontier nonempty bodies =>
      rw [callValue_erase] at frontier
      exact Or.inr ⟨_, nonempty, HERuns.frontier_bodies ground after.certified.satisfiable program
        fixed frontier, bodies⟩

/-- **HE's source semantics determines the atoms `t` publishes** under a lookup: every derivation
of HE's completed relation for `t` under `%Undefined%`, at any live list, scope and activation,
returns a batch whose atoms are `L`. -/
def DeterminedUnder (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (frame : Frame) (results : List Result),
    Completed.AtomRel (Space.ofList atoms) dispatch lookup live scope
      (Entry.Value.ofAtom t) Atom.undefinedType frame results (policy := policy) →
    results.map (fun r => r.1.erase) = L

/-- Determined under HE's historical lookup. -/
abbrev Determined (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (t : Atom)
    (L : List Atom) : Prop :=
  DeterminedUnder dispatch Completed.rawLookup policy atoms t L

/-- **The equation bodies**: each body's results are the atoms its own derivations determine. -/
theorem bodies_source {lookup : CastLookup} {atoms : List Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => DeterminedUnder dispatch lookup policy atoms w.body L ∧
        BodyFacts w.body) works Ls →
      ∀ {results : List Result},
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch lookup live scope
          original Atom.undefinedType frame works results (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, derived => by
      obtain ⟨L, Ls', ⟨determined, facts⟩, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons _ _ boundary batch later =>
          rw [HERuns.read_closed policy _ facts.closed] at boundary
          cases boundary with
          | producerFunction pending _ => exact absurd pending (facts.notFunction policy)
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          exact absurd (by simpa only [Entry.Value.erase_ofAtom] using same)
                            facts.notRefused
                      | stopped stopped =>
                          exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped)
                            facts.notStopped
                      | evaluate _ _ evaluated =>
                          rw [List.append_nil, List.map_append, determined _ _ _ _ evaluated,
                            bodies_source ws Ls' rest later, List.flatten_cons]

/-- A batch selected from the call itself publishes the call. -/
theorem single_call_published {f : String} {args : List Atom}
    (answerable : Answerable (.expression (.symbol f :: args))) {after : Frame}
    {results selected : List Result}
    (chosen : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(callValue f args, after)].map (Completed.readResult policy)) selected)
    (erased : results.map (fun r => r.1.erase) = selected.map (fun r => r.1.erase)) :
    results.map (fun r => r.1.erase) = [.expression (.symbol f :: args)] := by
  have unchanged : [(callValue f args, after)].map (Completed.readResult policy) =
      [(callValue f args, after)] := by
    rw [List.map_singleton, HERuns.readResult_closed policy _
      (by rw [callValue_erase]; exact answerable.closed)]
  rw [unchanged] at chosen
  have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
    chosen (HERuns.success_all _ fun r member => by
      rw [List.mem_singleton] at member
      subst member
      rw [callValue_erase]
      exact answerable.notError)
  rw [erased, same]
  simp [callValue_erase]

/-- **A call with an empty region** (no row of the program unifies with it): every derivation
publishes the call itself. -/
theorem empty_region_determined {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (empty : regionBodies atoms f args = []) :
    DeterminedUnder dispatch lookup policy atoms (.expression (.symbol f :: args))
      [.expression (.symbol f :: args)] := by
  intro live scope frame results derived
  obtain ⟨after, children, selected, called, chosen, erased⟩ :=
    call_source contract ordinary derived
  rcases callRel_source program ordinary (by rw [empty]; intro b member; cases member)
      called with ⟨rfl, _⟩ | ⟨works, nonemptyWorks, bodies, _⟩
  · exact single_call_published (call_answerable ordinary.head ordinary.arguments) chosen erased
  · rw [empty] at bodies
    exact absurd (List.map_eq_nil_iff.mp bodies) nonemptyWorks

/-- **A call whose region holds one row, with body `NotReducible`**: every derivation refuses the
reduction and publishes the call itself. -/
theorem refused_determined {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (refusing : regionBodies atoms f args = [Atom.notReducible]) :
    DeterminedUnder dispatch lookup policy atoms (.expression (.symbol f :: args))
      [.expression (.symbol f :: args)] := by
  have refusedData : DataAtom Atom.notReducible := .symbol (by decide) (by decide)
  have fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [refusing]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    simp [Atom.notReducible, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  intro live scope frame results derived
  obtain ⟨after, children, selected, called, chosen, erased⟩ :=
    call_source contract ordinary derived
  rcases callRel_source program ordinary fixed called with
    ⟨_, empty⟩ | ⟨works, _, bodies, equations⟩
  · rw [refusing] at empty
    cases empty
  · rw [refusing] at bodies
    obtain ⟨w, rfl, body⟩ : ∃ w : EquationWork, works = [w] ∧ w.body = Atom.notReducible := by
      cases works with
      | nil => cases bodies
      | cons w ws =>
          simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at bodies
          exact ⟨w, by rw [bodies.2], bodies.1⟩
    cases equations with
    | cons _ _ boundary batch later =>
        cases later
        rw [body, HERuns.read_closed policy _ (answerable_of_data refusedData).closed] at boundary
        cases boundary with
        | producerFunction pending _ =>
            obtain ⟨⟨_, same⟩, _⟩ := pending
            rw [Entry.Value.erase_ofAtom] at same
            simp [Atom.notReducible] at same
        | producerRaw _ =>
            cases batch with
            | cons returned tail =>
                cases tail
                cases returned with
                | returned answered =>
                    cases answered with
                    | notReducible _ =>
                        simp only [List.append_nil] at chosen
                        exact single_call_published (call_answerable ordinary.head
                          ordinary.arguments) chosen erased
                    | stopped stopped =>
                        exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped)
                          refusedData.not_stopped
                    | evaluate differs _ _ =>
                        exact absurd (Entry.Value.erase_ofAtom _) differs

/-- **On the fragment, HE's source semantics determines the published atoms.** For every term that
settles in a program of symbol-headed, `cons`-free equations, and every lookup meeting the
contract: one list `L` of answerable atoms such that every derivation of HE's completed relation for
the term, at any live list, scope and activation, returns a batch whose atoms are `L`. -/
theorem settles_determined_under {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {t : Atom}
    (settles : Settles dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ DeterminedUnder dispatch lookup policy atoms t L := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨[d], fun a member => ?_, fun live scope frame results derived => ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · obtain ⟨after, rfl⟩ := data_source contract data derived
        simp
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        empty_region_determined contract program ordinary
          (regionBodies_nil_of_no_equation args noEquation)⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionBodies atoms f args, ∃ L : List Atom,
          Settles dispatch atoms b ∧ (∀ a ∈ L, Answerable a) ∧
            DeterminedUnder dispatch lookup policy atoms b L := by
        intro b member
        obtain ⟨L, clean, determined⟩ := ih b member
        exact ⟨L, settled b member, clean, determined⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have cleanAll : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
        exact both.2.1 a inner
      have fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
          Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b :=
        fun b member => (settles_facts (settled b member)).fixed
      refine ⟨Ls.flatten, cleanAll, fun live scope frame results derived => ?_⟩
      obtain ⟨after, children, selected, called, chosen, erased⟩ :=
        call_source contract ordinary derived
      rcases callRel_source program ordinary fixed called with
        ⟨_, empty⟩ | ⟨works, _, bodies, equations⟩
      · exact absurd empty nonempty
      · have onWorks : List.Forall₂
            (fun w L => DeterminedUnder dispatch lookup policy atoms w.body L ∧ BodyFacts w.body)
            works Ls := by
          have onBodies := related
          rw [← bodies] at onBodies
          exact (List.forall₂_map_left_iff.mp onBodies).imp fun _ _ both =>
            ⟨both.2.2, settles_facts both.1⟩
        have erasedChildren := bodies_source works Ls onWorks equations
        have clean : ∀ r ∈ children, Answerable r.1.erase := by
          intro r member
          apply cleanAll
          rw [← erasedChildren]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        have unchanged : children.map (Completed.readResult policy) = children :=
          map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
        rw [unchanged] at chosen
        have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
          chosen (HERuns.success_all children fun r member => (clean r member).notError)
        rw [erased, same, erasedChildren]

/-- `settles_determined_under` for HE's historical lookup. -/
theorem settles_determined {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {t : Atom}
    (settles : Settles dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ Determined dispatch policy atoms t L :=
  settles_determined_under raw_contract program settles

/-! ## Every complete run -/

/-- **Every complete run of HE publishes PeTTa's answers, under any lookup meeting the contract.**
For a program of symbol-headed, `cons`-free equations and a term that settles in it: with a lookup
that answers every `%Undefined%` query (`AnswersUndefined`) and meets `LookupContract`, any policy
and any grounded dispatch, there is a fuel from which on PeTTa's streaming run of the translation
yields exactly the atoms that **every** run of HE's machine from its entry configuration to a
completed phase publishes, in the same order and with the same multiplicities. -/
theorem every_complete_run_under (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (contract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {c : Atom} (settles : Settles dispatch atoms c) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  obtain ⟨L, _, determined⟩ := settles_determined_under (policy := policy) contract program settles
  obtain ⟨heAnswers, N, path, _, agree⟩ := answers_agree dispatch answers policy program settles
  refine ⟨N, fun n bigger emitted run => ?_⟩
  rw [agree n bigger, determined _ _ _ _ (complete_source path),
    determined _ _ _ _ (complete_source run)]

/-- **Every complete run of HE publishes PeTTa's answers** (HE's historical lookup). -/
theorem every_complete_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {c : Atom}
    (settles : Settles dispatch atoms c) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) :=
  every_complete_run_under dispatch raw_answers raw_contract policy program settles

/-- **With either of HE's own lookups** (the historical list storage and the scoped fresh
variants), every complete run of HE publishes PeTTa's answers. -/
theorem every_complete_run_with_he_lookups (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {c : Atom} (settles : Settles dispatch atoms c) :
    ∀ lookup ∈ [Completed.rawLookup, Completed.scopedLookup],
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch lookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  intro lookup member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact every_complete_run_under dispatch raw_answers raw_contract policy program settles
  · exact every_complete_run_under dispatch scoped_answers scoped_contract policy program settles

/-- **The answer bags agree, for every complete run.** A complete run of HE exists, and the bag
of atoms every complete run publishes is the bag PeTTa's streaming run yields from some fuel on. -/
theorem answer_bags_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {c : Atom}
    (settles : Settles dispatch atoms c) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers) ∧
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          ((emitted.map fun r => r.1.erase : List Atom) : Multiset Atom) =
            (Streaming.values (Streaming.advance (translate atoms) n
              (Streaming.enter { state := store atoms } c)) : Multiset Atom) := by
  obtain ⟨heAnswers, _, path, observed, _⟩ :=
    answers_agree dispatch raw_answers policy program settles
  obtain ⟨N, every⟩ := every_complete_run dispatch policy program settles
  exact ⟨⟨heAnswers, path, observed⟩, N, fun n bigger emitted run => by
    rw [every n bigger emitted run]⟩

/-! ## The named differences, for every complete run -/

/-- **Uncovered calls differ on every run.** For an ordinary call whose head has an equation of its
arity but no row unifying with it: every complete run of HE publishes the call itself, and from
some fuel on PeTTa's run yields nothing. -/
theorem uncovered_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (empty : regionBodies atoms f args = [])
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) = [] :=
  ⟨fun _ run => empty_region_determined raw_contract program ordinary empty _ _ _ _
      (complete_source run),
    (uncovered_calls_differ dispatch raw_answers policy program ordinary empty defined).2⟩

/-- **Refused calls differ on every run.** For an ordinary call whose region holds one row, with
body `NotReducible`: every complete run of HE publishes the call itself, and from some fuel on
PeTTa's run yields `NotReducible`. -/
theorem refused_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (refusing : regionBodies atoms f args = [Atom.notReducible]) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) =
          [Atom.notReducible] :=
  ⟨fun _ run => refused_determined raw_contract program ordinary refusing _ _ _ _
      (complete_source run),
    (FragmentDifferences.refused_calls_differ (policy := policy) dispatch raw_answers program
      ordinary refusing).2⟩

/-- **Calls shorter than every equation of their head differ on every run.** Every complete run of
HE publishes the call itself; from some fuel on PeTTa's run yields the partial-application
carrier. -/
theorem arity_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (noArity : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length ≠ args.length)
    (longer : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      args.length < e.arguments.length) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) =
          [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue f args] :=
  ⟨fun _ run => empty_region_determined raw_contract program ordinary
      (FragmentDifferences.regionBodies_nil_of_arity noArity) _ _ _ _ (complete_source run),
    (FragmentDifferences.arity_calls_differ (policy := policy) dispatch raw_answers program
      ordinary noArity longer).2⟩

/-- **Calls longer than every equation of their head differ on every run.** Every complete run of
HE publishes the call itself; from some fuel on PeTTa's run is stopped at its uncaught
over-application fault, with no value. -/
theorem over_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (shorter : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length < args.length)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ (N : Nat) (reason : Effects.Fault), ∀ n, N ≤ n →
        (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))).agenda =
            [.execute ⟨.fault reason, []⟩] ∧
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) = [] :=
  ⟨fun _ run => empty_region_determined raw_contract program ordinary
      (FragmentDifferences.regionBodies_nil_of_arity fun e live head =>
        Nat.ne_of_lt (shorter e live head)) _ _ _ _ (complete_source run),
    (FragmentDifferences.over_calls_differ (policy := policy) dispatch raw_answers program
      ordinary shorter defined).2⟩

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app coinRows coin_program toss_settles toss_agrees ordinary_toss)
open WholeRunWords.Double (noHost)

/-- The configuration after the tuple entry of `(toss)`. -/
def afterTuple (policy : Policy) : HEOnTheStep.HEConfig :=
  ⟨Space.ofList coinRows,
    .work (.tuple [Atom.undefinedType] [] [Entry.Value.ofAtom (.symbol "toss")]
      Completed.Frame.empty),
    [.calls [] [] Atom.undefinedType,
      .publish (Completed.Frame.empty.read policy (Entry.Value.ofAtom (app "toss" []))).erase], []⟩

/-- The configuration after the tuple fallback of `(toss)`: one more continuation, the empty
diagnostics. -/
def afterFallback (policy : Policy) : HEOnTheStep.HEConfig :=
  ⟨Space.ofList coinRows,
    .work (.tuple [Atom.undefinedType] [] [Entry.Value.ofAtom (.symbol "toss")]
      Completed.Frame.empty),
    [.calls [] [] Atom.undefinedType, .diagnostics [] Completed.Frame.empty,
      .publish (Completed.Frame.empty.read policy (Entry.Value.ofAtom (app "toss" []))).erase], []⟩

/-- **HE's machine branches at the entry of `(toss)`**: the tuple entry and the tuple fallback
both fire, to different configurations. Every-run agreement is a statement about a relation with
more than one run. -/
theorem entry_branches (policy : Policy) :
    HEStep noHost Completed.rawLookup policy
        (load (Space.ofList coinRows) (app "toss" []) Atom.undefinedType) (afterTuple policy) ∧
      HEStep noHost Completed.rawLookup policy
        (load (Space.ofList coinRows) (app "toss" []) Atom.undefinedType)
        (afterFallback policy) ∧
      afterTuple policy ≠ afterFallback policy := by
  have ordinary := ordinary_toss
  have entry := call_entry policy ordinary.head []
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (app "toss" [])) =
      .expression .active (Entry.Value.ofAtom (.symbol "toss") :: []) := by
    rw [Completed.Frame.read_empty]
    simp only [app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList coinRows).atoms : Multiset Atom) (Entry.Value.ofAtom (.symbol "toss")).erase
      {Atom.undefinedType} := by
    rw [Entry.Value.erase_ofAtom]
    exact untyped_occurrences ordinary.untyped
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList coinRows)
      (.symbol "toss") [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences ordinary.untyped)
  have notArrow : ∀ candidate ∈ [Atom.undefinedType], ¬ ∃ domains returned,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.FunctionTypeRel candidate domains returned := by
    intro candidate member
    obtain rfl := List.mem_singleton.mp member
    rintro ⟨domains, returned, arrow⟩
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.FunctionTypeRel, Atom.undefinedType] at arrow
  have selection : Completed.ArgumentService.historical.selection (Space.ofList coinRows)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (app "toss" []))).erase
      (Entry.Value.ofAtom (.symbol "toss")).erase Atom.undefinedType Completed.Frame.empty
      (.exhausted [] true) := by
    rw [Entry.Value.erase_ofAtom]
    exact ⟨[Atom.undefinedType], storage, .nonFunction (notArrow _ List.mem_cons_self) .nil⟩
  refine ⟨.internal (LocalStepWith.atomTuple (admission := .historical)
      (space := Space.ofList coinRows) (live := []) (scope := []) (stack := []) entry shape
      occurrences),
    .internal (LocalStepWith.atomFallback (admission := .historical)
      (space := Space.ofList coinRows) (live := []) (scope := []) (stack := []) entry shape
      selection), fun same => ?_⟩
  have lengths := congrArg (fun config : HEOnTheStep.HEConfig => config.stack.length) same
  simp [afterTuple, afterFallback] at lengths

/-- **Positive control: every complete run of `(toss)` publishes `heads`, `tails`, `edge`.** -/
theorem toss_every_run (policy : Policy) (emitted : List Result)
    (run : Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
      (load (Space.ofList coinRows) (app "toss" []) Atom.undefinedType)
      ⟨Space.ofList coinRows, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = [sym "heads", sym "tails", sym "edge"] := by
  obtain ⟨L, _, determined⟩ := settles_determined (policy := policy) coin_program toss_settles
  obtain ⟨heAnswers, path, erased, _⟩ := toss_agrees raw_answers policy
  rw [determined _ _ _ _ (complete_source run), ← determined _ _ _ _ (complete_source path),
    erased]

/-- A cast lookup that answers the type list `[%Undefined%]` and also the empty list. -/
def looseLookup : CastLookup := fun _ _ _ _ _ types => types = [Atom.undefinedType] ∨ types = []

theorem loose_answers : AnswersUndefined looseLookup :=
  fun _ _ _ _ => ⟨Atom.undefinedType, [], Or.inl rfl⟩

/-- The loose lookup fails the contract: it may answer the empty type list. -/
theorem loose_not_contract : ¬ LookupContract looseLookup :=
  fun contract => contract.nonempty [] Space.empty Bindings.empty (sym "a") [] (Or.inr rfl) rfl

theorem a_data : DataAtom (sym "a") := .symbol (by decide) (by decide)

/-- **Negative control: the every-run statement needs a lookup whose answers are never empty.**
Under `looseLookup`, which meets `AnswersUndefined`, HE's machine has a complete run of the data
atom `a` that publishes nothing (its cast meets the empty type list) and one that publishes `a`;
PeTTa answers `a`. -/
theorem loose_lookup_two_bags (policy : Policy) :
    Relation.ReflTransGen (HEStep noHost looseLookup policy)
        (load (Space.ofList []) (sym "a") Atom.undefinedType)
        ⟨Space.ofList [], .returning [], [], []⟩ ∧
      Relation.ReflTransGen (HEStep noHost looseLookup policy)
        (load (Space.ofList []) (sym "a") Atom.undefinedType)
        ⟨Space.ofList [], .returning [], [], [(Entry.Value.ofAtom (sym "a"), Completed.Frame.empty)]⟩ ∧
      Streaming.values (Streaming.advance (translate []) 10
        (Streaming.enter { state := store [] } (sym "a"))) = [sym "a"] := by
  refine ⟨.single (.internal (LocalStepWith.cast (raw := []) ?_ ?_ .nil)), ?_, by decide +kernel⟩
  · simp only [CompleteRun.read_data policy _ a_data, Entry.Value.erase_ofAtom, a_data.status]
    exact a_data.entry policy.reentry
  · simp only [CompleteRun.read_data policy _ a_data, Entry.Value.erase_ofAtom]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel.failure (types := [])
      (Or.inr rfl) (fun _ member => by cases member)
  · exact .tail (.single (CompleteRun.cast_step_frame loose_answers (Space.ofList []) a_data
      Completed.Frame.empty [] [] [] [])) .publish

end Controls

#print axioms raw_contract
#print axioms scoped_contract
#print axioms complete_source
#print axioms data_source
#print axioms tuple_source
#print axioms call_source
#print axioms callRel_source
#print axioms bodies_source
#print axioms settles_determined_under
#print axioms settles_determined
#print axioms every_complete_run_under
#print axioms every_complete_run
#print axioms every_complete_run_with_he_lookups
#print axioms answer_bags_every_run
#print axioms single_call_published
#print axioms empty_region_determined
#print axioms refused_determined
#print axioms uncovered_every_run
#print axioms refused_every_run
#print axioms arity_every_run
#print axioms over_every_run
#print axioms Controls.entry_branches
#print axioms Controls.toss_every_run
#print axioms Controls.loose_lookup_two_bags
#print axioms Controls.loose_not_contract

end EveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
