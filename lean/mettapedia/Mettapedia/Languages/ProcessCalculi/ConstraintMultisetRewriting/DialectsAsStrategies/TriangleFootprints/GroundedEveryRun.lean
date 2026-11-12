import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedRuns

/-!
# Grounded operations: every complete run of HE's world machine publishes PeTTa's answers

`GroundedRuns.answersG_agree` builds one complete run of HE's world machine. Here every complete
run is covered, by the route of `EveryRun` on the world machine's own source semantics:

* HE's world machine reflects every terminal run into its completed stateful source relation
  (`RecursiveExecution.Contextual.Stateful.finished_to_source`, existing), so a complete run from
  the entry gives `Completed.Stateful.AtomRel` for the loaded term with the published batch
  (`complete_source_W`);
* on the fragment that relation determines the published atoms (`settlesG_determined_W`), by the
  inversions of `EveryRun` and `BoundVariables` read on the stateful relations, and one more for
  the grounded call (`grounded_source_W`): the host service and HE's integer dispatch fix the
  outcome; only `callGroundedResume` applies; its native boundary returns the value, which is
  evaluated again and cast.

`every_complete_run_G`: for every lookup meeting `LookupContract`, every complete run of HE's world
machine from the entry configuration of a settling term publishes the values of PeTTa's streaming
run from some fuel on. `Controls.double_every_run`: every complete run of `(double 4)` publishes
`8`, and PeTTa gives `8`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame WorldServices
  WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load WorldSteps worldObserve)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables GroundedTables GroundedRuns

/-- **HE's world environment with the integer dispatch.** -/
def worldEnv (minimal : Minimal.Services) (lookup : CastLookup) : WorldEnvironment Space Unit where
  view := fun _ => id
  services := services minimal
  dispatch := heDispatch
  lookup := lookup

variable {minimal : Minimal.Services} {policy : Policy}

/-! ## From complete runs to the world source semantics -/

/-- **A complete world run is a stateful source derivation.** -/
theorem complete_source_W {lookup : CastLookup} {space : Space} {c : Atom} {E : List Result}
    (run : WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly (load space c Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨space, .returning [], [], E⟩)) :
    Completed.Stateful.AtomRel (worldEnv minimal lookup) space () [] [] (Entry.Value.ofAtom c)
      Atom.undefinedType Completed.Frame.empty E () (policy := policy) := by
  have source := Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.finished_to_source
    (environment := worldEnv minimal lookup) (policy := policy) run
  obtain ⟨current, pending, childWorld, controlled, continued, same⟩ := source
  cases controlled with
  | work derived =>
      cases continued
      simp only [WorldConfiguration.ofReadOnly, load,
        Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial,
        List.nil_append] at same
      subst same
      exact derived

/-! ## The world source semantics on the fragment -/

/-- **A data atom has one result, itself.** -/
theorem data_source_W {lookup : CastLookup} (contract : LookupContract lookup) {space : Space}
    {world world' : Unit} {live : List Atom} {scope : List String} {d : Atom} (data : DataAtom d)
    {frame : Frame} {results : List Result}
    (derived : Completed.Stateful.AtomRel (worldEnv minimal lookup) space world live scope
      (Entry.Value.ofAtom d) Atom.undefinedType frame results world' (policy := policy)) :
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

/-- **The tuple of data atoms has one row**, the tuple itself. -/
theorem tuple_source_W {lookup : CastLookup} (contract : LookupContract lookup) {space : Space}
    {scope : List String} :
    ∀ (values : List Atom), values ≠ [] → (∀ v ∈ values, DataAtom v) →
      ∀ (world world' : Unit) (live : List Atom) (frame : Frame) (results : List Result),
        Completed.Stateful.TupleRel (worldEnv minimal lookup) space world live scope
          (values.map Entry.Value.ofAtom) frame results world' (policy := policy) →
        ∃ after : Frame,
          results = [(.expression .active (values.map Entry.Value.ofAtom), after)]
  | [], nonempty, _ => absurd rfl nonempty
  | [v], _, data => by
      intro world world' live frame results derived
      have here := data v List.mem_cons_self
      simp only [List.map_cons, List.map_nil] at derived
      cases derived with
      | singleton heads =>
          obtain ⟨after, rfl⟩ := data_source_W contract here heads
          refine ⟨after, ?_⟩
          rw [List.map_singleton, tupleSingleton_data here]
          rfl
  | v :: next :: rest, _, data => by
      intro world world' live frame results derived
      have here := data v List.mem_cons_self
      have later : ∀ w ∈ next :: rest, DataAtom w := fun w member =>
        data w (List.mem_cons_of_mem _ member)
      simp only [List.map_cons] at derived
      cases derived with
      | cons heads branches =>
          obtain ⟨after, rfl⟩ := data_source_W contract here heads
          cases branches with
          | stopped stopped _ =>
              exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped) here.not_stopped
          | continuing _ children tail =>
              cases tail
              obtain ⟨after', rfl⟩ := tuple_source_W contract (next :: rest) (List.cons_ne_nil _ _)
                later _ _ _ _ _ children
              refine ⟨after', ?_⟩
              rw [List.map_singleton, List.append_nil,
                tuplePrepend_data (later next List.mem_cons_self) rest]
              rfl

/-- **The entry of a call of data atoms with an undeclared head**, by the tuple entry or by the
fallback: the published atoms are those of the batch the call's `CallRel` returns. -/
theorem call_source_W {lookup : CastLookup} (contract : LookupContract lookup) {atoms : List Atom}
    {f : String} {args : List Atom} (head : DataAtom (.symbol f)) (arguments : ∀ a ∈ args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    {world world' : Unit} {live : List Atom} {scope : List String} {frame : Frame}
    {results : List Result}
    (derived : Completed.Stateful.AtomRel (worldEnv minimal lookup) (Space.ofList atoms) world live
      scope (Entry.Value.ofAtom (.expression (.symbol f :: args))) Atom.undefinedType frame results
      world' (policy := policy)) :
    ∃ (after : Frame) (children selected : List Result) (w₁ w₂ : Unit),
      Completed.Stateful.CallRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
        (callValue f args) Atom.undefinedType after children w₂ (policy := policy) ∧
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (children.map (Completed.readResult policy)) selected ∧
      results.map (fun r => r.1.erase) = selected.map (fun r => r.1.erase) := by
  have closed := (call_answerable head arguments).closed
  have readCall := HERuns.read_closed policy frame closed
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).status
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy head args
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
      (untyped_occurrences untyped)
  have data : ∀ a ∈ Atom.symbol f :: args, DataAtom a := by
    intro a member
    rcases List.mem_cons.mp member with rfl | inArgs
    · exact head
    · exact arguments a inArgs
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
        (.symbol f) Atom.undefinedType frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have rows : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result}
      {w₀ w₁ w₂ : Unit},
      Entry.Value.ofAtom (.symbol f) = operator → args.map Entry.Value.ofAtom = arguments →
      Completed.Stateful.TupleRel (worldEnv minimal lookup) (Space.ofList atoms) w₀
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows w₁ (policy := policy) →
      Completed.Stateful.CallsRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
        Atom.undefinedType rows raw w₂ (policy := policy) →
      ∃ (after : Frame) (v₁ v₂ : Unit), Completed.Stateful.CallRel (worldEnv minimal lookup)
        (Space.ofList atoms) v₁ live scope (callValue f args) Atom.undefinedType after raw v₂
          (policy := policy) := by
    intro operator arguments rows raw w₀ w₁ w₂ sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    obtain ⟨after, rfl⟩ := tuple_source_W contract (Atom.symbol f :: args) (List.cons_ne_nil _ _)
      data _ _ _ _ _ tuples
    cases calls with
    | cons called rest =>
        cases rest
        rw [List.append_nil]
        exact ⟨after, _, _, called⟩
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped _ tuples calls chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      obtain ⟨after, v₁, v₂, called⟩ := rows sameOperator sameArguments tuples calls
      exact ⟨after, _, _, v₁, v₂, called, chosen, by simp [Completed.publishResult]⟩
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
      obtain ⟨after, v₁, v₂, called⟩ := rows sameOperator sameArguments tuples calls
      have chosenRaw := selected
      simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
      exact ⟨after, _, _, v₁, v₂, called, chosenRaw, by simp [Completed.publishResult]⟩
  | selectionFailed _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      have exhausted := selectionExact chosen
      simp at exhausted

/-- **The batch of an ordinary call on the world machine**: the call itself when its region is
empty; otherwise its frontier and the bodies' derivations. -/
theorem callRel_source_W {lookup : CastLookup} {atoms : List Atom} (program : BoundProgram atoms)
    {f : String} {args : List Atom} (ordinary : Ordinary heDispatch atoms f args)
    {live : List Atom} {scope : List String} {after : Frame} {children : List Result}
    {w₁ w₂ : Unit}
    (called : Completed.Stateful.CallRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
      (callValue f args) Atom.undefinedType after children w₂ (policy := policy)) :
    (children = [(callValue f args, after)] ∧ regionSides atoms f args = []) ∨
      ∃ works : List EquationWork, works ≠ [] ∧
        EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
          (.expression (.symbol f :: args)) after.bindings works ∧
        Completed.Stateful.EquationBodiesRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live
          scope (callValue f args) Atom.undefinedType after works children w₂ (policy := policy) := by
  have ground : ∀ v ∈ args,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member))
  have notExecutable : ∀ {operator : Atom} {arguments : List Atom},
      (callValue f args).erase = .expression (operator :: arguments) →
      ¬ heDispatch.executable operator := by
    intro operator arguments shaped executable
    rw [callValue_erase] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    rw [← shaped.1] at executable
    exact ordinary.notHost executable
  cases called with
  | error failed => exact absurd failed (call_not_error ordinary.head args)
  | embedded _ _ instruction _ _ =>
      rw [callValue_erase, ordinary.notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [callValue_erase] at frontier
      have sidesEq := frontier_sides ground after.certified.satisfiable (bound_consFree program)
        frontier
      exact Or.inl ⟨rfl, sidesEq.symm⟩
  | equations _ _ frontier nonempty bodies =>
      rw [callValue_erase] at frontier
      exact Or.inr ⟨_, nonempty, frontier, bodies⟩
  | groundedDone shaped executable => exact absurd executable (notExecutable shaped)
  | groundedResume shaped executable => exact absurd executable (notExecutable shaped)

/-- **The equation bodies on the world machine, read as instances.** -/
theorem bodies_source_W {lookup : CastLookup} {atoms : List Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {frame : Frame}
    (determined : List Atom → Atom → List Atom → Prop)
    (sound : ∀ {L : List Atom} {i : Atom}, determined live i L → ∀ {w₀ w₁ : Unit} {output : Frame}
      {results : List Result},
      Completed.Stateful.AtomRel (worldEnv minimal lookup) (Space.ofList atoms) w₀ live scope
        (Entry.Value.ofAtom i) Atom.undefinedType output results w₁ (policy := policy) →
      results.map (fun r => r.1.erase) = L) :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
        determined live i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result} {w₀ w₁ : Unit},
        Completed.Stateful.EquationBodiesRel (worldEnv minimal lookup) (Space.ofList atoms) w₀ live
          scope original Atom.undefinedType frame works results w₁ (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, _, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, _, _, derived => by
      obtain ⟨L, Ls', ⟨i, readsAs, determinedI, facts⟩, rest, rfl⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons sameBindings _ boundary batch later =>
          rw [readsAs _ sameBindings] at boundary
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
                          rw [List.append_nil, List.map_append, sound determinedI evaluated,
                            bodies_source_W determined sound ws Ls' rest later, List.flatten_cons]

/-- **The grounded call on the world machine**: the host service and the integer dispatch fix the
outcome; only `callGroundedResume` applies, and its native boundary returns the value, evaluated
again and cast. -/
theorem grounded_source_W {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom} {op : String} (known : IntOp op) (a b : Int) {live : List Atom}
    {scope : List String} {after : Frame} {children : List Result} {w₁ w₂ : Unit}
    (called : Completed.Stateful.CallRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
      (callValue op [num a, num b]) Atom.undefinedType after children w₂ (policy := policy)) :
    children.map (fun r => r.1.erase) = [intValue op a b] := by
  have host : Minimal.HostCall heDispatch (callValue op [num a, num b]).erase :=
    ⟨.symbol op, [num a, num b], callValue_erase op [num a, num b], he_executable known⟩
  have rData := intValue_dataAtom known a b
  have outcomeOf : ∀ {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (services minimal).groundedAt (Space.ofList atoms) w₃ live scope after
        (callValue op [num a, num b]) outcome w₄ →
      outcome = .ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)] := by
    intro outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [callValue_erase] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    rw [(he_outcome_exact known a b raw).mp executed]
    rfl
  cases called with
  | error failed =>
      exact absurd failed (HERuns.value_not_error (intOp_head known) (callValue_erase op _))
  | embedded _ notHost _ _ _ => exact absurd host notHost
  | absent _ nonGrounded _ => exact absurd host nonGrounded.1
  | equations _ nonGrounded _ _ _ => exact absurd host nonGrounded.1
  | groundedDone _ _ _ produced planned =>
      rw [outcomeOf produced] at planned
      cases planned
  | groundedResume _ _ _ produced planned batch =>
      rw [outcomeOf produced] at planned
      cases planned with
      | success rows =>
          cases rows with
          | rejected impossible _ =>
              exact absurd ⟨_, ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _,
                after.certified.satisfiable⟩⟩ impossible
          | cons renewed rest =>
              cases rest
              have native : ∀ (operator : Atom) (arguments : List Atom) (frame' : Frame)
                  (value : Entry.Value),
                  Completed.nativeValue policy (worldEnv minimal lookup).dispatch operator arguments
                    frame' value = value := fun _ _ _ _ => rfl
              have provenance : ∀ (operator : Atom) (arguments : List Atom),
                  (worldEnv minimal lookup).dispatch.valueProvenance operator arguments = .emitted :=
                fun _ _ => rfl
              simp only [native, provenance] at batch
              have single := (Completed.Stateful.BoundaryBatchRel.single_iff).mp batch
              cases single with
              | nativeEmittedReturn producer returnedBatch =>
                  cases producer with
                  | producerFunction pending _ =>
                      obtain ⟨⟨body, same⟩, _⟩ := pending
                      rw [Entry.Value.erase_ofAtom] at same
                      rw [same] at rData
                      cases rData
                  | producerRaw _ =>
                      have answered := (Completed.Stateful.BoundaryBatchRel.single_iff).mp
                        returnedBatch
                      cases answered with
                      | returned returned =>
                          cases returned with
                          | notReducible same =>
                              exact absurd (by simpa only [Entry.Value.erase_ofAtom] using same)
                                (intValue_notRefused known a b)
                          | stopped stopped =>
                              exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped)
                                rData.not_stopped
                          | evaluate _ _ evaluated =>
                              obtain ⟨after', rfl⟩ := data_source_W contract rData evaluated
                              simp

/-- **On the extended fragment, HE's world source semantics determines the published atoms**, for
every lookup meeting the contract. -/
def DeterminedW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (world world' : Unit) (live : List Atom) (scope : List String) (frame : Frame)
    (results : List Result),
    Completed.Stateful.AtomRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope
      (Entry.Value.ofAtom t) Atom.undefinedType frame results world' (policy := policy) →
    results.map (fun r => r.1.erase) = L

/-- A batch selected from the call itself publishes the call (the world version of
`EveryRun.single_call_published`). -/
theorem settlesG_determined_W {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom} (program : BoundProgram atoms) {t : Atom} (settles : SettlesG atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ DeterminedW minimal lookup policy atoms t L := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨[d], fun a member => ?_, fun world world' live scope frame results derived => ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · obtain ⟨after, rfl⟩ := data_source_W contract data derived
        simp
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        fun world world' live scope frame results derived => ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact call_answerable ordinary.head ordinary.arguments
      · obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
          call_source_W contract ordinary.head ordinary.arguments ordinary.untyped derived
        have empty : regionBodies atoms f args = [] := regionBodies_nil_of_no_equation args noEquation
        rcases callRel_source_W program ordinary called with
          ⟨rfl, _⟩ | ⟨works, nonemptyWorks, frontier, _⟩
        · exact single_call_published (call_answerable ordinary.head ordinary.arguments) chosen erased
        · have sidesEq := frontier_sides
            (fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member)))
            after.certified.satisfiable (bound_consFree program) frontier
          have noSides : regionSides atoms f args = [] := by
            unfold regionSides
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro lr member
            obtain ⟨row, inRegion, found⟩ := List.mem_filterMap.mp member
            obtain ⟨inAtoms, region⟩ := List.mem_filter.mp inRegion
            have inBodies : regionBodies atoms f args ≠ [] := by
              unfold regionBodies
              intro none
              have := List.filterMap_eq_nil_iff.mp none row (List.mem_filter.mpr ⟨inAtoms, region⟩)
              cases equation : LiveEquations.equationOfRow row with
              | none =>
                  rw [pettaCallRegion_not_equation equation] at region
                  cases region
              | some e => simp [equation] at this
            exact inBodies empty
          rw [noSides] at sidesEq
          exact absurd (List.map_eq_nil_iff.mp sidesEq) nonemptyWorks
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L : List Atom,
          SettlesG atoms b ∧ (∀ a ∈ L, Answerable a) ∧ DeterminedW minimal lookup policy atoms b L := by
        intro b member
        obtain ⟨L, clean, determined⟩ := ih b member
        exact ⟨L, settled b member, clean, determined⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have cleanAll : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
        exact both.2.1 a inner
      refine ⟨Ls.flatten, cleanAll, fun world world' live scope frame results derived => ?_⟩
      obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
        call_source_W contract ordinary.head ordinary.arguments ordinary.untyped derived
      rcases callRel_source_W program ordinary called with
        ⟨_, empty⟩ | ⟨works, _, frontier, equations⟩
      · apply absurd _ nonempty
        rw [regionInstances_sides, empty]
        rfl
      · have instances := works_instances (policy := policy) ordinary.arguments program.scoped
          after.certified.satisfiable frontier
        have onWorks : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame,
              output.bindings = w.bindings →
                output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
            DeterminedW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls :=
          (forall₂_comp instances related).imp fun _ _ both => by
            obtain ⟨i, ⟨_, reads⟩, settlesI, _, determined⟩ := both
            exact ⟨i, reads, determined, settlesG_facts settlesI⟩
        have erasedChildren := bodies_source_W (minimal := minimal) (policy := policy)
          (lookup := lookup) (atoms := atoms) (live := live) (scope := scope)
          (fun _ i L => DeterminedW minimal lookup policy atoms i L)
          (fun determined _ _ _ _ evaluated => determined _ _ _ _ _ _ evaluated)
          works Ls (onWorks.imp fun _ _ both => both) equations
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
  | @grounded op a b known untyped =>
      refine ⟨[intValue op a b], fun x member => ?_, fun world world' live scope frame results
        derived => ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data (intValue_dataAtom known a b)
      · obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
          call_source_W contract (intOp_head known)
            (fun x member => intOp_items known a b x (List.mem_cons_of_mem _ member)) untyped derived
        have erasedChildren := grounded_source_W contract known a b called
        have clean : ∀ r ∈ children, Answerable r.1.erase := by
          intro r member
          have inside : r.1.erase ∈ [intValue op a b] := by
            rw [← erasedChildren]
            exact List.mem_map.mpr ⟨r, member, rfl⟩
          rw [List.mem_singleton] at inside
          rw [inside]
          exact answerable_of_data (intValue_dataAtom known a b)
        have unchanged : children.map (Completed.readResult policy) = children :=
          map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
        rw [unchanged] at chosen
        have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
          chosen (HERuns.success_all children fun r member => (clean r member).notError)
        rw [erased, same, erasedChildren]

/-- **Every complete run of HE's world machine publishes PeTTa's answers**, with grounded integer
operations, bodies that use their variables, under any lookup meeting the contract. -/
theorem every_complete_run_G (minimal : Minimal.Services) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (contract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} (program : BoundProgram atoms) {c : Atom} (settles : SettlesG atoms c) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) →
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  obtain ⟨L, _, determined⟩ := settlesG_determined_W (minimal := minimal) (policy := policy) contract
    program settles
  obtain ⟨heAnswers, N, path, _, agree⟩ := answersG_agree minimal (policy := policy) answers program
    settles
  refine ⟨N, fun n bigger emitted run => ?_⟩
  rw [agree n bigger, determined _ _ _ _ _ _ (complete_source_W path),
    determined _ _ _ _ _ _ (complete_source_W run)]

/-- **The answer bags agree for every complete run, with grounded operations** (HE's raw lookup): a
complete run exists, and every complete run publishes the bag PeTTa yields. -/
theorem answer_bags_every_run_G (minimal : Minimal.Services) (policy : Policy) {atoms : List Atom}
    (program : BoundProgram atoms) {c : Atom} (settles : SettlesG atoms c) :
    (∃ heAnswers : List Result,
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
        worldObserve (WorldConfiguration.ofReadOnly
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) = some heAnswers) ∧
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
            (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
            (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) →
          ((emitted.map fun r => r.1.erase : List Atom) : Multiset Atom) =
            (Streaming.values (Streaming.advance (translate atoms) n
              (Streaming.enter { state := store atoms } c)) : Multiset Atom) := by
  obtain ⟨heAnswers, _, path, observed, _⟩ :=
    answersG_agree minimal (policy := policy) raw_answers program settles
  obtain ⟨N, every⟩ := every_complete_run_G minimal raw_answers raw_contract policy program settles
  exact ⟨⟨heAnswers, path, observed⟩, N, fun n bigger emitted run => by
    rw [every n bigger emitted run]⟩

namespace Controls

open AnswerBags.Controls (app)
open GroundedRuns.Controls (doubleRows double_program double_settles)

/-- **H1's program end to end, on every complete run**: `(double 4)` on
`{(= (double $x) (+ $x $x))}`. A complete run of HE's world machine exists, every complete run
publishes `8`, and PeTTa's streaming run gives `8`. -/
theorem double_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList doubleRows) (app "double" [num 4]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList doubleRows, .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList doubleRows) (app "double" [num 4]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList doubleRows, .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [num 8]) ∧
      Streaming.values (Streaming.advance (translate doubleRows) 60
        (Streaming.enter { state := store doubleRows } (app "double" [num 4]))) = [num 8] := by
  have computed : Streaming.values (Streaming.advance (translate doubleRows) 60
      (Streaming.enter { state := store doubleRows } (app "double" [num 4]))) = [num 8] := by
    decide +kernel
  have finished : (Streaming.advance (translate doubleRows) 60
      (Streaming.enter { state := store doubleRows } (app "double" [num 4]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨heAnswers, path, _⟩, _⟩ := answer_bags_every_run_G minimal policy double_program
    double_settles
  obtain ⟨N, every⟩ := every_complete_run_G minimal raw_answers raw_contract policy double_program
    double_settles
  refine ⟨⟨⟨heAnswers, path⟩, fun emitted run => ?_⟩, computed⟩
  have later := every (max N 60) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

end Controls

#print axioms complete_source_W
#print axioms data_source_W
#print axioms tuple_source_W
#print axioms call_source_W
#print axioms callRel_source_W
#print axioms bodies_source_W
#print axioms grounded_source_W
#print axioms settlesG_determined_W
#print axioms every_complete_run_G
#print axioms answer_bags_every_run_G
#print axioms Controls.double_every_run

end GroundedEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
