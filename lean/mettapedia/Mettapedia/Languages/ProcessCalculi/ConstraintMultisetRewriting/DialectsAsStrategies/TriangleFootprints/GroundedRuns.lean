import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedTables
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution

/-!
# Grounded operations on both machines: `(double 4)` is `8`

HE's machine of `AnswerBags` (`RecursiveMachine.Contextual.Step`) has no rule for a host call: a call
whose operator the dispatch executes reaches `.work (.call …)` and no rule fires there
(`Controls.contextual_stuck`: `callAbsent` and `callEquations` need a non-grounded call,
`callEmbedded` excludes host calls). HE's grounded calls are rules of its **world machine**
(`WorldStep`: `callGroundedDone`, `callGroundedResume`), with the host service
`WorldServices.readOnlyGrounded`, which produces the dispatch's outcome as fresh syntax. Its source
semantics is `Completed.Stateful`.

Here the world machine runs HE with `GroundedTables.heDispatch`. Every step of the contextual
machine is a step of the world machine (`lift_step`; the dispatch has no minimal service), so the
runs of `AnswerBags` and `BoundVariables` carry over; the grounded call adds `callGroundedResume`
and the native boundary (`he_grounded_W`). PeTTa runs the call through its `primitive` rule
(`petta_open_grounded`).

## Results

* `SettlesG`: `SettlesV` with a fourth case, an integer operation `+ - * < <= > >=` on two integer
  literals, its operator undeclared in the program. It is still a condition on the program.
* `settlesG_agree`, `answersG_agree`: HE's world machine and PeTTa's streaming machine give the
  same answer list on every settling term, from both entries.
* `Controls.double_eight`: `(double 4)` on `{(= (double $x) (+ $x $x))}`: HE's world machine has a
  complete run publishing `8`, and PeTTa's run gives `8`.
* `Controls.contextual_stuck`: on the contextual machine of `AnswerBags`, the host call `(+ 4 4)`
  has no step.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedRuns

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith LocalStep Step load
  observe WorldStep WorldSteps WorldLocalStep WorldLocalStepWith worldObserve)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation
  WorldConfiguration managedContextControl)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags BoundVariables GroundedTables

/-! ## The world machine with HE's integer dispatch -/

/-- The host services: read-only, producing the dispatch's outcome as fresh syntax. -/
abbrev services (minimal : Minimal.Services) : WorldServices Space Unit :=
  WorldServices.readOnlyGrounded minimal heDispatch

theorem heDispatch_minimal : heDispatch.minimal = none := rfl

/-- **Every contextual step is a world step** when the dispatch has no minimal service, for any
host services. -/
theorem lift_local {space : Space} {dispatch : GroundedDispatch}
    (noMinimal : dispatch.minimal = none) (worldServices : WorldServices Space Unit)
    {lookup : CastLookup} {policy : Policy} {before after : Control × List Continuation}
    (step : LocalStep space dispatch lookup policy before after) :
    WorldLocalStep (fun _ context => context) worldServices dispatch lookup policy () space
      before () after := by
  have original := step
  induction step
  case contextStep => exact .context (by solve_by_elim)
  case contextReturn => exact .contextReturn
  case minimalEvalc =>
    rename_i actual
    rw [noMinimal] at actual
    cases actual
  case minimalMetta =>
    rename_i actual
    rw [noMinimal] at actual
    cases actual
  case minimalContextSpace =>
    rename_i actual
    rw [noMinimal] at actual
    cases actual
  all_goals
    apply WorldLocalStepWith.core
    · constructor
    · first
      | rfl
      | unfold managedContextControl
        split <;> simp_all [Minimal.embeddedInstruction, Entry.Value.erase]
    · exact original
    · constructor

theorem lift_step (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}
    {before after : HEConfig} (step : HEStep heDispatch lookup policy before after) :
    WorldStep (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly before) (WorldConfiguration.ofReadOnly after) := by
  cases step with
  | internal localStep => exact .internal (lift_local heDispatch_minimal (services minimal) localStep)
  | publish => exact .publish

/-- **Every contextual run is a world run.** -/
theorem lift_path (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}
    {before after : HEConfig}
    (path : Relation.ReflTransGen (HEStep heDispatch lookup policy) before after) :
    WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly before) (WorldConfiguration.ofReadOnly after) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (lift_step minimal step)

/-- **HE's world machine evaluates `t` to the answers `L`**: from pending work on `t` under
`%Undefined%`, with any live list, scope, activation, continuation stack and publication prefix. -/
def HEEvaluatesW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    ∃ results : List Result, results.map (fun result => result.1.erase) = L ∧
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms,
          .work (.atom live scope (Entry.Value.ofAtom t) Atom.undefinedType activation), stack,
            emitted⟩)
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning results, stack, emitted⟩)

theorem lift_evaluates (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}
    {atoms : List Atom} {t : Atom} {L : List Atom}
    (evaluates : HEEvaluates heDispatch lookup policy atoms t L) :
    HEEvaluatesW minimal lookup policy atoms t L := by
  intro live scope activation stack emitted
  obtain ⟨R, eraseR, path⟩ := evaluates live scope activation stack emitted
  exact ⟨R, eraseR, lift_path minimal path⟩

/-! ## The terms that settle, with grounded operations -/

/-- **The fragment with integer operations.** `SettlesV`'s three cases, and an integer operation on
two integer literals whose operator the program does not declare. -/
inductive SettlesG (atoms : List Atom) : Atom → Prop
  | data {a : Atom} : DataAtom a → a ≠ Atom.notReducible → SettlesG atoms a
  | constructor {f : String} {args : List Atom} : Ordinary heDispatch atoms f args →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      SettlesG atoms (.expression (.symbol f :: args))
  | call {f : String} {args : List Atom} : Ordinary heDispatch atoms f args →
      regionInstances atoms f args ≠ [] →
      (∀ b ∈ regionInstances atoms f args, SettlesG atoms b) →
      SettlesG atoms (.expression (.symbol f :: args))
  | grounded {op : String} (a b : Int) : IntOp op →
      (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = [] →
      SettlesG atoms (.expression [.symbol op, num a, num b])

theorem intOp_head {op : String} (known : IntOp op) : DataAtom (.symbol op) := by
  cases known <;> exact .symbol (by decide) (by decide)

theorem intOp_items {op : String} (known : IntOp op) (a b : Int) :
    ∀ x ∈ Atom.symbol op :: [num a, num b], DataAtom x := by
  intro x member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact intOp_head known
  · exact .grounded _
  · exact .grounded _

theorem intValue_dataAtom {op : String} (known : IntOp op) (a b : Int) :
    DataAtom (intValue op a b) := by
  obtain ⟨value, same⟩ := intValue_data known a b
  rw [same]
  exact .grounded value

theorem intValue_notRefused {op : String} (known : IntOp op) (a b : Int) :
    intValue op a b ≠ Atom.notReducible := by
  obtain ⟨value, same⟩ := intValue_data known a b
  rw [same]
  intro impossible
  cases impossible

theorem grounded_facts {op : String} (known : IntOp op) (a b : Int) :
    BodyFacts (.expression [.symbol op, num a, num b]) := by
  have answerable : Answerable (.expression (.symbol op :: [num a, num b])) :=
    call_answerable (intOp_head known) fun x member =>
      intOp_items known a b x (List.mem_cons_of_mem _ member)
  refine ⟨answerable.closed, fun policy pending => ?_, (fun same => by cases same), ?_,
    fun rename => ?_, answerable.ground⟩
  · obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    cases known <;> simp at same
  · rintro (same | ⟨tail, same⟩)
    · simp [Atom.empty] at same
    · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      cases known <;> simp at same
  · simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]

theorem settlesG_facts {atoms : List Atom} {t : Atom} (settles : SettlesG atoms t) : BodyFacts t := by
  cases settles with
  | data data notRefused => exact settles_facts (Settles.data (dispatch := heDispatch) (atoms := atoms)
      data notRefused)
  | constructor ordinary _ => exact call_facts ordinary
  | call ordinary _ _ => exact call_facts ordinary
  | grounded a b known _ => exact grounded_facts known a b

/-- A ground term of the extended fragment presents itself. -/
theorem presentsG_self {atoms : List Atom} {t : Atom} (settles : SettlesG atoms t) (σ : Subst) :
    Presents σ t t := by
  have items : ∀ (args : List Atom), (∀ a ∈ args, DataAtom a) →
      List.Forall₂ (PresentsItem σ) args args := by
    intro args data
    induction args with
    | nil => exact .nil
    | cons a rest ih =>
        exact .cons ⟨lit_of_data (data a List.mem_cons_self), Or.inl rfl⟩
          (ih fun b member => data b (List.mem_cons_of_mem _ member))
  cases settles with
  | data data _ => exact .item ⟨lit_of_data data, Or.inl rfl⟩
  | constructor ordinary _ => exact .call _ ordinary.notControl (items _ ordinary.arguments)
  | call ordinary _ _ => exact .call _ ordinary.notControl (items _ ordinary.arguments)
  | @grounded op a b known _ =>
      exact .call op (sourceControlForm_of_head (by cases known <;> decide) _)
        (items _ fun x member => intOp_items known a b x (List.mem_cons_of_mem _ member))

/-! ## HE's world machine on the extended fragment -/

section HEWorld

variable (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}

/-- **The equation loop on the world machine**, bodies read as instances. -/
theorem equations_steps_W {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
        HEEvaluatesW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
            (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms,
              .work (.equations live scope original Atom.undefinedType activation works), stack,
                emitted⟩)
            (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning results, stack, emitted⟩)
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (lift_step minimal (.internal .equationsNil))⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨i, readsAs, evaluates, facts⟩ := here
          obtain ⟨R, eraseR, pathR⟩ := evaluates live scope output
            (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_W works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (lift_step minimal (.internal (.equationsCons sameBindings unified))) ?_
            rw [readsAs output sameBindings]
            refine .head (lift_step minimal (.internal (.boundaryProducerRaw
              (facts.notFunction policy)))) ?_
            refine .head (lift_step minimal (.internal .boundaryBatch)) ?_
            refine .head (lift_step minimal (.internal .boundaryBatchCons)) ?_
            refine .head (lift_step minimal (.internal .boundaryReturned)) ?_
            refine .head (lift_step minimal (.internal (.returnEvaluate ?_ ?_))) ?_
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notRefused
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (lift_step minimal (.internal .append)) ?_
            refine .head (lift_step minimal (.internal .boundaryBatchNil)) ?_
            refine .head (lift_step minimal (.internal .prepend)) ?_
            refine .head (lift_step minimal (.internal .append)) ?_
            refine .trans pathR' ?_
            exact .single (lift_step minimal (.internal .prepend))

/-- **A call whose region has instances, on the world machine.** -/
theorem he_call_W (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : BoundProgram atoms) {f : String} {args : List Atom}
    (ordinary : Ordinary heDispatch atoms f args) (nonempty : regionInstances atoms f args ≠ [])
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluatesW minimal lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionInstances atoms f args) Ls) :
    HEEvaluatesW minimal lookup policy atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro live scope activation stack emitted
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances (policy := policy) ordinary.arguments program.scoped
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      (callValue f args).erase activation.bindings works := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment (callValue f args)
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
      HEEvaluatesW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts, _⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_W minimal works Ls unifiers related
    (.append (.calls live scope Atom.undefinedType []) ::
      .publish (.expression (.symbol f :: args)) :: stack) emitted
  have clean := HERuns.results_answerable (bodies.imp fun _ _ both => ⟨both.1, both.2.2⟩) eraseR
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := heDispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression (.symbol f :: args)) R clean stack emitted
  refine ⟨published, by rw [erased, eraseR], ?_⟩
  refine .trans (lift_path minimal (HERuns.call_entry_steps answers (HERuns.ordinary_data ordinary)
    ordinary.untyped live scope activation stack emitted)) ?_
  refine .head (lift_step minimal (.internal (.callEquations
    (HERuns.value_not_error ordinary.head (callValue_erase f args))
    (HERuns.value_nonGrounded ordinary.notHost ordinary.notInstruction (callValue_erase f args))
    frontier' worksNonempty))) ?_
  exact pathR.trans (lift_path minimal finish)

/-- The native boundary of one emitted row: the row is returned to the call, evaluated again
under `%Undefined%` (a data atom is cast), and the batches close. -/
theorem native_steps (answers : AnswersUndefined lookup) {atoms : List Atom} {d : Atom}
    (data : DataAtom d) (notRefused : d ≠ Atom.notReducible) (live : List Atom)
    (scope : List String) (original : Entry.Value) (activation : Frame)
    (stack : List Continuation) (emitted : List Result) :
    Relation.ReflTransGen (HEStep heDispatch lookup policy)
      ⟨Space.ofList atoms, .work (.boundaryBatch live scope none
        (.native original (some Atom.undefinedType) .emitted) [(Entry.Value.ofAtom d, activation)]),
        stack, emitted⟩
      ⟨Space.ofList atoms, .returning (([(Entry.Value.ofAtom d, activation)] ++ []) ++ []), stack,
        emitted⟩ := by
  have notFunction : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom d) := by
    rintro ⟨⟨body, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    subst same
    cases data
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryNativeEmittedReturn) ?_
  refine .head (.internal (.boundaryProducerRaw notFunction)) ?_
  refine .head (.internal .boundaryBatch) ?_
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryReturned) ?_
  refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
  · rw [Entry.Value.erase_ofAtom]
    exact notRefused
  · rw [Entry.Value.erase_ofAtom]
    exact data.not_stopped
  refine .head (CompleteRun.cast_step_frame answers _ data activation live scope _ emitted) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  exact .single (.internal .prepend)

/-- **An integer operation on HE's world machine**: the tuple entry, the grounded call through the
host service, the native boundary, the cast of the value, and the publication. -/
theorem he_grounded_W (answers : AnswersUndefined lookup) {atoms : List Atom} {op : String}
    (known : IntOp op) (a b : Int)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    HEEvaluatesW minimal lookup policy atoms (.expression [.symbol op, num a, num b])
      [intValue op a b] := by
  intro live scope activation stack emitted
  have rData := intValue_dataAtom known a b
  have clean : ∀ r ∈ [(Entry.Value.ofAtom (intValue op a b), activation)],
      Answerable r.1.erase := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [Entry.Value.erase_ofAtom]
    exact answerable_of_data rData
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := heDispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression [.symbol op, num a, num b]) [(Entry.Value.ofAtom (intValue op a b), activation)]
    clean stack emitted
  refine ⟨published, by rw [erased]; simp, ?_⟩
  have produced : (services minimal).groundedAt (Space.ofList atoms) () live scope activation
      (callValue op [num a, num b]) (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)])
      () :=
    ⟨.symbol op, [num a, num b], .ok [(intValue op a b, Bindings.empty)],
      callValue_erase op [num a, num b], (he_outcome_exact known a b _).mpr rfl, rfl⟩
  have rows : Completed.NativeOutcomeRel policy heDispatch (.symbol op) [num a, num b]
      (callValue op [num a, num b]) (some Atom.undefinedType) activation
      (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)])
      (.resume [(Entry.Value.ofAtom (intValue op a b), activation)]) :=
    .success (.cons (Frame.NativeRenewRel.empty policy activation) .nil)
  have notError : ¬ IsErrorRel (callValue op [num a, num b]).erase :=
    HERuns.value_not_error (intOp_head known) (callValue_erase op [num a, num b])
  refine .trans (lift_path minimal (HERuns.call_entry_steps answers (intOp_items known a b) untyped
    live scope activation stack emitted)) ?_
  refine .head (.internal (WorldLocalStepWith.callGroundedResume
    (callValue_erase op [num a, num b]) (he_executable known) notError produced rows)) ?_
  have native := lift_path minimal (native_steps (policy := policy) answers (atoms := atoms) rData
    (intValue_notRefused known a b) live scope (callValue op [num a, num b]) activation
    (.append (.calls live scope Atom.undefinedType []) ::
      .publish (.expression [.symbol op, num a, num b]) :: stack) emitted)
  simp only [List.append_nil] at native
  exact native.trans (lift_path minimal finish)

end HEWorld

/-! ## PeTTa's primitive run -/

theorem rawDemand_false {atoms : List Atom} {op : String} (known : IntOp op) (index : Nat) :
    PeTTaRuns.rawDemand (translate atoms) (.function op) index = false := by
  show Mettapedia.Languages.MeTTa.PeTTa.Eval.argumentIsRaw (translate atoms) op index = false
  unfold Mettapedia.Languages.MeTTa.PeTTa.Eval.argumentIsRaw
  rw [if_pos (petta_known known)]
  cases known <;> simp [StdLib.rawArgument]

/-- **PeTTa's primitive step on two integers.** -/
theorem primitive_step {registry : SpaceSemantics.Program} {op : String} (known : IntOp op)
    (a b : Int) (world : Streaming.World) (σ : Subst) (index : Nat)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.arguments σ (.function op) [] [num a, num b] index, frames⟩ :: older,
        answers, next⟩
      ⟨world, .execute ⟨.returned [⟨intValue op a b, σ⟩], frames⟩ :: older, answers, next⟩ := by
  have resolved : [num a, num b].map (Unifying.resolve σ) = [num a, num b] :=
    PeTTaRuns.map_resolve_ground σ fun v member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
  cases known <;>
    exact .phase rfl rfl (.primitive rfl rfl (by decide) (by decide) rfl
      (by rw [resolved]; rfl)) (.plain rfl)

/-- **An integer operation, every presentation**: PeTTa evaluates the presented arguments and runs
its primitive. -/
theorem petta_open_grounded (atoms : List Atom) {op : String} (known : IntOp op) (a b : Int) :
    PeTTaOpen atoms (.expression [.symbol op, num a, num b]) [intValue op a b] := by
  intro frames K deliver world σ state privateCode range fresh t presented older answers next
  obtain ⟨us, rfl, notControl, items⟩ := presents_call presented
  have notCollapse : op ≠ "collapse" := by cases known <;> decide
  have notOnce : op ≠ "once" := by cases known <;> decide
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead op || StdLib.known op ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == op)) =
      true := by
    rw [petta_known known]
    simp
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver (intValue op a b) List.mem_cons_self world σ
    state privateCode range fresh older answers next
  refine ⟨uses, out, grown, by simp [valuesOut], ?_⟩
  refine .head (PeTTaRuns.call_enter world σ notCollapse notOnce notControl callable frames older
    answers next) ?_
  have traversed := PeTTaOpenRuns.arguments_open (registry := translate atoms) world σ (.function op)
    (fun index => rawDemand_false known index) frames older answers next us [num a, num b] [] 0 items
  rw [List.nil_append] at traversed
  exact traversed.trans (.head (primitive_step known a b world σ _ frames older answers next) path)

/-! ## Both machines -/

section Joint

variable (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to the same answer list**, with HE's world machine
and PeTTa on every open presentation. -/
theorem settlesG_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : BoundProgram atoms) {t : Atom} (settles : SettlesG atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ HEEvaluatesW minimal lookup policy atoms t L ∧
      PeTTaOpen atoms t L := by
  induction settles with
  | @data d data _ =>
      refine ⟨[d], fun a member => ?_, lift_evaluates minimal (HERuns.he_data answers atoms data),
        petta_open_data atoms data⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        lift_evaluates minimal (HERuns.he_absent answers (bound_consFree program) ordinary
          (regionBodies_nil_of_no_equation args noEquation)),
        petta_open_constructor ordinary noEquation⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L, SettlesG atoms b ∧
          (∀ a ∈ L, Answerable a) ∧ HEEvaluatesW minimal lookup policy atoms b L ∧
          PeTTaOpen atoms b L := by
        intro b member
        obtain ⟨L, rest⟩ := ih b member
        exact ⟨L, settled b member, rest⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
          e.arguments.length = args.length := by
        obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
        rw [regionInstances_eq] at inRegion
        obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
        obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
        simp only [Bool.and_eq_true, beq_iff_eq] at selected
        exact ⟨e, live, selected.1, selected.2⟩
      refine ⟨Ls.flatten, ?_, he_call_W minimal answers program ordinary nonempty
          (related.imp fun _ _ both => ⟨both.2.2.1, settlesG_facts both.1, both.2.1⟩),
        petta_open_call program ordinary defined (related.imp fun _ _ both => both.2.2.2)⟩
      intro a member
      obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
      obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
      exact both.2.1 a inner
  | @grounded op a b known untyped =>
      refine ⟨[intValue op a b], fun x member => ?_, he_grounded_W minimal answers known a b untyped,
        petta_open_grounded atoms known a b⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data (intValue_dataAtom known a b)

/-- **The answers agree with grounded operations**: HE's world machine runs from its entry
configuration to a completed phase, and from some fuel on PeTTa's streaming run yields exactly the
atoms HE published, in the same order and with the same multiplicities. -/
theorem answersG_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : BoundProgram atoms) {c : Atom} (settles : SettlesG atoms c) :
    ∃ (heAnswers : List Result) (N : Nat),
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
        worldObserve (WorldConfiguration.ofReadOnly
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) = some heAnswers ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = heAnswers.map (fun r => r.1.erase) := by
  obtain ⟨L, clean, he, petta⟩ := settlesG_agree minimal (policy := policy) answers program settles
  obtain ⟨R, eraseR, path⟩ := he [] [] Completed.Frame.empty [] []
  obtain ⟨N, stable⟩ := petta_complete (settlesG_facts settles).ground clean
    (fun frames K deliver world σ state privateCode range fresh older answers next =>
      petta frames K deliver world σ state privateCode range fresh c (presentsG_self settles σ)
        older answers next)
  exact ⟨R, N, path.trans (lift_path minimal (HERuns.publish_all _ R [])), rfl,
    fun n bigger => by rw [stable n bigger, eraseR]⟩

end Joint

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (bound_rule var_items sym_data)

/-- H1's program: `(= (double $x) (+ $x $x))`. -/
def doubleRows : List Atom := [rule (app "double" [.var "x"]) (app "+" [.var "x", .var "x"])]

theorem double_program : BoundProgram doubleRows := by
  intro row member
  simp only [doubleRows, List.mem_singleton] at member
  subst member
  exact bound_rule "double" ["x"] (by decide)
    (.call "+" [.var "x", .var "x"] (by decide) (var_items ["x", "x"]))

theorem double_not_host : ¬ heDispatch.executable (.symbol "double") := by
  rintro ⟨name, same, member⟩
  cases same
  simp [heIntegerNames] at member

/-- **`(double 4)` settles**: its one instance is `(+ 4 4)`. -/
theorem double_settles : SettlesG doubleRows (app "double" [num 4]) := by
  have instances : regionInstances doubleRows "double" [num 4] = [app "+" [num 4, num 4]] := by
    decide +kernel
  refine .call ⟨sym_data "double" (by decide) (by decide), fun v member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _, by decide +kernel, double_not_host, by decide +kernel, by decide,
    by decide, by decide +kernel, by decide, by decide⟩ (by rw [instances]; simp) ?_
  rw [instances]
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  exact .grounded 4 4 .plus (by decide +kernel)

/-- **H1's program end to end**: `(double 4)` on `{(= (double $x) (+ $x $x))}`. HE's world machine,
with the tree's integer dispatch and HE's raw lookup, has a complete run from its entry publishing
`8`, and PeTTa's streaming run of the translation gives `8`. -/
theorem double_eight (minimal : Minimal.Services) (policy : Policy) :
    (∃ heAnswers : List Result,
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList doubleRows) (app "double" [num 4]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList doubleRows, .returning [], [], heAnswers⟩) ∧
        heAnswers.map (fun r => r.1.erase) = [num 8]) ∧
      Streaming.values (Streaming.advance (translate doubleRows) 60
        (Streaming.enter { state := store doubleRows } (app "double" [num 4]))) = [num 8] := by
  have computed : Streaming.values (Streaming.advance (translate doubleRows) 60
      (Streaming.enter { state := store doubleRows } (app "double" [num 4]))) = [num 8] := by
    decide +kernel
  have finished : (Streaming.advance (translate doubleRows) 60
      (Streaming.enter { state := store doubleRows } (app "double" [num 4]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨R, N, path, _, agree⟩ := answersG_agree minimal (policy := policy) raw_answers
    double_program double_settles
  refine ⟨⟨R, path, ?_⟩, computed⟩
  have later := agree (max N 60) (le_max_left _ _)
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- **Negative control: the contextual machine has no rule for a host call.** With HE's integer
dispatch, the call `(+ 4 4)` reached by `AnswerBags`'s machine has no successor. -/
theorem contextual_stuck {lookup : CastLookup} {policy : Policy} (space : Space)
    (live : List Atom) (scope : List String) (expected : Atom) (activation : Frame)
    (stack : List Continuation) (emitted : List Result) :
    ¬ ∃ next, HEStep heDispatch lookup policy
      ⟨space, .work (.call live scope (callValue "+" [num 4, num 4]) expected activation), stack,
        emitted⟩ next := by
  have host : Minimal.HostCall heDispatch (callValue "+" [num 4, num 4]).erase :=
    ⟨.symbol "+", [num 4, num 4], callValue_erase "+" [num 4, num 4], he_executable .plus⟩
  rintro ⟨next, step⟩
  cases step with
  | internal localStep =>
      cases localStep with
      | callError failed =>
          exact HERuns.value_not_error (intOp_head .plus) (callValue_erase "+" [num 4, num 4]) failed
      | callEmbedded _ notHost _ => exact notHost host
      | callAbsent _ nonGrounded _ => exact nonGrounded.1 host
      | callEquations _ nonGrounded _ _ => exact nonGrounded.1 host

end Controls

#print axioms lift_step
#print axioms lift_path
#print axioms equations_steps_W
#print axioms he_call_W
#print axioms native_steps
#print axioms he_grounded_W
#print axioms primitive_step
#print axioms petta_open_grounded
#print axioms settlesG_agree
#print axioms answersG_agree
#print axioms Controls.double_eight
#print axioms Controls.contextual_stuck

end GroundedRuns

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
