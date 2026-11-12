import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags

/-!
# Where HE and PeTTa differ inside the fragment of flat ground calls

`AnswerBags.answers_agree` needs a settling call: every reached call is covered (its head has no
equation, or some row of its region matches) and no body is the symbol `NotReducible`. Both
conditions are needed: each failure is a program inside the fragment of flat ground calls on
symbol-headed, `cons`-free equations with undeclared atoms where the answers differ.

* **An uncovered call** (`AnswerBags.uncovered_calls_differ`, `AnswerBags.Controls.five_differs`):
  the head has an equation of the call's arity but none matches. HE answers the call itself, PeTTa
  answers nothing.
* **A body `NotReducible`** (`refused_calls_differ`, instance `refused_differs`): HE reads the
  symbol as a refusal to reduce and answers the call itself (`returnRefused`); PeTTa answers the
  symbol.
* **A call shorter than every equation of its head** (`arity_calls_differ`, instance
  `arity_differs`): HE's region is empty and HE answers the call itself; PeTTa answers its
  partial-application carrier.
* **A call longer than every equation of its head** (`over_calls_differ`): HE answers the call
  itself; PeTTa's run ends in an uncaught over-application fault with no value.

All four are HE's rule "a call with nothing to reduce answers itself" against PeTTa's reading of an
authored head as a Prolog predicate (failure, partial application, arity error), plus HE's reserved
symbol `NotReducible`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace FragmentDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags
open AnswerBags.Controls (sym app rule rule_consFree)
open WholeRunWords.Double (noHost)

variable {lookup : CastLookup} {policy : Policy}

/-! ## A body `NotReducible` -/

/-- `{(= (stuck) NotReducible)}`. -/
abbrev stuckRows : List Atom := [rule (app "stuck" []) Atom.notReducible]

theorem stuck_ordinary : Ordinary noHost stuckRows "stuck" [] :=
  ⟨.symbol (by decide) (by decide), by simp, by decide +kernel, fun impossible => impossible,
    by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩

theorem stuck_program : ∀ row ∈ stuckRows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  simp only [List.mem_singleton] at member
  subst member
  exact rule_consFree (by simp)

/-- **The refused work**: the one work's body is `NotReducible`, so HE returns the call value
itself (`returnRefused`) and the loop closes. -/
theorem refused_steps (dispatch : GroundedDispatch) {atoms : List Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {activation : Frame} (work : EquationWork)
    (output : Frame) (sameBindings : output.bindings = work.bindings)
    (unified : Entry.Value.UnifyRel policy.rebuilding activation.environment original
      (Entry.Value.ofAtom work.pattern) output.environment)
    (refused : work.body = Atom.notReducible) (stack : List Continuation) (emitted : List Result) :
    HERuns.HESteps dispatch lookup policy
      ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
        [work]), stack, emitted⟩
      ⟨Space.ofList atoms, .returning (([(original, output)] ++ []) ++ []), stack, emitted⟩ := by
  have closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs work.body name := by
    rw [refused]
    intro name occurs
    cases occurs
  have readBody := HERuns.read_closed policy output closed
  refine .head (.internal (.equationsCons sameBindings unified)) ?_
  rw [readBody, refused]
  refine .head (.internal (.boundaryProducerRaw ?_)) ?_
  · rintro ⟨⟨body, same⟩, _⟩
    simp [Atom.notReducible, Entry.Value.ofAtom, Entry.Value.erase] at same
  refine .head (.internal .boundaryBatch) ?_
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryReturned) ?_
  refine .head (.internal (.returnRefused (by rw [Entry.Value.erase_ofAtom]))) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .equationsNil) ?_
  exact .single (.internal .prepend)

/-- **HE answers `(stuck)`**: its one equation's body refuses the reduction. -/
theorem he_stuck (answers : AnswersUndefined lookup) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList stuckRows) (app "stuck" []) Atom.undefinedType)
          ⟨Space.ofList stuckRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [app "stuck" []] := by
  have bodies : regionBodies stuckRows "stuck" [] = [Atom.notReducible] := by decide +kernel
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList stuckRows) [Atom.undefinedType]
    (app "stuck" []) Completed.Frame.empty.bindings
  have fixed : ∀ b ∈ regionBodies stuckRows "stuck" [], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [bodies]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    simp [Atom.notReducible, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  have bodiesEq := HERuns.frontier_bodies (fun _ member => by cases member)
    Completed.Frame.empty.certified.satisfiable stuck_program fixed frontier
  rw [bodies] at bodiesEq
  obtain ⟨work, rfl⟩ : ∃ work, works = [work] := by
    cases works with
    | nil => simp at bodiesEq
    | cons work rest =>
        cases rest with
        | nil => exact ⟨work, rfl⟩
        | cons _ _ => simp at bodiesEq
  have refused : work.body = Atom.notReducible := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
    exact bodiesEq
  have frontier' : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.EquationFrontierRel
      (Space.ofList stuckRows) [Atom.undefinedType] (callValue "stuck" []).erase
      Completed.Frame.empty.bindings [work] := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired work List.mem_cons_self
  let output : Frame := ⟨work.bindings, after, certificate⟩
  have clean : ∀ r ∈ (([(callValue "stuck" [], output)] ++ []) ++ []), Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil, List.mem_singleton] at member
    subst member
    rw [callValue_erase]
    exact call_answerable (.symbol (by decide) (by decide)) (fun _ member => by cases member)
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := noHost) (lookup := lookup)
    (policy := policy) (atoms := stuckRows) (live := []) (scope := []) (app "stuck" [])
    _ clean [] []
  refine ⟨published, ?_, ?_⟩
  · refine .trans (HERuns.call_entry_steps (dispatch := noHost) (policy := policy) answers
      (HERuns.ordinary_data stuck_ordinary) stuck_ordinary.untyped [] [] Completed.Frame.empty [] [])
      ?_
    refine .head (.internal (.callEquations (call_not_error stuck_ordinary.head [])
      (HERuns.nonGrounded_call stuck_ordinary) frontier' (List.cons_ne_nil _ _))) ?_
    refine .trans (refused_steps noHost (atoms := stuckRows) work output rfl unified refused _ [])
      ?_
    exact finish.trans (HERuns.publish_all _ published [])
  · rw [erased]
    simp [callValue_erase]

/-- **A body `NotReducible` separates the dialects**: HE answers `(stuck)`, PeTTa `NotReducible`. -/
theorem refused_differs (answers : AnswersUndefined lookup) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList stuckRows) (app "stuck" []) Atom.undefinedType)
          ⟨Space.ofList stuckRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [app "stuck" []]) ∧
      Streaming.values (Streaming.advance (translate stuckRows) 30
        (Streaming.enter { state := store stuckRows } (app "stuck" []))) = [Atom.notReducible] ∧
      (Streaming.advance (translate stuckRows) 30
        (Streaming.enter { state := store stuckRows } (app "stuck" []))).agenda.length = 0 :=
  ⟨he_stuck answers, by decide +kernel, by decide +kernel⟩

/-- **A refused call, in general**: for an ordinary call whose region holds one row and its body is
`NotReducible`, on a program of symbol-headed, `cons`-free equations, HE answers the call itself and
PeTTa answers `NotReducible`. -/
theorem refused_calls_differ (dispatch : GroundedDispatch) (answers : AnswersUndefined lookup)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {f : String} {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (refusing : regionBodies atoms f args = [Atom.notReducible]) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) =
          [Atom.notReducible] := by
  have refusedData : DataAtom Atom.notReducible := .symbol (by decide) (by decide)
  constructor
  · obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) [Atom.undefinedType]
      (.expression (.symbol f :: args)) Completed.Frame.empty.bindings
    have fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
      rw [refusing]
      intro b member rename
      rw [List.mem_singleton] at member
      subst member
      simp [Atom.notReducible,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
    have bodiesEq := HERuns.frontier_bodies
      (fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member)))
      Completed.Frame.empty.certified.satisfiable program fixed frontier
    rw [refusing] at bodiesEq
    obtain ⟨work, rfl⟩ : ∃ work, works = [work] := by
      cases works with
      | nil => simp at bodiesEq
      | cons work rest =>
          cases rest with
          | nil => exact ⟨work, rfl⟩
          | cons _ _ => simp at bodiesEq
    have refused : work.body = Atom.notReducible := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
      exact bodiesEq
    have frontier' : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.EquationFrontierRel
        (Space.ofList atoms) [Atom.undefinedType] (callValue f args).erase
        Completed.Frame.empty.bindings [work] := by
      rw [callValue_erase]
      exact frontier
    obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
      (policy := policy.rebuilding) Completed.Frame.empty.certified frontier'
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired work List.mem_cons_self
    let output : Frame := ⟨work.bindings, after, certificate⟩
    have clean : ∀ r ∈ (([(callValue f args, output)] ++ []) ++ []), Answerable r.1.erase := by
      intro r member
      simp only [List.append_nil, List.mem_singleton] at member
      subst member
      rw [callValue_erase]
      exact call_answerable ordinary.head ordinary.arguments
    obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := dispatch)
      (lookup := lookup) (policy := policy) (atoms := atoms) (live := []) (scope := [])
      (.expression (.symbol f :: args)) _ clean [] []
    refine ⟨published, ?_, ?_⟩
    · refine .trans (HERuns.call_entry_steps (dispatch := dispatch) (policy := policy) answers
        (HERuns.ordinary_data ordinary) ordinary.untyped [] [] Completed.Frame.empty [] []) ?_
      refine .head (.internal (.callEquations (call_not_error ordinary.head args)
        (HERuns.nonGrounded_call ordinary) frontier' (List.cons_ne_nil _ _))) ?_
      refine .trans (refused_steps dispatch (atoms := atoms) work output rfl unified refused _ [])
        ?_
      exact finish.trans (HERuns.publish_all _ published [])
    · rw [erased]
      simp [callValue_erase]
  · obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ (by rw [refusing]; simp :
      regionBodies atoms f args ≠ [])
    obtain ⟨e, live, head, arity, _⟩ := mem_regionBodies inRegion
    have bodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
        (regionBodies atoms f args) [[Atom.notReducible]] := by
      rw [refusing]
      exact .cons ⟨PeTTaRuns.petta_data atoms refusedData, rfl⟩ .nil
    exact petta_complete (call_answerable ordinary.head ordinary.arguments).ground
      (fun a member => by
        simp at member
        subst member
        exact answerable_of_data refusedData)
      (PeTTaRuns.petta_call ordinary ⟨e, live, head, arity⟩ bodies)

/-! ## A call of an arity no equation has -/

/-- `{(= (g 1 2) yes)}`. -/
abbrev twoRows : List Atom := [rule (app "g" [.grounded (.int 1), .grounded (.int 2)]) (sym "yes")]

/-- **A call of an arity no equation has separates the dialects**: on `{(= (g 1 2) yes)}` the call
`(g 1)` has an empty region, HE answers `(g 1)`, and PeTTa answers the partial application of `g`
to `1`. -/
theorem arity_differs (answers : AnswersUndefined lookup) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList twoRows) (app "g" [.grounded (.int 1)]) Atom.undefinedType)
          ⟨Space.ofList twoRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [app "g" [.grounded (.int 1)]]) ∧
      Streaming.values (Streaming.advance (translate twoRows) 30
        (Streaming.enter { state := store twoRows } (app "g" [.grounded (.int 1)]))) =
        [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue "g" [.grounded (.int 1)]] ∧
      (Streaming.advance (translate twoRows) 30
        (Streaming.enter { state := store twoRows } (app "g" [.grounded (.int 1)]))).agenda.length =
        0 := by
  have program : ∀ row ∈ twoRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [List.mem_singleton] at member
    subst member
    exact rule_consFree fun a member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .grounded _
  have ordinary : Ordinary noHost twoRows "g" [.grounded (.int 1)] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .grounded _, by decide +kernel, fun impossible => impossible, by decide +kernel,
      by decide, by decide, by decide +kernel, by decide, by decide⟩
  have empty : regionBodies twoRows "g" [.grounded (.int 1)] = [] := by decide +kernel
  obtain ⟨R, eraseR, path, _⟩ := he_complete (dispatch := noHost) (lookup := lookup)
    (policy := policy) (HERuns.he_absent answers program ordinary empty)
  exact ⟨⟨R, path, eraseR⟩, by decide +kernel, by decide +kernel⟩

/-- No equation of the call's arity: the region is empty. -/
theorem regionBodies_nil_of_arity {atoms : List Atom} {f : String} {args : List Atom}
    (noArity : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length ≠ args.length) :
    regionBodies atoms f args = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b member
  obtain ⟨e, live, head, arity, _⟩ := mem_regionBodies member
  exact noArity e live head arity

/-- The partial-application carrier of PeTTa is an answer of the fragment. -/
theorem partial_answerable {f : String} {args : List Atom} (data : ∀ a ∈ args, DataAtom a) :
    Answerable (Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue f args) := by
  refine ⟨fun name occurs => ?_, rfl, ?_, ?_, fun same => by cases same⟩
  · cases occurs with
    | expression member deeper =>
        simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialTag, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · cases deeper
        · cases deeper
        · cases deeper with
          | expression member' deeper' =>
              exact (answerable_of_data (data _ member')).closed name deeper'
  · simp [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue,
      Mettapedia.Languages.MeTTa.PeTTa.Eval.partialTag, isGroundAtom, isGroundAtom.isGroundList,
      args_ground data]
  · rintro (same | ⟨tail, same⟩)
    · simp [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue, Atom.empty] at same
    · simp [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue,
        Mettapedia.Languages.MeTTa.PeTTa.Eval.partialTag] at same

/-- **PeTTa answers the partial application** of a defined head called with fewer arguments than
some equation takes, and with no equation of the call's arity. -/
theorem petta_partial {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (noArity : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length ≠ args.length)
    (longer : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      args.length < e.arguments.length) :
    PeTTaEvaluates atoms (.expression (.symbol f :: args))
      [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue f args] := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  obtain ⟨e, live, head, arity⟩ := longer
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
  have groundArgs : ∀ v ∈ args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (ordinary.arguments v member)).ground
  have unknown : args.length ∉ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations, List.mem_map, List.mem_filter, beq_iff_eq, not_exists, not_and, and_imp]
    intro e' live' same' arity'
    exact noArity e' live' same' arity'
  have notOver : ((Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f).all (· < args.length) &&
      !(Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
        (Unifying.codeRegistry (translate atoms) world.privateCode) f).isEmpty) = false := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations, Bool.and_eq_false_iff]
    left
    apply List.all_eq_false.mpr
    refine ⟨e.arguments.length, List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [head]⟩,
      rfl⟩, ?_⟩
    simp only [decide_eq_true_eq, not_lt]
    omega
  have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f
      (args.map (Unifying.resolve σ)) σ world.uses =
      some (.returned [⟨Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue f args, σ⟩], 0) := by
    rw [PeTTaRuns.map_resolve_ground σ groundArgs]
    unfold Unifying.application
    rw [if_neg unknown, notOver]
    rfl
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver _ List.mem_cons_self world σ state
    privateCode range fresh older answers next
  refine ⟨uses, out, grown, by simp [valuesOut], ?_⟩
  refine .head (PeTTaRuns.call_enter world σ ordinary.notCollapse ordinary.notOnce
    ordinary.notControl callable frames older answers next) ?_
  have entered := PeTTaRuns.arguments_data (registry := translate atoms) world σ (.function f)
    (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index) frames older
    answers next args [] 0 ordinary.arguments
  rw [List.nil_append] at entered
  refine .trans entered ?_
  refine .head (PeTTaRuns.apply_equations world σ args (0 + args.length) ordinary.notIO
    ordinary.notNative applied frames older answers next) ?_
  exact path

/-- **A call shorter than every equation of its head, in general**: HE's region is empty and HE
answers the call itself; PeTTa answers its partial-application carrier. -/
theorem arity_calls_differ (dispatch : GroundedDispatch) (answers : AnswersUndefined lookup)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {f : String} {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (noArity : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length ≠ args.length)
    (longer : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      args.length < e.arguments.length) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) =
          [Mettapedia.Languages.MeTTa.PeTTa.Eval.partialValue f args] := by
  constructor
  · obtain ⟨R, eraseR, path, _⟩ := he_complete (dispatch := dispatch) (lookup := lookup)
      (policy := policy) (HERuns.he_absent answers program ordinary (regionBodies_nil_of_arity noArity))
    exact ⟨R, path, eraseR⟩
  · exact petta_complete (call_answerable ordinary.head ordinary.arguments).ground
      (fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact partial_answerable ordinary.arguments)
      (petta_partial ordinary noArity longer)

/-- **A call longer than every equation of its head, in general**: HE's region is empty and HE
answers the call itself; PeTTa's run ends in its uncaught over-application fault, with no value. -/
theorem over_calls_differ (dispatch : GroundedDispatch) (answers : AnswersUndefined lookup)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {f : String} {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (shorter : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length < args.length)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [.expression (.symbol f :: args)]) ∧
      ∃ (N : Nat) (reason : Effects.Fault), ∀ n, N ≤ n →
        (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))).agenda =
            [.execute ⟨.fault reason, []⟩] ∧
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) = [] := by
  have noArity : ∀ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f →
      e.arguments.length ≠ args.length := fun e live head => Nat.ne_of_lt (shorter e live head)
  constructor
  · obtain ⟨R, eraseR, path, _⟩ := he_complete (dispatch := dispatch) (lookup := lookup)
      (policy := policy) (HERuns.he_absent answers program ordinary (regionBodies_nil_of_arity noArity))
    exact ⟨R, path, eraseR⟩
  · let world : Streaming.World := { state := store atoms, uses := 1 }
    have ground := (call_answerable ordinary.head ordinary.arguments).ground
    have entered : Streaming.enter { state := store atoms } (.expression (.symbol f :: args)) =
        ⟨world, [.execute ⟨.evaluate [] (.expression (.symbol f :: args)), []⟩], [], 0⟩ := by
      simp only [Streaming.enter, Unifying.rename_ground 0 _ ground]
      rfl
    obtain ⟨e, live, head⟩ := defined
    have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
        (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
        true := by
      show (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
        (Unifying.codeRegistry (translate atoms) []).equations.any (·.head == f)) = true
      rw [ordinary.notIO, ordinary.notNative]
      simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
      exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
    have groundArgs : ∀ v ∈ args, isGroundAtom v = true :=
      fun v member => (answerable_of_data (ordinary.arguments v member)).ground
    have unknown : args.length ∉ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
        (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
      show args.length ∉ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
        (Unifying.codeRegistry (translate atoms) []) f
      simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry,
        List.nil_append, translate_equations, List.mem_map, List.mem_filter, beq_iff_eq, not_exists,
        not_and, and_imp]
      intro e' live' same' arity'
      exact noArity e' live' same' arity'
    have overApplied : ((Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
        (Unifying.codeRegistry (translate atoms) world.privateCode) f).all (· < args.length) &&
        !(Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
          (Unifying.codeRegistry (translate atoms) world.privateCode) f).isEmpty) = true := by
      show ((Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
        (Unifying.codeRegistry (translate atoms) []) f).all (· < args.length) &&
        !(Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
          (Unifying.codeRegistry (translate atoms) []) f).isEmpty) = true
      simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry,
        List.nil_append, translate_equations, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff]
      refine ⟨List.all_eq_true.mpr fun n member => ?_, ?_⟩
      · obtain ⟨e', inFilter, rfl⟩ := List.mem_map.mp member
        obtain ⟨live', same'⟩ := List.mem_filter.mp inFilter
        simpa using shorter e' live' (by simpa using same')
      · exact List.ne_nil_of_mem (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [head]⟩,
          rfl⟩)
    set reason : Effects.Fault := .overApplication f
      (Mettapedia.Languages.MeTTa.PeTTa.Eval.knownArities
        (Unifying.codeRegistry (translate atoms) world.privateCode) f) args.length with reasonEq
    have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
        (Unifying.codeEquations world.state world.privateCode) f
        (args.map (Unifying.resolve [])) [] world.uses = some (.fault reason, 0) := by
      rw [PeTTaRuns.map_resolve_ground [] groundArgs]
      unfold Unifying.application
      rw [if_neg unknown, if_pos overApplied]
    have path : PeTTaRuns.PSteps (translate atoms)
        ⟨world, [.execute ⟨.evaluate [] (.expression (.symbol f :: args)), []⟩], [], 0⟩
        ⟨{world with uses := world.uses + 0}, [.execute ⟨.fault reason, []⟩], [], 0⟩ := by
      refine .head (PeTTaRuns.call_enter world [] ordinary.notCollapse ordinary.notOnce
        ordinary.notControl callable [] [] [] 0) ?_
      have argumentsRun := PeTTaRuns.arguments_data (registry := translate atoms) world []
        (.function f) (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index)
        [] [] [] 0 args [] 0 ordinary.arguments
      rw [List.nil_append] at argumentsRun
      refine .trans argumentsRun ?_
      exact .single (PeTTaRuns.apply_equations world [] args (0 + args.length) ordinary.notIO
        ordinary.notNative applied [] [] [] 0)
    obtain ⟨N, reached⟩ := (Streaming.path_iff_advance _ _ _).mp path
    refine ⟨N, reason, fun n bigger => ?_⟩
    have stays : ∀ m, Streaming.advance (translate atoms) m
        ⟨{world with uses := world.uses + 0}, [.execute ⟨.fault reason, []⟩], [], 0⟩ =
        ⟨{world with uses := world.uses + 0}, [.execute ⟨.fault reason, []⟩], [], 0⟩ :=
      fun m => Mettapedia.Machines.BoundedDeterministicRun.run_of_none _ _ rfl m
    rw [entered, show n = N + (n - N) by omega, Streaming.advance_add, reached, stays]
    exact ⟨rfl, rfl⟩

#print axioms over_calls_differ
#print axioms refused_steps
#print axioms he_stuck
#print axioms refused_differs
#print axioms refused_calls_differ
#print axioms arity_differs
#print axioms partial_answerable
#print axioms petta_partial
#print axioms arity_calls_differ

end FragmentDifferences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
