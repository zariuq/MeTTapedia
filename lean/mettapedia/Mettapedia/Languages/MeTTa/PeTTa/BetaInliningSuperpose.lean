import Mettapedia.Languages.MeTTa.PeTTa.BetaInlining

/-!
# Inlining every equation of a call as an ordered superposition

`BetaInlining` inlines a call of a one-equation function. A function with several
equations whose heads are distinct variables of the call's arity is inlined as the
literal superposition of its bodies, each with its parameters renamed to the argument
variables, in source order: the call and the superposition have the same observations
beneath every continuation (`beta_superpose`). Order and multiplicity of answers, the
threading of the store from one body to the next, and faults are kept.

An argument that is an expression, evaluated by the call, is inlined through a binding:
the call is equivalent to `(let $a argument body)`, with `$a` fresh for the caller and the
parameter renamed to it (`beta_let`). Substituting the expression itself for the parameter
is not equivalent; see `BetaInliningControls.nondeterministic_argument_call`.

`SameObservations` relates two configurations whose completed runs coincide and whose
faults have the same reason, store and input/output; `Equivalent` lifts it to controls
beneath every continuation. Sequencing respects it (`sequence_equivalent`), and empty
sequencing frames are transparent (`transparent_sequences`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInliningSuperpose

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Effects (Fault)
open Eval
open DeclarativeSpec (Transition Runs)
open Mettapedia.Languages.MeTTa.TypeSchemeActivation (rename)
open BetaInlining

/-- The same completed observations, and faults for the same reason with the same store
and input/output. -/
def SameObservations (program : Program) (one two : Configuration) : Prop :=
  (∀ after answers input output,
    Runs program one (.complete after answers input output) ↔
      Runs program two (.complete after answers input output)) ∧
  (∀ reason after input output,
    (∃ faulted, Runs program one (.fault reason faulted) ∧
      faulted.state = after ∧ faulted.input = input ∧ faulted.output = output) ↔
    (∃ faulted, Runs program two (.fault reason faulted) ∧
      faulted.state = after ∧ faulted.input = input ∧ faulted.output = output))

theorem SameObservations.refl (program : Program) (c : Configuration) :
    SameObservations program c c :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

theorem SameObservations.symm {program : Program} {one two : Configuration}
    (same : SameObservations program one two) : SameObservations program two one :=
  ⟨fun a b c d => (same.1 a b c d).symm, fun a b c d => (same.2 a b c d).symm⟩

theorem SameObservations.trans {program : Program} {one two three : Configuration}
    (first : SameObservations program one two) (second : SameObservations program two three) :
    SameObservations program one three :=
  ⟨fun a b c d => (first.1 a b c d).trans (second.1 a b c d),
    fun a b c d => (first.2 a b c d).trans (second.2 a b c d)⟩

theorem sameObservations_of_path {program : Program} {one two : Configuration}
    (path : (theory program).MultiStep one two) : SameObservations program one two :=
  ⟨fun _ _ _ _ => runs_path_iff path,
    fun _ _ _ _ => exists_congr fun _ => and_congr_left' (runs_path_iff path)⟩

/-- Controls with the same observations beneath every continuation. -/
def Equivalent (program : Program) (one two : Control) : Prop :=
  ∀ (state : Effects.State) (frames : List Frame) (input output : List Atom),
    SameObservations program ⟨state, one, frames, input, output⟩ ⟨state, two, frames, input, output⟩

theorem Equivalent.refl (program : Program) (c : Control) : Equivalent program c c :=
  fun _ _ _ _ => SameObservations.refl program _

/-- Callers with the same observations once the computation has answered may replace each
other beneath it. -/
theorem swap_callers {program : Program} (one two : List Frame)
    (same : ∀ state answers input output,
      SameObservations program ⟨state, .returned answers, one, input, output⟩
        ⟨state, .returned answers, two, input, output⟩)
    (state : Effects.State) (control : Control) (input output : List Atom) :
    SameObservations program ⟨state, control, one, input, output⟩
      ⟨state, control, two, input, output⟩ := by
  have split (callers : List Frame) {o : Outcome}
      (running : Runs program ⟨state, control, callers, input, output⟩ o) :=
    runs_split_frames callers running ⟨state, control, [], input, output⟩ rfl
  refine ⟨fun after answers input' output' => ⟨fun running => ?_, fun running => ?_⟩,
    fun reason after input' output' => ⟨?_, ?_⟩⟩
  · rcases split one running with ⟨st, returned, i, o, inner, outer⟩ | ⟨_, _, _, eq⟩
    · exact runs_join_frames two _ inner (((same st returned i o).1 _ _ _ _).mp outer)
    · cases eq
  · rcases split two running with ⟨st, returned, i, o, inner, outer⟩ | ⟨_, _, _, eq⟩
    · exact runs_join_frames one _ inner (((same st returned i o).1 _ _ _ _).mpr outer)
    · cases eq
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rcases split one running with ⟨st, returned, i, o, inner, outer⟩ | ⟨r, f, inner, eq⟩
    · obtain ⟨faulted', running', hs', hi', ho'⟩ :=
        ((same st returned i o).2 reason after input' output').mp ⟨faulted, outer, hs, hi, ho⟩
      exact ⟨faulted', runs_join_frames two _ inner running', hs', hi', ho'⟩
    · cases eq
      exact ⟨withFrames f two, runs_join_fault two inner, hs, hi, ho⟩
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rcases split two running with ⟨st, returned, i, o, inner, outer⟩ | ⟨r, f, inner, eq⟩
    · obtain ⟨faulted', running', hs', hi', ho'⟩ :=
        ((same st returned i o).2 reason after input' output').mpr ⟨faulted, outer, hs, hi, ho⟩
      exact ⟨faulted', runs_join_frames one _ inner running', hs', hi', ho'⟩
    · cases eq
      exact ⟨withFrames f one, runs_join_fault one inner, hs, hi, ho⟩

/-- Empty sequencing frames above the callers are transparent. -/
theorem transparent_sequences (program : Program) (count : Nat) (callers : List Frame)
    (state : Effects.State) (control : Control) (input output : List Atom) :
    SameObservations program
      ⟨state, control, List.replicate count (.sequence [] []) ++ callers, input, output⟩
      ⟨state, control, callers, input, output⟩ := by
  apply swap_callers
  intro state answers input output
  induction count with
  | zero => exact SameObservations.refl program _
  | succ count ih =>
      refine SameObservations.trans (sameObservations_of_path
        (.step (Transition.sequence_return rfl rfl) (.step (Transition.sequence_done rfl) (.refl _))))
        ?_
      simpa using ih

/-- **Sequencing respects equivalence**, element by element, for every collected prefix. -/
theorem sequence_equivalent (program : Program) :
    ∀ {ones twos : List Control}, List.Forall₂ (Equivalent program) ones twos →
      ∀ (collected : List Atom),
        Equivalent program (.sequence ones collected) (.sequence twos collected)
  | [], [], .nil, collected => Equivalent.refl program _
  | one :: ones, two :: twos, .cons head tail, collected => by
      intro state frames input output
      have rest := sequence_equivalent program tail
      have enterOne := sameObservations_of_path (program := program)
        (one := ⟨state, .sequence (one :: ones) collected, frames, input, output⟩)
        (.step (Transition.sequence_enter rfl) (.refl _))
      have enterTwo := sameObservations_of_path (program := program)
        (one := ⟨state, .sequence (two :: twos) collected, frames, input, output⟩)
        (.step (Transition.sequence_enter rfl) (.refl _))
      refine enterOne.trans (SameObservations.trans ?_ enterTwo.symm)
      refine (head state (.sequence ones collected :: frames) input output).trans ?_
      apply swap_callers
      intro state' answers input' output'
      have returnOne := sameObservations_of_path (program := program)
        (one := ⟨state', .returned answers, .sequence ones collected :: frames, input', output'⟩)
        (.step (Transition.sequence_return rfl rfl) (.refl _))
      have returnTwo := sameObservations_of_path (program := program)
        (one := ⟨state', .returned answers, .sequence twos collected :: frames, input', output'⟩)
        (.step (Transition.sequence_return rfl rfl) (.refl _))
      exact returnOne.trans ((rest (collected ++ answers) state' frames input' output').trans
        returnTwo.symm)

/-- **A body under the callee's bindings is equivalent to its renaming under the
caller's**, beneath every continuation. -/
theorem evaluate_equivalent (program : Program) {callee caller : Subst}
    {names : String → String} {vars : List String} (agree : Agree callee caller names vars)
    (body : Atom) (closed : Within vars body) :
    Equivalent program (.evaluate callee body) (.evaluate caller (rename names body)) := by
  intro state frames input output
  have related : Rel callee caller names vars ⟨state, .evaluate callee body, [], input, output⟩
      ⟨state, .evaluate caller (rename names body), [], input, output⟩ :=
    ⟨rfl, rfl, rfl, .evaluate body closed, .nil⟩
  have split (control : Control) {o : Outcome}
      (running : Runs program ⟨state, control, frames, input, output⟩ o) :=
    runs_split_frames frames running ⟨state, control, [], input, output⟩ rfl
  refine ⟨fun after answers input' output' => ⟨fun running => ?_, fun running => ?_⟩,
    fun reason after input' output' => ⟨?_, ?_⟩⟩
  · rcases split _ running with ⟨st, returned, i, o, inner, outer⟩ | ⟨_, _, _, eq⟩
    · exact runs_join_frames frames _ (runs_complete_forward agree inner rfl related) outer
    · cases eq
  · rcases split _ running with ⟨st, returned, i, o, inner, outer⟩ | ⟨_, _, _, eq⟩
    · exact runs_join_frames frames _ (runs_complete_backward agree inner rfl related) outer
    · cases eq
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rcases split _ running with ⟨st, returned, i, o, inner, outer⟩ | ⟨r, f, inner, eq⟩
    · exact ⟨faulted, runs_join_frames frames _ (runs_complete_forward agree inner rfl related)
        outer, hs, hi, ho⟩
    · cases eq
      obtain ⟨f', running', related'⟩ := runs_fault_forward agree inner rfl related
      exact ⟨withFrames f' frames, runs_join_fault frames running',
        related'.state ▸ hs, related'.input ▸ hi, related'.output ▸ ho⟩
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rcases split _ running with ⟨st, returned, i, o, inner, outer⟩ | ⟨r, f, inner, eq⟩
    · exact ⟨faulted, runs_join_frames frames _ (runs_complete_backward agree inner rfl related)
        outer, hs, hi, ho⟩
    · cases eq
      obtain ⟨f', running', related'⟩ := runs_fault_backward agree inner rfl related
      exact ⟨withFrames f' frames, runs_join_fault frames running',
        related'.state.symm ▸ hs, related'.input.symm ▸ hi, related'.output.symm ▸ ho⟩

/-! ## Every equation of the call -/

/-- The call reaches the ordered alternatives of its equations, above one empty sequencing
frame per argument. -/
theorem call_reaches_clauses (program : Program) (f : String) (args : List String)
    (callable : (ioHead f || StdLib.known f || program.equations.any (·.head == f)) = true)
    (notPrimitive : StdLib.known f = false) (notIO : ioHead f = false)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (saturated : args.length ∈ arities program f)
    (caller : Subst) (state : Effects.State) (frames : List Frame) (input output : List Atom) :
    (theory program).MultiStep
      ⟨state, .evaluate caller (.expression (.symbol f :: args.map .var)), frames, input, output⟩
      ⟨state, .sequence (clauses program f (args.map fun a => applySubst caller (.var a))) [],
        List.replicate args.length (.sequence [] []) ++ frames, input, output⟩ := by
  have enter : Transition program
      ⟨state, .evaluate caller (.expression (.symbol f :: args.map .var)), frames, input, output⟩
      ⟨state, .arguments caller (.function f) (args.map .var) [] 0, frames, input, output⟩ :=
    .call_enter rfl (ordinary_not_control f _ ordinary (ne_match_of_not_known notPrimitive)) callable
  have argumentsPath := arguments_path program caller f state input output args [] 0 frames
  simp only [List.nil_append, Nat.zero_add] at argumentsPath
  have dispatch : Transition program
      ⟨state, .arguments caller (.function f) [] (args.map fun a => applySubst caller (.var a))
        args.length, List.replicate args.length (.sequence [] []) ++ frames, input, output⟩
      ⟨state, .sequence (clauses program f (args.map fun a => applySubst caller (.var a))) [],
        List.replicate args.length (.sequence [] []) ++ frames, input, output⟩ := by
    have selected := Transition.equations (program := program)
      (source := ⟨state, .arguments caller (.function f) []
        (args.map fun a => applySubst caller (.var a)) args.length,
        List.replicate args.length (.sequence [] []) ++ frames, input, output⟩) rfl notIO notPrimitive
    rwa [application_saturated (by simpa using saturated)] at selected
  exact .step enter (path_trans argumentsPath (.step dispatch (.refl _)))

/-- The callee's bindings for one equation's parameters. -/
def calleeOf (values : List Atom) (params : List String) : Subst :=
  (SpaceSemantics.matchValue [] (.expression (params.map .var)) (.expression values)).getD []

theorem matchValue_parameters (params : List String) (values : List Atom) (distinct : params.Nodup)
    (lengths : values.length = params.length) :
    SpaceSemantics.matchValue [] (.expression (params.map .var)) (.expression values) =
        some (calleeOf values params) ∧
      ∀ i (h₁ : i < params.length) (h₂ : i < values.length),
        Subst.lookup (calleeOf values params) params[i] = some values[i] := by
  obtain ⟨bound, matched, lookups, _⟩ := matchValues_parameters params values [] distinct lengths
    (by simp [Subst.lookup])
  have matchedValue : SpaceSemantics.matchValue [] (.expression (params.map .var))
      (.expression values) = some bound := by
    rw [SpaceSemantics.matchValue_expression_of_not_cons]
    · exact matched
    · intro first rest same
      cases params with
      | nil => simp at same
      | cons p ps => simp at same
  have same : calleeOf values params = bound := by simp [calleeOf, matchedValue]
  rw [same]
  exact ⟨matchedValue, lookups⟩

/-- The same bindings, from the element-by-element match of the argument list. -/
theorem matchValues_parameters_callee (params : List String) (values : List Atom)
    (distinct : params.Nodup) (lengths : values.length = params.length) :
    SpaceSemantics.matchValue.matchValues [] (params.map .var) values =
      some (calleeOf values params) := by
  have here := (matchValue_parameters params values distinct lengths).1
  rwa [SpaceSemantics.matchValue_expression_of_not_cons] at here
  intro first rest same
  cases params with
  | nil => simp at same
  | cons p ps => simp at same

/-- With every equation's head made of distinct variables of the call's arity, the call's
alternatives are every equation's body under its parameters' bindings, in source order. -/
theorem clauses_all (program : Program) (f : String) (equations : List (List String × Atom))
    (all : program.equations.filter (fun equation => equation.head == f) =
      equations.map fun e => ⟨f, e.1.map .var, e.2⟩)
    (values : List Atom) (shapes : ∀ e ∈ equations, e.1.Nodup ∧ values.length = e.1.length) :
    clauses program f values =
      equations.map fun e => Control.evaluate (calleeOf values e.1) e.2 := by
  unfold clauses
  have rewritten := filterMap_ite_eq_filter (fun equation : SpaceSemantics.Equation =>
      equation.head = f)
    (fun equation => (SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
      fun bindings => Control.evaluate bindings equation.body)
    program.equations
  rw [rewritten]
  have sameFilter : (fun equation : SpaceSemantics.Equation => decide (equation.head = f)) =
      (fun equation => equation.head == f) := by
    funext equation
    by_cases same : equation.head = f <;> simp [same]
  rw [sameFilter, all, List.filterMap_map]
  clear all
  induction equations with
  | nil => rfl
  | cons e rest ih =>
      have here := matchValues_parameters_callee e.1 values (shapes e List.mem_cons_self).1
        (shapes e List.mem_cons_self).2
      simp only [List.filterMap_cons, Function.comp_apply, here, Option.map_some, List.map_cons]
      have tail := ih (fun e' member => shapes e' (List.mem_cons_of_mem _ member))
      simp only [Function.comp_def] at tail
      rw [tail]

/-- **Inlining every equation.** A call of a function whose equations all have heads of
distinct variables, one per argument, is equivalent beneath every continuation to the
ordered superposition of the equations' bodies, each with its parameters renamed to the
argument variables, when every argument variable is bound and each body mentions only its
parameters. -/
theorem beta_superpose (program : Program) (f : String) (equations : List (List String × Atom))
    (args : List String) (names : List String × Atom → String → String) (caller : Subst)
    (all : program.equations.filter (fun equation => equation.head == f) =
      equations.map fun e => ⟨f, e.1.map .var, e.2⟩)
    (nonempty : equations ≠ [])
    (shapes : ∀ e ∈ equations, e.1.Nodup ∧ Within e.1 e.2 ∧ e.1.length = args.length ∧
      ∀ i (h₁ : i < e.1.length) (h₂ : i < args.length), names e e.1[i] = args[i])
    (notPrimitive : StdLib.known f = false) (notIO : ioHead f = false)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (bound : ∀ a ∈ args, ∃ value, Subst.lookup caller a = some value) :
    Equivalent program (.evaluate caller (.expression (.symbol f :: args.map .var)))
      (.evaluate caller (.expression [.symbol "superpose",
        .expression (equations.map fun e => rename (names e) e.2)])) := by
  intro state frames input output
  set values := args.map fun a => applySubst caller (.var a) with valuesDef
  have callable : (ioHead f || StdLib.known f || program.equations.any (·.head == f)) = true := by
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, equations = e :: rest := by
      cases equations with
      | nil => exact absurd rfl nonempty
      | cons e rest => exact ⟨e, rest, rfl⟩
    have member : (⟨f, e.1.map .var, e.2⟩ : SpaceSemantics.Equation) ∈
        program.equations.filter (fun equation => equation.head == f) := by
      rw [all]; simp
    have found := List.mem_filter.mp member
    simp only [List.any_eq_true, Bool.or_eq_true]
    exact .inr ⟨_, found.1, found.2⟩
  have saturated : args.length ∈ arities program f := by
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, equations = e :: rest := by
      cases equations with
      | nil => exact absurd rfl nonempty
      | cons e rest => exact ⟨e, rest, rfl⟩
    simp only [arities, all, List.map_map, List.mem_map]
    exact ⟨e, List.mem_cons_self, by simp [(shapes e List.mem_cons_self).2.2.1]⟩
  have callPath := call_reaches_clauses program f args callable notPrimitive notIO ordinary
    saturated caller state frames input output
  rw [clauses_all program f equations all values (fun e member =>
    ⟨(shapes e member).1, by simp [values, (shapes e member).2.2.1]⟩)] at callPath
  have inlinedPath : (theory program).MultiStep
      ⟨state, .evaluate caller (.expression [.symbol "superpose",
        .expression (equations.map fun e => rename (names e) e.2)]), frames, input, output⟩
      ⟨state, .sequence ((equations.map fun e => rename (names e) e.2).map (.evaluate caller)) [],
        frames, input, output⟩ :=
    .step (Transition.superpose_enter rfl) (.refl _)
  have pointwise : ∀ (rest : List (List String × Atom)), (∀ e ∈ rest, e ∈ equations) →
      List.Forall₂ (Equivalent program)
        (rest.map fun e => Control.evaluate (calleeOf values e.1) e.2)
        ((rest.map fun e => rename (names e) e.2).map (.evaluate caller)) := by
    intro rest inside
    induction rest with
    | nil => exact .nil
    | cons e rest ih =>
        have member := inside e List.mem_cons_self
        obtain ⟨distinct, closed, saturated, renamed⟩ := shapes e member
        obtain ⟨_, lookups⟩ := matchValue_parameters e.1 values distinct
          (by simp [values, saturated])
        have agree : Agree (calleeOf values e.1) caller (names e) e.1 := by
          intro x found
          obtain ⟨i, h₁, rfl⟩ := List.getElem_of_mem found
          have h₂ : i < args.length := by rw [← saturated]; exact h₁
          obtain ⟨value, located⟩ := bound args[i] (List.getElem_mem h₂)
          refine ⟨value, ?_, ?_⟩
          · rw [lookups i h₁ (by simpa [values] using h₂)]
            simp [values, applySubst, located]
          · rw [renamed i h₁ h₂]
            exact located
        exact .cons (evaluate_equivalent program agree e.2 closed)
          (ih (fun e' found => inside e' (List.mem_cons_of_mem _ found)))
  have sequenced := sequence_equivalent program (pointwise equations fun _ found => found) []
    state frames input output
  exact (sameObservations_of_path callPath).trans
    ((transparent_sequences program args.length frames state _ input output).trans
      (sequenced.trans (sameObservations_of_path inlinedPath).symm))

/-! ## An argument that is an expression -/

/-- **Inlining through a binding.** A call of a one-equation, one-parameter function on an
arbitrary argument expression, evaluated by the call (no literal `Atom` domain), is
equivalent beneath every continuation to binding a variable fresh for the caller to the
argument and running the body with its parameter renamed to that variable: the argument
is evaluated once, before the body, for each of its answers. -/
theorem beta_let (program : Program) (f x fresh : String) (body argument : Atom)
    (single : program.equations.filter (fun equation => equation.head == f) =
      [⟨f, [.var x], body⟩])
    (closed : Within [x] body)
    (notPrimitive : StdLib.known f = false) (notIO : ioHead f = false)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (evaluated : argumentIsRaw program f 0 = false)
    (caller : Subst) (unbound : Subst.lookup caller fresh = none) :
    Equivalent program (.evaluate caller (.expression [.symbol f, argument]))
      (.evaluate caller (.expression [.symbol "let", .var fresh, argument,
        rename (fun _ => fresh) body])) := by
  intro state frames input output
  have callable : (ioHead f || StdLib.known f || program.equations.any (·.head == f)) = true := by
    have member : (⟨f, [.var x], body⟩ : SpaceSemantics.Equation) ∈
        program.equations.filter (fun equation => equation.head == f) := by
      rw [single]; simp
    have found := List.mem_filter.mp member
    simp only [List.any_eq_true, Bool.or_eq_true]
    exact .inr ⟨_, found.1, found.2⟩
  -- both runs evaluate the argument first, beneath different frames
  have callPath : (theory program).MultiStep
      ⟨state, .evaluate caller (.expression [.symbol f, argument]), frames, input, output⟩
      ⟨state, .evaluate caller argument,
        .argument caller (.function f) [] [] 0 :: frames, input, output⟩ :=
    .step (Transition.call_enter rfl (ordinary_not_control f _ ordinary (ne_match_of_not_known notPrimitive)) callable)
      (.step (Transition.evaluated_argument rfl (by simpa using evaluated)) (.refl _))
  have letPath : (theory program).MultiStep
      ⟨state, .evaluate caller (.expression [.symbol "let", .var fresh, argument,
        rename (fun _ => fresh) body]), frames, input, output⟩
      ⟨state, .evaluate caller argument,
        .bind caller (.var fresh) (rename (fun _ => fresh) body) :: frames, input, output⟩ :=
    .step (Transition.let_enter rfl) (.refl _)
  refine (sameObservations_of_path callPath).trans (SameObservations.trans ?_
    (sameObservations_of_path letPath).symm)
  apply swap_callers
  intro state' answers input' output'
  -- each answer of the argument: the equation's body under the parameter's binding, and
  -- the renamed body under the fresh variable's binding
  have pointwise : ∀ (values : List Atom),
      List.Forall₂ (Equivalent program)
        (values.map fun value => Control.arguments caller (.function f) [] ([] ++ [value]) 1)
        (values.filterMap fun value =>
          (SpaceSemantics.matchBinding caller (.var fresh) value).map
            fun bound => Control.evaluate bound (rename (fun _ => fresh) body)) := by
    intro values
    induction values with
    | nil => exact .nil
    | cons value rest ih =>
        have bindsFresh : SpaceSemantics.matchBinding caller (.var fresh) value =
            some ((fresh, value) :: caller) := by
          rw [SpaceSemantics.matchBinding_var, matchValue_atomic _ _ _ (by simp)]
          simp [matchAtom, unbound]
        simp only [List.map_cons, List.filterMap_cons, bindsFresh, Option.map_some]
        refine .cons ?_ ih
        obtain ⟨matched, lookups⟩ := matchValue_parameters [x] [value] (by simp) rfl
        have agree : Agree (calleeOf [value] [x]) ((fresh, value) :: caller) (fun _ => fresh) [x] := by
          intro y found
          simp only [List.mem_singleton] at found
          subst found
          refine ⟨value, by simpa using lookups 0 (by simp) (by simp), ?_⟩
          simp [Subst.lookup]
        intro state'' frames'' input'' output''
        have clausesHere : clauses program f [value] = [.evaluate (calleeOf [value] [x]) body] := by
          rw [clauses_single program f [x] body (by simpa using single) [value],
            matchValues_parameters_callee [x] [value] (by simp) rfl]
          rfl
        have dispatch : (theory program).MultiStep
            ⟨state'', .arguments caller (.function f) [] ([] ++ [value]) 1, frames'', input'',
              output''⟩
            ⟨state'', .evaluate (calleeOf [value] [x]) body,
              List.replicate 1 (.sequence [] []) ++ frames'', input'', output''⟩ := by
          have equations := Transition.equations (program := program)
            (source := ⟨state'', .arguments caller (.function f) [] [value] 1, frames'', input'',
              output''⟩) rfl notIO notPrimitive
          rw [application_of_selected clausesHere] at equations
          exact .step equations (.step (Transition.sequence_enter rfl) (.refl _))
        exact (sameObservations_of_path dispatch).trans
          ((transparent_sequences program 1 frames'' state'' _ input'' output'').trans
            (evaluate_equivalent program agree body closed state'' frames'' input'' output''))
  have callReturn := sameObservations_of_path (program := program)
    (one := ⟨state', .returned answers, .argument caller (.function f) [] [] 0 :: frames, input',
      output'⟩) (.step (Transition.argument_return rfl rfl) (.refl _))
  have letReturn := sameObservations_of_path (program := program)
    (one := ⟨state', .returned answers,
      .bind caller (.var fresh) (rename (fun _ => fresh) body) :: frames, input', output'⟩)
    (.step (Transition.binding_return rfl rfl) (.refl _))
  exact callReturn.trans ((sequence_equivalent program (pointwise answers) [] state' frames input'
    output').trans letReturn.symm)

end Mettapedia.Languages.MeTTa.PeTTa.BetaInliningSuperpose
