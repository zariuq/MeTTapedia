import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Equations that are live when a call is made

PeTTa keeps a function's equations as `=` rows of `&self`. Loading a program
adds one row per equation; `(add-atom &self (= (f a ...) body))` adds another
row and defines it as an equation; `(remove-atom &self (= (f a ...) body))`
removes the rows it matches and withdraws them as equations (SWI-PeTTa
`src/spaces.pl`; P-SPACE-4, P-SPACE-5). With `(= (f $x) (a $x))` loaded:

    !(f 1)                                  ; (a 1)
    !(add-atom &self (= (f $x) (b $x)))     ; True
    !(f 1)                                  ; (a 1) (b 1)
    !(remove-atom &self (= (f $x) (a $x)))  ; True
    !(f 1)                                  ; (b 1)

Two moments decide a call, as in the reference:

* *Translation.* A request is translated when it starts. Whether `(f a ...)`
  is a call, a partial application, an over-application or data is decided
  then, from the functions registered at that moment, which are those with `=`
  rows in `&self` (P-APP-1). So `!(let $u (add-atom &self (= (g) 5)) (g))`
  answers `(g)`, because `g` was not registered when the request was
  translated, and a later `!(g)` answers `5`.
* *Call.* A call runs the bodies of the `=` rows of its name that are in
  `&self` when the call is made and match its arguments, in row order (P-APP-3).
  So `!(let $u (add-atom &self (= (f $x) (b $x))) (f 1))` answers `(a 1) (b 1)`.

`liveStep registry` is the machine of one request translated against
`registry`. It is `Eval.step registry` except at a call of an authored
function, which selects from the live rows (`liveApplication`).
`liveRequests` runs requests in order, each translated against the program as
it stands when the request starts (`atState`).

`Eval.step program` is this machine on every configuration whose live rows are
`program`'s equations (`EquationsLive`, `liveStep_eq_step_of_live`). Loading a
program establishes that (`loaded_live`), and only an `add-atom` or
`remove-atom` on `&self` can change it (`transition_keeps_core`). So a path of
`Eval.step` from such a configuration that adds and removes no row of `&self`
is a path of this machine, and conversely (`live_path_of_path`,
`path_of_live_path`).

Recorded, not modelled: an `=` row added to a private space (the reference
`e1db30d` gives the function to that space, so a call in `&self` leaves it
data, as here); type declarations added at run time; the arity list carried
by an over-application fault when the request itself added an arity (SWI-PeTTa
lists the arities known when the fault is raised, this machine those known at
translation); and re-translation of stored equation bodies when a function they
call gains its first equation or a new arity (the reference `e1db30d` does it at
once; `b74af1b`, `fea8317` and CeTTa never do; here a body is classified
against the registry of the request that runs it).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LiveEquations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Equation)
open Effects (State Fault)
open Eval
open DeclarativeSpec (Transition)

/-! ## The equations stored in `&self` -/

/-- An `=` row read as an equation: exactly the forms that loading indexes as
equations (`SpaceSemantics.collect`). `(= (f $x) (a $x))` is the equation of
`f` with the argument `$x` and the body `(a $x)`; `(= f a)` and `(: f T)` are
not equations. -/
def equationOfRow : Atom → Option Equation
  | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
      some ⟨head, arguments, body⟩
  | _ => none

@[simp] theorem equationOfRow_toAtom (equation : Equation) :
    equationOfRow equation.toAtom = some equation := rfl

theorem equationOfRow_declaration (name type : Atom) :
    equationOfRow (.expression [.symbol ":", name, type]) = none := by
  simp [equationOfRow]

/-- The equations stored in `&self`, in row order. -/
def liveEquations (state : State) : List Equation :=
  state.core.filterMap equationOfRow

/-- `program` with the equations live in `state`. Its type declarations are
kept: declarations added at run time are not modelled. -/
def atState (program : Program) (state : State) : Program :=
  { program with equations := liveEquations state }

@[simp] theorem atState_equations (program : Program) (state : State) :
    (atState program state).equations = liveEquations state := rfl

@[simp] theorem atState_declarations (program : Program) (state : State) :
    (atState program state).declarations = program.declarations := rfl

/-- The live rows of `state` are exactly `program`'s equations, in order. -/
def EquationsLive (program : Program) (state : State) : Prop :=
  liveEquations state = program.equations

theorem atState_live (program : Program) (state : State) :
    EquationsLive (atState program state) state := rfl

theorem atState_of_live {program : Program} {state : State}
    (live : EquationsLive program state) : atState program state = program := by
  unfold atState
  rw [live]

theorem live_of_same_core {program : Program} {state after : State}
    (live : EquationsLive program state) (same : after.core = state.core) :
    EquationsLive program after := by
  unfold EquationsLive liveEquations at *
  rw [same]
  exact live

/-- A row read as an equation is that equation's stored atom. -/
theorem equationOfRow_eq_some {row : Atom} {equation : Equation}
    (read : equationOfRow row = some equation) : row = equation.toAtom := by
  unfold equationOfRow at read
  split at read
  · cases read
    rfl
  · cases read

/-- Loading indexes as equations exactly the forms read as `=` rows. -/
theorem collect_equations {forms : List Atom} {program : Program}
    (collected : SpaceSemantics.collect forms = .ok program) :
    forms.filterMap equationOfRow = program.equations := by
  induction forms generalizing program with
  | nil =>
      simp only [SpaceSemantics.collect, Except.ok.injEq] at collected
      subst collected
      rfl
  | cons form rest ih =>
      simp only [SpaceSemantics.collect, bind, Except.bind] at collected
      cases restCollected : SpaceSemantics.collect rest with
      | error message => simp [restCollected] at collected
      | ok restProgram =>
          simp only [restCollected] at collected
          have restEquations := ih restCollected
          split at collected <;> (simp only [Except.ok.injEq] at collected; subst collected)
          · simp [equationOfRow, restEquations]
          · simp [equationOfRow, restEquations]
          · rename_i notOne _
            have none : equationOfRow form = none := by
              cases read : equationOfRow form with
              | none => rfl
              | some equation =>
                  exact absurd (equationOfRow_eq_some read)
                    (notOne equation.head equation.arguments equation.body)
            simp [none, restEquations]

/-- A loaded program's live rows are its equations. -/
theorem loaded_live {forms : List Atom} {program : Program}
    (collected : SpaceSemantics.collect forms = .ok program) :
    EquationsLive program (Effects.loaded program) := by
  show (SpaceSemantics.loadedAtoms program).filterMap equationOfRow = program.equations
  rw [SpaceSemantics.loadedAtoms_collect collected]
  exact collect_equations collected

/-! ## What a primitive does to `&self` -/

theorem insert_core {state after : State} {handle : NamedSpaces.Handle} {atom : Atom}
    (inserted : Effects.insert state handle atom = some after) :
    (handle = .self ∧ after.core = state.core ++ [atom]) ∨ after.core = state.core := by
  unfold Effects.insert at inserted
  cases handle with
  | self =>
      simp only [NamedSpaces.Store.read_self, Option.bind_eq_bind, Option.bind_some,
        NamedSpaces.Store.write, Option.some.injEq] at inserted
      subst after
      exact .inl ⟨rfl, rfl⟩
  | privateSpace index =>
      right
      simp only [NamedSpaces.Store.read, Option.bind_eq_bind] at inserted
      split at inserted
      · simp only [Option.bind_some, NamedSpaces.Store.write] at inserted
        split at inserted
        · cases inserted
          rfl
        · contradiction
      · contradiction

theorem erase_core {state after : State} {handle : NamedSpaces.Handle} {pattern : Atom}
    (erased : Effects.erase state handle pattern = some after) :
    (handle = .self ∧
        after.core = state.core.filter fun row => !Effects.removalMatches pattern row) ∨
      after.core = state.core := by
  unfold Effects.erase at erased
  cases handle with
  | self =>
      simp only [NamedSpaces.Store.read_self, Option.bind_eq_bind, Option.bind_some,
        NamedSpaces.Store.write, Option.some.injEq] at erased
      subst after
      exact .inl ⟨rfl, rfl⟩
  | privateSpace index =>
      right
      simp only [NamedSpaces.Store.read, Option.bind_eq_bind] at erased
      split at erased
      · simp only [Option.bind_some, NamedSpaces.Store.write] at erased
        split at erased
        · cases erased
          rfl
        · contradiction
      · contradiction

theorem readHandle_self {location : Atom} (decoded : Effects.readHandle location = some .self) :
    location = .symbol "&self" := by
  unfold Effects.readHandle at decoded
  split at decoded
  · rfl
  · split at decoded <;> simp at decoded
  · simp at decoded

/-- `add-atom` with two arguments, as the primitive table computes it. -/
theorem apply_add_atom (state : State) (location atom : Atom) :
    StdLib.apply state "add-atom" [location, atom] =
      match Effects.readHandle location >>= fun handle => Effects.insert state handle atom with
      | some after => .ok (after, [Effects.boolean true])
      | none => .error .invalidSpace := rfl

/-- `remove-atom` with two arguments, as the primitive table computes it. -/
theorem apply_remove_atom (state : State) (location atom : Atom) :
    StdLib.apply state "remove-atom" [location, atom] =
      match Effects.readHandle location with
      | none => .error .invalidSpace
      | some handle =>
          match state.read handle with
          | none => .error .invalidSpace
          | some _ =>
              match atom with
              | .var _ => .ok (state, [Effects.boolean true])
              | .expression (_ :: _) =>
                  match Effects.erase state handle atom with
                  | some after => .ok (after, [Effects.boolean true])
                  | none => .error .invalidSpace
              | _ => .ok (state, []) := rfl

private theorem no_ok {state after : State} {head : String} {values answers : List Atom}
    {reason : Fault} (failed : StdLib.apply state head values = .error reason)
    (returned : StdLib.apply state head values = .ok (after, answers)) : False := by
  rw [failed] at returned
  cases returned

private theorem ok_state {state after result : State} {head : String}
    {values answers out : List Atom}
    (computed : StdLib.apply state head values = .ok (result, out))
    (returned : StdLib.apply state head values = .ok (after, answers)) : after = result := by
  rw [computed] at returned
  cases returned
  rfl

/-- A successful primitive leaves the rows of `&self` as they were, unless it
is `add-atom` or `remove-atom` on `&self`. -/
theorem apply_core {state after : State} {head : String} {values answers : List Atom}
    (returned : StdLib.apply state head values = .ok (after, answers)) :
    after.core = state.core ∨
      ((head = "add-atom" ∨ head = "remove-atom") ∧
        ∃ atom, values = [.symbol "&self", atom]) := by
  by_cases new : head = "new-space"
  · subst new
    left
    rcases values with _ | ⟨first, rest⟩
    · rw [ok_state rfl returned]
    · exact (no_ok rfl returned).elim
  by_cases change : head = "change-state!"
  · subst change
    left
    rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
    · exact (no_ok rfl returned).elim
    · rcases first with name | name | value | items <;> exact (no_ok rfl returned).elim
    · rcases first with name | name | value | items
      · rw [ok_state rfl returned]
        rfl
      all_goals exact (no_ok rfl returned).elim
    · rcases first with name | name | value | items <;> exact (no_ok rfl returned).elim
    · rcases first with name | name | value | items <;> exact (no_ok rfl returned).elim
  by_cases add : head = "add-atom"
  · subst add
    rcases values with _ | ⟨location, _ | ⟨atom, _ | ⟨third, rest⟩⟩⟩
    · exact (no_ok rfl returned).elim
    · exact (no_ok rfl returned).elim
    · rw [apply_add_atom] at returned
      cases decoded : Effects.readHandle location with
      | none => simp [decoded] at returned
      | some handle =>
          cases inserted : Effects.insert state handle atom with
          | none => simp [decoded, inserted] at returned
          | some written =>
              simp only [decoded, inserted, Option.bind_eq_bind, Option.bind_some,
                Except.ok.injEq, Prod.mk.injEq] at returned
              obtain ⟨rfl, -⟩ := returned
              rcases insert_core inserted with ⟨rfl, _⟩ | same
              · refine .inr ⟨.inl rfl, atom, ?_⟩
                rw [readHandle_self decoded]
              · exact .inl same
    · exact (no_ok rfl returned).elim
  by_cases remove : head = "remove-atom"
  · subst remove
    rcases values with _ | ⟨location, _ | ⟨atom, _ | ⟨third, rest⟩⟩⟩
    · exact (no_ok rfl returned).elim
    · exact (no_ok rfl returned).elim
    · rw [apply_remove_atom] at returned
      cases decoded : Effects.readHandle location with
      | none => simp [decoded] at returned
      | some handle =>
          cases present : state.read handle with
          | none => simp [decoded, present] at returned
          | some rows =>
              simp only [decoded, present] at returned
              rcases atom with name | name | value | _ | ⟨first, rest⟩
              · cases returned
                exact .inl rfl
              · cases returned
                exact .inl rfl
              · cases returned
                exact .inl rfl
              · cases returned
                exact .inl rfl
              · cases erased : Effects.erase state handle (.expression (first :: rest)) with
                | none => simp [erased] at returned
                | some written =>
                    simp only [erased, Except.ok.injEq, Prod.mk.injEq] at returned
                    obtain ⟨rfl, -⟩ := returned
                    rcases erase_core erased with ⟨rfl, _⟩ | same
                    · refine .inr ⟨.inr rfl, .expression (first :: rest), ?_⟩
                      rw [readHandle_self decoded]
                    · exact .inl same
    · exact (no_ok rfl returned).elim
  left
  rw [StdLib.successful_apply_state new add remove change returned]

/-- A configuration about to add or remove a row of `&self`. -/
def EditsSelf (configuration : Configuration) : Prop :=
  ∃ bindings head atom index,
    configuration.control = .arguments bindings (.function head) [] [.symbol "&self", atom] index ∧
      (head = "add-atom" ∨ head = "remove-atom")

/-- Only an `add-atom` or `remove-atom` on `&self` changes the rows of `&self`. -/
theorem transition_keeps_core {registry : Program} {source target : Configuration}
    (transition : Transition registry source target) (keeps : ¬ EditsSelf source) :
    target.state.core = source.state.core := by
  cases transition
  case primitive bindings head index values answers after control ordinary native result =>
    rcases apply_core result with same | ⟨edit, atom, rfl⟩
    · exact same
    · exact absurd ⟨bindings, head, atom, index, control, edit⟩ keeps
  all_goals rfl

/-- Adding an equation row to `&self` appends that equation to the live ones. -/
theorem add_equation_live (state after : State) (equation : Equation) (answers : List Atom)
    (returned : StdLib.apply state "add-atom" [.symbol "&self", equation.toAtom] =
      .ok (after, answers)) :
    liveEquations after = liveEquations state ++ [equation] := by
  have computed : StdLib.apply state "add-atom" [.symbol "&self", equation.toAtom] =
      .ok ({ state with core := state.core ++ [equation.toAtom] }, [Effects.boolean true]) := rfl
  rw [computed] at returned
  cases returned
  simp [liveEquations]

/-! ## The machine of one request -/

/-- The control of a call translated against `registry` whose equations are
selected from `live`. The registry decides, by the arity, whether the call is a
call, a partial application or an over-application (P-APP-1); a call runs the
bodies of the live equations whose argument patterns match, in row order. -/
def liveApplication (registry : Program) (live : List Equation) (head : String)
    (values : List Atom) : Control :=
  if values.length ∈ arities registry head then
    .sequence (clauses { registry with equations := live } head values) []
  else if (arities registry head).all (· < values.length) &&
      !(arities registry head).isEmpty then
    .fault (.overApplication head (knownArities registry head) values.length)
  else .returned [partialValue head values]

/-- When the live rows are the registry's equations, a call is the ordinary
application. -/
theorem liveApplication_of_live {registry : Program} {state : State}
    (live : EquationsLive registry state) (head : String) (values : List Atom) :
    liveApplication registry (liveEquations state) head values =
      application registry head values := by
  rw [application_classified]
  unfold liveApplication
  rw [live]

/-- One step of a request translated against `registry`. -/
def liveStep (registry : Program) (configuration : Configuration) : Option Configuration :=
  match configuration.control with
  | .arguments _ (.function head) [] values _ =>
      if ioHead head || StdLib.known head then step registry configuration
      else some { configuration with
        control := liveApplication registry (liveEquations configuration.state) head values }
  | _ => step registry configuration

/-- A call of an authored function whose arguments are values: the only
configuration at which the live rows are read. -/
def Dispatches (configuration : Configuration) : Prop :=
  ∃ bindings head values index,
    configuration.control = .arguments bindings (.function head) [] values index ∧
      ioHead head = false ∧ StdLib.known head = false

theorem liveStep_of_not_dispatches {registry : Program} {configuration : Configuration}
    (notCall : ¬ Dispatches configuration) :
    liveStep registry configuration = step registry configuration := by
  unfold liveStep
  split
  · rename_i bindings head values index control
    split
    · rfl
    · rename_i native
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at native
      exact absurd ⟨bindings, head, values, index, control, native.1, native.2⟩ notCall
  · rfl

theorem liveStep_eq_step_of_live {registry : Program} {configuration : Configuration}
    (live : EquationsLive registry configuration.state) :
    liveStep registry configuration = step registry configuration := by
  unfold liveStep
  split
  · rename_i bindings head values index control
    split
    · rfl
    · rename_i native
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at native
      simp only [step, control, native.1, native.2, Bool.false_eq_true, ↓reduceIte,
        liveApplication_of_live live]
  · rfl

/-- The declarative rules of one request translated against `registry`: the
rules of `DeclarativeSpec.Transition`, with a call of an authored function
selecting from the live rows. -/
inductive LiveTransition (registry : Program) : Configuration → Configuration → Prop where
  | call {source : Configuration} {bindings : Subst} {head : String} {values : List Atom}
      {index : Nat}
      (control : source.control = .arguments bindings (.function head) [] values index)
      (ordinary : ioHead head = false) (notNative : StdLib.known head = false) :
      LiveTransition registry source
        { source with control := liveApplication registry (liveEquations source.state) head values }
  | rule {source target : Configuration} (transition : Transition registry source target)
      (notCall : ¬ Dispatches source) :
      LiveTransition registry source target

theorem liveStep_iff_transition (registry : Program) (source target : Configuration) :
    liveStep registry source = some target ↔ LiveTransition registry source target := by
  constructor
  · intro computed
    by_cases dispatches : Dispatches source
    · obtain ⟨bindings, head, values, index, control, ordinary, notNative⟩ := dispatches
      have equal : liveStep registry source = some { source with
          control := liveApplication registry (liveEquations source.state) head values } := by
        simp [liveStep, control, ordinary, notNative]
      rw [equal, Option.some.injEq] at computed
      subst target
      exact .call control ordinary notNative
    · rw [liveStep_of_not_dispatches dispatches] at computed
      exact .rule (step_transition computed) dispatches
  · intro transition
    cases transition with
    | call control ordinary notNative => simp [liveStep, control, ordinary, notNative]
    | rule transition notCall =>
        rw [liveStep_of_not_dispatches notCall]
        exact transition_step transition

/-- The rows of `&self` change only at an `add-atom` or `remove-atom` on
`&self`, in this machine too. -/
theorem liveTransition_keeps_core {registry : Program} {source target : Configuration}
    (transition : LiveTransition registry source target) (keeps : ¬ EditsSelf source) :
    target.state.core = source.state.core := by
  cases transition with
  | call => rfl
  | rule transition _ => exact transition_keeps_core transition keeps

/-! ## Runs of one request -/

def liveRun (registry : Program) : Nat → Configuration → Outcome
  | fuel, configuration =>
      match configuration.control, configuration.frames with
      | .returned answers, [] =>
          .complete configuration.state answers configuration.input configuration.output
      | .fault fault, _ => .fault fault configuration
      | _, _ =>
          match fuel with
          | 0 => .exhausted configuration
          | fuel + 1 =>
              match liveStep registry configuration with
              | some next => liveRun registry fuel next
              | none => .exhausted configuration

/-- The whole-request judgment of the live machine. -/
inductive LiveRuns (registry : Program) : Configuration → Outcome → Prop where
  | completed {source : Configuration} {answers : List Atom}
      (control : source.control = .returned answers) (frames : source.frames = []) :
      LiveRuns registry source (.complete source.state answers source.input source.output)
  | fault {source : Configuration} {reason : Fault}
      (control : source.control = .fault reason) :
      LiveRuns registry source (.fault reason source)
  | next {source target : Configuration} {result : Outcome}
      (transition : LiveTransition registry source target) (rest : LiveRuns registry target result) :
      LiveRuns registry source result

theorem liveRun_succ_of_step (registry : Program) (fuel : Nat)
    (source target : Configuration) (transition : liveStep registry source = some target) :
    liveRun registry (fuel + 1) source = liveRun registry fuel target := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals try solve | simp [liveStep, step] at transition
      all_goals simp only [liveRun, transition]

theorem live_derivation_has_run {registry : Program} {source : Configuration} {result : Outcome}
    (derivation : LiveRuns registry source result) :
    ∃ fuel, liveRun registry fuel source = result := by
  induction derivation with
  | completed control frames =>
    refine ⟨0, ?_⟩
    rename_i source answers
    cases source
    simp_all [liveRun]
  | fault control =>
    refine ⟨0, ?_⟩
    rename_i source reason
    cases source
    simp_all [liveRun]
  | next transition _ ih =>
    obtain ⟨fuel, computed⟩ := ih
    exact ⟨fuel + 1, (liveRun_succ_of_step _ _ _ _
      ((liveStep_iff_transition _ _ _).mpr transition)).trans computed⟩

theorem live_run_has_derivation (registry : Program) (fuel : Nat) (source : Configuration)
    (result : Outcome) (notExhausted : ∀ unfinished, result ≠ .exhausted unfinished)
    (computed : liveRun registry fuel source = result) :
    LiveRuns registry source result := by
  induction fuel generalizing source with
  | zero =>
    cases source with
    | mk state control frames input output =>
      cases control <;> cases frames <;> simp only [liveRun] at computed
      all_goals first
        | exact False.elim (notExhausted _ computed.symm)
        | (subst result; exact .completed rfl rfl)
        | (subst result; exact .fault rfl)
  | succ fuel ih =>
    have advance (current : Configuration)
        (computed : liveRun registry (fuel + 1) current = result)
        (unfolded : liveRun registry (fuel + 1) current =
          match liveStep registry current with
          | some next => liveRun registry fuel next
          | none => .exhausted current) :
        LiveRuns registry current result := by
      rw [unfolded] at computed
      cases transition : liveStep registry current with
      | none =>
        simp only [transition] at computed
        exact False.elim (notExhausted _ computed.symm)
      | some next =>
        exact .next ((liveStep_iff_transition _ _ _).mp transition)
          (ih next (by simpa [transition] using computed))
    cases source with
    | mk state control frames input output =>
      cases control <;> cases frames
      all_goals try solve
        | simp only [liveRun] at computed
          subst result
          first | exact .completed rfl rfl | exact .fault rfl
      all_goals exact advance _ computed rfl

/-- The executable live machine and its judgment agree on the entire store
and the ordered answer, remaining-input and output observations. -/
theorem completed_live_run_iff_derivation (registry : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    (∃ fuel, liveRun registry fuel source = .complete state answers input output) ↔
      LiveRuns registry source (.complete state answers input output) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact live_run_has_derivation registry fuel source _ (by simp) computed
  · exact live_derivation_has_run

theorem fault_live_run_iff_derivation (registry : Program) (source : Configuration)
    (reason : Fault) (faulted : Configuration) :
    (∃ fuel, liveRun registry fuel source = .fault reason faulted) ↔
      LiveRuns registry source (.fault reason faulted) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact live_run_has_derivation registry fuel source _ (by simp) computed
  · exact live_derivation_has_run

/-! ## The fixed and the live machine agree while `&self` keeps its rows -/

/-- The operational graph of one request translated against `registry`. -/
def liveTheory (registry : Program) : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := LiveTransition registry
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

theorem liveTransition_of_live {registry : Program} {source target : Configuration}
    (live : EquationsLive registry source.state) (transition : Transition registry source target) :
    LiveTransition registry source target :=
  (liveStep_iff_transition registry source target).mp
    ((liveStep_eq_step_of_live live).trans (transition_step transition))

theorem transition_of_live {registry : Program} {source target : Configuration}
    (live : EquationsLive registry source.state) (transition : LiveTransition registry source target) :
    Transition registry source target :=
  step_transition ((liveStep_eq_step_of_live live).symm.trans
    ((liveStep_iff_transition registry source target).mpr transition))

/-- A path of `Eval.step registry` from a configuration whose live rows are
`registry`'s equations, along which no step adds or removes a row of `&self`,
is a path of PeTTa's machine. -/
theorem live_path_of_path {registry : Program} :
    {source target : Configuration} →
    (theory registry).MultiStep source target →
    EquationsLive registry source.state →
    (∀ current, (theory registry).MultiStep source current →
      (theory registry).MultiStep current target → ¬ EditsSelf current) →
    (liveTheory registry).MultiStep source target
  | _, _, .refl current, _, _ => Mettapedia.GSLT.GSLT.MultiStep.refl (S := liveTheory registry) current
  | _, _, .step transition rest, live, keeps => by
      have notEdit := keeps _ (.refl _) (.step transition rest)
      have next := live_of_same_core live (transition_keeps_core transition notEdit)
      refine Mettapedia.GSLT.GSLT.MultiStep.step (S := liveTheory registry)
        (liveTransition_of_live live transition) (live_path_of_path rest next ?_)
      intro current before after
      exact keeps current (.step transition before) after

/-- Conversely, such a path of PeTTa's machine is a path of `Eval.step registry`. -/
theorem path_of_live_path {registry : Program} :
    {source target : Configuration} →
    (liveTheory registry).MultiStep source target →
    EquationsLive registry source.state →
    (∀ current, (liveTheory registry).MultiStep source current →
      (liveTheory registry).MultiStep current target → ¬ EditsSelf current) →
    (theory registry).MultiStep source target
  | _, _, .refl current, _, _ => Mettapedia.GSLT.GSLT.MultiStep.refl (S := theory registry) current
  | _, _, .step transition rest, live, keeps => by
      have notEdit := keeps _ (.refl _) (.step transition rest)
      have next := live_of_same_core live (liveTransition_keeps_core transition notEdit)
      refine Mettapedia.GSLT.GSLT.MultiStep.step (S := theory registry)
        (transition_of_live live transition) (path_of_live_path rest next ?_)
      intro current before after
      exact keeps current (.step transition before) after

/-- A live path to a returned configuration with no pending frames is a
completed live run. -/
theorem liveRuns_of_path {registry : Program} :
    {source target : Configuration} → (liveTheory registry).MultiStep source target →
    {answers : List Atom} → target.control = .returned answers → target.frames = [] →
    LiveRuns registry source (.complete target.state answers target.input target.output)
  | _, _, .refl _, _, control, frames => .completed control frames
  | _, _, .step transition rest, _, control, frames =>
      .next transition (liveRuns_of_path rest control frames)

/-- A completed run of `Eval.step registry` from a configuration whose live rows
are `registry`'s equations, which adds and removes no row of `&self`, is a
completed run of PeTTa's machine with the same store, answers, input and
output. Every completed-run theorem about `Eval.step` transfers this way. -/
theorem live_completed_of_path {registry : Program} {source : Configuration} {state : State}
    {answers input output : List Atom}
    (live : EquationsLive registry source.state)
    (path : (theory registry).MultiStep source (finished state answers input output))
    (keeps : ∀ current, (theory registry).MultiStep source current →
      (theory registry).MultiStep current (finished state answers input output) →
        ¬ EditsSelf current) :
    LiveRuns registry source (.complete state answers input output) :=
  liveRuns_of_path (live_path_of_path path live keeps) rfl rfl

/-- The first request after loading is translated against the loaded program. -/
theorem atState_loaded {forms : List Atom} {program : Program}
    (collected : SpaceSemantics.collect forms = .ok program) :
    atState program (Effects.loaded program) = program :=
  atState_of_live (loaded_live collected)

/-! ## Requests in order -/

/-- Requests run in order. Each is translated against the program as it stands
in the store when it starts, and starts from the store the previous one left;
a request that does not complete ends the sequence. -/
def liveRequests (program : Program) (fuel : Nat) : State → List Atom → List Outcome
  | _, [] => []
  | state, request :: rest =>
      match liveRun (atState program state) fuel (start state request) with
      | .complete after answers input output =>
          .complete after answers input output :: liveRequests program fuel after rest
      | outcome => [outcome]

/-- The same requests on `Eval.step program`, whose equations stay those
loaded. -/
def fixedRequests (program : Program) (fuel : Nat) : State → List Atom → List Outcome
  | _, [] => []
  | state, request :: rest =>
      match run program fuel (start state request) with
      | .complete after answers input output =>
          .complete after answers input output :: fixedRequests program fuel after rest
      | outcome => [outcome]

/-- What a request shows: its answers when it completes without reading input or
printing, or its fault. -/
inductive Observation where
  | answers (values : List Atom)
  | fault (reason : Fault)
  | other
  deriving DecidableEq

def observed : Outcome → Observation
  | .complete _ answers [] [] => .answers answers
  | .fault reason _ => .fault reason
  | _ => .other

/-! ## Controls

Each control runs a program with the loaded store on the live machine and, for
contrast, on `Eval.step` of the loaded program. The live answers are those of
SWI-PeTTa `e1db30d`, `b74af1b` and `fea8317` and of CeTTa's PeTTa lane for the
same program, except where a control says otherwise.
-/

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private def row (head : String) (arguments : List Atom) (body : Atom) : Atom :=
  call "=" [call head arguments, body]
private def truth : Atom := Effects.boolean true

/-- `(= (f $x) (a $x))` -/
def redefined : Program where
  equations := [⟨"f", [.var "x"], call "a" [.var "x"]⟩]
  declarations := []
  layout := [.equation]

theorem redefined_collected :
    SpaceSemantics.collect [row "f" [.var "x"] (call "a" [.var "x"])] = .ok redefined := rfl

/-- Adding an equation defines it for later calls; removing one withdraws it. -/
theorem added_and_removed_equations :
    (liveRequests redefined 64 (Effects.loaded redefined)
      [call "f" [int 1],
       call "add-atom" [sym "&self", row "f" [.var "x"] (call "b" [.var "x"])],
       call "f" [int 1],
       call "remove-atom" [sym "&self", row "f" [.var "x"] (call "a" [.var "x"])],
       call "f" [int 1]]).map observed =
      [.answers [call "a" [int 1]], .answers [truth], .answers [call "a" [int 1], call "b" [int 1]],
       .answers [truth], .answers [call "b" [int 1]]] := by
  decide +kernel

/-- `Eval.step` of the loaded program keeps the loaded equation throughout. -/
theorem fixed_equations_ignore_rows :
    (fixedRequests redefined 64 (Effects.loaded redefined)
      [call "f" [int 1],
       call "add-atom" [sym "&self", row "f" [.var "x"] (call "b" [.var "x"])],
       call "f" [int 1],
       call "remove-atom" [sym "&self", row "f" [.var "x"] (call "a" [.var "x"])],
       call "f" [int 1]]).map observed =
      [.answers [call "a" [int 1]], .answers [truth], .answers [call "a" [int 1]],
       .answers [truth], .answers [call "a" [int 1]]] := by
  decide +kernel

/-- A call made in the request that adds or removes an equation of an already
registered function selects from the rows live at the call. -/
theorem same_request_selection :
    (liveRequests redefined 64 (Effects.loaded redefined)
      [call "let" [.var "u", call "add-atom" [sym "&self", row "f" [.var "x"] (call "b" [.var "x"])],
         call "f" [int 1]],
       call "let" [.var "u", call "remove-atom" [sym "&self", row "f" [.var "x"] (call "a" [.var "x"])],
         call "f" [int 1]]]).map observed =
      [.answers [call "a" [int 1], call "b" [int 1]], .answers [call "b" [int 1]]] := by
  decide +kernel

/-- The empty program. -/
def emptyProgram : Program where
  equations := []
  declarations := []

/-- A function first defined by a request is data in that request, which was
translated before `g` was registered, and a call in the next. -/
theorem first_definition_registers_for_later_requests :
    (liveRequests emptyProgram 64 (Effects.loaded emptyProgram)
      [call "let" [.var "u", call "add-atom" [sym "&self", row "g" [] (int 5)], call "g" []],
       call "g" []]).map observed =
      [.answers [call "g" []], .answers [int 5]] := by
  decide +kernel

/-- A new arity added by one request is a call in the next; the old arity still
selects its own equation. -/
theorem added_arity :
    (liveRequests redefined 64 (Effects.loaded redefined)
      [call "add-atom" [sym "&self", row "f" [.var "x", .var "y"] (call "c" [.var "x", .var "y"])],
       call "f" [int 1, int 2],
       call "f" [int 1]]).map observed =
      [.answers [truth], .answers [call "c" [int 1, int 2]], .answers [call "a" [int 1]]] := by
  decide +kernel

/-- Removing the last equation of a function makes its applications data again. -/
theorem removed_last_equation :
    (liveRequests redefined 64 (Effects.loaded redefined)
      [call "remove-atom" [sym "&self", row "f" [.var "x"] (call "a" [.var "x"])],
       call "f" [int 1]]).map observed =
      [.answers [truth], .answers [call "f" [int 1]]] := by
  decide +kernel

/-- An arity added by the request itself is unknown when the request was
translated: the call is an over-application, as SWI-PeTTa classifies it.
SWI-PeTTa's error lists the arities known when it is raised, `[1, 2]`; this
fault lists those known at translation, `[1]`. CeTTa calls `(c 1 2)`. -/
theorem same_request_arity_is_over_application :
    (liveRequests redefined 64 (Effects.loaded redefined)
      [call "let" [.var "u",
         call "add-atom" [sym "&self", row "f" [.var "x", .var "y"] (call "c" [.var "x", .var "y"])],
         call "f" [int 1, int 2]]]).map observed =
      [.fault (.overApplication "f" [1] 2)] := by
  decide +kernel

/-- An `=` row added to a private space is a row of that space, not an equation
of `&self`: `(pf 1)` stays data and `&self` holds no `pf` row. SWI-PeTTa
`e1db30d` gives the function to the private space, and CeTTa agrees;
`b74af1b` and `fea8317` stop at `(new-space)` inside `let`. -/
theorem private_space_row_is_not_an_equation :
    (liveRequests emptyProgram 64 (Effects.loaded emptyProgram)
      [call "let" [.var "s", call "new-space" [],
         call "add-atom" [.var "s", row "pf" [.var "x"] (call "p" [.var "x"])]],
       call "pf" [int 1],
       call "collapse" [call "match" [sym "&self", row "pf" [.var "x"] (.var "b"), .var "b"]]]).map
        observed =
      [.answers [truth], .answers [call "pf" [int 1]], .answers [.expression []]] := by
  decide +kernel

/-- `(= (h) (g))` -/
def consumer : Program where
  equations := [⟨"h", [], call "g" []⟩]
  declarations := []
  layout := [.equation]

/-- A stored body is classified with the request that runs it: `(h)` gives `(g)`
in the request that defines `g` and `5` in the next. The runtimes differ here:
SWI-PeTTa `e1db30d` translates `h` again as soon as `g` is defined and gives
`(g)`, `5`, `5`; `b74af1b`, `fea8317` and CeTTa keep `h` as loaded and give
`(g)` three times. -/
theorem body_classified_with_its_request :
    (liveRequests consumer 64 (Effects.loaded consumer)
      [call "h" [],
       call "let" [.var "u", call "add-atom" [sym "&self", row "g" [] (int 5)], call "h" []],
       call "h" []]).map observed =
      [.answers [call "g" []], .answers [call "g" []], .answers [int 5]] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.LiveEquations
