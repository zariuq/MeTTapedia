import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRunFinishes

/-!
# HE's `Atom` demand passes its argument unevaluated

HE's standard library declares `if` as `(-> Bool Atom Atom $t)` and `let` as
`(-> Atom %Undefined% Atom %Undefined%)`. A position demanded as `Atom` is passed to the function
without evaluation; this is how HE's `if` leaves the branch it does not take alone. PeTTa reaches
the same behaviour by a special form: it evaluates the condition, then only the chosen branch.

This module proves HE's half of that mechanism, at both levels of HE's semantics, for every atom:

* `atom_demand_deliver`: every atom enters an `Atom` demand by delivery (`Entry.Rel.pass`, or
  `Entry.Rel.stopped` for `Empty` and errors), so by no other action.
* `atom_demand_source`: every derivation of HE's completed relation under an `Atom` demand returns
  exactly the read argument, at the same frame.
* `atom_demand_step`, `atom_demand_fine`: on HE's machine, delivery is the only step of pending work
  under an `Atom` demand, and the work finishes under every continuation that finishes on it.
* `atom_demand_every_run`: loaded under an `Atom` demand, every atom `c` finishes on every run, and
  every complete run publishes `c` itself.
* `atom_demand_accepts`, `variable_meets_undefined`: in HE's type checks an `Atom` demand accepts every
  type, and a type-variable demand (the return type `$t` of `if`) accepts an undeclared result,
  with the bindings unchanged.

PeTTa's `if` on the same program is checked by evaluation at small fuel (`Controls.petta_if_lazy`,
`Controls.petta_if_non_boolean`).

HE's end-to-end `if` (admission of `(-> Bool Atom Atom $t)`, the function path, the query, the cast
under `$t`) is not proved here: casting `if` against its own arrow matches `$t` with itself, which
records an equality and renews the frame, unlike the closed arrow of `TypedEveryRun`.

## Controls

* `Controls.loop_by_demand` (positive and negative, one atom): `(loop)` on `{(= (loop) (loop))}` under
  an `Atom` demand finishes on every run and publishes `(loop)`; under `%Undefined%` HE has an
  infinite run.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace AtomDemands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun EveryRunFinishes

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-! ## Entry -/

/-- **Every atom enters an `Atom` demand by delivery.** -/
theorem atom_demand_deliver {reentry : Entry.ReentryPolicy} {status : Entry.Status} (atom : Atom) :
    Entry.Rel reentry status atom Atom.atomType .deliver := by
  by_cases stopped : IsEmptyOrErrorRel atom
  · exact .stopped stopped
  · cases atom with
    | symbol name => exact .pass stopped (.symbol name) (Or.inl rfl)
    | var name => exact .pass stopped (.variable name) (Or.inl rfl)
    | grounded value => exact .pass stopped (.grounded value) (Or.inl rfl)
    | expression atoms => exact .pass stopped (.expression atoms) (Or.inl rfl)

/-- Delivery is the only action under an `Atom` demand. -/
theorem atom_demand_only {reentry : Entry.ReentryPolicy} {status : Entry.Status} {atom : Atom}
    {action : Entry.Action} (entered : Entry.Rel reentry status atom Atom.atomType action) :
    action = .deliver :=
  Entry.functional entered (atom_demand_deliver atom)

/-! ## HE's completed relation -/

/-- **Every derivation under an `Atom` demand delivers the read argument**, at its frame. -/
theorem atom_demand_source {space : Space} {live : List Atom} {scope : List String}
    {value : Entry.Value} {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel space dispatch lookup live scope value Atom.atomType frame results
      (policy := policy)) :
    results = [(frame.read policy value, frame)] := by
  cases derived with
  | delivered _ => rfl
  | cast entered => cases atom_demand_only entered
  | tuple entered => cases atom_demand_only entered
  | function entered => cases atom_demand_only entered
  | fallback entered => cases atom_demand_only entered
  | selectionFailed entered => cases atom_demand_only entered

/-! ## HE's machine -/

/-- **Delivery is the only step of pending work under an `Atom` demand.** -/
theorem atom_demand_step {space : Space} {live : List Atom} {scope : List String}
    {value : Entry.Value} {activation : Frame} {stack : List Continuation} {emitted : List Result}
    {y : HEConfig}
    (step : HEStep dispatch lookup policy
      ⟨space, .work (.atom live scope value Atom.atomType activation), stack, emitted⟩ y) :
    y = ⟨space, .returning [(activation.read policy value, activation)], stack, emitted⟩ := by
  cases step with
  | internal l =>
      cases l with
      | delivered _ => rfl
      | cast entered => cases atom_demand_only entered
      | atomTuple entered => cases atom_demand_only entered
      | atomFunction entered => cases atom_demand_only entered
      | atomFallback entered => cases atom_demand_only entered
      | atomSelectionFailed entered => cases atom_demand_only entered

/-- **Pending work under an `Atom` demand finishes** whenever its continuation finishes on the read
argument. -/
theorem atom_demand_fine {space : Space} {live : List Atom} {scope : List String}
    {value : Entry.Value} {activation : Frame} {stack : List Continuation} {emitted : List Result}
    (next : Fine dispatch lookup policy
      ⟨space, .returning [(activation.read policy value, activation)], stack, emitted⟩) :
    Fine dispatch lookup policy
      ⟨space, .work (.atom live scope value Atom.atomType activation), stack, emitted⟩ :=
  fine_det (.internal (.delivered (atom_demand_deliver _))) (fun _ step => atom_demand_step step)
    next

/-- A complete run from a loaded atom, under any demand, gives HE's completed relation. -/
theorem complete_source_at {space : Space} {c expected : Atom} {E : List Result}
    (run : Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c expected)
      ⟨space, .returning [], [], E⟩) :
    Completed.AtomRel space dispatch lookup [] [] (Entry.Value.ofAtom c) expected
      Completed.Frame.empty E (policy := policy) := by
  have final : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.SourceRel
      dispatch lookup policy ⟨space, .returning [], [], E⟩ E :=
    ⟨[], [], .returning [], .nil [], (List.append_nil E).symm⟩
  have initial := Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.steps_source_back
    run final
  exact (Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.initial_source_iff space
    dispatch lookup policy (.atom [] [] (Entry.Value.ofAtom c) expected Completed.Frame.empty) E).mp
    initial

/-- **Every atom under an `Atom` demand, on every run**: every run finishes, and every complete run
publishes the atom itself, whatever the program, dispatch, lookup and policy. -/
theorem atom_demand_every_run (space : Space) (c : Atom) :
    Fine dispatch lookup policy (load space c Atom.atomType) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.atomType)
          ⟨space, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [c] := by
  refine ⟨atom_demand_fine (fine_top _ []), fun emitted run => ?_⟩
  rw [atom_demand_source (complete_source_at run)]
  simp [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]

/-! ## Type checks -/

/-- **An `Atom` demand accepts every type**, with the bindings unchanged. -/
theorem atom_demand_accepts (actual : Atom) (frame : Frame) :
    ∃ output, policy.matching.Rel Atom.atomType actual frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (.atomLeft _ _)⟩

/-- **A type-variable demand accepts an undeclared result**, with the bindings unchanged. -/
theorem variable_meets_undefined (name : String) (frame : Frame) :
    ∃ output, policy.matching.Rel (.var name) Atom.undefinedType frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (.undefinedRight _ _)⟩

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule loopRows)
open WholeRunWords.Double (noHost)

/-- **One atom, two demands.** `(loop)` on `{(= (loop) (loop))}`: under an `Atom` demand every run
finishes and every complete run publishes `(loop)` itself; under `%Undefined%` HE has an infinite
run. -/
theorem loop_by_demand (policy : Policy) :
    Fine noHost Completed.rawLookup policy
        (load (Space.ofList loopRows) (app "loop" []) Atom.atomType) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList loopRows) (app "loop" []) Atom.atomType)
            ⟨Space.ofList loopRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [app "loop" []]) ∧
      ¬ Acc (fun b a => HEStep noHost Completed.rawLookup policy a b)
        (load (Space.ofList loopRows) (app "loop" []) Atom.undefinedType) :=
  ⟨(atom_demand_every_run _ _).1, (atom_demand_every_run _ _).2,
    (EveryRunFinishes.Controls.loop_diverges policy).1⟩

/-- HE's standard-library `if` with `(= (loop) (loop))`:
`{(: if (-> Bool Atom Atom $t)), (= (if True $then $else) $then), (= (if False $then $else) $else),
(= (loop) (loop))}`. -/
abbrev ifRows : List Atom :=
  [.expression [.symbol ":", sym "if",
      .expression [.symbol "->", sym "Bool", Atom.atomType, Atom.atomType, .var "t"]],
   rule (app "if" [.grounded (.bool true), .var "then", .var "else"]) (.var "then"),
   rule (app "if" [.grounded (.bool false), .var "then", .var "else"]) (.var "else"),
   rule (app "loop" []) (app "loop" [])]

/-- **PeTTa's `if` does not evaluate the branch it does not take**: `(if True yes (loop))` yields
`yes` and `(if False (loop) no)` yields `no`, from fuel `10` on. -/
theorem petta_if_lazy :
    (∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifRows) n
      (Streaming.enter { state := store ifRows }
        (app "if" [.grounded (.bool true), sym "yes", app "loop" []]))) = [sym "yes"]) ∧
      ∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifRows) n
        (Streaming.enter { state := store ifRows }
          (app "if" [.grounded (.bool false), app "loop" [], sym "no"]))) = [sym "no"] := by
  have yesDone : (Streaming.advance (translate ifRows) 10 (Streaming.enter { state := store ifRows }
      (app "if" [.grounded (.bool true), sym "yes", app "loop" []]))).agenda.length = 0 := by
    decide +kernel
  have yesValue : Streaming.values (Streaming.advance (translate ifRows) 10
      (Streaming.enter { state := store ifRows }
        (app "if" [.grounded (.bool true), sym "yes", app "loop" []]))) = [sym "yes"] := by
    decide +kernel
  have noDone : (Streaming.advance (translate ifRows) 10 (Streaming.enter { state := store ifRows }
      (app "if" [.grounded (.bool false), app "loop" [], sym "no"]))).agenda.length = 0 := by
    decide +kernel
  have noValue : Streaming.values (Streaming.advance (translate ifRows) 10
      (Streaming.enter { state := store ifRows }
        (app "if" [.grounded (.bool false), app "loop" [], sym "no"]))) = [sym "no"] := by
    decide +kernel
  refine ⟨fun n bigger => ?_, fun n bigger => ?_⟩
  · rw [advance_stable (List.eq_nil_of_length_eq_zero yesDone) n bigger]
    exact yesValue
  · rw [advance_stable (List.eq_nil_of_length_eq_zero noDone) n bigger]
    exact noValue

/-- **PeTTa sends every answer other than `True` to the else branch**: `(if Foo yes no)` yields `no`
from fuel `10` on. HE's `if` has equations for `True` and `False` only. -/
theorem petta_if_non_boolean :
    ∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifRows) n
      (Streaming.enter { state := store ifRows } (app "if" [sym "Foo", sym "yes", sym "no"]))) =
      [sym "no"] := by
  have done : (Streaming.advance (translate ifRows) 10 (Streaming.enter { state := store ifRows }
      (app "if" [sym "Foo", sym "yes", sym "no"]))).agenda.length = 0 := by
    decide +kernel
  have value : Streaming.values (Streaming.advance (translate ifRows) 10
      (Streaming.enter { state := store ifRows } (app "if" [sym "Foo", sym "yes", sym "no"]))) =
      [sym "no"] := by
    decide +kernel
  intro n bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero done) n bigger]
  exact value

end Controls

#print axioms atom_demand_deliver
#print axioms atom_demand_source
#print axioms atom_demand_step
#print axioms atom_demand_fine
#print axioms complete_source_at
#print axioms atom_demand_every_run
#print axioms atom_demand_accepts
#print axioms variable_meets_undefined
#print axioms Controls.loop_by_demand
#print axioms Controls.petta_if_lazy
#print axioms Controls.petta_if_non_boolean

end AtomDemands

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
