import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedEveryRun

/-!
# Grounded operations without a value: HE leaves the call, PeTTa faults, on every run

`GroundedTables` names the operations where HE's integer dispatch has no value
(`incorrectArgument`) and PeTTa's primitive raises a fault. Here the difference is read on both
machines, for every complete run of HE's world machine.

* `he_unreduced_W`, `unreduced_source_W`: for a host operation of HE's integer dispatch on two data
  atoms with no value, HE's grounded call takes `callGroundedDone` with the `incorrectArgument`
  plan (`Completed.NativeOutcomeRel.incorrectArgument`), which returns the call itself; every
  derivation of the call does so.
* `Controls.non_numeric_every_run`: `(+ a 4)`: every complete run of HE's world machine publishes
  `(+ a 4)`; PeTTa's run stops at the uncaught `invalidArguments` fault, with no value.
* `Controls.zero_divisor_every_run`: `(% 7 0)`: every complete HE run publishes `(% 7 0)`; PeTTa
  stops at the `zeroDivisor` fault, with no value.

The reason is one design split: HE's grounded dispatch reports an operation without a value and
HE's machine keeps the unreduced call as data; PeTTa's primitive raises, and with no enclosing
handler the request has no answer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundedDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load WorldSteps)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables GroundedTables GroundedRuns
  GroundedEveryRun

variable {minimal : Minimal.Services} {lookup : CastLookup} {policy : Policy}

/-- **HE's world machine on a host operation without a value**: the tuple entry, the grounded call
with the `incorrectArgument` plan returning the call itself, and the publication. -/
theorem he_unreduced_W (minimal : Minimal.Services) (answers : AnswersUndefined lookup)
    {atoms : List Atom} {op : String} (executable : heDispatch.executable (.symbol op))
    (head : DataAtom (.symbol op)) {u v : Atom} (uData : DataAtom u) (vData : DataAtom v)
    (incorrect : heOutcome (.symbol op) [u, v] = .incorrectArgument)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) :
    HEEvaluatesW minimal lookup policy atoms (.expression [.symbol op, u, v])
      [.expression [.symbol op, u, v]] := by
  intro live scope activation stack emitted
  have items : ∀ x ∈ Atom.symbol op :: [u, v], DataAtom x := by
    intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact head
    · exact uData
    · exact vData
  have clean : ∀ r ∈ [(callValue op [u, v], activation)], Answerable r.1.erase := by
    intro r member
    rw [List.mem_singleton] at member
    subst member
    rw [callValue_erase]
    exact call_answerable head fun x member => items x (List.mem_cons_of_mem _ member)
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := heDispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression [.symbol op, u, v]) [(callValue op [u, v], activation)] clean stack emitted
  refine ⟨published, by rw [erased]; simp [callValue_erase], ?_⟩
  have produced : (services minimal).groundedAt (Space.ofList atoms) () live scope activation
      (callValue op [u, v]) .incorrectArgument () :=
    ⟨.symbol op, [u, v], .incorrectArgument, callValue_erase op [u, v], incorrect.symm, rfl⟩
  have planned : Completed.NativeOutcomeRel policy heDispatch (.symbol op) [u, v]
      (callValue op [u, v]) (some Atom.undefinedType) activation .incorrectArgument
      (.done [(callValue op [u, v], activation)]) :=
    .incorrectArgument
  have notError : ¬ IsErrorRel (callValue op [u, v]).erase :=
    HERuns.value_not_error head (callValue_erase op [u, v])
  refine .trans (lift_path minimal (HERuns.call_entry_steps answers items untyped live scope
    activation stack emitted)) ?_
  refine .head (.internal
    (Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.WorldLocalStepWith.callGroundedDone
      (callValue_erase op [u, v]) executable notError produced planned)) ?_
  exact lift_path minimal finish

/-- **Every derivation of a host operation without a value returns the call itself.** -/
theorem unreduced_source_W {atoms : List Atom} {op : String}
    (executable : heDispatch.executable (.symbol op)) (head : DataAtom (.symbol op)) {u v : Atom}
    (incorrect : heOutcome (.symbol op) [u, v] = .incorrectArgument) {live : List Atom}
    {scope : List String} {after : Frame} {children : List Result} {w₁ w₂ : Unit}
    (called : Completed.Stateful.CallRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
      (callValue op [u, v]) Atom.undefinedType after children w₂ (policy := policy)) :
    children = [(callValue op [u, v], after)] := by
  have host : Minimal.HostCall heDispatch (callValue op [u, v]).erase :=
    ⟨.symbol op, [u, v], callValue_erase op [u, v], executable⟩
  have outcomeOf : ∀ {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (services minimal).groundedAt (Space.ofList atoms) w₃ live scope after
        (callValue op [u, v]) outcome w₄ → outcome = .incorrectArgument := by
    intro outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [callValue_erase] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    have same : raw = heOutcome (.symbol op) [u, v] := executed
    rw [same, incorrect]
    rfl
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head (callValue_erase op _))
  | embedded _ notHost _ _ _ => exact absurd host notHost
  | absent _ nonGrounded _ => exact absurd host nonGrounded.1
  | equations _ nonGrounded _ _ _ => exact absurd host nonGrounded.1
  | groundedDone _ _ _ produced planned =>
      rw [outcomeOf produced] at planned
      cases planned
      rfl
  | groundedResume _ _ _ produced planned _ =>
      rw [outcomeOf produced] at planned
      cases planned

/-- **Every complete run of HE's world machine on a host operation without a value publishes the
call itself.** -/
theorem unreduced_every_run (minimal : Minimal.Services) (contract : LookupContract lookup)
    {atoms : List Atom} {op : String} (executable : heDispatch.executable (.symbol op))
    (head : DataAtom (.symbol op)) {u v : Atom} (uData : DataAtom u) (vData : DataAtom v)
    (incorrect : heOutcome (.symbol op) [u, v] = .incorrectArgument)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = [])
    (emitted : List Result)
    (run : WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
      (WorldConfiguration.ofReadOnly
        (load (Space.ofList atoms) (.expression [.symbol op, u, v]) Atom.undefinedType))
      (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩)) :
    emitted.map (fun r => r.1.erase) = [.expression [.symbol op, u, v]] := by
  have items : ∀ a ∈ [u, v], DataAtom a := by
    intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact uData
    · exact vData
  obtain ⟨after, children, selected, w₁, w₂, called, chosen, erased⟩ :=
    call_source_W contract head items untyped (complete_source_W run)
  rw [unreduced_source_W executable head incorrect called] at chosen
  exact single_call_published (call_answerable head items) chosen erased

/-- The fault a stopped PeTTa run holds: its one remaining job is a fault at the root. -/
def stoppedAt : List Streaming.Job → Option Effects.Fault
  | [.execute ⟨.fault reason, []⟩] => some reason
  | _ => none

namespace Controls

open AnswerBags.Controls (sym app)

theorem plus_executable : heDispatch.executable (.symbol "+") := ⟨"+", rfl, by decide⟩
theorem mod_executable : heDispatch.executable (.symbol "%") := ⟨"%", rfl, by decide⟩

/-- **Non-numeric argument, on both machines**: `(+ a 4)`. A complete run of HE's world machine
exists, and every complete run publishes `(+ a 4)`; PeTTa's run stops at the uncaught
`invalidArguments` fault, with no value. -/
theorem non_numeric_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [sym "a", num 4])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "+" [sym "a", num 4])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [app "+" [sym "a", num 4]]) ∧
      stoppedAt (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "+" [sym "a", num 4]))).agenda =
          some (.invalidArguments "+") ∧
      Streaming.values (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "+" [sym "a", num 4]))) = [] := by
  have head : DataAtom (.symbol "+") := .symbol (by decide) (by decide)
  have aData : DataAtom (sym "a") := .symbol (by decide) (by decide)
  have incorrect : heOutcome (.symbol "+") [sym "a", num 4] = .incorrectArgument := rfl
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "+")) = [] := rfl
  obtain ⟨R, eraseR, path⟩ := he_unreduced_W (policy := policy) minimal raw_answers (atoms := [])
    plus_executable head aData (.grounded _) incorrect untyped [] [] Completed.Frame.empty [] []
  refine ⟨⟨⟨R, path.trans (lift_path minimal (HERuns.publish_all _ R []))⟩,
    fun emitted run => unreduced_every_run minimal raw_contract plus_executable head aData
      (.grounded _) incorrect untyped emitted run⟩, by decide +kernel, by decide +kernel⟩

/-- **Division by zero, on both machines**: `(% 7 0)`. A complete run of HE's world machine exists,
and every complete run publishes `(% 7 0)`; PeTTa's run stops at the `zeroDivisor` fault, with no
value. -/
theorem zero_divisor_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "%" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList []) (app "%" [num 7, num 0])
            Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [app "%" [num 7, num 0]]) ∧
      stoppedAt (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "%" [num 7, num 0]))).agenda =
          some .zeroDivisor ∧
      Streaming.values (Streaming.advance (translate []) 30
        (Streaming.enter { state := store [] } (app "%" [num 7, num 0]))) = [] := by
  have head : DataAtom (.symbol "%") := .symbol (by decide) (by decide)
  have incorrect : heOutcome (.symbol "%") [num 7, num 0] = .incorrectArgument := by decide
  have untyped : (Space.ofList []).atoms.filter (typeRegion (.symbol "%")) = [] := rfl
  obtain ⟨R, eraseR, path⟩ := he_unreduced_W (policy := policy) minimal raw_answers (atoms := [])
    mod_executable head (.grounded _) (.grounded _) incorrect untyped [] [] Completed.Frame.empty [] []
  refine ⟨⟨⟨R, path.trans (lift_path minimal (HERuns.publish_all _ R []))⟩,
    fun emitted run => unreduced_every_run minimal raw_contract mod_executable head (.grounded _)
      (.grounded _) incorrect untyped emitted run⟩, by decide +kernel, by decide +kernel⟩

end Controls

#print axioms he_unreduced_W
#print axioms unreduced_source_W
#print axioms unreduced_every_run
#print axioms Controls.non_numeric_every_run
#print axioms Controls.zero_divisor_every_run

end GroundedDifferences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
