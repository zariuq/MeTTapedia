import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.SyntacticMerge

/-!
# Runs of the variant machine, by continuation: data, casts, tuples, calls and constructor nodes

`SyntacticMerge` gives the variant machine (`VStep`: HE's machine whose frontier steps carry the
syntactic merge) and `GoodV`: every run from a configuration finishes and publishes a given target.
The model's every-run results transfer to it as they stand (`SyntacticMerge.every_run_of_model`). A
program whose answers differ between the model and the variant machine (a declared branch of `if`)
needs runs of the variant machine built directly. This module gives the combinators for that, in the
same continuation form as `EveryRunFinishes`:

* `GoodRuns`, `GoodQuery`: every run of the variant machine from pending work on a value (from a
  query of a call) goes on to the target, under every continuation good on the answers.
* `goodv_data`: a data atom; `goodv_cast`: a data atom's cast under any demand, whose continuation
  also receives the type match that produced the result frame; `goodv_deliver_closed`.
* `goodv_branches`, `goodv_tuple`, `goodv_calls`: the tuple traversal and the calls continuation.
* `goodv_query_absent`: a query with an empty region returns the call.
* `goodv_equations`, `goodv_query_bodies`: a query whose rows have closed bodies: one work per row,
  each body run at its work's frame.
* `goodv_node`: a call whose root HE interprets as a tuple: the argument product, the calls of each
  combination, the publication; `goodv_constructor`: a head with no equation.
* `goodv_entry`: from the entry of a term.

Every step outside a query's frontier is unconstrained in the variant machine, so these are the
model's steps. The frontier step of `goodv_query_absent` returns no work; the frontier step of
`goodv_query_bodies` exists by `SyntacticMerge.frontier_represented`, and its works' records are not
consulted, since a closed body is read as it is at every frame.

## Controls

* `Controls.symbol_runs` (positive): a symbol runs to itself.
* `Controls.constructor_runs` (positive): `(pair yes no)` runs to itself through `goodv_node`.
* `Controls.target_fixed` (negative): the published target is fixed by the run: `(pair yes no)` does
  not go on to the target `[(pair no yes)]`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace VariantRuns

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom isEmptyOrError)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings EveryRunFinishes
  ScopedTransfer SyntacticMerge

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy} {target : List Atom}

/-! ## The continuation form -/

/-- **Every run of the variant machine from pending work on `v` goes on to `target`, with answers
`L`**: under every continuation stack good on every batch whose atoms are `L`, pending work on `v`
is good. -/
def GoodRuns (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (target : List Atom) (atoms : List Atom) (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    (∀ R : List Result, R.map (fun r => r.1.erase) = L →
      GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
    GoodV dispatch lookup policy target ⟨Space.ofList atoms,
      .work (.atom live scope v Atom.undefinedType activation), stack, emitted⟩

/-- **Every query of `(f vals)`, on every call value, goes on to `target`, with answers `A`.** -/
def GoodQuery (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (target : List Atom) (atoms : List Atom) (f : String) (vals A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) →
    ∀ (stack : List Continuation) (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = A →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      GoodV dispatch lookup policy target ⟨Space.ofList atoms,
        .work (.call live scope value Atom.undefinedType activation), stack, emitted⟩

/-- **From the entry of a term**: the top level drains the answers. -/
theorem goodv_entry {atoms : List Atom} {c : Atom} {L : List Atom}
    (runs : GoodRuns dispatch lookup policy L atoms (Entry.Value.ofAtom c) L) :
    GoodV dispatch lookup policy L (load (Space.ofList atoms) c Atom.undefinedType) :=
  runs [] [] Completed.Frame.empty [] [] fun R eraseR =>
    goodv_top R [] (by rw [List.nil_append]; exact eraseR)

/-! ## Data atoms and casts -/

/-- **A data atom**: its cast is the only step, and every cast result is the atom. -/
theorem goodv_data (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    GoodRuns dispatch lookup policy target atoms (Entry.Value.ofAtom d) [d] := by
  intro live scope activation stack emitted cont
  have entry : Entry.Rel policy.reentry (activation.read policy (Entry.Value.ofAtom d)).status
      (activation.read policy (Entry.Value.ofAtom d)).erase Atom.undefinedType .cast := by
    simp only [CompleteRun.read_data policy activation data, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  refine .step ⟨_, CompleteRun.cast_step_frame (dispatch := dispatch) (policy := policy) answers
    (Space.ofList atoms) data activation live scope stack emitted, True.intro⟩ ?_
  intro y step
  obtain ⟨model, -⟩ := step
  cases model with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered batch related =>
          have derived : Completed.AtomRel (Space.ofList atoms) dispatch lookup _ _ _ _ _ _
              (policy := policy) := .cast entered batch related
          obtain ⟨after, rfl⟩ := data_source contract data derived
          exact cont _ (by simp)
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-- **A data atom's cast under any demand and any lookup**: some answer of one type renews the
frame, every answer holds a type the demand accepts, and every cast result is the atom at a frame
reached by a type match of the demand with one of the answered types. -/
theorem goodv_cast {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {d E : Atom}
    (data : DataAtom d) (entry : Entry.Rel policy.reentry .active d E .cast) {frame : Frame}
    (firstStep : ∃ (T : Atom) (after : Frame),
      lookup (invocationTypeScope scope live d E frame.bindings) space frame.bindings d E [T] ∧
        Completed.Frame.TypeRenewRel policy E T frame after)
    (accepts : ∀ types, lookup (invocationTypeScope scope live d E frame.bindings) space
      frame.bindings d E types →
      ∃ actual ∈ types, ∃ output, policy.matching.Rel E actual frame.bindings output)
    (next : ∀ after : Frame,
      (∃ types actual, lookup (invocationTypeScope scope live d E frame.bindings) space
        frame.bindings d E types ∧ actual ∈ types ∧
          policy.matching.Rel E actual frame.bindings after.bindings) →
      GoodV dispatch lookup policy target ⟨space,
        .returning [(Entry.Value.ofAtom d, after)], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.atom live scope (Entry.Value.ofAtom d) E frame), stack, emitted⟩ := by
  obtain ⟨T, after, queried, renewed⟩ := firstStep
  refine .step ⟨_, ScopedIf.renewed_cast_step_any dispatch policy (answerable_of_data data).closed
    entry queried renewed stack emitted, True.intro⟩ ?_
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom d)).status
      (frame.read policy (Entry.Value.ofAtom d)).erase E .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  intro y step
  obtain ⟨model, -⟩ := step
  cases model with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry'
      | cast _ batch related =>
          rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
          cases batch with
          | success answered split _ matched =>
              obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
              obtain rfl := List.forall₂_nil_left_iff.mp rest
              have value : r.1 = Entry.Value.ofAtom d := by
                have payload := first.payload
                split at payload <;> exact payload
              have readout := first.readout
              obtain ⟨rv, rf⟩ := r
              simp only at value
              subst value
              simp only [Completed.rawResult, Prod.mk.injEq] at readout
              obtain ⟨-, rfl⟩ := readout
              refine next rf ⟨_, _, answered, ?_, matched⟩
              rw [split]
              simp
          | failure answered rejected =>
              obtain ⟨actual, member, output, matched⟩ := accepts _ answered
              exact (rejected actual member output matched).elim
      | atomTuple entered => cases Entry.functional entered entry'
      | atomFunction entered => cases Entry.functional entered entry'
      | atomFallback entered => cases Entry.functional entered entry'
      | atomSelectionFailed entered => cases Entry.functional entered entry'

/-- A data atom's cast, when the result frame is not needed. -/
theorem goodv_data_cast {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {d E : Atom}
    (data : DataAtom d) (entry : Entry.Rel policy.reentry .active d E .cast) {frame : Frame}
    (firstStep : ∃ (T : Atom) (after : Frame),
      lookup (invocationTypeScope scope live d E frame.bindings) space frame.bindings d E [T] ∧
        Completed.Frame.TypeRenewRel policy E T frame after)
    (accepts : ∀ types, lookup (invocationTypeScope scope live d E frame.bindings) space
      frame.bindings d E types →
      ∃ actual ∈ types, ∃ output, policy.matching.Rel E actual frame.bindings output)
    (next : ∀ after : Frame, GoodV dispatch lookup policy target ⟨space,
      .returning [(Entry.Value.ofAtom d, after)], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.atom live scope (Entry.Value.ofAtom d) E frame), stack, emitted⟩ :=
  goodv_cast data entry firstStep accepts fun after _ => next after

/-- A closed atom under an `Atom` demand is delivered as it is. -/
theorem goodv_deliver_closed {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {a : Atom}
    (closed : ∀ name, ¬ AtomOccurs a name) {frame : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning [(Entry.Value.ofAtom a, frame)], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.atom live scope (Entry.Value.ofAtom a) Atom.atomType frame), stack, emitted⟩ :=
  goodv_atom_demand (by rw [HERuns.read_closed policy frame closed]; exact next)

/-! ## Tuples -/

/-- **The branches of a tuple's head**: each answer's tail is a good tuple. -/
theorem goodv_branches (atoms : List Atom) {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ts : List (List Atom)}
    (tailGood : ∀ (live' : List Atom) (activation : Frame) (stack : List Continuation)
      (emitted : List Result),
      (∀ R : List Result, R.map (fun r => r.1.erase) = Ts.map Atom.expression →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
      GoodV dispatch lookup policy target ⟨Space.ofList atoms,
        .work (.tuple live' scope tail activation), stack, emitted⟩)
    (tailClean : ∀ c ∈ Ts, ∃ c0 cs, c = c0 :: cs ∧ Answerable c0) :
    ∀ (heads : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            heads.flatMap (fun h => Ts.map fun c => Atom.expression (h.1.erase :: c)) →
          GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms,
          .work (.branches live scope tail heads), stack, emitted⟩
  | [], _, stack, emitted, cont => goodv_branches_nil (cont [] rfl)
  | h :: hs, clean, stack, emitted, cont => by
      have hClean := clean h List.mem_cons_self
      apply goodv_branches_cons hClean.notStopped
      apply tailGood (h.1.erase :: live) h.2
        (.tupleTail h.1 :: .append (.branches live scope tail hs) :: stack) emitted
      intro Rt eraseRt
      apply goodv_tupleTail
      apply goodv_append
      apply goodv_branches atoms tailGood tailClean hs
        (fun x member => clean x (List.mem_cons_of_mem _ member))
        (.prepend (Rt.map (Completed.tuplePrepend h.1)) :: stack) emitted
      intro Rh eraseRh
      apply goodv_prepend
      apply cont
      have pointwise : ∀ r ∈ Rt, (Completed.tuplePrepend h.1 r).1.erase =
          HENested.prependAtom h.1.erase r.1.erase := by
        intro r member
        have inTs : r.1.erase ∈ Ts.map Atom.expression := by
          rw [← eraseRt]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        obtain ⟨c, cMem, cEq⟩ := List.mem_map.mp inTs
        obtain ⟨c0, cs, rfl, clean0⟩ := tailClean c cMem
        rw [tuplePrepend_erase_any h.1 cEq.symm clean0, ← cEq]
        rfl
      rw [List.map_append, eraseRh, List.flatMap_cons, List.map_map]
      congr 1
      have mapped : (Rt.map ((fun r : Result => r.1.erase) ∘ Completed.tuplePrepend h.1)) =
          (Rt.map fun r => r.1.erase).map (HENested.prependAtom h.1.erase) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro r member
        exact pointwise r member
      rw [mapped, eraseRt, List.map_map]
      rfl

/-- **The tuple traversal**, for every successor. -/
theorem goodv_tuple (atoms : List Atom) :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)), vs ≠ [] →
      List.Forall₂ (fun v L => GoodRuns dispatch lookup policy target atoms v L ∧
        ∀ a ∈ L, Answerable a) vs Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression →
          GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms,
          .work (.tuple live scope vs activation), stack, emitted⟩
  | [], _, nonempty, _ => absurd rfl nonempty
  | [v], Ls, _, related => by
      intro live scope activation stack emitted cont
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          apply goodv_tuple_singleton
          apply here.1 live scope activation (.singleton :: stack) emitted
          intro R eraseR
          apply goodv_singleton
          apply cont
          have clean := HENested.clean_of_erase eraseR here.2
          have singled : ∀ r ∈ R, Completed.tupleSingleton r = (.expression .active [r.1], r.2) := by
            intro r member
            unfold Completed.tupleSingleton
            rw [HENested.emptyOrError_false (clean r member)]
            rfl
          rw [List.map_map]
          have mapped : R.map ((fun r : Result => r.1.erase) ∘ Completed.tupleSingleton) =
              (R.map fun r => r.1.erase).map fun a => Atom.expression [a] := by
            rw [List.map_map]
            apply List.map_congr_left
            intro r member
            simp only [Function.comp_apply, singled r member, Entry.Value.erase, List.map_cons,
              List.map_nil]
          rw [mapped, eraseR, combos_singleton, List.map_map]
          rfl
  | v :: v2 :: rest, Ls, _, related => by
      intro live scope activation stack emitted cont
      cases related with
      | cons here later =>
          rename_i L Ls'
          have tailGood := goodv_tuple atoms (v2 :: rest) Ls' (List.cons_ne_nil _ _) later
          have tailClean : ∀ c ∈ combos Ls', ∃ c0 cs, c = c0 :: cs ∧ Answerable c0 := by
            intro c member
            have lengths := combos_length member
            have positive : Ls'.length = (v2 :: rest).length := (List.Forall₂.length_eq later).symm
            obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, c = c0 :: cs := by
              cases c with
              | nil =>
                  simp only [List.length_nil] at lengths
                  simp only [List.length_cons] at positive
                  omega
              | cons c0 cs => exact ⟨c0, cs, rfl⟩
            refine ⟨c0, cs, rfl, ?_⟩
            have allClean : ∀ L' ∈ Ls', ∀ a ∈ L', Answerable a := by
              intro L' member' a inside
              obtain ⟨t', both⟩ := forall₂_right_exists later L' member'
              exact both.2 a inside
            exact combos_answerable allClean _ member c0 List.mem_cons_self
          apply goodv_tuple_cons
          apply here.1 _ scope activation (.branches live scope (v2 :: rest) :: stack) emitted
          intro R eraseR
          apply goodv_branches_frame
          apply goodv_branches atoms (live := live) (fun live' activation' stack' emitted' cont' =>
            tailGood live' scope activation' stack' emitted' cont') tailClean R
            (HENested.clean_of_erase eraseR here.2) stack emitted
          intro R' eraseR'
          apply cont
          rw [eraseR']
          have flat : R.flatMap (fun h => (combos Ls').map fun c => Atom.expression (h.1.erase :: c)) =
              (R.map fun h => h.1.erase).flatMap
                (fun a => (combos Ls').map fun c => Atom.expression (a :: c)) := by
            rw [List.flatMap_map]
          rw [flat, eraseR]
          simp only [combos, List.map_flatMap, List.map_map]
          rfl

/-! ## Calls -/

/-- **The calls continuation over rows**, for every successor. -/
theorem goodv_calls (atoms : List Atom) {live : List Atom} {scope : List String} {f : String}
    (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        GoodQuery dispatch lookup policy target atoms f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) =
            rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) →
          GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms,
          .work (.calls live scope Atom.undefinedType rows), stack, emitted⟩
  | [], _, stack, emitted, cont => goodv_calls_nil (cont [] rfl)
  | r :: rs, queries, stack, emitted, cont => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      apply goodv_calls_cons
      apply query live scope r.2 r.1 erased
        (.append (.calls live scope Atom.undefinedType rs) :: stack) emitted
      intro Qr eraseQr
      apply goodv_append
      apply goodv_calls atoms Q rs (fun x member => queries x (List.mem_cons_of_mem _ member))
        (.prepend Qr :: stack) emitted
      intro Rs eraseRs
      apply goodv_prepend
      apply cont
      rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
      rfl

/-- **A query with an empty region**: `callAbsent` is the only step, returning the call. Its
frontier has no work, so the variant machine's step is the model's. -/
theorem goodv_query_absent {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (empty : regionBodies atoms f vals = []) :
    GoodQuery dispatch lookup policy target atoms f vals [.expression (.symbol f :: vals)] := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  have noBodies : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [empty]
    intro b member
    cases member
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies := HERuns.frontier_bodies ground activation.certified.satisfiable program noBodies
    frontier
  rw [empty] at bodies
  have none : works = [] := List.map_eq_nil_iff.mp bodies
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings [] := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callAbsent (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction vals) erased) frontier'),
    True.intro⟩ ?_
  intro y step
  obtain ⟨model, -⟩ := step
  cases model with
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

/-- **The equation loop over closed bodies**: each work's body is read as it is, evaluated under
the caller's demand, and the batches are concatenated in work order. The records of the works are
not consulted: a closed body is the same at every frame. -/
theorem goodv_equations (atoms : List Atom) {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => GoodRuns dispatch lookup policy target atoms
        (Entry.Value.ofAtom work.body) L ∧ BodyFacts work.body) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = Ls.flatten →
          GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms,
          .work (.equations live scope original Atom.undefinedType activation works), stack,
          emitted⟩
  | [], Ls, _, related, stack, emitted, cont => by
      cases related
      exact goodv_equations_nil (cont [] rfl)
  | work :: works, Ls, unifiers, related, stack, emitted, cont => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨goodBody, facts⟩ := here
          obtain ⟨output₀, sameBindings₀, unified₀⟩ := unifiers work List.mem_cons_self
          refine .step ⟨_, .internal (.equationsCons sameBindings₀ unified₀), True.intro⟩ ?_
          intro y step
          obtain ⟨model, -⟩ := step
          cases model with
          | internal l =>
              cases l with
              | equationsCons sameBindings _ =>
                  rw [HERuns.read_closed policy _ facts.closed]
                  apply goodv_boundary_producer (facts.notFunction policy)
                  apply goodv_boundaryBatch_frame
                  apply goodv_boundaryBatch_cons
                  apply goodv_boundary_returned
                  apply goodv_returned_evaluate
                    (by rw [Entry.Value.erase_ofAtom]; exact facts.notRefused)
                    (by rw [Entry.Value.erase_ofAtom]; exact facts.notStopped)
                  refine goodBody _ _ _ _ _ ?_
                  intro Rb eraseRb
                  apply goodv_append
                  apply goodv_boundaryBatch_nil
                  apply goodv_prepend
                  apply goodv_append
                  apply goodv_equations atoms works Ls'
                    (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
                    (.prepend (Rb ++ []) :: stack) emitted
                  intro Rs eraseRs
                  apply goodv_prepend
                  apply cont
                  rw [List.append_nil, List.map_append, eraseRb, eraseRs, List.flatten_cons]

/-- **A query whose rows have closed bodies**: every variant frontier fires, with one work per row
of the call's region, and each body runs at its work's frame. Its answers are the bodies' answers in
row order. -/
theorem goodv_query_bodies {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (nonempty : regionBodies atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => GoodRuns dispatch lookup policy target atoms
      (Entry.Value.ofAtom b) L ∧ BodyFacts b) (regionBodies atoms f vals) Ls) :
    GoodQuery dispatch lookup policy target atoms f vals Ls.flatten := by
  intro live scope activation value erased stack emitted cont
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  have fixed : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    intro b member
    obtain ⟨L, both⟩ := forall₂_left_exists bodies b member
    exact both.2.fixed
  have fromFrontier : ∀ works : List EquationWork,
      EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
        (.expression (.symbol f :: vals)) activation.bindings works →
      GoodV dispatch lookup policy target ⟨Space.ofList atoms,
        .work (.equations live scope value Atom.undefinedType activation works), stack,
        emitted⟩ := by
    intro works frontier
    have bodiesEq := HERuns.frontier_bodies ground activation.certified.satisfiable program fixed
      frontier
    have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
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
    have related : List.Forall₂ (fun work L => GoodRuns dispatch lookup policy target atoms
        (Entry.Value.ofAtom work.body) L ∧ BodyFacts work.body) works Ls := by
      have viaBodies := bodies
      rw [← bodiesEq] at viaBodies
      exact List.forall₂_map_left_iff.mp viaBodies
    exact goodv_equations atoms works Ls unifiers related stack emitted cont
  obtain ⟨works0, frontier0⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: vals)) activation.bindings
  have bodies0 := HERuns.frontier_bodies ground activation.certified.satisfiable program fixed
    frontier0
  have nonempty0 : works0 ≠ [] := by
    intro isEmpty
    subst isEmpty
    exact nonempty bodies0.symm
  obtain ⟨works1, syn1, same1⟩ := frontier_represented frontier0
  have syn1' : SynFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live) value.erase
      activation.bindings works1 := by
    rw [erased]
    exact syn1
  refine .step ⟨_, vstep_call_iff.mpr ⟨HERuns.value_not_error head.head erased,
    HERuns.value_nonGrounded head.notHost (head.instruction vals) erased, syn1',
    same_length same1 nonempty0⟩⟩ ?_
  intro y step
  obtain ⟨model, -⟩ := step
  cases model with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed (HERuns.value_not_error head.head erased)
      | callEmbedded _ _ instruction =>
          rw [erased, head.instruction vals] at instruction
          cases instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have bodiesW := HERuns.frontier_bodies ground activation.certified.satisfiable program
            fixed frontierEmpty
          exact absurd bodiesW.symm nonempty
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-! ## Constructor nodes -/

/-- **A call whose root HE interprets as a tuple**: the tuple entry or the fallback (with no
diagnostics), the argument product, the calls of each combination, the publication. -/
theorem goodv_node (contract : LookupContract lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    (headGood : GoodRuns dispatch lookup policy target atoms (.symbol f) [.symbol f])
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => GoodRuns dispatch lookup policy target atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, GoodQuery dispatch lookup policy target atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    GoodRuns dispatch lookup policy target atoms (.expression readiness (.symbol f :: vs))
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
      Atom.undefinedType .interpret := by
    rw [readV, eraseV]
    exact .expression (call_not_stopped head) undefined_not_raw interpreted
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol f).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences untyped
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope
        (activation.read policy (.expression readiness (.symbol f :: vs))).erase
        (.symbol f) Atom.undefinedType activation outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  -- the publication, then the caller's continuation
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol f :: ts)) :: stack, emitted⟩ := by
    intro R eraseR
    apply goodv_publish (HENested.clean_of_erase eraseR answerableAll)
    apply cont
    rw [publish_erase, eraseR]
  -- the rows of the argument product, then their calls
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning R, rest, emitted⟩) →
      ∀ rows : List Result, rows.map (fun r => r.1.erase) =
          (combos ([.symbol f] :: Ls)).map Atom.expression →
        GoodV dispatch lookup policy target ⟨Space.ofList atoms, .returning rows,
          .calls live scope Atom.undefinedType :: rest, emitted⟩ := by
    intro rest restGood rows eraseRows
    rw [combos_head] at eraseRows
    apply goodv_calls_frame
    have queries : ∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        GoodQuery dispatch lookup policy target atoms f vals (Q vals) := by
      intro r member
      have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
        rw [← eraseRows]
        exact List.mem_map.mpr ⟨r, member, rfl⟩
      rw [List.map_map] at inRows
      obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
      exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
    apply goodv_calls atoms Q rows queries rest emitted
    intro R eraseR
    apply restGood
    rw [eraseR]
    have viaAtoms : rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (rows.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseRows, List.map_map, List.flatMap_map]
    rfl
  have argsAll : List.Forall₂ (fun v L => GoodRuns dispatch lookup policy target atoms v L ∧
      ∀ a ∈ L, Answerable a) (Entry.Value.symbol f :: vs) ([.symbol f] :: Ls) :=
    .cons ⟨headGood, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args
  refine .step ⟨_, .internal (LocalStepWith.atomTuple entry readV occurrences), True.intro⟩ ?_
  intro y step
  obtain ⟨model, -⟩ := step
  cases model with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped _ =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [published]
          exact goodv_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
            argsAll _ scope activation _ emitted (afterRows _ afterPublish)
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
          refine goodv_tuple atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
            argsAll _ scope activation _ emitted (afterRows _ ?_)
          intro R eraseR
          apply goodv_diagnostics
          simp only [Completed.diagnosticResults, List.map_nil, List.append_nil]
          exact afterPublish R eraseR
      | atomSelectionFailed _ shaped chosen =>
          rw [readV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp at exhausted

/-- **A constructor node**: a call whose head has no equation and no declared type, over good
arguments: every combination of the arguments' answers answers itself. -/
theorem goodv_constructor (answers : AnswersUndefined lookup) (contract : LookupContract lookup)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {f : String} (head : NodeHead dispatch atoms f)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    {ts : List Atom} {Ls : List (List Atom)}
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    {vs : List Entry.Value} (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => GoodRuns dispatch lookup policy target atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls) :
    GoodRuns dispatch lookup policy target atoms (.expression .active (.symbol f :: vs))
      ((combos Ls).map fun vals => Atom.expression (.symbol f :: vals)) := by
  have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
    intro L member a inside
    obtain ⟨v, both⟩ := forall₂_right_exists args L member
    exact both.2 a inside
  have headGood : GoodRuns dispatch lookup policy target atoms (.symbol f) [.symbol f] := by
    have runs := goodv_data (dispatch := dispatch) (policy := policy) (target := target) answers
      contract atoms head.head
    simpa only [Entry.Value.ofAtom] using runs
  have built := goodv_node (dispatch := dispatch) (policy := policy) (target := target) contract
    head.head head.untyped closed headGood (Or.inr rfl) erased args
    (fun vals => [.expression (.symbol f :: vals)])
    (fun vals member => ⟨goodv_query_absent program head (combos_answerable allClean vals member)
        (regionBodies_nil_of_no_equation vals noEquation),
      fun a inside => by
        rw [List.mem_singleton] at inside
        subst inside
        exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  have same : (combos Ls).flatMap (fun vals => [Atom.expression (.symbol f :: vals)]) =
      (combos Ls).map fun vals => Atom.expression (.symbol f :: vals) := by
    induction combos Ls with
    | nil => rfl
    | cons c cs ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]
  rw [← same]
  exact built

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)
open IfEveryRun (ifProgram)

/-- **Positive control**: a symbol runs to itself on the variant machine. -/
theorem symbol_runs (policy : Policy) :
    GoodV noHost Completed.scopedLookup policy [sym "yes"]
      (load (Space.ofList ifProgram) (sym "yes") Atom.undefinedType) :=
  goodv_entry (goodv_data scoped_answers scoped_contract ifProgram (.symbol (by decide) (by decide)))

theorem pair_head : NodeHead noHost ifProgram "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem pair_value : Entry.Value.ofAtom (app "pair" [sym "yes", sym "no"]) =
    .expression .active (.symbol "pair" :: [Entry.Value.ofAtom (sym "yes"),
      Entry.Value.ofAtom (sym "no")]) := by
  simp [Entry.Value.ofAtom]

/-- **Positive control**: `(pair yes no)` runs to itself on the variant machine, through the
constructor node. -/
theorem constructor_runs (policy : Policy) :
    GoodV noHost Completed.scopedLookup policy [app "pair" [sym "yes", sym "no"]]
      (load (Space.ofList ifProgram) (app "pair" [sym "yes", sym "no"]) Atom.undefinedType) := by
  apply goodv_entry
  rw [pair_value]
  have built := goodv_constructor (dispatch := noHost) (policy := policy)
    (target := [app "pair" [sym "yes", sym "no"]]) scoped_answers scoped_contract
    (scoped_consFree IfEveryRun.if_program) pair_head (by decide +kernel)
    (ts := [sym "yes", sym "no"]) (Ls := [[sym "yes"], [sym "no"]])
    (fun name occurs => by
      cases occurs with
      | expression member inner =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> cases inner)
    (vs := [Entry.Value.ofAtom (sym "yes"), Entry.Value.ofAtom (sym "no")])
    (by simp [Entry.Value.erase_ofAtom])
    (.cons ⟨goodv_data scoped_answers scoped_contract ifProgram (.symbol (by decide) (by decide)),
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data (.symbol (by decide) (by decide))⟩
      (.cons ⟨goodv_data scoped_answers scoped_contract ifProgram
          (.symbol (by decide) (by decide)),
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data (.symbol (by decide) (by decide))⟩ .nil))
  simpa [combos] using built

/-- **Negative control**: the target is fixed by the run: `(pair yes no)` does not go on to the
target `[(pair no yes)]`. -/
theorem target_fixed (policy : Policy) :
    ¬ GoodV noHost Completed.scopedLookup policy [app "pair" [sym "no", sym "yes"]]
      (load (Space.ofList ifProgram) (app "pair" [sym "yes", sym "no"]) Atom.undefinedType) := by
  intro wrong
  obtain ⟨⟨answers, run⟩, _⟩ := (constructor_runs policy).every_run
  have published := wrong.every_run.2.1 answers run
  have actual := (constructor_runs policy).every_run.2.1 answers run
  rw [actual] at published
  simp at published

end Controls

#print axioms goodv_entry
#print axioms goodv_data
#print axioms goodv_cast
#print axioms goodv_tuple
#print axioms goodv_calls
#print axioms goodv_query_absent
#print axioms goodv_equations
#print axioms goodv_query_bodies
#print axioms goodv_node
#print axioms goodv_constructor
#print axioms Controls.symbol_runs
#print axioms Controls.constructor_runs
#print axioms Controls.target_fixed

end VariantRuns

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
