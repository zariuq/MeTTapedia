import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.CompoundBindings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedEveryRun

/-!
# Arithmetic in nested positions, with compound bindings, on every run of HE's world machine

`GroundedEveryRun` compares HE's world machine with PeTTa on integer operations whose arguments are
literals, in flat bodies. Here an integer operation may sit anywhere in a term and take calls as
arguments, and calls may take integer operations as arguments:

* `(= (quad $x) (double (double $x)))` with `(= (double $x) (+ $x $x))`: `(quad 4)` is `16`;
* `(= (toInt Z) 0)`, `(= (toInt (S $x)) (+ (toInt $x) 1))`: `(toInt (S (S Z)))` is `2`, recursion over
  compound data whose body applies `+` to a recursive call;
* `(+ (* 2 3) 1)` is `7`.

HE's grounded calls exist only on its world machine (`GroundedRuns`). The compositional machinery of
`MarkedValues` is carried to that machine and to its stateful source semantics: the argument product
(`tuple_product_MW`, `tuple_rows_MW`), the calls of each combination (`calls_loop_W`, `calls_rows_W`),
nested calls with marked arguments (`he_nested_MW`, `nested_determined_MW`), equation queries with
bodies read as marked instances (`he_query_KW`, `query_determined_KW`), and one more query: an
integer operation on a combination of integers, on any call value (`he_grounded_query_W`,
`grounded_query_determined_W`). PeTTa runs the operation through its primitive rule, after its
argument frames (`over_prim_K`).

## Results

* `SettlesKG t L`: `CompoundBindings.SettlesK` with a fourth case, an integer operation
  `+ - * < <= > >=`, undeclared, over settling arguments whose every combination of answers is a pair
  of integers. A condition on the program only.
* `settlesKG_agree`, `settlesKG_determined`, `every_complete_run_kg`: a complete run of HE's world
  machine exists; every complete run publishes `L`; PeTTa yields `L` from some fuel on.

## Controls

* `Controls.quad_every_run`, `Controls.toInt_every_run`, `Controls.arith_every_run` (positive).
* `Controls.quad_not_settlesG` (negative): `(quad 4)` lies outside `GroundedRuns.SettlesG`, whose
  bodies are flat; the extension is strict.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace NestedArithmetic

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom GroundedResult)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load WorldSteps
  WorldLocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings GroundedTables GroundedRuns
  GroundedEveryRun

/-! ## HE's world machine on marked values -/

/-- **HE's world machine runs the contextual value `v` to the answers `L`.** -/
def WRunsTo (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy) (atoms : List Atom)
    (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    ∃ results : List Result, results.map (fun result => result.1.erase) = L ∧
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms,
          .work (.atom live scope v Atom.undefinedType activation), stack, emitted⟩)
        (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning results, stack, emitted⟩)

/-- **HE's world machine evaluates every marked presentation of `t` to `L`.** -/
def HEEvaluatesMW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked heDispatch atoms v → WRunsTo minimal lookup policy atoms v L

/-- **HE's world machine queries every call value of `(f vals)` to `A`.** -/
def HEQueryW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy) (atoms : List Atom)
    (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) → ∀ (stack : List Continuation) (emitted : List Result),
      ∃ results : List Result, results.map (fun result => result.1.erase) = A ∧
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms,
            .work (.call live scope value Atom.undefinedType activation), stack, emitted⟩)
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning results, stack, emitted⟩)

section WorldMachine

variable (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}

theorem lift_runs {atoms : List Atom} {v : Entry.Value} {L : List Atom}
    (runs : HERunsTo heDispatch lookup policy atoms v L) : WRunsTo minimal lookup policy atoms v L := by
  intro live scope activation stack emitted
  obtain ⟨R, eraseR, path⟩ := runs live scope activation stack emitted
  exact ⟨R, eraseR, lift_path minimal path⟩

theorem lift_query {atoms : List Atom} {f : String} {vals A : List Atom}
    (query : HEQuery heDispatch lookup policy atoms f vals A) :
    HEQueryW minimal lookup policy atoms f vals A := by
  intro live scope activation value erased stack emitted
  obtain ⟨R, eraseR, path⟩ := query live scope activation value erased stack emitted
  exact ⟨R, eraseR, lift_path minimal path⟩

theorem he_data_MW (answers : AnswersUndefined lookup) (atoms : List Atom) {d : Atom}
    (data : DataAtom d) : HEEvaluatesMW minimal lookup policy atoms d [d] :=
  fun v erased marked => lift_runs minimal (he_data_M answers atoms data v erased marked)

/-- **The branches of a tuple's head, on the world machine.** -/
theorem branches_loop_W (atoms : List Atom) {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ts : List (List Atom)}
    (tailRuns : ∀ (live' : List Atom) (activation : Frame) (stack : List Continuation)
      (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) = Ts.map Atom.expression ∧
        (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .work (.tuple live' scope tail activation),
            stack, emitted⟩)
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning R, stack, emitted⟩))
    (tailClean : ∀ c ∈ Ts, ∃ c0 cs, c = c0 :: cs ∧ Answerable c0) :
    ∀ (heads : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      ∀ (stack : List Continuation) (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) =
          heads.flatMap (fun h => Ts.map fun c => Atom.expression (h.1.erase :: c)) ∧
        (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .work (.branches live scope tail heads),
            stack, emitted⟩)
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning R, stack, emitted⟩)
  | [], _, stack, emitted => ⟨[], rfl, (fun _ member => by cases member),
      .single (lift_step minimal (.internal .branchesNil))⟩
  | h :: hs, clean, stack, emitted => by
      have hClean := clean h List.mem_cons_self
      obtain ⟨Rt, eraseRt, shapeRt, pathRt⟩ := tailRuns (h.1.erase :: live) h.2
        (.tupleTail h.1 :: .append (.branches live scope tail hs) :: stack) emitted
      have pointwise : ∀ r ∈ Rt, (∃ children,
            (Completed.tuplePrepend h.1 r).1 = .expression .active children) ∧
          (Completed.tuplePrepend h.1 r).1.erase = HENested.prependAtom h.1.erase r.1.erase := by
        intro r member
        obtain ⟨children, shape⟩ := shapeRt r member
        have inTs : r.1.erase ∈ Ts.map Atom.expression := by
          rw [← eraseRt]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        obtain ⟨c, cMem, cEq⟩ := List.mem_map.mp inTs
        obtain ⟨c0, cs, rfl, clean0⟩ := tailClean c cMem
        have result := HENested.tuplePrepend_erase h.1 shape cEq.symm clean0
        refine ⟨⟨_, result.1⟩, ?_⟩
        rw [result.2, ← cEq]
        rfl
      obtain ⟨Rh, eraseRh, shapeRh, pathRh⟩ := branches_loop_W atoms tailRuns tailClean hs
        (fun x member => clean x (List.mem_cons_of_mem _ member))
        (.prepend (Rt.map (Completed.tuplePrepend h.1)) :: stack) emitted
      refine ⟨Rt.map (Completed.tuplePrepend h.1) ++ Rh, ?_, ?_, ?_⟩
      · rw [List.map_append, eraseRh, List.flatMap_cons, List.map_map]
        congr 1
        have mapped : (Rt.map ((fun r : Result => r.1.erase) ∘ Completed.tuplePrepend h.1)) =
            (Rt.map fun r => r.1.erase).map (HENested.prependAtom h.1.erase) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro r member
          exact (pointwise r member).2
        rw [mapped, eraseRt, List.map_map]
        rfl
      · intro r member
        rcases List.mem_append.mp member with inPrepended | inRest
        · obtain ⟨r', member', rfl⟩ := List.mem_map.mp inPrepended
          exact (pointwise r' member').1
        · exact shapeRh r inRest
      · refine .head (lift_step minimal (.internal (.branchesContinue hClean.notStopped))) ?_
        refine .trans pathRt ?_
        refine .head (lift_step minimal (.internal .tupleTail)) ?_
        refine .head (lift_step minimal (.internal .append)) ?_
        refine .trans pathRh ?_
        exact .single (lift_step minimal (.internal .prepend))

/-- **HE's tuple traversal of marked values, on the world machine.** -/
theorem tuple_product_MW (atoms : List Atom) :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)), vs ≠ [] →
      List.Forall₂ (fun v L => WRunsTo minimal lookup policy atoms v L ∧
        ∀ a ∈ L, Answerable a) vs Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result), ∃ R : List Result,
          R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression ∧
          (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
          WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
            (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .work (.tuple live scope vs activation),
              stack, emitted⟩)
            (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning R, stack, emitted⟩)
  | [], _, nonempty, _ => absurd rfl nonempty
  | [v], Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          obtain ⟨R, eraseR, path⟩ := here.1 live scope activation (.singleton :: stack) emitted
          have clean := HENested.clean_of_erase eraseR here.2
          have singled : ∀ r ∈ R, Completed.tupleSingleton r = (.expression .active [r.1], r.2) := by
            intro r member
            unfold Completed.tupleSingleton
            rw [HENested.emptyOrError_false (clean r member)]
            rfl
          refine ⟨R.map Completed.tupleSingleton, ?_, ?_, ?_⟩
          · rw [List.map_map]
            have mapped : R.map ((fun r : Result => r.1.erase) ∘ Completed.tupleSingleton) =
                (R.map fun r => r.1.erase).map fun a => Atom.expression [a] := by
              rw [List.map_map]
              apply List.map_congr_left
              intro r member
              simp only [Function.comp_apply, singled r member, Entry.Value.erase, List.map_cons,
                List.map_nil]
            rw [mapped, eraseR, combos_singleton, List.map_map]
            rfl
          · intro r member
            obtain ⟨r', member', rfl⟩ := List.mem_map.mp member
            exact ⟨_, by rw [singled r' member']⟩
          · refine .head (lift_step minimal (.internal .tupleSingleton)) ?_
            refine .trans path ?_
            exact .single (lift_step minimal (.internal .singleton))
  | v :: v2 :: rest, Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨R, eraseR, path⟩ := here.1 _ scope activation
            (.branches live scope (v2 :: rest) :: stack) emitted
          have clean := HENested.clean_of_erase eraseR here.2
          have tailRuns := tuple_product_MW atoms (v2 :: rest) Ls' (List.cons_ne_nil _ _) later
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
          obtain ⟨R', eraseR', shapeR', loop⟩ := branches_loop_W minimal atoms (live := live)
            (fun live' activation' stack' emitted' => tailRuns live' scope activation' stack' emitted')
            tailClean R clean stack emitted
          refine ⟨R', ?_, shapeR', ?_⟩
          · rw [eraseR']
            have flat : R.flatMap (fun h => (combos Ls').map fun c => Atom.expression (h.1.erase :: c)) =
                (R.map fun h => h.1.erase).flatMap
                  (fun a => (combos Ls').map fun c => Atom.expression (a :: c)) := by
              rw [List.flatMap_map]
            rw [flat, eraseR]
            simp only [combos, List.map_flatMap, List.map_map]
            rfl
          · refine .head (lift_step minimal (.internal .tupleCons)) ?_
            refine .trans path ?_
            refine .head (lift_step minimal (.internal .branches)) ?_
            exact loop

/-- **The calls continuation over the rows, on the world machine.** -/
theorem calls_loop_W (atoms : List Atom) {live : List Atom} {scope : List String} {f : String}
    (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        HEQueryW minimal lookup policy atoms f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) = rows.flatMap (fun r => Q (HENested.argsOf r.1.erase)) ∧
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch lookup policy
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms,
            .work (.calls live scope Atom.undefinedType rows), stack, emitted⟩)
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning R, stack, emitted⟩)
  | [], _, stack, emitted => ⟨[], rfl, .single (lift_step minimal (.internal .callsNil))⟩
  | r :: rs, queries, stack, emitted => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      obtain ⟨Qr, eraseQr, pathQr⟩ := query live scope r.2 r.1 erased
        (.append (.calls live scope Atom.undefinedType rs) :: stack) emitted
      obtain ⟨Rs, eraseRs, pathRs⟩ := calls_loop_W atoms Q rs
        (fun x member => queries x (List.mem_cons_of_mem _ member)) (.prepend Qr :: stack) emitted
      refine ⟨Qr ++ Rs, ?_, ?_⟩
      · rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
        rfl
      · refine .head (lift_step minimal (.internal .callsCons)) ?_
        refine .trans pathQr ?_
        refine .head (lift_step minimal (.internal .append)) ?_
        refine .trans pathRs ?_
        exact .single (lift_step minimal (.internal .prepend))

/-- **HE's world machine evaluates a marked call whose root it interprets.** -/
theorem he_nested_MW (answers : AnswersUndefined lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => WRunsTo minimal lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, HEQueryW minimal lookup policy atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    WRunsTo minimal lookup policy atoms (.expression readiness (.symbol f :: vs))
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
      Atom.undefinedType .interpret := by
    rw [readV, eraseV]
    exact .expression (call_not_stopped head) undefined_not_raw interpreted
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol f).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := heDispatch) (lookup := lookup) (live := live) (scope := scope) (stack := stack)
    entry readV occurrences
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  rw [published] at step
  have headRuns : WRunsTo minimal lookup policy atoms (.symbol f) [.symbol f] :=
    he_data_MW minimal answers atoms head (.symbol f) (by simp only [Entry.Value.erase]) (.symbol f)
  obtain ⟨T, eraseT, _, pathT⟩ := tuple_product_MW minimal (lookup := lookup)
    (policy := policy) atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
    (.cons ⟨headRuns, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args) (Atom.undefinedType :: live) scope activation
    (.calls live scope Atom.undefinedType :: .publish (.expression (.symbol f :: ts)) :: stack)
    emitted
  rw [combos_head] at eraseT
  have rows : ∀ r ∈ T, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
      HEQueryW minimal lookup policy atoms f vals (Q vals) := by
    intro r member
    have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
      rw [← eraseT]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.map_map] at inRows
    obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
    exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
  obtain ⟨R, eraseR, pathR⟩ := calls_loop_W minimal (lookup := lookup) (policy := policy) atoms
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
  obtain ⟨final, eraseFinal, pathFinal⟩ := HENested.publish_step (dispatch := heDispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (.expression (.symbol f :: ts)) R clean
    stack emitted
  refine ⟨final, by rw [eraseFinal, eraseR], ?_⟩
  refine .head (lift_step minimal (.internal step)) ?_
  refine .trans pathT ?_
  refine .head (lift_step minimal (.internal .calls)) ?_
  exact pathR.trans (lift_path minimal pathFinal)

/-- **The equation loop on marked reads, on the world machine.** -/
theorem equations_steps_KW {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        HEEvaluatesMW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls →
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
          obtain ⟨readErase, readMarked⟩ := readsAs output sameBindings
          obtain ⟨R, eraseR, pathR⟩ := evaluates _ readErase readMarked live scope output
            (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_KW works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (lift_step minimal (.internal (.equationsCons sameBindings unified))) ?_
            refine .head (lift_step minimal (.internal
              (.boundaryProducerRaw (not_pending facts readErase)))) ?_
            refine .head (lift_step minimal (.internal .boundaryBatch)) ?_
            refine .head (lift_step minimal (.internal .boundaryBatchCons)) ?_
            refine .head (lift_step minimal (.internal .boundaryReturned)) ?_
            refine .head (lift_step minimal (.internal (.returnEvaluate ?_ ?_))) ?_
            · rw [readErase]
              exact facts.notRefused
            · rw [readErase]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (lift_step minimal (.internal .append)) ?_
            refine .head (lift_step minimal (.internal .boundaryBatchNil)) ?_
            refine .head (lift_step minimal (.internal .prepend)) ?_
            refine .head (lift_step minimal (.internal .append)) ?_
            refine .trans pathR' ?_
            exact .single (lift_step minimal (.internal .prepend))

/-- **HE's equation query on a call of values, on the world machine.** -/
theorem he_query_KW {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {args : List Atom} (head : NodeHead heDispatch atoms f)
    (argsValues : ∀ a ∈ args, NestedValues.Value heDispatch atoms a)
    (nonempty : regionInstances atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluatesMW minimal lookup policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f args) Ls) :
    HEQueryW minimal lookup policy atoms f args Ls.flatten := by
  intro live scope activation value erased stack emitted
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances_K policy argsValues program
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
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
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
      HEEvaluatesMW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_KW minimal works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (lift_step minimal (.internal (.callEquations
    (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction args) erased) frontier'
    worksNonempty))) pathR⟩

/-- **An integer operation on a combination of integers, on any call value**: the grounded call
through the host service, the native boundary, the cast of the value. -/
theorem he_grounded_query_W (answers : AnswersUndefined lookup) {atoms : List Atom} {op : String}
    (known : IntOp op) (a b : Int) :
    HEQueryW minimal lookup policy atoms op [num a, num b] [intValue op a b] := by
  intro live scope activation value erased stack emitted
  have rData := intValue_dataAtom known a b
  have produced : (services minimal).groundedAt (Space.ofList atoms) () live scope activation
      value (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)]) () :=
    ⟨.symbol op, [num a, num b], .ok [(intValue op a b, Bindings.empty)], erased,
      (he_outcome_exact known a b _).mpr rfl, rfl⟩
  have rows : Completed.NativeOutcomeRel policy heDispatch (.symbol op) [num a, num b]
      value (some Atom.undefinedType) activation
      (.ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)])
      (.resume [(Entry.Value.ofAtom (intValue op a b), activation)]) :=
    .success (.cons (Frame.NativeRenewRel.empty policy activation) .nil)
  have notError : ¬ IsErrorRel value.erase := HERuns.value_not_error (intOp_head known) erased
  have native := lift_path minimal (native_steps (policy := policy) answers (atoms := atoms) rData
    (intValue_notRefused known a b) live scope value activation stack emitted)
  simp only [List.append_nil] at native
  refine ⟨[(Entry.Value.ofAtom (intValue op a b), activation)], by simp, ?_⟩
  exact .head (.internal (WorldLocalStepWith.callGroundedResume erased (he_executable known)
    notError produced rows)) native

end WorldMachine

/-! ## HE's world source semantics on marked values -/

/-- **Every derivation of HE's stateful source relation for `v` returns the atoms `L`.** -/
def RunsDeterminedW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (world world' : Unit) (live : List Atom) (scope : List String) (frame : Frame)
    (results : List Result),
    Completed.Stateful.AtomRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope v
      Atom.undefinedType frame results world' (policy := policy) →
    results.map (fun r => r.1.erase) = L

/-- **Every marked presentation of `t` is determined to `L`, on the world source semantics.** -/
def DeterminedMW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked heDispatch atoms v →
    RunsDeterminedW minimal lookup policy atoms v L

/-- **The world query of `(f vals)` is determined to `A`**, on every call value. -/
def QueryDeterminedW (minimal : Minimal.Services) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (world world' : Unit) (live : List Atom) (scope : List String) (value : Entry.Value)
    (frame : Frame) (children : List Result), value.erase = .expression (.symbol f :: vals) →
    Completed.Stateful.CallRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope value
      Atom.undefinedType frame children world' (policy := policy) →
    children.map (fun r => r.1.erase) = A

section WorldSource

variable {minimal : Minimal.Services} {lookup : CastLookup} {policy : Policy}

theorem data_determined_MW (contract : LookupContract lookup) {atoms : List Atom} {d : Atom}
    (data : DataAtom d) : DeterminedMW minimal lookup policy atoms d [d] := by
  intro v erased _ world world' live scope frame results derived
  rw [value_of_data data erased] at derived
  obtain ⟨after, rfl⟩ := data_source_W contract data derived
  simp

/-- **The branches of a tuple's head, on the world source semantics.** -/
theorem branches_rows_W {atoms : List Atom} {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ls : List (List Atom)}
    (tupleRows : ∀ (world world' : Unit) (live : List Atom) (frame : Frame) (results : List Result),
      Completed.Stateful.TupleRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope tail
        frame results world' (policy := policy) → List.Forall₂ CleanRow results (combos Ls)) :
    ∀ (heads results : List Result) (world world' : Unit), (∀ h ∈ heads, Answerable h.1.erase) →
      Completed.Stateful.TupleBranchesRel (worldEnv minimal lookup) (Space.ofList atoms) world live
        scope tail heads results world' (policy := policy) →
      List.Forall₂ CleanRow results (heads.flatMap fun h => (combos Ls).map (h.1.erase :: ·))
  | [], _, _, _, _, derived => by
      cases derived
      exact .nil
  | h :: hs, _, _, _, clean, derived => by
      cases derived with
      | stopped stopped _ => exact absurd stopped (clean h List.mem_cons_self).notStopped
      | continuing _ children rest =>
          rw [List.flatMap_cons]
          refine forall₂_append ?_ (branches_rows_W tupleRows hs _ _ _
            (fun r member => clean r (List.mem_cons_of_mem _ member)) rest)
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact (tupleRows _ _ _ _ _ children).imp fun _ _ row =>
            prepend_row h.1 (clean h List.mem_cons_self) row

/-- **HE's tuple of marked arguments, on the world source semantics**: one row per combination. -/
theorem tuple_rows_MW {atoms : List Atom} {scope : List String} :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)),
      List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
        RunsDeterminedW minimal lookup policy atoms v L) vs Ls →
      vs ≠ [] → ∀ (world world' : Unit) (live : List Atom) (frame : Frame) (results : List Result),
        Completed.Stateful.TupleRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope
          vs frame results world' (policy := policy) →
        List.Forall₂ CleanRow results (combos Ls)
  | [], _, _, nonempty, _, _, _, _, _, _ => absurd rfl nonempty
  | [v], _, related, _, world, world', live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      obtain rfl := List.forall₂_nil_left_iff.mp rest
      cases derived with
      | singleton headDerived =>
          have erased := determined _ _ _ _ _ _ headDerived
          have rows := singleton_rows (HENested.clean_of_erase erased clean)
          subst erased
          rw [combos_singleton, List.map_map]
          exact rows
  | v :: v2 :: rest, _, related, _, world, world', live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, restRel, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons headDerived branches =>
          have erased := determined _ _ _ _ _ _ headDerived
          have rows := branches_rows_W
            (fun world'' world''' live' frame' results' tupled =>
              tuple_rows_MW (v2 :: rest) Ls' restRel (List.cons_ne_nil _ _) world'' world''' live'
                frame' results' tupled)
            _ _ _ _ (HENested.clean_of_erase erased clean) branches
          rwa [flatMap_heads erased] at rows

/-- **The calls continuation over the rows, on the world source semantics.** -/
theorem calls_rows_W {atoms : List Atom} {live : List Atom} {scope : List String} {f : String}
    {Q : List Atom → List Atom} :
    ∀ (rows : List Result) (cs : List (List Atom)) (raw : List Result) (world world' : Unit),
      List.Forall₂ (fun r vals => r.1.erase = .expression (.symbol f :: vals)) rows cs →
      (∀ vals ∈ cs, QueryDeterminedW minimal lookup policy atoms f vals (Q vals)) →
      Completed.Stateful.CallsRel (worldEnv minimal lookup) (Space.ofList atoms) world live scope
        Atom.undefinedType rows raw world' (policy := policy) →
      raw.map (fun r => r.1.erase) = cs.flatMap Q
  | [], _, _, _, _, related, _, derived => by
      cases related
      cases derived
      rfl
  | _ :: rs, _, _, _, _, related, queries, derived => by
      obtain ⟨vals, cs', erased, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons called later =>
          rw [List.map_append, queries vals List.mem_cons_self _ _ _ _ _ _ _ erased called,
            calls_rows_W rs cs' _ _ _ rest (fun v member => queries v (List.mem_cons_of_mem _ member))
              later, List.flatMap_cons]

/-- **Marked nested calls on the world source semantics are determined, compositionally.** -/
theorem nested_determined_MW (contract : LookupContract lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value} (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
      RunsDeterminedW minimal lookup policy atoms v L) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      QueryDeterminedW minimal lookup policy atoms f vals (Q vals))
    (held : readiness = .held → policy.reentry = .reuse →
      (combos Ls).flatMap Q = [.expression (.symbol f :: ts)]) :
    RunsDeterminedW minimal lookup policy atoms (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).1 a inner
  intro world world' live scope frame results derived
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : frame.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy frame (by rw [eraseV]; exact closed)
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope
        (frame.read policy (.expression readiness (.symbol f :: vs))).erase
        (.symbol f) Atom.undefinedType frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have batch : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result}
      {w₀ w₁ w₂ : Unit},
      Entry.Value.symbol f = operator → vs = arguments →
      Completed.Stateful.TupleRel (worldEnv minimal lookup) (Space.ofList atoms) w₀
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows w₁ (policy := policy) →
      Completed.Stateful.CallsRel (worldEnv minimal lookup) (Space.ofList atoms) w₁ live scope
        Atom.undefinedType rows raw w₂ (policy := policy) →
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro operator arguments rows raw w₀ w₁ w₂ sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    have headDetermined : RunsDeterminedW minimal lookup policy atoms (.symbol f) [.symbol f] :=
      fun w w' live' scope' frame' results' derived' =>
        data_determined_MW (minimal := minimal) (policy := policy) contract head (.symbol f)
          (by simp only [Entry.Value.erase]) (.symbol f) w w' live' scope' frame' results' derived'
    have rowsShape := tuple_rows_MW (Entry.Value.symbol f :: vs) ([Atom.symbol f] :: Ls)
      (.cons ⟨fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data head, headDetermined⟩ args)
      (List.cons_ne_nil _ _) _ _ _ _ _ tuples
    rw [combos_head, List.forall₂_map_right_iff] at rowsShape
    exact calls_rows_W _ _ _ _ _ (rowsShape.imp fun _ _ row => row.2.1)
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
        Atom.undefinedType .deliver := by
      rw [readV, eraseV]
      exact .held (call_not_stopped head) undefined_not_raw reusedHeld.1 reusedHeld.2
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
        Atom.undefinedType .interpret := by
      rw [readV, eraseV]
      exact .expression (call_not_stopped head) undefined_not_raw interpreted
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
        cases selectionExact chosen
    | fallback _ shaped chosen tuples calls selected =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, sameOperator, sameArguments⟩ := shaped
        rw [← sameOperator, operatorErase] at chosen
        have exhausted := selectionExact chosen
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
        have exhausted := selectionExact chosen
        simp at exhausted

/-- **The equation bodies on the world source semantics, read as marked values.** -/
theorem bodies_source_MW {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
          Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
        DeterminedMW minimal lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result} {w₀ w₁ : Unit},
        Completed.Stateful.EquationBodiesRel (worldEnv minimal lookup) (Space.ofList atoms) w₀ live
          scope original Atom.undefinedType frame works results w₁ (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, _, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, _, _, derived => by
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
                            determined _ readErase readMarked _ _ _ _ _ _ evaluated,
                            bodies_source_MW ws Ls' rest later, List.flatten_cons]

/-- **The world query of a call of values with open bodies is determined.** -/
theorem query_determined_KW {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {vals : List Atom} (head : NodeHead heDispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value heDispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => DeterminedMW minimal lookup policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    QueryDeterminedW minimal lookup policy atoms f vals Ls.flatten := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  intro world world' live scope value frame children erased called
  have notExecutable : ∀ {operator : Atom} {arguments : List Atom},
      value.erase = .expression (operator :: arguments) → ¬ heDispatch.executable operator := by
    intro operator arguments shaped executable
    rw [erased] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    rw [← shaped.1] at executable
    exact head.notHost executable
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
              Marked heDispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
          DeterminedMW minimal lookup policy atoms i L ∧ BodyFacts i) _ Ls :=
        (forall₂_comp instances bodies).imp fun _ _ both => by
          obtain ⟨i, ⟨_, reads⟩, determined, facts⟩ := both
          exact ⟨i, reads, determined, facts⟩
      exact bodies_source_MW _ Ls onWorks equations
  | groundedDone shaped executable => exact absurd executable (notExecutable shaped)
  | groundedResume shaped executable => exact absurd executable (notExecutable shaped)

/-- **A world query with an empty region returns the call.** -/
theorem query_absent_W {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : NodeHead heDispatch atoms f) (valsClean : ∀ v ∈ vals, Answerable v)
    (empty : regionBodies atoms f vals = []) :
    QueryDeterminedW minimal lookup policy atoms f vals [.expression (.symbol f :: vals)] := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  intro world world' live scope value frame children erased called
  have notExecutable : ∀ {operator : Atom} {arguments : List Atom},
      value.erase = .expression (operator :: arguments) → ¬ heDispatch.executable operator := by
    intro operator arguments shaped executable
    rw [erased] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    rw [← shaped.1] at executable
    exact head.notHost executable
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head.head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, head.instruction vals] at instruction
      cases instruction
  | absent _ _ _ => simp [erased]
  | equations _ _ frontier nonempty _ =>
      rw [erased] at frontier
      have bodies := HERuns.frontier_bodies ground frame.certified.satisfiable program
        (by rw [empty]; intro b member; cases member) frontier
      rw [empty] at bodies
      exact absurd (List.map_eq_nil_iff.mp bodies) nonempty
  | groundedDone shaped executable => exact absurd executable (notExecutable shaped)
  | groundedResume shaped executable => exact absurd executable (notExecutable shaped)

/-- **An integer operation on a combination of integers is determined on every call value.** -/
theorem grounded_query_determined_W (contract : LookupContract lookup) {atoms : List Atom}
    {op : String} (known : IntOp op) (a b : Int) :
    QueryDeterminedW minimal lookup policy atoms op [num a, num b] [intValue op a b] := by
  intro world world' live scope value after children erased called
  have host : Minimal.HostCall heDispatch value.erase :=
    ⟨.symbol op, [num a, num b], erased, he_executable known⟩
  have rData := intValue_dataAtom known a b
  have outcomeOf : ∀ {outcome : GroundedResult Entry.Value} {w₃ w₄ : Unit},
      (services minimal).groundedAt (Space.ofList atoms) w₃ live scope after value outcome w₄ →
      outcome = .ok [(Entry.Value.ofAtom (intValue op a b), Bindings.empty)] := by
    intro outcome w₃ w₄ produced
    obtain ⟨operator, arguments, raw, shaped, executed, rfl⟩ := produced
    rw [erased] at shaped
    simp only [Atom.expression.injEq, List.cons.injEq] at shaped
    obtain ⟨rfl, rfl⟩ := shaped
    rw [(he_outcome_exact known a b raw).mp executed]
    rfl
  cases called with
  | error failed =>
      exact absurd failed (HERuns.value_not_error (intOp_head known) erased)
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
                  (value' : Entry.Value),
                  Completed.nativeValue policy (worldEnv minimal lookup).dispatch operator arguments
                    frame' value' = value' := fun _ _ _ _ => rfl
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

end WorldSource

/-! ## PeTTa's primitive on argument frames -/

/-- The value of an integer operation on a combination of its arguments' answers. -/
def arith (op : String) : List Atom → Atom
  | [.grounded (.int a), .grounded (.int b)] => intValue op a b
  | other => .expression (.symbol op :: other)

theorem arith_num (op : String) (a b : Int) : arith op [num a, num b] = intValue op a b := rfl

/-- **PeTTa's primitive on two integers held by its argument frames.** -/
theorem applies_prim (atoms : List Atom) {op : String} (known : IntOp op) (a b : Int) :
    AppliesOver atoms (.function op) [num a, num b] [intValue op a b] := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh index older answers next
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver (intValue op a b) List.mem_cons_self world σ
    keeps state privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut],
    .head (primitive_step known a b world σ index frames older answers next) path⟩

theorem intOp_not_constructor {dispatch : GroundedDispatch} {atoms : List Atom} {op : String}
    (known : IntOp op) (head : ConstructorHead dispatch atoms op) : False := by
  have native := head.notNative
  rw [petta_known known] at native
  cases native

/-- **An integer operation, every presentation**: PeTTa evaluates the arguments through its
argument frames, streaming, and applies its primitive to each combination. -/
theorem over_prim_K {dispatch : GroundedDispatch} {atoms : List Atom} {op : String}
    {ts : List Atom} {Ls : List (List Atom)} (known : IntOp op)
    (args : List.Forall₂ (fun t L => PeTTaOverK dispatch atoms t L) ts Ls)
    (ints : ∀ vals ∈ combos Ls, ∃ a b : Int, vals = [num a, num b]) :
    PeTTaOverK dispatch atoms (.expression (.symbol op :: ts))
      ((combos Ls).flatMap fun vals => [arith op vals]) := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  rcases shown.node_or_var with ⟨us, rfl, notControl, shownArgs⟩ | ⟨x, rfl, _, value⟩
  · have notCollapse : op ≠ "collapse" := by cases known <;> decide
    have notOnce : op ≠ "once" := by cases known <;> decide
    have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead op || StdLib.known op ||
        (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == op)) =
        true := by
      rw [petta_known known]
      simp
    obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over_K atoms (.function op)
      (fun index => rawDemand_false known index) ts Ls args [] (fun c => [arith op c])
      (fun c cMem => by
        obtain ⟨a, b, rfl⟩ := ints c cMem
        rw [List.nil_append, arith_num]
        exact applies_prim atoms known a b)
      σ₀ frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ
      keeps state privateCode range fresh us shownArgs 0 older answers next
    exact ⟨uses, out, grown, valuesOut,
      .head (PeTTaRuns.call_enter world σ notCollapse notOnce
        (sourceControlForm_of_head notControl us) callable frames older answers next) path⟩
  · exfalso
    cases value with
    | data data => cases data
    | node head _ => exact intOp_not_constructor known head

/-! ## The terms that settle, with arithmetic in nested positions -/

/-- **`t` settles with the answers `L`**: `CompoundBindings.SettlesK`'s cases on HE's integer
dispatch, and an integer operation, undeclared, over settling arguments whose every combination of
answers is a pair of integers. A condition on the program only. -/
inductive SettlesKG (atoms : List Atom) : Atom → List Atom → Prop
  | data {d : Atom} : DataAtom d → d ≠ Atom.notReducible → SettlesKG atoms d [d]
  | build {f : String} {ts : List Atom} {Ls : List (List Atom)} : NodeHead heDispatch atoms f →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesKG atoms p.1 p.2) →
      SettlesKG atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)])
  | call {f : String} {ts : List Atom} {Ls : List (List Atom)} (R : List Atom → List (List Atom)) :
      NodeHead heDispatch atoms f →
      (∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f) →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesKG atoms p.1 p.2) →
      (∀ vals ∈ combos Ls, regionInstances atoms f vals ≠ []) →
      (∀ vals ∈ combos Ls, (regionInstances atoms f vals).length = (R vals).length) →
      (∀ vals ∈ combos Ls, ∀ p ∈ (regionInstances atoms f vals).zip (R vals),
        SettlesKG atoms p.1 p.2) →
      SettlesKG atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap fun vals => (R vals).flatten)
  | grounded {op : String} {ts : List Atom} {Ls : List (List Atom)} : IntOp op →
      (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = [] →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesKG atoms p.1 p.2) →
      (∀ vals ∈ combos Ls, ∃ a b : Int, vals = [num a, num b]) →
      SettlesKG atoms (.expression (.symbol op :: ts)) ((combos Ls).flatMap fun vals => [arith op vals])

theorem intOp_control {op : String} (known : IntOp op) : controlHead op = false := by
  cases known <;> decide

/-- What every settling term and its answers are. -/
theorem settlesKG_shape {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesKG atoms t L) :
    Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a := by
  induction settles with
  | @data d data _ =>
      refine ⟨⟨answerable_of_data data, ?_, fun rename => ?_, fun a member => ?_⟩, fun a member => ?_⟩
      · cases data with
        | symbol _ _ => exact .item (.symbol _)
        | grounded value => exact .item (.grounded value)
      · cases data <;> simp [renameTypeVars]
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · rw [List.mem_singleton] at member
        subst member
        exact .data data
  | @build f ts Ls head noEquation length _ ih =>
      have args := forall₂_of_zip
        (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a) length ih
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, shape⟩ := forall₂_right_exists args L member
        exact shape.1.answers a inside
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value heDispatch atoms a := by
        intro L member a inside
        obtain ⟨t, shape⟩ := forall₂_right_exists args L member
        exact shape.2 a inside
      refine ⟨node_shape head (fun t member => ⟨_, (forall₂_left_exists args t member).choose_spec.1⟩)
        ?_, ?_⟩
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        exact app_answerable head.head (combos_answerable allClean vals valsMem)
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        exact .node (constructor_of_node head noEquation) (combos_all allValues vals valsMem)
  | @call f ts Ls R head _ length _ _ lengths _ ihArgs ihBodies =>
      have args := forall₂_of_zip
        (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a) length ihArgs
      refine ⟨node_shape head (fun t member => ⟨_, (forall₂_left_exists args t member).choose_spec.1⟩)
        ?_, ?_⟩
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        obtain ⟨L, inR, inL⟩ := List.mem_flatten.mp inner
        have regions := forall₂_of_zip
          (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a)
          (lengths vals valsMem) (ihBodies vals valsMem)
        obtain ⟨b, shape⟩ := forall₂_right_exists regions L inR
        exact shape.1.answers a inL
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        obtain ⟨L, inR, inL⟩ := List.mem_flatten.mp inner
        have regions := forall₂_of_zip
          (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a)
          (lengths vals valsMem) (ihBodies vals valsMem)
        obtain ⟨b, shape⟩ := forall₂_right_exists regions L inR
        exact shape.2 a inL
  | @grounded op ts Ls known _ length _ ints ih =>
      have args := forall₂_of_zip
        (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value heDispatch atoms a) length ih
      have answers : ∀ a ∈ (combos Ls).flatMap (fun vals => [arith op vals]),
          DataAtom a := by
        intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        obtain ⟨x, y, rfl⟩ := ints vals valsMem
        rw [arith_num]
        exact intValue_dataAtom known x y
      have headData := intOp_head known
      have nodeHead : ∀ t ∈ ts, ∃ L, Shape t L := fun t member =>
        ⟨_, (forall₂_left_exists args t member).choose_spec.1⟩
      refine ⟨⟨app_answerable headData fun t member => (nodeHead t member).choose_spec.answerable,
        .node (intOp_control known) fun t member => (nodeHead t member).choose_spec.tree,
        fun rename => ?_, fun a member => answerable_of_data (answers a member)⟩,
        fun a member => .data (answers a member)⟩
      simp only [renameTypeVars, List.map_cons]
      rw [map_fixed fun t member => (nodeHead t member).choose_spec.fixed rename]

theorem settlesKG_facts {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesKG atoms t L) : BodyFacts t := by
  have shape := (settlesKG_shape settles).1
  have node : ∀ {f : String} {ts : List Atom}, f ≠ "function" →
      Shape (.expression (.symbol f :: ts)) L → BodyFacts (.expression (.symbol f :: ts)) := by
    intro f ts notFunction shape
    refine ⟨shape.answerable.closed, fun policy pending => ?_, (fun same => by cases same),
      shape.answerable.notStopped, shape.fixed, shape.answerable.ground⟩
    obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact notFunction same.1
  cases settles with
  | data data notRefused =>
      exact settles_facts (Settles.data (dispatch := heDispatch) (atoms := atoms) data notRefused)
  | build head _ _ _ => exact node head.notFunction shape
  | call _ head _ _ _ _ _ _ => exact node head.notFunction shape
  | grounded known _ _ _ _ => exact node (by cases known <;> decide) shape

/-- **A value settles only with itself.** -/
theorem settlesKG_value_self {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesKG atoms t L) : NestedValues.Value heDispatch atoms t → L = [t] := by
  induction settles with
  | data _ _ => intro _; rfl
  | @build f ts Ls head noEquation length _ ih =>
      intro value
      have each : ∀ t ∈ ts, NestedValues.Value heDispatch atoms t := fun t member =>
        value_children value t (List.mem_cons_of_mem _ member)
      have singles : Ls = ts.map fun t => [t] := zip_singletons length fun p member =>
        ih p member (each p.1 (List.of_mem_zip member).1)
      subst singles
      rw [combos_singletons]
      simp
  | call _ _ defined _ _ _ _ _ _ _ =>
      intro value
      exact (value_not_defined defined value).elim
  | grounded known _ _ _ _ _ =>
      intro value
      cases value with
      | data data => cases data
      | node head _ => exact (intOp_not_constructor known head).elim

/-- **The extension is conservative**: `CompoundBindings`'s settling terms (on HE's integer
dispatch) settle here with the same answers. -/
theorem settlesK_settlesKG {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesK heDispatch atoms t L) : SettlesKG atoms t L := by
  induction settles with
  | data data notRefused => exact .data data notRefused
  | build head noEquation length _ ih => exact .build head noEquation length ih
  | call R head defined length _ nonempty lengths _ ihArgs ihBodies =>
      exact .call R head defined length ihArgs nonempty lengths ihBodies

/-! ## Both machines -/

section Joint

variable (minimal : Minimal.Services) {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to its answers**: HE's world machine every marked
presentation, PeTTa every presentation under extending bindings. -/
theorem settlesKG_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : CallProgram atoms) {t : Atom} {L : List Atom} (settles : SettlesKG atoms t L) :
    HEEvaluatesMW minimal lookup policy atoms t L ∧ PeTTaOverK heDispatch atoms t L := by
  induction settles with
  | @data d data _ => exact ⟨he_data_MW minimal answers atoms data, over_data_K atoms data⟩
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesKG.build head noEquation length settled
      have args : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          (HEEvaluatesMW minimal lookup policy atoms t L ∧ PeTTaOverK heDispatch atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact (settlesKG_shape both.1).1.answers a inside
      have closed := (settlesKG_shape whole).1.answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQueryW minimal lookup policy atoms f vals
          [.expression (.symbol f :: vals)] ∧
          ∀ a ∈ [Atom.expression (.symbol f :: vals)], Answerable a := by
        intro vals member
        have valsClean := combos_answerable allClean vals member
        refine ⟨lift_query minimal fun live scope activation value erased stack emitted => ?_,
          fun a inside => ?_⟩
        · refine ⟨[(value, activation)], by simp [erased], ?_⟩
          exact HERuns.he_query_absent (scoped_consFree program.scoped) head.head head.notHost
            (head.instruction vals) (fun v inside => HERuns.ground_typeVars (valsClean v inside))
            (regionBodies_nil_of_no_equation vals noEquation) live scope activation value erased
            stack emitted
        · rw [List.mem_singleton] at inside
          subst inside
          exact app_answerable head.head valsClean
      refine ⟨fun v erased marked => ?_, over_build_K head noEquation
        (args.imp fun _ _ both => ⟨both.2.2, (settlesKG_shape both.1).1.answers⟩)
        (fun value => settlesKG_value_self whole value)⟩
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have argRuns : List.Forall₂ (fun v L => WRunsTo minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp args) fun w member L both =>
          ⟨both.2.1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesKG_value_self whole value]
        have runs := he_held (dispatch := heDispatch) (lookup := lookup) atoms reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rw [eraseList] at runs
        exact lift_runs minimal runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact he_nested_MW minimal answers head.head head.untyped closed interpreted rfl argRuns _
          query
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesKG.call R head defined length settled nonempty lengths bodies
      have args : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          (HEEvaluatesMW minimal lookup policy atoms t L ∧ PeTTaOverK heDispatch atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have regions : ∀ vals ∈ combos Ls, List.Forall₂ (fun b L => SettlesKG atoms b L ∧
          (HEEvaluatesMW minimal lookup policy atoms b L ∧ PeTTaOverK heDispatch atoms b L))
          (regionInstances atoms f vals) (R vals) :=
        fun vals member => forall₂_of_zip (lengths vals member) fun p inside =>
          ⟨bodies vals member p inside, ihBodies vals member p inside⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value heDispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact (settlesKG_shape both.1).2 a inside
      have valsValues : ∀ vals ∈ combos Ls, ∀ v ∈ vals, NestedValues.Value heDispatch atoms v :=
        combos_all allValues
      have closed := (settlesKG_shape whole).1.answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQueryW minimal lookup policy atoms f vals (R vals).flatten ∧
          ∀ a ∈ (R vals).flatten, Answerable a := by
        intro vals member
        refine ⟨he_query_KW minimal program.scoped head (valsValues vals member) (nonempty vals member)
            ((regions vals member).imp fun _ _ both => ⟨both.2.1, settlesKG_facts both.1⟩),
          fun a inside => ?_⟩
        obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
        obtain ⟨b, both⟩ := forall₂_right_exists (regions vals member) L inR
        exact (settlesKG_shape both.1).1.answers a inner
      have applies : ∀ vals ∈ combos Ls, AppliesOver atoms (.function f) vals (R vals).flatten := by
        intro vals member
        have definedHere : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
            e.arguments.length = vals.length := by
          obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ (nonempty vals member)
          rw [regionInstances_eq] at inRegion
          obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
          obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
          simp only [Bool.and_eq_true, beq_iff_eq] at selected
          exact ⟨e, live, selected.1, selected.2⟩
        exact applies_defined_K program head.notIO head.notNative (valsValues vals member)
          definedHere ((regions vals member).imp fun _ _ both => both.2.2)
      refine ⟨fun v erased marked => ?_,
        over_call_K head defined (args.imp fun _ _ both => both.2.2) _ applies⟩
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have argRuns : List.Forall₂ (fun v L => WRunsTo minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp args) fun w member L both =>
          ⟨both.2.1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim
      | active =>
          exact he_nested_MW minimal answers head.head head.untyped closed (Or.inr rfl) rfl argRuns
            _ query
  | @grounded op ts Ls known untyped length settled ints ih =>
      have whole := SettlesKG.grounded known untyped length settled ints
      have args : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          (HEEvaluatesMW minimal lookup policy atoms t L ∧ PeTTaOverK heDispatch atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have closed := (settlesKG_shape whole).1.answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQueryW minimal lookup policy atoms op vals [arith op vals] ∧
          ∀ a ∈ [arith op vals], Answerable a := by
        intro vals member
        obtain ⟨a, b, rfl⟩ := ints vals member
        rw [arith_num]
        refine ⟨he_grounded_query_W minimal answers known a b, fun x inside => ?_⟩
        rw [List.mem_singleton] at inside
        subst inside
        exact answerable_of_data (intValue_dataAtom known a b)
      refine ⟨fun v erased marked => ?_,
        over_prim_K known (args.imp fun _ _ both => both.2.2) ints⟩
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have argRuns : List.Forall₂ (fun v L => WRunsTo minimal lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp args) fun w member L both =>
          ⟨both.2.1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesKG_shape both.1).1.answers⟩
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          cases value with
          | data data => cases data
          | node head _ => exact (intOp_not_constructor known head).elim
      | active =>
          exact he_nested_MW minimal answers (intOp_head known) untyped closed (Or.inr rfl) rfl
            argRuns _ query

end Joint

/-! ## Every complete run -/

/-- **HE's world source semantics determines the answers of every settling term**, on every marked
presentation, under every lookup meeting the contract. -/
theorem settlesKG_determined {minimal : Minimal.Services} {lookup : CastLookup} {policy : Policy}
    (contract : LookupContract lookup) {atoms : List Atom} (program : CallProgram atoms) {t : Atom}
    {L : List Atom} (settles : SettlesKG atoms t L) :
    DeterminedMW minimal lookup policy atoms t L := by
  induction settles with
  | @data d data _ => exact data_determined_MW contract data
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesKG.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          DeterminedMW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesKG_shape both.1).1.answers a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
          RunsDeterminedW minimal lookup policy atoms v L) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT)
          fun w member L both => ⟨(settlesKG_shape both.1).1.answers,
            both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member))⟩
      exact nested_determined_MW contract head.head head.untyped closed rfl args
        (fun vals => [.expression (.symbol f :: vals)])
        (fun vals member => ⟨fun a inside => by
            rw [List.mem_singleton] at inside
            subst inside
            exact app_answerable head.head (combos_answerable allClean vals member),
          query_absent_W (scoped_consFree program.scoped) head
            (combos_answerable allClean vals member)
            (regionBodies_nil_of_no_equation vals noEquation)⟩)
        (fun isHeld _ => by
          subst isHeld
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact settlesKG_value_self whole value)
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesKG.call R head defined length settled nonempty lengths bodies
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          DeterminedMW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value heDispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesKG_shape both.1).2 a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
          RunsDeterminedW minimal lookup policy atoms v L) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT)
          fun w member L both => ⟨(settlesKG_shape both.1).1.answers,
            both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member))⟩
      exact nested_determined_MW contract head.head head.untyped closed rfl args
        (fun vals => (R vals).flatten)
        (fun vals member => ⟨fun a inside => by
            obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
            have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
            obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
            exact (settlesKG_shape settlesB).1.answers a inner,
          query_determined_KW program.scoped head (combos_all allValues vals member)
            (nonempty vals member)
            (forall₂_of_zip (lengths vals member) fun p inside =>
              ⟨ihBodies vals member p inside, settlesKG_facts (bodies vals member p inside)⟩)⟩)
        (fun isHeld _ => by
          subst isHeld
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim)
  | @grounded op ts Ls known untyped length settled ints ih =>
      have whole := SettlesKG.grounded known untyped length settled ints
      have argsT : List.Forall₂ (fun t L => SettlesKG atoms t L ∧
          DeterminedMW minimal lookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesKG_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
          RunsDeterminedW minimal lookup policy atoms v L) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT)
          fun w member L both => ⟨(settlesKG_shape both.1).1.answers,
            both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member))⟩
      exact nested_determined_MW contract (intOp_head known) untyped closed rfl args
        (fun vals => [arith op vals])
        (fun vals member => by
          obtain ⟨a, b, rfl⟩ := ints vals member
          rw [arith_num]
          exact ⟨fun x inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact answerable_of_data (intValue_dataAtom known a b),
            grounded_query_determined_W contract known a b⟩)
        (fun isHeld _ => by
          subst isHeld
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          cases value with
          | data data => cases data
          | node head _ => exact (intOp_not_constructor known head).elim)

/-- **Every complete run of HE's world machine publishes PeTTa's answers, with arithmetic in nested
positions and variables bound to compound values** (historical lookup, any policy, any minimal
services): a complete run exists; from some fuel on PeTTa's streaming run yields `L`; every complete
run of HE's world machine publishes `L`. -/
theorem every_complete_run_kg (minimal : Minimal.Services) (policy : Policy) {atoms : List Atom}
    (program : CallProgram atoms) {c : Atom} {L : List Atom} (settles : SettlesKG atoms c L) :
    (∃ heAnswers : List Result,
      WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], heAnswers⟩)) ∧
      ∃ N : Nat, ∀ n, N ≤ n →
        Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = L ∧
          ∀ emitted : List Result,
            WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
                (WorldConfiguration.ofReadOnly (load (Space.ofList atoms) c Atom.undefinedType))
                (WorldConfiguration.ofReadOnly ⟨Space.ofList atoms, .returning [], [], emitted⟩) →
              emitted.map (fun r => r.1.erase) = L := by
  obtain ⟨he, petta⟩ := settlesKG_agree minimal (lookup := Completed.rawLookup) (policy := policy)
    raw_answers program settles
  have shape := (settlesKG_shape settles).1
  obtain ⟨R, _, path⟩ := he (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c) (marked_ofAtom c)
    [] [] Completed.Frame.empty [] []
  obtain ⟨N, stable⟩ := petta_complete shape.answerable.ground shape.answers
    (over_root_K petta fun σ => shows_ground_K shape.tree shape.answerable)
  have determined := settlesKG_determined (minimal := minimal) (lookup := Completed.rawLookup)
    (policy := policy) raw_contract program settles
  exact ⟨⟨R, path.trans (lift_path minimal (HERuns.publish_all _ R []))⟩, N, fun n bigger =>
    ⟨stable n bigger, fun emitted run => determined (Entry.Value.ofAtom c)
      (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ _ _ (complete_source_W run)⟩⟩

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (sym_data)
open NestedCalls.Controls (one_consFree)

theorem int_data (n : Int) : DataAtom (num n) := .grounded _

theorem int_settles {atoms : List Atom} (n : Int) : SettlesKG atoms (num n) [num n] :=
  .data (int_data n) (by intro impossible; cases impossible)

/-- An integer operation on two arguments that each settle with one integer. -/
theorem arith_single {atoms : List Atom} {op : String} (known : IntOp op)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol op)) = []) {s t : Atom}
    {a b : Int} (first : SettlesKG atoms s [num a]) (second : SettlesKG atoms t [num b]) :
    SettlesKG atoms (app op [s, t]) [intValue op a b] := by
  have only : combos [[num a], [num b]] = [[num a, num b]] := rfl
  have built := SettlesKG.grounded (Ls := [[num a], [num b]]) known untyped rfl
    (zip_of_forall₂ (.cons first (.cons second .nil)))
    (by
      intro vals member
      rw [only, List.mem_singleton] at member
      exact ⟨a, b, member⟩)
  rw [only] at built
  simpa [arith_num] using built

/-- A call of a defined head with one instance, on HE's integer dispatch. -/
theorem call_one {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    {vals : List Atom} {b : Atom} {Lb : List Atom} (head : NodeHead heDispatch atoms f)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (SettlesKG atoms) ts Ls) (only : combos Ls = [vals])
    (instances : regionInstances atoms f vals = [b]) (body : SettlesKG atoms b Lb) :
    SettlesKG atoms (.expression (.symbol f :: ts)) Lb := by
  have built := SettlesKG.call (fun _ => [Lb]) head defined args.length_eq (zip_of_forall₂ args)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      simp)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      rfl)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      intro p inside
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      exact body)
  rw [only] at built
  simpa using built

/-- `quad` doubles twice: `(= (double $x) (+ $x $x))`, `(= (quad $x) (double (double $x)))`. -/
def quadRows : List Atom :=
  [rule (app "double" [.var "x"]) (app "+" [.var "x", .var "x"]),
   rule (app "quad" [.var "x"]) (app "double" [app "double" [.var "x"]])]

theorem quad_program : CallProgram quadRows := by
  intro row member
  simp only [quadRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨rule_consFree (one_consFree _ (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .item (.var _)
  · refine ⟨rule_consFree (one_consFree _ (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    rw [List.mem_singleton] at member
    subst member
    exact .node (by decide) fun w inner => by
      rw [List.mem_singleton] at inner
      subst inner
      exact .item (.var _)

theorem not_host (name : String) (outside : name ∉ heIntegerNames) :
    ¬ heDispatch.executable (.symbol name) := by
  rintro ⟨other, same, member⟩
  cases same
  exact outside member

theorem double_head : NodeHead heDispatch quadRows "double" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, not_host "double" (by decide), by decide,
    by decide, by decide, by decide⟩

theorem quad_head : NodeHead heDispatch quadRows "quad" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, not_host "quad" (by decide), by decide,
    by decide, by decide, by decide⟩

theorem double_defined : ∃ e ∈ quadRows.filterMap LiveEquations.equationOfRow, e.head = "double" := by
  decide +kernel

theorem quad_defined : ∃ e ∈ quadRows.filterMap LiveEquations.equationOfRow, e.head = "quad" := by
  decide +kernel

theorem plus_untyped : (Space.ofList quadRows).atoms.filter (typeRegion (.symbol "+")) = [] := by
  decide +kernel

theorem double_four : SettlesKG quadRows (app "double" [num 4]) [num 8] := by
  have instances : regionInstances quadRows "double" [num 4] = [app "+" [num 4, num 4]] := by
    decide +kernel
  have eight : intValue "+" 4 4 = num 8 := by decide
  have built := call_one double_head double_defined (.cons (int_settles 4) .nil) rfl instances
    (arith_single .plus plus_untyped (int_settles 4) (int_settles 4))
  rwa [eight] at built

/-- **`(quad 4)` settles with `16`**: `(double (double 4))`, the inner call's answer `8` doubled. -/
theorem quad_four : SettlesKG quadRows (app "quad" [num 4]) [num 16] := by
  have instances : regionInstances quadRows "quad" [num 4] =
      [app "double" [app "double" [num 4]]] := by decide +kernel
  have inner : regionInstances quadRows "double" [num 8] = [app "+" [num 8, num 8]] := by
    decide +kernel
  have sixteen : intValue "+" 8 8 = num 16 := by decide
  have built := call_one quad_head quad_defined (.cons (int_settles 4) .nil) rfl instances
    (call_one double_head double_defined (.cons double_four .nil) rfl inner
      (arith_single .plus plus_untyped (int_settles 8) (int_settles 8)))
  rwa [sixteen] at built

theorem quad_value : Streaming.values (Streaming.advance (translate quadRows) 60
    (Streaming.enter { state := store quadRows } (app "quad" [num 4]))) = [num 16] := by
  decide +kernel

/-- **Positive control: arithmetic under a nested call.** `(quad 4)` is `16` on every complete run
of HE's world machine and in PeTTa. -/
theorem quad_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList quadRows) (app "quad" [num 4]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList quadRows, .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList quadRows) (app "quad" [num 4]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList quadRows, .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [num 16]) ∧
      Streaming.values (Streaming.advance (translate quadRows) 60
        (Streaming.enter { state := store quadRows } (app "quad" [num 4]))) = [num 16] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_kg minimal policy quad_program quad_four
  exact ⟨⟨complete, (every N le_rfl).2⟩, quad_value⟩

/-- `toInt` reads a Peano numeral: `(= (toInt Z) 0)`, `(= (toInt (S $x)) (+ (toInt $x) 1))`. -/
def toIntRows : List Atom :=
  [rule (app "toInt" [sym "Z"]) (num 0),
   rule (app "toInt" [app "S" [.var "x"]]) (app "+" [app "toInt" [.var "x"], num 1])]

theorem toInt_program : CallProgram toIntRows := by
  intro row member
  simp only [toIntRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨rule_consFree (one_consFree _ (.symbol _)), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.grounded _)⟩
  · refine ⟨rule_consFree (one_consFree _
      (.expression _ (by intro first rest same; simp at same) fun item inside => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact .symbol _
        · exact .var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .node (by decide) fun w inner => by
        rw [List.mem_singleton] at inner
        subst inner
        exact .item (.var _)
    · exact .item (.grounded _)

theorem toInt_head : NodeHead heDispatch toIntRows "toInt" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, not_host "toInt" (by decide), by decide,
    by decide, by decide, by decide⟩

theorem s_head_int : NodeHead heDispatch toIntRows "S" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, not_host "S" (by decide), by decide,
    by decide, by decide, by decide⟩

theorem s_noEquation_int : (toIntRows.filterMap LiveEquations.equationOfRow).all
    (fun equation => equation.head != "S") = true := by
  decide +kernel

theorem toInt_defined : ∃ e ∈ toIntRows.filterMap LiveEquations.equationOfRow, e.head = "toInt" := by
  decide +kernel

theorem plus_untyped_int : (Space.ofList toIntRows).atoms.filter (typeRegion (.symbol "+")) = [] := by
  decide +kernel

theorem z_int : SettlesKG toIntRows (sym "Z") [sym "Z"] :=
  .data (sym_data "Z" (by decide) (by decide)) (by decide)

theorem sz_int : SettlesKG toIntRows (app "S" [sym "Z"]) [app "S" [sym "Z"]] := by
  have built := SettlesKG.build (Ls := [[sym "Z"]]) s_head_int s_noEquation_int rfl
    (zip_of_forall₂ (.cons z_int .nil))
  simpa [combos] using built

theorem ssz_int : SettlesKG toIntRows (app "S" [app "S" [sym "Z"]]) [app "S" [app "S" [sym "Z"]]] := by
  have built := SettlesKG.build (Ls := [[app "S" [sym "Z"]]]) s_head_int s_noEquation_int rfl
    (zip_of_forall₂ (.cons sz_int .nil))
  simpa [combos] using built

theorem toInt_z : SettlesKG toIntRows (app "toInt" [sym "Z"]) [num 0] := by
  have instances : regionInstances toIntRows "toInt" [sym "Z"] = [num 0] := by decide +kernel
  exact call_one toInt_head toInt_defined (.cons z_int .nil) rfl instances (int_settles 0)

theorem toInt_sz : SettlesKG toIntRows (app "toInt" [app "S" [sym "Z"]]) [num 1] := by
  have instances : regionInstances toIntRows "toInt" [app "S" [sym "Z"]] =
      [app "+" [app "toInt" [sym "Z"], num 1]] := by decide +kernel
  have one : intValue "+" 0 1 = num 1 := by decide
  have built := call_one toInt_head toInt_defined (.cons sz_int .nil) rfl instances
    (arith_single .plus plus_untyped_int toInt_z (int_settles 1))
  rwa [one] at built

/-- **`(toInt (S (S Z)))` settles with `2`**: `$x` is bound to the compound value `(S Z)`, and `+`
is applied to the recursive call's answer. -/
theorem toInt_ssz : SettlesKG toIntRows (app "toInt" [app "S" [app "S" [sym "Z"]]]) [num 2] := by
  have instances : regionInstances toIntRows "toInt" [app "S" [app "S" [sym "Z"]]] =
      [app "+" [app "toInt" [app "S" [sym "Z"]], num 1]] := by decide +kernel
  have two : intValue "+" 1 1 = num 2 := by decide
  have built := call_one toInt_head toInt_defined (.cons ssz_int .nil) rfl instances
    (arith_single .plus plus_untyped_int toInt_sz (int_settles 1))
  rwa [two] at built

theorem toInt_value : Streaming.values (Streaming.advance (translate toIntRows) 60
    (Streaming.enter { state := store toIntRows } (app "toInt" [app "S" [app "S" [sym "Z"]]]))) =
      [num 2] := by
  decide +kernel

/-- **Positive control: recursion over compound data with arithmetic on the recursive answer.**
`(toInt (S (S Z)))` is `2` on every complete run of HE's world machine and in PeTTa. -/
theorem toInt_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList toIntRows) (app "toInt" [app "S" [app "S" [sym "Z"]]])
              Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList toIntRows, .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList toIntRows) (app "toInt" [app "S" [app "S" [sym "Z"]]])
              Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList toIntRows, .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [num 2]) ∧
      Streaming.values (Streaming.advance (translate toIntRows) 60
        (Streaming.enter { state := store toIntRows } (app "toInt" [app "S" [app "S" [sym "Z"]]]))) =
        [num 2] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_kg minimal policy toInt_program toInt_ssz
  exact ⟨⟨complete, (every N le_rfl).2⟩, toInt_value⟩

theorem empty_program : CallProgram [] := fun row member => by cases member

/-- `(+ (* 2 3) 1)` settles with `7`, with no program at all. -/
theorem arith_seven : SettlesKG [] (app "+" [app "*" [num 2, num 3], num 1]) [num 7] := by
  have six : intValue "*" 2 3 = num 6 := by decide
  have seven : intValue "+" 6 1 = num 7 := by decide
  have inner := arith_single (atoms := []) .times (by decide +kernel) (int_settles 2) (int_settles 3)
  rw [six] at inner
  have built := arith_single .plus (by decide +kernel) inner (int_settles 1)
  rwa [seven] at built

theorem arith_value : Streaming.values (Streaming.advance (translate []) 20
    (Streaming.enter { state := store [] } (app "+" [app "*" [num 2, num 3], num 1]))) = [num 7] := by
  decide +kernel

/-- **Positive control: an operation on an operation.** `(+ (* 2 3) 1)` is `7` on every complete run
of HE's world machine and in PeTTa. -/
theorem arith_every_run (minimal : Minimal.Services) (policy : Policy) :
    ((∃ heAnswers : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList []) (app "+" [app "*" [num 2, num 3], num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], heAnswers⟩)) ∧
      ∀ emitted : List Result,
        WorldSteps (fun (_ : Unit) => id) (services minimal) heDispatch Completed.rawLookup policy
          (WorldConfiguration.ofReadOnly
            (load (Space.ofList []) (app "+" [app "*" [num 2, num 3], num 1]) Atom.undefinedType))
          (WorldConfiguration.ofReadOnly ⟨Space.ofList [], .returning [], [], emitted⟩) →
        emitted.map (fun r => r.1.erase) = [num 7]) ∧
      Streaming.values (Streaming.advance (translate []) 20
        (Streaming.enter { state := store [] } (app "+" [app "*" [num 2, num 3], num 1]))) =
        [num 7] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_kg minimal policy empty_program arith_seven
  exact ⟨⟨complete, (every N le_rfl).2⟩, arith_value⟩

/-- **Negative control: the extension is strict.** `(quad 4)` lies outside `GroundedRuns.SettlesG`:
its instance `(double (double 4))` has a call as an argument. -/
theorem quad_not_settlesG : ¬ SettlesG quadRows (app "quad" [num 4]) := by
  have instances : regionInstances quadRows "quad" [num 4] =
      [app "double" [app "double" [num 4]]] := by decide +kernel
  have defined : (quadRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "quad") = false := by decide +kernel
  intro settles
  cases settles with
  | data data _ => cases data
  | constructor _ noEquation =>
      rw [defined] at noEquation
      cases noEquation
  | call _ _ settled =>
      have body := settled (app "double" [app "double" [num 4]]) (by rw [instances]; simp)
      cases body with
      | data data _ => cases data
      | constructor ordinary _ => cases ordinary.arguments (app "double" [num 4]) (by simp)
      | call ordinary _ _ => cases ordinary.arguments (app "double" [num 4]) (by simp)

end Controls

#print axioms branches_loop_W
#print axioms tuple_product_MW
#print axioms he_nested_MW
#print axioms he_query_KW
#print axioms he_grounded_query_W
#print axioms tuple_rows_MW
#print axioms nested_determined_MW
#print axioms query_determined_KW
#print axioms grounded_query_determined_W
#print axioms over_prim_K
#print axioms settlesKG_agree
#print axioms settlesKG_determined
#print axioms settlesK_settlesKG
#print axioms every_complete_run_kg
#print axioms Controls.quad_every_run
#print axioms Controls.toInt_every_run
#print axioms Controls.arith_every_run
#print axioms Controls.quad_not_settlesG

end NestedArithmetic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
