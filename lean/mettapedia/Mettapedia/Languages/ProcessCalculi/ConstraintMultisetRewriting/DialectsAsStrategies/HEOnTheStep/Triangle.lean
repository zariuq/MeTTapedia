import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.HEMachine
import Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateCore

/-!
# The triangle: HE on the step against HE → PeTTa → PeTTa's store projection

**Superseded in part by `DialectsAsStrategies.TriangleFootprints`.**
* `triangle_reached_store` and `triangle_double` take an HE configuration that is not tied to the
  expression whose translation PeTTa runs, so their two halves are independent facts
  (`TriangleFootprints.Untied.untied_is_vacuous`). The tied statement is
  `TriangleFootprints.expression_triangle_reached_store`. Because this machine keeps its world, it
  too says only that both stores stay as loaded.
* The read-word difference below comes from this module's encoding, in which every reading firing
  reads the single world cell. With one occurrence per row, HE and PeTTa read the same rows
  (`TriangleFootprints.read_word_triangle`, `TriangleFootprints.WholeRunWords.whole_run_rows`), and
  they agree on answers over a whole fragment (`TriangleFootprints.EveryRun.answer_bags_every_run`).

Two ways from an HE program to the step:

* **HE → step** (`HEMachine`): HE's machine as firings; its observations are the answer bag, the
  world reached, and which occurrences each firing reads, takes and makes.
* **HE → PeTTa → projection**: the existing translation (`Translation.translateHE`), then PeTTa's
  store effects as one run of the ordered-store step (`PeTTa.RunsAsFirings`). The projection keeps the
  word of requests (rows taken, read, made) and the store reached. It does not keep answers.

So the triangle is asked on exactly two observations: the store reached and the read word.

## Where it holds: the store reached, on read-only runs

* `he_rules_read_world`: no rule of HE's read-only machine writes the world; every firing reads it or
  is a publication (`he_world_reached`: along every run, the world is the start space).
* `read_only_keeps`: a PeTTa run whose requests take and make nothing keeps its occurrences, and they
  track the store reached; from a loaded program the store reached is the loaded one
  (`read_only_reaches_loaded`).
* `triangle_reached_store`: on a program whose PeTTa evaluation requests only reads, HE on the step and
  HE → PeTTa → projection reach the same store, the loaded one. The condition is a property of the
  PeTTa run; it is checked by the kernel on the instance `(double 4)` (`double_read_only`).

## The read word in this encoding

* `reads_differ`: evaluating `(double 4)` against `{(p a), (= (double $x) (+ $x $x))}`, the translation
  leaves the program as it is, PeTTa's projection reads exactly the equation's row, and in this
  encoding every firing of HE on the step that reads anything reads the world cell, which holds
  `(p a)` too. So the read words differ on the row `(p a)`. This is an artifact of the encoding, not
  of the dialects. HE's complete equation query needs its region's rows and a guard that no other row
  of the region exists, not the whole world (`TriangleFootprints.HEFootprints`); PeTTa's call request
  carries the same guard over the rows it enumerated (`TriangleFootprints.PeTTaFootprints`).
* The store reached also differs once removal is involved: `NamedDifferences.removal` is the
  distinguishing program.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
open MeTTaCalculus.OccurrenceCommits (labels)

/-! ## HE on the step only reads its space -/

section HE

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **No rule of HE's read-only machine writes the world**: each is a reading rule or a
publication. -/
theorem he_rules_read_world {rule : RuleInstance (Cell Space Control Continuation Result)}
    (member : Rules (heMachine dispatch lookup policy) rule) :
    (∃ (space : Space) (c : Control) (pop : List Continuation) (c' : Control)
        (push : List Continuation) (b : ℕ), rule = readingRule space c pop c' push b) ∨
      ∃ (c : Control) (a : Result) (c' : Control), rule = publishRule c a c' := by
  cases member with
  | reading b _ => exact Or.inl ⟨_, _, _, _, _, b, rfl⟩
  | writing _ changed framed => exact absurd (framed []).1 changed
  | publish _ => exact Or.inr ⟨_, _, _, rfl⟩

/-- HE's read-only machine keeps its world along every run. -/
theorem he_machine_keeps_world {x y : Config Space Control Continuation Result}
    (path : Relation.ReflTransGen (heMachine dispatch lookup policy).Step x y) : y.world = x.world := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
      cases step with
      | internal transition => exact transition.1.trans ih
      | publish _ => exact ih

/-- **The world reached is the start space**, along every run of the step under HE's rules. -/
theorem he_world_reached {S S' : Store Space Control Continuation Result} {x : HEConfig}
    (represented : Represents S (toConfig x))
    (path : Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S') :
    worldsOf (labels Prod.fst S'.present) = {x.space} := by
  obtain ⟨y, run, here⟩ := store_path_to_machine represented path
  rw [here.2, worldsOf_encode, he_machine_keeps_world run]
  rfl

/-- **In this encoding, every reading firing of HE reads the whole world**: from a store
representing a configuration, a firing of HE's rules that reads anything reads the world occurrence
holding the configuration's space. This is a property of the encoding, whose reading rules read the
single world cell even for moves with no premise; the honest footprints are in
`TriangleFootprints.HEFootprints`. -/
theorem he_reads_world {S S' : Store Space Control Continuation Result} {x : HEConfig}
    {rule : RuleInstance (Cell Space Control Continuation Result)}
    (represented : Represents S (toConfig x)) (member : Rules (heMachine dispatch lookup policy) rule)
    (fires : ConstraintMultisetRewriting.Step (groundAction _) Prod.fst rule S S')
    (reads : rule.read ≠ []) : rule.read = [Cell.world x.space] := by
  rcases he_rules_read_world member with ⟨space, c, pop, c', push, b, rfl⟩ | ⟨c, a, c', rfl⟩
  · have inStore := (read_firing fires).2.1 (Cell.world space) (by simp [readingRule])
    rw [represented.2] at inStore
    have same := world_mem_encode inStore
    simp only [readingRule]
    rw [same]
    rfl
  · exact absurd rfl reads

end HE

/-! ## PeTTa's projection keeps the store on read-only runs -/

section PeTTa

/-- A request that takes and makes nothing publishes the same occurrences. -/
theorem publish_read_only {O : Type} [DecidableEq O] (rows : List O) {sel : Selection O}
    (noTake : sel.taken = []) (noMake : sel.made = []) :
    Interface.OrderedStore.publish rows sel = rows := by
  simp [Interface.OrderedStore.publish, Interface.OrderedStore.survivors, noTake, noMake]

/-- **A read-only PeTTa run keeps its occurrences**, and they track the store it reaches. -/
theorem read_only_keeps {O : Type} [DecidableEq O] {S : Supply O}
    (registry : SpaceSemantics.Program) :
    ∀ (fuel : ℕ) (state : Streaming.State) (ids : List O), Tracks S ids state.world.state →
      (∀ r ∈ requests S registry fuel state ids, r.selection.taken = [] ∧ r.selection.made = []) →
      Tracks S ids (Streaming.advance registry fuel state).world.state
  | 0, _, _, tracks, _ => tracks
  | fuel + 1, state, ids, tracks, readOnly => by
      cases stepped : Streaming.step registry state with
      | none =>
          have stays : Streaming.advance registry (fuel + 1) state = state := by
            simp [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, stepped]
          rw [stays]
          exact tracks
      | some next =>
          have taken := Streaming.transition_of_computed registry state next stepped
          have tracked := stream_tracks tracks taken
          have advanced : Streaming.advance registry (fuel + 1) state =
              Streaming.advance registry fuel next := by
            simp [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, stepped]
          rw [advanced]
          cases asked : askStream S registry ids state with
          | none =>
              simp only [publishedStream, asked] at tracked
              refine read_only_keeps registry fuel next ids tracked fun r member => readOnly r ?_
              simp [requests, stepped, asked, member]
          | some request =>
              have here := readOnly request (by simp [requests, stepped, asked])
              have same : Interface.OrderedStore.publish ids request.selection = ids :=
                publish_read_only ids here.1 here.2
              simp only [publishedStream, asked, same] at tracked
              refine read_only_keeps registry fuel next ids tracked fun r member => readOnly r ?_
              simp [requests, stepped, asked, same, member]

/-- **From a loaded program, a read-only evaluation reaches the loaded store.** -/
theorem read_only_reaches_loaded (registry : SpaceSemantics.Program) (atoms : List Atom)
    (expression : Atom) (fuel : ℕ)
    (readOnly : ∀ r ∈ requests rowSupply registry fuel
        (Streaming.enter { state := NamedSpaces.Store.new atoms [] } expression) (Row.load 0 atoms),
      r.selection.taken = [] ∧ r.selection.made = []) :
    (Streaming.advance registry fuel
      (Streaming.enter { state := NamedSpaces.Store.new atoms [] } expression)).world.state.core =
        atoms := by
  have kept := read_only_keeps registry fuel
    (Streaming.enter { state := NamedSpaces.Store.new atoms [] } expression) (Row.load 0 atoms)
    (tracks_load atoms) readOnly
  have final := kept.rows .self _ rfl
  have initial := (tracks_load atoms).rows .self atoms rfl
  rw [final, ← initial]

end PeTTa

/-! ## The triangle -/

open Mettapedia.Languages.MeTTa.Translation (translateHE)

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **The triangle on the store reached.** For an HE configuration whose space holds a program's
atoms, every run of HE on the step keeps that space; and when the PeTTa evaluation of the translated
expression requests only reads, PeTTa's projection reaches the same atoms. -/
theorem triangle_reached_store (registry : SpaceSemantics.Program) (atoms : List Atom)
    (expression : Atom) (fuel : ℕ)
    (readOnly : ∀ r ∈ requests rowSupply registry fuel
        (Streaming.enter { state := NamedSpaces.Store.new atoms [] } (translateHE expression 0).1)
        (Row.load 0 atoms), r.selection.taken = [] ∧ r.selection.made = [])
    {S : Store Space Control Continuation Result} {x : HEConfig}
    (represented : Represents S (toConfig x)) (loaded : x.space = Space.ofList atoms) :
    (∀ S', Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S' →
        worldsOf (labels Prod.fst S'.present) = {Space.ofList atoms}) ∧
      (Streaming.advance registry fuel
        (Streaming.enter { state := NamedSpaces.Store.new atoms [] }
          (translateHE expression 0).1)).world.state.core = atoms :=
  ⟨fun _ path => by
      rw [← loaded]
      exact he_world_reached represented path,
    read_only_reaches_loaded registry atoms _ fuel readOnly⟩

/-- The translation leaves `(double 4)` as it is. -/
theorem translate_double : translateHE Controls.callDouble 0 = (Controls.callDouble, 0) := rfl

/-- **The instance**: PeTTa's evaluation of `(double 4)` requests only reads. -/
theorem double_read_only :
    ∀ r ∈ requests rowSupply Controls.doubling 30
        (Streaming.enter { state := NamedSpaces.Store.new [Controls.p Controls.a,
          Controls.doubleEquation] [] } (translateHE Controls.callDouble 0).1)
        (Row.load 0 [Controls.p Controls.a, Controls.doubleEquation]),
      r.selection.taken = [] ∧ r.selection.made = [] := by
  rw [translate_double]
  have word := Controls.callDouble_requests.1
  intro r member
  have shaped : Controls.shape r ∈ [([], [⟨1, .self, Controls.doubleEquation⟩], [])] := by
    rw [← word]
    exact List.mem_map.mpr ⟨r, member, rfl⟩
  simp only [List.mem_singleton, Controls.shape, Prod.mk.injEq] at shaped
  exact ⟨shaped.1, shaped.2.2⟩

/-- **The triangle holds on the store reached for `(double 4)`.** -/
theorem triangle_double {S : Store Space Control Continuation Result} {x : HEConfig}
    (represented : Represents S (toConfig x))
    (loaded : x.space = Space.ofList [Controls.p Controls.a, Controls.doubleEquation]) :
    (∀ S', Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S' →
        worldsOf (labels Prod.fst S'.present) =
          {Space.ofList [Controls.p Controls.a, Controls.doubleEquation]}) ∧
      (Streaming.advance Controls.doubling 30
        (Streaming.enter { state := NamedSpaces.Store.new [Controls.p Controls.a,
          Controls.doubleEquation] [] } (translateHE Controls.callDouble 0).1)).world.state.core =
        [Controls.p Controls.a, Controls.doubleEquation] :=
  triangle_reached_store Controls.doubling _ Controls.callDouble 30 double_read_only represented loaded

/-- **The read words differ in this encoding.** For `(double 4)` against
`{(p a), (= (double $x) (+ $x $x))}`, the translation keeps the program, PeTTa's projection reads
exactly the equation's row, and `(p a)` is not among the rows it reads; in this module's encoding
every firing of HE on the step that reads anything reads the world cell holding both atoms, `(p a)`
included. With one occurrence per row the two read the same rows
(`TriangleFootprints.Instance.h1_triangle`). -/
theorem reads_differ :
    translateHE Controls.callDouble 0 = (Controls.callDouble, 0) ∧
      (requests rowSupply Controls.doubling 30
          (Streaming.enter { state := Controls.codeStore } Controls.callDouble) Controls.codeIds).map
          Controls.shape = [([], [⟨1, .self, Controls.doubleEquation⟩], [])] ∧
      Controls.p Controls.a ∉ ([⟨1, .self, Controls.doubleEquation⟩] : List Row).map Row.atom ∧
      ∀ {S S' : Store Space Control Continuation Result} {x : HEConfig}
        {rule : RuleInstance (Cell Space Control Continuation Result)},
        Represents S (toConfig x) →
        x.space = Space.ofList [Controls.p Controls.a, Controls.doubleEquation] →
        Rules (heMachine dispatch lookup policy) rule →
        ConstraintMultisetRewriting.Step (groundAction _) Prod.fst rule S S' → rule.read ≠ [] →
        rule.read = [Cell.world (Space.ofList [Controls.p Controls.a, Controls.doubleEquation])] ∧
          Controls.p Controls.a ∈ (Space.ofList [Controls.p Controls.a, Controls.doubleEquation]).atoms := by
  refine ⟨translate_double, Controls.callDouble_requests.1, by decide, ?_⟩
  intro S S' x rule represented loaded member fires reads
  refine ⟨?_, by simp [Space.ofList]⟩
  rw [← loaded]
  exact he_reads_world represented member fires reads

#print axioms he_rules_read_world
#print axioms he_world_reached
#print axioms he_reads_world
#print axioms read_only_keeps
#print axioms read_only_reaches_loaded
#print axioms triangle_reached_store
#print axioms double_read_only
#print axioms triangle_double
#print axioms reads_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
