import Mettapedia.Languages.MeTTa.PeTTa.BetaInliningControls
import Mettapedia.Machines.NestedQueryEffects

/-!
# The inlined call of a search round is a branch on an absence test

A breadth-first search over a state graph runs, for every state `$s` of layer `$k`
and every move from `$s` to `$t`, the call `(fresh $L $km $t $N)` of the one-equation
function

`(= (fresh $L $km $t $N) (if (== (collapse (match $L (layer $km $t) t)) ()) (add-atom $N $t) done))`.

Under any environment binding the four argument variables, the call completes as its
body does (`BetaInlining.beta_complete`, `fresh_inlinable`). The body is a branch on an
absence test: when no row of the layer space meets `(layer km t)` it adds `t` to the
output space and answers `True`, otherwise it changes nothing and answers `done`
(`fresh_body_returns`).

Read on the rows of the two spaces, tagged with their space, the run of the call is
`NestedQueryEffects.condBody` for that test, one addition in the `then` branch and none
in the `else` branch (`fresh_call_is_condBody`). That is the body whose live and
snapshot schedules `source_cond_eq_fused` and `native_eq_source_cond` compare.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInliningRound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open NamedSpaces (Handle)
open Eval
open DeclarativeSpec (Runs)
open BetaInlining
open BetaInliningControls (freshProgram freshBody fresh_inlinable fresh_inlined_is_body)
open Mettapedia.Machines.NestedQuerySchedule (Level Body)
open Mettapedia.Machines.NestedQueryEffects

/-- The pattern of the absence test under the solution's values. -/
def layerPattern (km t : Atom) : Atom := .expression [.symbol "layer", km, t]

theorem freshBody_shape : freshBody =
    .expression [.symbol "if",
      .expression [.symbol "==",
        .expression [.symbol "collapse", .expression [.symbol "match", .var "L",
          .expression [.symbol "layer", .var "km", .var "t"], .symbol "t"]],
        .expression []],
      .expression [.symbol "add-atom", .var "N", .var "t"], .symbol "done"] := rfl

theorem apply_match (state : Effects.State) (handle : Handle) (pattern template : Atom)
    (rows : List Atom) (read : state.read handle = some rows) :
    StdLib.apply state "match" [Effects.handleValue handle, pattern, template] =
      .ok (state, SpaceSemantics.query rows pattern template) := by
  have located : (Effects.readHandle (Effects.handleValue handle) >>= state.read) = some rows := by
    rw [Effects.readHandle_handleValue]; exact read
  show (match Effects.readHandle (Effects.handleValue handle) >>= state.read with
    | some rows => Except.ok (state, SpaceSemantics.query rows pattern template)
    | none => Except.error Effects.Fault.invalidSpace) = _
  rw [located]

theorem apply_add_atom (state after : Effects.State) (handle : Handle) (atom : Atom)
    (inserted : Effects.insert state handle atom = some after) :
    StdLib.apply state "add-atom" [Effects.handleValue handle, atom] =
      .ok (after, [Effects.boolean true]) := by
  have located : (Effects.readHandle (Effects.handleValue handle) >>= fun handle =>
      Effects.insert state handle atom) = some after := by
    rw [Effects.readHandle_handleValue]; exact inserted
  show (match Effects.readHandle (Effects.handleValue handle) >>= fun handle =>
      Effects.insert state handle atom with
    | some after => Except.ok (after, [Effects.boolean true])
    | none => Except.error Effects.Fault.invalidSpace) = _
  rw [located]

/-- The answers of the absence test's query: `t` once for every row of the layer space
that is `(layer km t)`. With `km` and `t` bound, the pattern `(layer $km $t)` tests
equality with the bound values. -/
def layerAnswers (rows : List Atom) (km t : Atom) : List Atom :=
  rows.filterMap fun row => if row = layerPattern km t then some (.symbol "t") else none

theorem layer_match (caller : Subst) (km t row : Atom)
    (boundKm : Subst.lookup caller "km" = some km) (boundT : Subst.lookup caller "t" = some t) :
    SpaceSemantics.matchValue caller (.expression [.symbol "layer", .var "km", .var "t"]) row =
      if row = layerPattern km t then some caller else none := by
  cases row with
  | var name => simp [SpaceSemantics.matchValue, layerPattern]
  | symbol name => simp [SpaceSemantics.matchValue, layerPattern]
  | grounded value => simp [SpaceSemantics.matchValue, layerPattern]
  | expression items =>
      rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by intro first rest same; simp at same)]
      rcases items with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
      · simp [SpaceSemantics.matchValue.matchValues, layerPattern]
      · simp [SpaceSemantics.matchValue.matchValues, layerPattern]
      · simp [SpaceSemantics.matchValue.matchValues, layerPattern]
      · have layerHead : SpaceSemantics.matchValue caller (.symbol "layer") first =
            if first = .symbol "layer" then some caller else none := by
          rw [SpaceSemantics.matchValue_literal (SpaceSemantics.Literal.symbol "layer")]
          by_cases same : first = .symbol "layer" <;> simp [same, eq_comm]
        have kmVar : SpaceSemantics.matchValue caller (.var "km") second =
            if second = km then some caller else none := by
          simp [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, boundKm]
        have tVar : SpaceSemantics.matchValue caller (.var "t") third =
            if third = t then some caller else none := by
          simp [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, boundT]
        simp only [SpaceSemantics.matchValue.matchValues, layerHead, layerPattern,
          Atom.expression.injEq, List.cons.injEq, and_true]
        by_cases one : first = .symbol "layer"
        · simp only [one, if_true, Option.bind_eq_bind, Option.bind_some, kmVar, true_and]
          by_cases two : second = km
          · simp only [two, if_true, Option.bind_some, tVar, true_and]
            by_cases three : third = t <;> simp [three]
          · simp [two]
        · simp [one]
      · simp [SpaceSemantics.matchValue.matchValues, layerPattern]

theorem layerAnswers_eq_nil_iff (rows : List Atom) (km t : Atom) :
    layerAnswers rows km t = [] ↔ rows.filter (fun row => decide (row = layerPattern km t)) = [] := by
  simp only [layerAnswers, List.filterMap_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro none row member same
    have := none row member
    simp_all
  · intro none row member
    have := none row member
    split <;> simp_all

/-- The body branches on the absence test. -/
theorem fresh_body_returns (caller : Subst) (layer output : Handle) (km t : Atom)
    (before : Effects.State) (layerRows : List Atom)
    (boundL : Subst.lookup caller "L" = some (Effects.handleValue layer))
    (boundKm : Subst.lookup caller "km" = some km)
    (boundT : Subst.lookup caller "t" = some t)
    (boundN : Subst.lookup caller "N" = some (Effects.handleValue output))
    (layerRead : before.read layer = some layerRows) :
    (layerAnswers layerRows km t = [] →
      ∀ after, Effects.insert before output t = some after →
        Returns freshProgram caller before freshBody after [Effects.boolean true]) ∧
    (layerAnswers layerRows km t ≠ [] →
      Returns freshProgram caller before freshBody before [.symbol "done"]) := by
  have collapsed : PureReturns freshProgram caller before
      (.expression [.symbol "collapse", .expression [.symbol "match", .var "L",
        .expression [.symbol "layer", .var "km", .var "t"], .symbol "t"]]) before
      (.expression (layerAnswers layerRows km t)) := by
    have location : applySubst caller (.var "L") = Effects.handleValue layer := by
      simp [applySubst, boundL]
    have space : (Effects.readHandle (applySubst caller (.var "L")) >>= before.read) =
        some layerRows := by
      rw [location, Effects.readHandle_handleValue]
      exact layerRead
    have collected := match_collapse_returns freshProgram caller before "L"
      (.expression [.symbol "layer", .var "km", .var "t"]) (.symbol "t") layerRows space
      (fun _ => .symbol "t") (fun _ bound _ => symbol_returns freshProgram bound before "t")
    have answers : (layerRows.filterMap fun row =>
        (SpaceSemantics.matchValue caller (.expression [.symbol "layer", .var "km", .var "t"])
          row).map fun _ => Atom.symbol "t") = layerAnswers layerRows km t := by
      unfold layerAnswers
      apply List.filterMap_congr
      intro row _
      rw [layer_match caller km t row boundKm boundT]
      split <;> rfl
    rwa [answers] at collected
  have unit : PureReturns freshProgram caller before (.expression []) before (.expression []) :=
    .step (step_transition rfl) (.step (step_transition rfl) (.refl _))
  have tested := native_binary_call_returns freshProgram caller before before before before "=="
    _ _ _ _ _ rfl (by decide) rfl rfl collapsed unit
    (StdLib.structural_equality before _ _) (by decide)
  rw [freshBody_shape]
  constructor
  · intro absent after inserted
    rw [absent] at tested
    refine if_returns freshProgram caller before before after _ _ _ _ _ tested ?_
    have added : PureReturns freshProgram caller before
        (.expression (.symbol "add-atom" :: ["N", "t"].map Atom.var)) after
        (Effects.boolean true) :=
      native_variable_call_returns freshProgram caller before after "add-atom" ["N", "t"]
        (Effects.boolean true) rfl (by decide)
        (by
          simp only [List.map_cons, List.map_nil, applySubst, boundN, boundT, Option.getD_some]
          exact apply_add_atom before after output t inserted) (by decide)
    simpa using added
  · intro present
    refine if_returns freshProgram caller before before before _ _ _ _ _ tested ?_
    have different : (Atom.expression (layerAnswers layerRows km t) == Atom.expression []) = false := by
      simpa using present
    simp only [different]
    have notTrue : (Effects.boolean false == Effects.boolean true) = false := by decide
    simp only [notTrue, Bool.false_eq_true, ↓reduceIte]
    exact symbol_returns freshProgram caller before "done"

theorem returns_runs {program : Program} {bindings : Subst} {before after : Effects.State}
    {e : Atom} {answers : List Atom} (returned : Returns program bindings before e after answers) :
    Runs program ⟨before, .evaluate bindings e, [], [], []⟩ (.complete after answers [] []) :=
  (completed_derivation_iff_path program _ after answers [] []).mpr returned

/-- The call completes as its body does. -/
theorem fresh_call_runs (caller : Subst)
    (bound : ∀ a ∈ ["L", "km", "t", "N"], ∃ value, Subst.lookup caller a = some value)
    (before after : Effects.State) (answers : List Atom)
    (body : Runs freshProgram ⟨before, .evaluate caller freshBody, [], [], []⟩
      (.complete after answers [] [])) :
    Runs freshProgram (callConfiguration "fresh" ["L", "km", "t", "N"] caller before [] [] [])
      (.complete after answers [] []) := by
  have beta := beta_complete before [] [] [] (fresh_inlinable caller bound) after answers [] []
  rw [beta]
  unfold inlinedConfiguration
  rw [fresh_inlined_is_body]
  exact body

/-! ## Read on the rows of the two spaces -/
/-! ## Read on the rows of the spaces -/

/-- The rows of the spaces the round reads, then the rows of the space it writes, each
tagged with its space. -/
def view (spaces : List Handle) (output : Handle) (state : Effects.State) :
    List (Handle × Atom) :=
  (spaces.flatMap fun space => ((state.read space).getD []).map (space, ·)) ++
    ((state.read output).getD []).map (output, ·)

/-- The absence test: a row of the layer space meeting `(layer km t)`. -/
def layerTest (layer : Handle) (km t : Atom) : Level (Handle × Atom) :=
  fun _ row => decide (row.1 = layer) && decide (row.2 = layerPattern km t)

theorem query_eq_nil_iff (rows : List Atom) (pattern template : Atom) :
    SpaceSemantics.query rows pattern template = [] ↔
      rows.filter (fun row => (SpaceSemantics.matchValue [] pattern row).isSome) = [] := by
  simp only [SpaceSemantics.query, List.filterMap_eq_nil_iff, List.filter_eq_nil_iff,
    Option.map_eq_none_iff, Option.isSome_iff_ne_none, ne_eq, not_not]

theorem mem_view_layer (spaces : List Handle) (layer output : Handle) (member : layer ∈ spaces)
    (separate : layer ≠ output) (state : Effects.State) (layerRows : List Atom)
    (layerRead : state.read layer = some layerRows) (x : Atom) :
    (layer, x) ∈ view spaces output state ↔ x ∈ layerRows := by
  simp only [view, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨space, _, atom, found, rfl, rfl⟩ | ⟨atom, _, same, rfl⟩)
    · rw [layerRead, Option.getD_some] at found
      exact found
    · exact absurd same.symm separate
  · intro found
    exact .inl ⟨layer, member, x, by rw [layerRead, Option.getD_some]; exact found, rfl, rfl⟩

theorem view_test_empty (spaces : List Handle) (layer output : Handle) (member : layer ∈ spaces)
    (separate : layer ≠ output) (km t : Atom) (state : Effects.State) (layerRows : List Atom)
    (layerRead : state.read layer = some layerRows) (chosen : List (Handle × Atom)) :
    ((view spaces output state).filter (layerTest layer km t chosen)).isEmpty =
      decide (layerAnswers layerRows km t = []) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.isEmpty_iff, List.filter_eq_nil_iff, decide_eq_true_iff, layerAnswers_eq_nil_iff,
    List.filter_eq_nil_iff]
  constructor
  · intro none x found matched
    exact none (layer, x) ((mem_view_layer spaces layer output member separate state layerRows
      layerRead x).mpr found) (by simp_all [layerTest])
  · rintro none ⟨space, x⟩ found tested
    simp only [layerTest, Bool.and_eq_true, decide_eq_true_eq] at tested
    obtain ⟨rfl, matched⟩ := tested
    exact none x ((mem_view_layer spaces space output member separate state layerRows
      layerRead x).mp found) (by simp [matched])

theorem view_insert (spaces : List Handle) (output : Handle) (outside : output ∉ spaces)
    {before after : Effects.State} {t : Atom} {outputRows : List Atom}
    (outputRead : before.read output = some outputRows)
    (inserted : Effects.insert before output t = some after) :
    view spaces output after = view spaces output before ++ [(output, t)] := by
  have reads : ∀ space ∈ spaces, after.read space = before.read space := by
    intro space member
    exact Effects.insert_read_other inserted (fun same => outside (same ▸ member))
  obtain ⟨rows, outputBefore, outputAfter⟩ := Effects.insert_reads_back inserted
  rw [outputRead, Option.some.injEq] at outputBefore
  subst outputBefore
  simp only [view, List.append_assoc, outputAfter, outputRead, Option.getD_some, List.map_append,
    List.map_cons, List.map_nil]
  congr 1
  exact List.flatMap_congr fun space member => by rw [reads space member]

/-- **The call of the round, solution by solution, is the branching body of the fused
round.** Under an environment binding the layer space, the two values and the output
space, the call `(fresh $L $km $t $N)` completes. Read on the rows of the spaces, its
final rows and answers are those of `condBody` for the absence test, with the addition of
`t` to the output space in the `then` branch, no change in the `else` branch, and the
answers `True` and `done`. Every space other than the output space is left as it was. -/
theorem fresh_call_is_condBody (caller : Subst) (spaces : List Handle) (layer output : Handle)
    (member : layer ∈ spaces) (outside : output ∉ spaces) (km t : Atom) (before : Effects.State)
    (layerRows outputRows : List Atom)
    (boundL : Subst.lookup caller "L" = some (Effects.handleValue layer))
    (boundKm : Subst.lookup caller "km" = some km)
    (boundT : Subst.lookup caller "t" = some t)
    (boundN : Subst.lookup caller "N" = some (Effects.handleValue output))
    (layerRead : before.read layer = some layerRows)
    (outputRead : before.read output = some outputRows)
    (deletes : Handle × Atom → Handle × Atom → Bool) (chosen : List (Handle × Atom)) :
    ∃ after answers,
      Runs freshProgram (callConfiguration "fresh" ["L", "km", "t", "N"] caller before [] [] [])
        (.complete after answers [] []) ∧
      (view spaces output after, answers) =
        condBody deletes (layerTest layer km t) (fun _ => [.add (output, t)]) (fun _ => [])
          (fun _ => [Effects.boolean true]) (fun _ => [.symbol "done"]) chosen
          (view spaces output before) ∧
      (∀ space ∈ spaces, after.read space = before.read space) ∧
      ∃ rows, after.read output = some rows := by
  have separate : layer ≠ output := fun same => outside (same ▸ member)
  have bound : ∀ a ∈ ["L", "km", "t", "N"], ∃ value, Subst.lookup caller a = some value := by
    intro a found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl | rfl | rfl
    · exact ⟨_, boundL⟩
    · exact ⟨_, boundKm⟩
    · exact ⟨_, boundT⟩
    · exact ⟨_, boundN⟩
  obtain ⟨whenAbsent, whenPresent⟩ := fresh_body_returns caller layer output km t before
    layerRows boundL boundKm boundT boundN layerRead
  have verdict := view_test_empty spaces layer output member separate km t before layerRows
    layerRead chosen
  by_cases absent : layerAnswers layerRows km t = []
  · obtain ⟨after, inserted⟩ : ∃ after, Effects.insert before output t = some after := by
      unfold Effects.insert
      simp only [outputRead, Option.bind_eq_bind, Option.bind_some]
      exact NamedSpaces.Store.write_exists_of_read_some before output outputRows
        (outputRows ++ [t]) outputRead
    refine ⟨after, [Effects.boolean true],
      fresh_call_runs caller bound before after _ (returns_runs (whenAbsent absent after inserted)),
      ?_, fun space found => Effects.insert_read_other inserted
        (fun same => outside (same ▸ found)), ?_⟩
    · simp only [condBody]
      rw [verdict, decide_eq_true absent]
      simp only [↓reduceIte, List.foldl_cons, List.foldl_nil, Effect.apply]
      rw [view_insert spaces output outside outputRead inserted]
    · obtain ⟨rows, _, outputAfter⟩ := Effects.insert_reads_back inserted
      exact ⟨_, outputAfter⟩
  · refine ⟨before, [.symbol "done"],
      fresh_call_runs caller bound before before _ (returns_runs (whenPresent absent)), ?_,
      fun _ _ => rfl, ⟨outputRows, outputRead⟩⟩
    simp only [condBody]
    rw [verdict, decide_eq_false absent]
    simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_nil]

/-! ## The round -/

/-- Complete runs of a call, one per environment, each from the store the one before
left, with their answers concatenated. -/
inductive RunsEach (program : Program) (call : Subst → Effects.State → Configuration) :
    List Subst → Effects.State → Effects.State → List Atom → Prop
  | nil (state : Effects.State) : RunsEach program call [] state state []
  | cons {environment : Subst} {rest : List Subst} {before middle after : Effects.State}
      {answers more : List Atom}
      (first : Runs program (call environment before) (.complete middle answers [] []))
      (others : RunsEach program call rest middle after more) :
      RunsEach program call (environment :: rest) before after (answers ++ more)

/-- The call of the round under an environment. -/
def freshCall (environment : Subst) (state : Effects.State) : Configuration :=
  callConfiguration "fresh" ["L", "km", "t", "N"] environment state [] [] []

/-- The body of the round over tagged rows: the absence test for the solution's target,
an addition of the target to the output space, and the answers `True` and `done`. -/
def roundBody (deletes : Handle × Atom → Handle × Atom → Bool) (layer output : Handle)
    (km : Atom) (target : List (Handle × Atom) → Atom) : Body (Handle × Atom) Atom :=
  condBody deletes (fun chosen => layerTest layer km (target chosen) chosen)
    (fun chosen => [.add (output, target chosen)]) (fun _ => [])
    (fun _ => [Effects.boolean true]) (fun _ => [.symbol "done"])

/-- The environment of each solution binds the layer space, the layer index, the target
and the output space. -/
def BindsRound (environment : List (Handle × Atom) → Subst) (layer output : Handle) (km : Atom)
    (target : List (Handle × Atom) → Atom) : Prop :=
  ∀ chosen, Subst.lookup (environment chosen) "L" = some (Effects.handleValue layer) ∧
    Subst.lookup (environment chosen) "km" = some km ∧
    Subst.lookup (environment chosen) "t" = some (target chosen) ∧
    Subst.lookup (environment chosen) "N" = some (Effects.handleValue output)

/-- **The calls, run one per solution, run the round's body.** Running the call under
each solution's environment, in order, from a store whose spaces are allocated, gives the
rows and answers of the round's body sequenced over the same solutions. -/
theorem calls_run_round (deletes : Handle × Atom → Handle × Atom → Bool)
    (spaces : List Handle) (layer output : Handle) (member : layer ∈ spaces)
    (outside : output ∉ spaces) (km : Atom) (target : List (Handle × Atom) → Atom)
    (environment : List (Handle × Atom) → Subst)
    (binds : BindsRound environment layer output km target) :
    ∀ (solutions : List (List (Handle × Atom))) (before : Effects.State) (acc : List Atom),
      (∃ rows, before.read layer = some rows) → (∃ rows, before.read output = some rows) →
      ∃ after answers,
        RunsEach freshProgram freshCall (solutions.map environment) before after answers ∧
        Mettapedia.Machines.NestedQuerySchedule.sequence (roundBody deletes layer output km target) solutions
            (view spaces output before, acc) = (view spaces output after, acc ++ answers)
  | [], before, acc, _, _ => ⟨before, [], .nil before, by simp [Mettapedia.Machines.NestedQuerySchedule.sequence]⟩
  | chosen :: rest, before, acc, ⟨layerRows, layerRead⟩, ⟨outputRows, outputRead⟩ => by
      obtain ⟨boundL, boundKm, boundT, boundN⟩ := binds chosen
      obtain ⟨middle, answers, running, step, reads, outputMiddle⟩ :=
        fresh_call_is_condBody (environment chosen) spaces layer output member outside km
          (target chosen) before layerRows outputRows boundL boundKm boundT boundN layerRead
          outputRead deletes chosen
      have layerMiddle : ∃ rows, middle.read layer = some rows :=
        ⟨layerRows, by rw [reads layer member, layerRead]⟩
      obtain ⟨after, more, others, sequenced⟩ :=
        calls_run_round deletes spaces layer output member outside km target environment binds
          rest middle (acc ++ answers) layerMiddle outputMiddle
      refine ⟨after, answers ++ more, .cons running others, ?_⟩
      have stepEq : roundBody deletes layer output km target chosen (view spaces output before) =
          (view spaces output middle, answers) := step.symm
      simp only [Mettapedia.Machines.NestedQuerySchedule.sequence, stepEq, sequenced, List.append_assoc]

/-- **The round of calls answers as the native round.** Over the solutions of the
snapshot join, the calls run one per solution leave, read on the rows of the spaces, the
bag of rows the native run leaves when it decides each absence test on the snapshot and
makes the additions in any order, and give the answers the snapshot verdicts give, when
no addition is read by the test or by a level after the first. -/
theorem calls_eq_native (deletes : Handle × Atom → Handle × Atom → Bool)
    (spaces : List Handle) (layer output : Handle) (member : layer ∈ spaces)
    (outside : output ∉ spaces) (km : Atom) (target : List (Handle × Atom) → Atom)
    (environment : List (Handle × Atom) → Subst)
    (binds : BindsRound environment layer output km target)
    (first : Level (Handle × Atom)) (rest : List (Level (Handle × Atom)))
    (before : Effects.State) (layerAllocated : ∃ rows, before.read layer = some rows)
    (outputAllocated : ∃ rows, before.read output = some rows)
    (keep : ∀ c ∈ Mettapedia.Machines.NestedQuerySchedule.join (view spaces output before) (first :: rest) [],
      ∀ e ∈ [Effect.add (output, target c)],
        KeepsReads deletes (view spaces output before)
          (guardedReads (fun chosen => layerTest layer km (target chosen) chosen) first rest
            (view spaces output before)) e)
    (commute : ∀ e ∈ changes (condSnapshotEffects (view spaces output before)
          (fun chosen => layerTest layer km (target chosen) chosen)
          (fun chosen => [.add (output, target chosen)]) (fun _ => []))
          first rest (view spaces output before),
      ∀ e' ∈ changes (condSnapshotEffects (view spaces output before)
          (fun chosen => layerTest layer km (target chosen) chosen)
          (fun chosen => [.add (output, target chosen)]) (fun _ => []))
          first rest (view spaces output before), Effect.Commute deletes e e')
    (native : List (Effect (Handle × Atom)))
    (perm : native.Perm (changes (condSnapshotEffects (view spaces output before)
          (fun chosen => layerTest layer km (target chosen) chosen)
          (fun chosen => [.add (output, target chosen)]) (fun _ => []))
          first rest (view spaces output before))) :
    ∃ after answers,
      RunsEach freshProgram freshCall
        ((Mettapedia.Machines.NestedQuerySchedule.join (view spaces output before) (first :: rest) []).map environment)
        before after answers ∧
      ((view spaces output after : List (Handle × Atom)) : Multiset (Handle × Atom)) =
        ((native.foldl (fun s e => e.apply deletes s) (view spaces output before) :
          List (Handle × Atom)) : Multiset (Handle × Atom)) ∧
      answers = (Mettapedia.Machines.NestedQuerySchedule.join (view spaces output before) (first :: rest) []).flatMap
        (condSnapshotAnswers (view spaces output before)
          (fun chosen => layerTest layer km (target chosen) chosen)
          (fun _ => [Effects.boolean true]) (fun _ => [.symbol "done"])) := by
  set initial := view spaces output before
  set test : Level (Handle × Atom) := fun chosen => layerTest layer km (target chosen) chosen
  obtain ⟨after, answers, running, sequenced⟩ := calls_run_round deletes spaces layer output
    member outside km target environment binds
    (Mettapedia.Machines.NestedQuerySchedule.join initial (first :: rest) []) before [] layerAllocated outputAllocated
  have keep' : ∀ c ∈ Mettapedia.Machines.NestedQuerySchedule.join initial (first :: rest) [],
      ∀ e ∈ (fun chosen => [Effect.add (output, target chosen)]) c ++ (fun _ => []) c,
        KeepsReads deletes initial (guardedReads test first rest initial) e := by
    intro c hc e he
    simp only [List.append_nil] at he
    exact keep c hc e he
  -- the live round is the fused round: no change touches what is read again
  have start : Keeps initial (guardedReads test first rest initial) initial :=
    ⟨fun _ _ => rfl, fun _ hu => Or.inl hu⟩
  have preserve : ∀ c ∈ Mettapedia.Machines.NestedQuerySchedule.join initial (first :: rest) [], ∀ s,
      Keeps initial (guardedReads test first rest initial) s →
        Keeps initial (guardedReads test first rest initial)
          (roundBody deletes layer output km target c s).1 := by
    intro c hc s k
    simp only [roundBody, condBody]
    split
    · exact keeps_foldl deletes _ (fun e he => keep' c hc e (List.mem_append_left _ he)) s k
    · exact keeps_foldl deletes _ (fun e he => keep' c hc e (List.mem_append_right _ he)) s k
  have liveFused : Mettapedia.Machines.NestedQuerySchedule.source id (roundBody deletes layer output km target)
      (first :: rest) [] initial =
      Mettapedia.Machines.NestedQuerySchedule.fused (roundBody deletes layer output km target) (first :: rest) initial :=
    source_eq_fused (roundBody deletes layer output km target) initial
      (Keeps initial (guardedReads test first rest initial)) first rest start
      (fun s k e he => k.1 e (List.mem_append_left _ he)) preserve
  have nativeSource := native_eq_source_cond deletes test
    (fun chosen => [.add (output, target chosen)]) (fun _ => [])
    (fun _ => [Effects.boolean true]) (fun _ => [.symbol "done"]) first rest initial keep'
    commute native perm
  have runsFused : Mettapedia.Machines.NestedQuerySchedule.fused (roundBody deletes layer output km target)
      (first :: rest) initial = (view spaces output after, answers) := by
    simpa [Mettapedia.Machines.NestedQuerySchedule.fused] using sequenced
  refine ⟨after, answers, running, ?_, ?_⟩
  · rw [nativeSource.1]
    have : (Mettapedia.Machines.NestedQuerySchedule.source id (condBody deletes test
        (fun chosen => [.add (output, target chosen)]) (fun _ => [])
        (fun _ => [Effects.boolean true]) (fun _ => [.symbol "done"])) (first :: rest) [] initial).1 =
        view spaces output after := by
      have := congrArg Prod.fst (liveFused.trans runsFused)
      simpa [roundBody, test] using this
    rw [this]
  · have := congrArg Prod.snd (liveFused.trans runsFused)
    rw [← nativeSource.2]
    simpa [roundBody, test] using this.symm

end Mettapedia.Languages.MeTTa.PeTTa.BetaInliningRound
