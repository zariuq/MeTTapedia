import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Schedule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.DispatchCost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedWork
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.InterpretationCost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Meter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationCache
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.ListSpaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleWaiting

/-! # Source effect, continuation, and waiting controls -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.ContinuationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleRace (D H h0 a program supply)
open Evaluation (Evaluator)

private abbrev Knowledge := List (Constraint mkeys [] ())
private abbrev Storage := ListStorage mkeys [] ()
private abbrev State := Machine.State mkeys [] () MTy Storage

private noncomputable def search {A : Type} (test : A → Prop) : SearchAnswer test := by
  classical
  exact if found : ∃ value, test value then
    .found (Classical.choose found) (Classical.choose_spec found)
  else .absent (fun value valid => found ⟨value, valid⟩)

private noncomputable def live (knowledge : Knowledge) : Decidable (Solvable knowledge) :=
  if reflexive : knowledge.all (fun equation => decide (equation.1 = equation.2)) = true then
    isTrue ⟨Name mkeys, fam mkeys, generator (fam mkeys), by
      intro equation member
      have same := of_decide_eq_true ((List.all_eq_true.mp reflexive) equation member)
      rw [same]⟩
  else Classical.propDecidable _

private noncomputable def address (knowledge : Knowledge) (datum : MData) :
    SearchAnswer (Determines knowledge datum) :=
  if atH : datum = H then
    match live knowledge with
    | isTrue ready =>
      .found h0 ⟨ready, fun _ assign _ => by
        rw [atH]
        exact Rigid.instantiate_include assign h0⟩
    | isFalse dead => .absent (fun _ resolved => dead resolved.1)
  else if empty : knowledge = [] then
    if unknown : datum = ExampleWaiting.S then .absent (by
      rw [empty, unknown]
      exact ExampleWaiting.undetermined)
    else search (Determines knowledge datum)
  else search (Determines knowledge datum)

private noncomputable def evaluator : Evaluator mkeys D Storage where
  solver := ⟨live, address, fun knowledge => search (Principal knowledge),
    fun _ _ _ => Classical.propDecidable _⟩
  checks := ⟨fun _ _ _ => isTrue (fun _ _ => trivial), fun _ _ _ => Classical.propDecidable _⟩
  spaces := listSpaces
  program := program
  supply := supply

private def strategy : Strategy mkeys [] () MTy where
  chooses config branch := branch ∈ config.branches
  solverSteps _ branch := branch.store.length
  selectionVisits _ _ := 1
  spaceSteps _ _ := 1

private def first : Machine.Scheduler evaluator strategy
  | ⟨_, []⟩ => none
  | ⟨world, active :: pending⟩ => some
    ⟨⟨0, Nat.zero_lt_succ _⟩, by
      change active ∈ ((active :: pending : List (Branch mkeys [] () MTy)) : Multiset _)
      simp⟩

private def start (code : Comp mkeys [] () MTy) (stored : List (Row mkeys [] ()) := []) : State :=
  ⟨⟨0, 0, fun _ => stored⟩, [⟨[], .eval code, [], []⟩]⟩

private def values (state : State) : List MData :=
  state.agenda.filterMap fun branch =>
    match branch.focus, branch.frames with
    | .value value, [] => some value
    | _, _ => none

private def mutateThenFail : Comp mkeys [] () MTy :=
  .choice (.add H a .fail) (.query H a (.ret (num 7)))

theorem the_failure_continuation_keeps_the_insert :
    let result := Machine.run evaluator strategy first 7 (start mutateThenFail)
    values result.1 = [num 7] ∧
    (result.1.world.storage h0).map Row.atom = [a] ∧
    result.2.map Charge.request = [none, some (.insert H a), none, some (.query H a), none] := by
  decide +kernel

private def removeOne : Comp mkeys [] () MTy :=
  .remove H a (.query H a (.ret (num 2)))

theorem one_copy_removal_preserves_the_other :
    let result := Machine.run evaluator strategy first 6 (start removeOne [⟨a, []⟩, ⟨a, []⟩])
    values result.1 = [num 2] ∧
    (result.1.world.storage h0).map Row.atom = [a] ∧
    result.2.map Charge.request = [some (.erase H a), some (.query H a), none] := by
  decide +kernel

theorem query_keeps_duplicate_occurrences :
    let result := Machine.run evaluator strategy first 1
      (start (.query H a (.ret (num 2))) [⟨a, []⟩, ⟨a, []⟩])
    result.1.agenda.length = 2 ∧ result.2.map Charge.alternatives = [2] := by
  decide +kernel

theorem unavailable_address_keeps_the_pending_branch :
    let waiting := Machine.run evaluator strategy first 4 (start ExampleWaiting.addQuery)
    let failed := Machine.run evaluator strategy first 4 (start .fail)
    waiting.1.agenda.length = 1 ∧ waiting.2.isEmpty = true ∧
      failed.1.agenda.isEmpty = true ∧ failed.2.length = 1 := by
  decide +kernel

private def binder : Comp mkeys [] () MTy := .let_ [9] (mvar [9] 0) (.ret (num 5)) (.ret (mvar [9] 0))

theorem value_resumes_the_lexical_binding :
    let result := Machine.run evaluator strategy first 3 (start binder)
    result.1.world.scope = 1 ∧
      result.1.agenda.map Branch.store = [[(instantiate (openAt mkeys [9] 0) (mvar [9] 0), num 5)]] :=
  ⟨rfl, rfl⟩

private def permits (state : State) (position : Fin state.agenda.length) :
    Decidable (strategy.chooses (state.source evaluator.spaces) (state.agenda.get position)) :=
  isTrue (List.get_mem state.agenda position)

theorem firstReady_skips_a_finished_branch :
    let state := start (.ret (num 2))
    let state := {state with agenda := ⟨[], .value (num 2), [], []⟩ :: state.agenda}
    (Machine.firstReady evaluator strategy permits state).map (fun transition => values transition.next) =
      some [num 2, num 2] := by
  decide +kernel

open Mettapedia.Machines (MachineCore)
open Mettapedia.Machines.Specialization.Driving (Advance)

private abbrev TraceState := Meter.Ledger mkeys [] () MTy Storage
private noncomputable def traceMachine := Meter.core evaluator strategy first

/-- A test provider certifies a two-move prefix from the ordinary
evaluator. Subsequent admission checks can therefore be exercised
without requiring a separate backend. -/
private noncomputable def twoMoves (before : TraceState) :
    Option (Advance traceMachine before) :=
  let result := traceMachine.runSlice 2 before
  if finished : result.2 = 2 then
    some ⟨result.1, 2, by decide, Prod.ext rfl finished⟩
  else none

private noncomputable def beforeFirstPublication (before : TraceState) :
    Option (Advance traceMachine before) :=
  if before.reverseWork.isEmpty then twoMoves before else none

theorem refusal_keeps_the_effect_and_prior_charge :
    let initial : TraceState := ⟨start mutateThenFail, []⟩
    let driven := Mettapedia.Machines.Specialization.Driving.run traceMachine beforeFirstPublication 2 7 initial
    driven.used = 2 ∧ driven.reason = .refusal ∧
      (driven.target.current.world.storage h0).map Row.atom = [a] ∧
      driven.target.reverseWork.reverse.map Charge.request = [none, some (.insert H a)] := by
  decide +kernel

theorem short_credit_stays_before_the_prepared_segment :
    let initial : TraceState := ⟨start mutateThenFail, []⟩
    let driven := Mettapedia.Machines.Specialization.Driving.run traceMachine twoMoves 1 1 initial
    driven.used = 0 ∧ driven.reason = .credit ∧
      (driven.target.current.world.storage h0).isEmpty = true := by
  decide +kernel

theorem ordinary_handback_retains_the_exact_work :
    let initial : TraceState := ⟨start mutateThenFail, []⟩
    let driven := Mettapedia.Machines.Specialization.Driving.run traceMachine beforeFirstPublication 2 7 initial
    let emitted := (traceMachine.runSlice (7 - driven.used) driven.target).1
    values emitted.current = [num 7] ∧
      emitted.reverseWork.reverse.map Charge.request = [none, some (.insert H a), none, some (.query H a), none] := by
  decide +kernel

private def callF : MData := tuple [sym "f"]
private def equation : PreparedCall.Clause D := ⟨[0], callF, .ret (num 11)⟩

private def withEquation : Program mkeys [] () MTy :=
  {program with equations := [equation, ⟨[1], tuple [sym "g"], .ret (num 12)⟩]}

private def selectedHead : PreparedCall.Head := .inl "f"

theorem duplicate_equation_occurrences_refuse_compilation :
    (PreparedCall.compile (D := D) {program with equations := [equation, equation]} selectedHead).isNone = true := by
  decide +kernel

private noncomputable def tryEntry (representable fits : Branch mkeys [] () MTy → Bool) :
    Option (Except PreparedCall.Decline (Branch mkeys [] () MTy)) :=
  (PreparedCall.compile (D := D) withEquation selectedHead).map fun plan =>
    PreparedCall.activate plan evaluator.solver ((start (.ret a)).world.source evaluator.spaces)
      [] callF [] [] representable fits

theorem prepared_entry_uses_the_selected_equation :
    (tryEntry (fun branch => branch.store.length ≤ 1) (fun branch => branch.frames.isEmpty)).map
      (fun outcome => match outcome with
      | .ok branch => match branch.focus with
        | .eval (.ret value) => some value
        | _ => none
      | .error _ => none) = some (some (num 11)) := by
  decide +kernel

private def refusal (outcome : Except PreparedCall.Decline (Branch mkeys [] () MTy)) :
    Option PreparedCall.Decline :=
  match outcome with
  | .ok _ => none
  | .error reason => some reason

theorem prepared_entry_refuses_unrepresentable_and_short_storage :
    (tryEntry (fun branch => branch.store.isEmpty) (fun branch => branch.frames.isEmpty)).map refusal =
      some (some .unrepresentable) ∧
    (tryEntry (fun branch => branch.store.length ≤ 1) (fun branch => branch.store.isEmpty)).map refusal =
      some (some .capacity) := by
  decide +kernel

private def last : Machine.Scheduler evaluator strategy
  | ⟨_, []⟩ => none
  | ⟨_, head :: rest⟩ => some
    ⟨⟨rest.length, Nat.lt_succ_self _⟩, List.get_mem (head :: rest) _⟩

theorem choosing_the_query_first_does_not_see_the_later_insert :
    let result := Machine.run evaluator strategy last 7 (start mutateThenFail)
    (values result.1).isEmpty = true ∧
    (result.1.world.storage h0).map Row.atom = [a] ∧
    result.2.map Charge.request = [none, some (.query H a), some (.insert H a), none] := by
  decide +kernel

private def changedOther : Program mkeys [] () MTy :=
  {withEquation with equations := [⟨[1], tuple [sym "g"], .ret (num 50)⟩, equation]}

theorem an_excluded_equation_edit_keeps_the_compiled_body :
    (PreparedCall.compile (D := D) withEquation selectedHead).map
      (fun plan => match (plan.rebind (current := changedOther) rfl).selected.rhs with
        | .ret value => some value
        | _ => none) = some (some (num 11)) := by decide +kernel

private def editedEquation : Program mkeys [] () MTy :=
  {withEquation with equations := [{equation with rhs := .ret (num 22)}]}

private noncomputable def compiledAgainst : Evaluator mkeys D Storage :=
  {evaluator with program := withEquation}

private noncomputable def resumedAgainst : Evaluator mkeys D Storage :=
  {evaluator with program := editedEquation}

theorem new_equation_takes_effect_at_the_retained_boundary :
    let original : TraceState := ⟨start (.add H a (.apply callF)), []⟩
    let cut := ((Meter.core compiledAgainst strategy first).runSlice 1 original).1
    let result := ((Meter.core resumedAgainst strategy first).runSlice 5 cut).1
    values result.current = [num 22] ∧ (result.current.world.storage h0).map Row.atom = [a] ∧
      result.reverseWork.reverse.map Charge.request = [some (.insert H a), none, none] := by
  decide +kernel

private def indexed (handle : MClosed) : Bool × MClosed := (false, handle)

private theorem indexed_injective : Function.Injective indexed :=
  fun _ _ same => congrArg Prod.snd same

theorem encoded_space_preserves_other_handle_and_duplicate :
    let spaces : Spaces mkeys [] () ((Bool × MClosed) → List (Row mkeys [] ())) :=
      indexedSpaces indexed indexed_injective
    let first := spaces.insert (fun _ => []) h0 ⟨a, []⟩
    let second := spaces.insert first h0 ⟨a, []⟩
    (spaces.erase second h0 (fun _ => true)).map
      (fun (_, rest) => ((spaces.rows rest h0).length, (spaces.rows rest (csym "other")).length)) =
      some (1, 0) := by
  decide +kernel


section BodyPreparation

open BindingPlans BindingTemplates
open BindingSimulation (Surrounding Keeps)

private def between (after : List (Branch mkeys [] () MTy) := []) : Surrounding mkeys [] () MTy :=
  ⟨[], after⟩

private theorem first_holds_position (after : List (Branch mkeys [] () MTy)) :
    Keeps evaluator strategy first (between after) := by
  intro _ _
  rfl

private def openVar (scopes : List Nat) : MData :=
  nameAt mkeys scopes ⟨[0], 0, ([], ())⟩

private def shadowing : Comp mkeys [] () MTy :=
  .let_ [0] (openVar []) (.ret (num 6))
    (.let_ [0] (openVar []) (.ret (openVar [])) (.ret (tuple [openVar [], openVar []])))

private def localProducer : Comp mkeys [] () MTy :=
  .let_ [0] (openVar [])
    (.let_ [0] (openVar []) (.ret (num 6)) (.ret (openVar [])))
    (.ret (openVar []))

private def compiledReadback (code : Comp mkeys [] () MTy) : Option (Except Refusal (Knowledge × MData)) :=
  (compile code).map fun plan =>
    let implementation := Words.templates (κ := mkeys) (Γ := []) (star := ()) 2 4
    (BindingTemplates.run implementation plan 7 [3] 0 (Vector.replicate 2 [])).map fun result =>
      (result.1.2.map implementation.equation, implementation.view result.2)

theorem shadowing_preserves_outer_alias_and_repeated_use :
    compiledReadback shadowing =
      some (.ok ([(openVar [7, 3], num 6), (openVar [8, 7, 3], openVar [7, 3])],
        tuple [openVar [8, 7, 3], openVar [8, 7, 3]])) := rfl

theorem a_producers_own_binding_does_not_open_its_continuation :
    compiledReadback localProducer =
      some (.ok ([(openVar [7, 3], num 6), (openVar [8, 3], openVar [7, 3])], openVar [8, 3])) := rfl

private def smallBody : Comp mkeys [] () MTy :=
  .let_ [0] (num 0) (.ret (num 0)) (.let_ [0] (num 1) (.ret (num 1)) (.ret (num 9)))

private def world : ExecutionWorld Storage := ⟨1, 3, fun _ => [⟨a, []⟩]⟩

private noncomputable def tryBody (code : Comp mkeys [] () MTy) (capacity width credit : Nat) :
    Option (Except Refusal (PreparedBodies.Publication mkeys [] () MTy Storage)) :=
  (compile code).map fun plan =>
    PreparedBodies.activate (Words.templates capacity width) evaluator.solver plan (between []) world
      [] [] [] [] (Vector.replicate capacity []) credit

theorem checked_body_preserves_world_and_publishes_one_value :
    (tryBody smallBody 2 3 7).map (Except.map fun result =>
      (result.state.world.scope, result.state.world.handles, (result.state.world.storage h0).map Row.atom,
        values result.state, result.debit)) = some (.ok (3, 3, [a], [num 9], 7)) := rfl

theorem guards_distinguish_table_exhaustion_word_overflow_and_source_credit :
    tryBody smallBody 1 3 7 = some (.error .capacity) ∧
    tryBody smallBody 2 1 7 = some (.error .scopeOverflow) ∧
    tryBody smallBody 2 3 6 = some (.error .credit) := ⟨rfl, rfl, rfl⟩

theorem ordinary_handback_runs_from_before_the_failed_segment :
    let before := PreparedBodies.entryState (between []) world [] smallBody [] [] []
    let ordinary := Machine.run evaluator strategy first 7 before
    (tryBody smallBody 2 1 7).map (PreparedBodies.resume first 7 before) =
      some (ordinary.1, ordinary.2.length) := by
  rw [guards_distinguish_table_exhaustion_word_overflow_and_source_credit.2.1]
  rfl

theorem a_different_selection_policy_cannot_admit_the_region :
    let after : List (Branch mkeys [] () MTy) := [⟨[], .value (num 0), [], []⟩]
    Keeps evaluator strategy first (between after) ∧
      ¬ Keeps evaluator strategy last (between after) := by
  refine ⟨first_holds_position _, ?_⟩
  intro kept
  have choosesSlot := kept world ⟨[], .eval (.ret (num 1)), [], []⟩
  change (some 1 : Option Nat) = some 0 at choosesSlot
  cases choosesSlot

theorem effect_and_choice_remain_source_boundaries :
    let selection : Comp mkeys [] () MTy :=
      .let_ [0] (num 0) (.ret (num 0)) (.choice (.ret (num 7)) (.ret (num 8)))
    compile mutateThenFail = none ∧ compile selection = none := ⟨rfl, rfl⟩

theorem equation_preparation_respects_its_static_template_budget :
    (EquationPlans.compile (D := D) withEquation selectedHead 2).isSome = true ∧
    (EquationPlans.compile (D := D) withEquation selectedHead 1).isSome = false := ⟨rfl, rfl⟩

theorem duplicate_entry_requests_share_one_prepared_body :
    let cache := EquationCache.prepare (D := D) withEquation [selectedHead, selectedHead, selectedHead]
    cache.entries.length = 1 ∧ cache.used = 2 := ⟨rfl, rfl⟩

private def tailBody : Comp mkeys [] () MTy :=
  .let_ [0] (num 0) (.ret (num 0)) (.apply callF)

theorem tail_region_stops_before_the_next_equation_entry :
    (tryBody tailBody 1 3 5).map (Except.map fun result =>
      (result.state.agenda.map Branch.focus, result.state.world.scope, result.debit)) =
        some (.ok ([.eval (.apply callF)], 2, 3)) := rfl

theorem a_producer_call_requires_the_ordinary_continuation :
    let code : Comp mkeys [] () MTy := .let_ [0] (num 0) (.apply callF) (.ret (num 9))
    compile code = none := rfl

private noncomputable def caller : Evaluator mkeys D Storage := {evaluator with program := withEquation}

theorem ordinary_equation_entry_can_resume_the_prepared_tail :
    let initial := PreparedBodies.entryState (between []) world [] tailBody [] [] []
    let resumed := (tryBody tailBody 1 3 5).map
      (PreparedBodies.resume (machine := caller) first 5 initial)
    (resumed.map fun result => (result.1.world.scope, values result.1, result.2)) =
      some (3, [num 11], 5) := rfl

private def bodyPrices : BindingExpenses.Prices mkeys [] () where
  openScope := 3
  hold _ := 2

private noncomputable def preparedWithWork (capacity budget : Nat) :
    Option (Except Refusal (List MData) × Nat) :=
  (compile smallBody).map fun plan =>
    let attempt := PreparedWork.activate (Words.templates capacity 3) bodyPrices evaluator.solver
      (BindingExpenses.reserve bodyPrices plan) (between []) world [] [] [] []
      (Vector.replicate capacity []) 5 budget 7
    (attempt.answer.map fun result => values result.state, attempt.elapsed)

theorem the_reserved_body_pays_the_final_check_once :
    preparedWithWork 2 21 = some (.ok [num 9], 21) := rfl

theorem a_failed_template_pays_only_its_reached_prefix :
    preparedWithWork 1 21 = some (.error .capacity, 12) := rfl

theorem inadequate_work_is_rejected_before_any_template :
    preparedWithWork 2 20 = some (.error .credit, 0) := rfl

private def smallShape : Fragment mkeys [] () MTy .answer smallBody :=
  .binding [0] (num 0) (.hold (num 0)) (.binding [0] (num 1) (.hold (num 1)) (.hold (num 9)))

theorem prepared_small_body_pays_only_its_authored_work :
    let tariff : InterpretationCost.Tariff := ⟨3, 2, 1, 1⟩
    let measured := BindingExpenses.measure (Words.templates 2 3) tariff.prepared
      (lower smallShape [] 0) 1 [] 0 (Vector.replicate 2 [])
    InterpretationCost.sourceWork tariff smallShape = 21 ∧ measured.elapsed = 21 := ⟨rfl, rfl⟩

theorem interpreting_a_held_value_pays_a_dispatch :
    let code : Comp mkeys [] () MTy := .ret (num 9)
    let shape : Fragment mkeys [] () MTy .answer code := .hold (num 9)
    let ordinary := InterpretationCost.interpreted first 1 (start code)
    let productive := InterpretationCost.sourceWork InterpretationCost.handleTariff shape
    values ordinary.state = [num 9] ∧ ordinary.dispatches = 1 ∧
      productive < productive + ordinary.dispatches := ⟨rfl, rfl, by decide⟩

private theorem unequal_constraint_is_dead : ¬ Solvable ([(num 1, num 2)] : Knowledge) := by
  apply FunctionVariables.dead_of_roots (K := []) (a := num 1) (b := num 2) (c := .inr (.inl 1))
    (c' := .inr (.inl 2)) rfl rfl
  decide

theorem incompatible_binding_never_publishes :
    tryBody (.let_ [0] (num 1) (.ret (num 2)) (.ret (num 9))) 1 3 4 = some (.error .inconsistent) := by
  have rejects : evaluator.solver.satisfiable [(num 1, num 2)] = false :=
    Bool.eq_false_iff.mpr fun trueValue => unequal_constraint_is_dead ((evaluator.solver.satisfiable_iff _).mp trueValue)
  change some (if evaluator.solver.satisfiable [(num 1, num 2)] then _ else Except.error Refusal.inconsistent) = _
  rw [rejects]
  rfl

end BodyPreparation

section DispatchPricing

private def prices : DispatchCost.Prices mkeys [] () MTy Storage where
  selection _ := 1
  live _ _ := 1
  reduction _ _ := 1

theorem lookup_and_grafting_charge_new_alternatives :
    let result := DispatchCost.run evaluator strategy first prices 1 (start (.ret (num 9)))
    result.elapsed = 8 ∧ result.moves.length = 1 ∧ units result.moves = 4 ∧
      values result.state = [num 9] := ⟨rfl, rfl, rfl, rfl⟩

private def noneSelected : Machine.Scheduler evaluator strategy := fun _ => none

private def scanPrices : DispatchCost.Prices mkeys [] () MTy Storage where
  selection state := state.agenda.length
  live _ _ := 0
  reduction _ _ := 0

theorem a_paid_scan_can_end_without_a_source_move :
    DispatchCost.Adequate evaluator strategy noneSelected scanPrices
      (fun state => state.agenda.length) 1 := by
  constructor
  · intro _ _ unavailable
    cases unavailable
  · intro state
    simp [scanPrices, DispatchCost.selectionQuota, noneSelected]
  · intros
    exact Nat.zero_le _
  · intros
    exact Nat.zero_le _

theorem moves_alone_cannot_bound_an_unproductive_scan (factor startup : Nat) :
    ∃ input : State,
      let result := DispatchCost.run evaluator strategy noneSelected scanPrices 1 input
      factor * units result.moves + startup < result.elapsed := by
  refine ⟨⟨world, List.replicate (startup + 1) ⟨[], .value (num 0), [], []⟩⟩, ?_⟩
  simp [DispatchCost.run, DispatchCost.step, scanPrices, noneSelected, units]

end DispatchPricing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.ContinuationControls
