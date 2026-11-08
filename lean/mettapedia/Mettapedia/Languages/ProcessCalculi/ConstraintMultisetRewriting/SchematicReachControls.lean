import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

/-!
# One physical schema, two private read instances and an atomic delivery

The selected event reads occurrence 7 twice, matching different data values.
It publishes one correlated pair at a write-only destination. A distinct
occurrence retains an explicit shared reference. The joint problem accepts
every assignment of that retained caller reference. Replacing the reusable
schema by the shared reference makes the same two reads inconsistent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

inductive DataOperator where
  | symbol : Nat → DataOperator
  | pair
  deriving DecidableEq

abbrev dataSignature : Signature where
  Srt := Unit
  Op _ := DataOperator
  arity
    | .symbol _ => []
    | .pair => [([],()),([],())]

local instance : DecidableEq dataSignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : dataSignature.Srt) : DecidableEq (dataSignature.Op sort) :=
  inferInstanceAs (DecidableEq DataOperator)

abbrev spaceSignature := SchematicReach.base dataSignature () Nat
abbrev locals (_ : Nat) : MetaArity spaceSignature := ([],())
abbrev captures (_ : Nat) : MetaArity spaceSignature := ([],())
abbrev active := Active locals captures

def symbol {Variables : Type} {decl : Variables → MetaArity spaceSignature} (number : Nat) : Closed decl :=
  .op (.inl (.inl (DataOperator.symbol number))) .nil

def pair {Variables : Type} {decl : Variables → MetaArity spaceSignature}
    (first second : Closed decl) : Closed decl :=
  .op (.inl (.inl DataOperator.pair)) (.cons first (.cons second .nil))

theorem symbol_injective {Variables : Type} {decl : Variables → MetaArity spaceSignature}
    {a b : Nat} (same : (symbol a : Closed decl) = symbol b) : a = b := by
  have operators := Sum.inl.inj (Sum.inl.inj (Term.op.inj same).1)
  exact DataOperator.symbol.inj operators

def addresses (occurrence : Nat) : Closed captures := if occurrence = 7 then name 1 else name 2
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if occurrence = 7 then ContextualStoredRows.store locals captures (generator locals 0)
  else .shared (generator captures 0)

def before : Configuration (Closed captures) Nat := ⟨[],{7,11}⟩
def selection : Selection Nat := ⟨[],[7,7],[8]⟩
def rule : NamedSpaces.LocatedRule (Closed active) :=
  ⟨[],[(name 1,symbol 10),(name 1,symbol 20)],[],[],[(name 9,pair (symbol 10) (symbol 20))]⟩

def known : Set (Closed active) :=
  {name 1,symbol 10,symbol 20,pair (symbol 10) (symbol 20),
    place (name 1) (symbol 10),place (name 1) (symbol 20)}
def written : Set Nat := {9}
def produced (_ : Nat) : Closed active × Closed active := (name 9,pair (symbol 10) (symbol 20))
def outputs (occurrence : Nat) : Closed active := place (produced occurrence).1 (produced occurrence).2
def problem := eventProblem locals captures ∅ selection addresses rows before rule

def localVariable (scope identity : Nat) : Closed active :=
  generator active (.inl (ScopedVar.at scope identity))

theorem problem_explicit : problem =
    [(place (name 1) (symbol 10),place (name 1) (localVariable 2 0)),
     (place (name 1) (symbol 20),place (name 1) (localVariable 3 0))] := by
  with_unfolding_all rfl

def solution {Future : Type} (future : Future → MetaArity spaceSignature)
    (caller : Assignment captures future) : Assignment active future
  | .inl ⟨scope,_⟩ => if scope = 2 then symbol 10 else symbol 20
  | .inr identity => caller identity

theorem two_reads_accept_every_caller {Future : Type} (future : Future → MetaArity spaceSignature)
    (caller : Assignment captures future) : ContextualFrameUnifier.Models (solution future caller) problem := by
  rw [problem_explicit]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · with_unfolding_all rfl
  · obtain rfl := List.mem_singleton.mp member
    with_unfolding_all rfl

theorem consistent : ContextualFrameUnifier.Solvable problem :=
  ContextualFrameUnifier.solvable_of_model (two_reads_accept_every_caller captures (generator captures))

theorem held : Held locals captures known written rule := by
  constructor
  · intro term member
    simp only [lowerRule,rule,List.map_nil,List.map_cons,List.nil_append,List.mem_cons,List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> simp [known]
  · intro equation member
    cases member
  · intro address member
    simp only [rule,List.map_nil,List.map_cons,List.filterMap_nil,List.append_nil,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst address
    simp [known]
  · intro port member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr ⟨9,by simp [written],rfl,by simp [known]⟩

theorem enabled : Enabled outputs before.present selection.commit := by decide

theorem one_reached : Reached locals captures ∅ selection known addresses rows before 1 := by
  apply Reach.of_possesses
  apply written_name_possessed (store := [])
  · exact ContextualFrameUnifier.solvable_of_model
      (show ContextualFrameUnifier.Models (generator active) [] by simp [ContextualFrameUnifier.Models])
  · simp [known]

theorem admitted : Admits locals captures ∅ selection known written addresses rows before rule outputs := by
  refine ⟨held,?_,rfl,rfl,?_,consistent,?_,?_,?_⟩
  · exact (ContextualInteractionFactors.resources_iff outputs selection before.present).mpr
      ⟨by decide,by decide,enabled⟩
  · with_unfolding_all rfl
  · intro occurrence member
    have same : occurrence = 7 := by simpa [selection] using member
    subst occurrence
    exact ⟨1,one_reached,resolves_name _ 1⟩
  · intro address member
    simp only [NamedSpaces.LocatedRule.spaces,rule,List.map_nil,List.map_cons,List.filterMap_nil,
      List.append_nil,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨1,resolves_name _ 1⟩
    · exact ⟨1,resolves_name _ 1⟩
    · exact ⟨9,resolves_name _ 9⟩
  · intro check member
    cases member

theorem joined_atomic_step :
    Step locals captures (3 : Nat) true ∅ selection known written addresses rows before rule produced []
      (result locals captures ∅ selection addresses rows before rule)
      (resultAddresses locals captures selection addresses produced)
      (resultPayloads locals captures selection rows produced)
      (ContextualActivationScopes.after ∅ selection)
      (PropagationHistory.record ⟨3,true,selection⟩ []) :=
  admitted.commit_with_history produced 3 true [] (PropagationHistory.fresh_empty _)

theorem one_new_row_and_two_retained_rows :
    (result locals captures ∅ selection addresses rows before rule).present = {7,11,8} := by decide

theorem the_schema_is_still_reusable :
    resultPayloads locals captures selection rows produced 7 =
      ContextualStoredRows.store locals active (generator locals 0) :=
  retained_schema produced (by decide) (generator locals 0) (by simp [rows])

def sharedRows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] () :=
  .shared (generator captures occurrence)

theorem shared_problem_explicit : eventProblem locals captures ∅ selection addresses sharedRows before rule =
    [(place (name 1) (symbol 10),place (name 1)
       (instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 7))),
     (place (name 1) (symbol 20),place (name 1)
       (instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 7)))] := by
  with_unfolding_all rfl

theorem the_shared_reference_cannot_take_both_values :
    ¬ ContextualFrameUnifier.Solvable
      (eventProblem locals captures ∅ selection addresses sharedRows before rule) := by
  rintro ⟨Future,future,candidate,model⟩
  rw [shared_problem_explicit] at model
  have firstEq := model _ List.mem_cons_self
  have secondEq := model _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only [Prod.fst,Prod.snd] at firstEq secondEq
  rw [instantiate_place,instantiate_place] at firstEq secondEq
  have first := (place_injective firstEq).2
  have second := (place_injective secondEq).2
  have impossible : (10 : Nat) = 20 := symbol_injective (first.trans second.symm)
  omega

theorem a_second_fresh_opening_is_not_a_new_event :
    ¬ PropagationHistory.Fresh (⟨3,true,selection⟩ : PropagationHistory.Event Nat Nat)
      (PropagationHistory.record ⟨3,true,selection⟩ []) :=
  PropagationHistory.propagation_cannot_replay rfl rfl []

theorem the_retained_reference_is_outside_the_changed_component :
    ¬ Frame.Variables (ContextualActivatedStep.frame locals captures before).equations
      (eventEquations locals captures ∅ selection addresses rows rule) (Sum.inr 0) := by
  change ¬ Frame.Variables [] problem (Sum.inr 0)
  rw [Frame.variables_empty_iff,problem_explicit]
  simp [Frame.Roots,Frame.equationSupport,support,supportArgs,localVariable,generator,
    selfArgs,place,name,symbol]

theorem every_retained_reference_equality_is_unchanged (value : Nat) :
    Frame.Entails problem (generator active (.inr 0)) (symbol value) ↔
      Frame.Entails ([] : EquationStore (Closed active)) (generator active (.inr 0)) (symbol value) := by
  apply admitted.meaning_frame
  intro identity member
  have same : identity = .inr 0 := by
    change identity ∈ [Sum.inr 0] at member
    exact List.mem_singleton.mp member
  subst identity
  exact the_retained_reference_is_outside_the_changed_component

theorem passing_a_shared_reference_can_transmit_any_name (reference value : Nat) :
    (∃ other, other ≠ value ∧
      Indistinguishable [] ({generator active (.inr reference)} : Set (Closed active)) value other) ∧
    Possesses [(generator active (.inr reference),name value)] {generator active (.inr reference)} value := by
  constructor
  · refine ⟨value + 1,by omega,indistinguishable_of_invariant ?_ ?_⟩
    · intro term member
      obtain rfl := Set.mem_singleton_iff.mp member
      exact mapNames_generator _ _
    · simp
  · refine resolved_name_possessed (term := generator active (.inr reference)) ?_ (Set.mem_singleton _) ?_
    · apply ContextualFrameUnifier.solvable_of_model (candidate := fun _ => name (decl := captures) value)
      intro equation member
      obtain rfl := List.mem_singleton.mp member
      exact instantiate_generator _ _
    · intro Future future candidate model
      exact model _ List.mem_cons_self

theorem binding_the_private_copy_grants_no_owner_name (scope owner value : Nat) :
    ∃ other, other ≠ value ∧
      Indistinguishable [(localVariable scope 0,name value)]
        ({generator active (.inr owner)} : Set (Closed active)) value other := by
  refine ⟨value + 1,by omega,?_⟩
  intro Future future candidate model
  let other : Assignment active future := fun identity =>
    if identity = .inr owner then mapNames (Equiv.swap value (value + 1)) (candidate identity)
    else candidate identity
  refine ⟨other,?_,?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    have same : candidate (.inl (ScopedVar.at scope 0)) = name value :=
      (instantiate_generator candidate (.inl (ScopedVar.at scope 0))).symm.trans (model _ List.mem_cons_self)
    change instantiate other (localVariable scope 0) = name value
    calc
      _ = other (.inl (ScopedVar.at scope 0)) := instantiate_generator other _
      _ = candidate (.inl (ScopedVar.at scope 0)) := rfl
      _ = name value := same
  · intro term member
    obtain rfl := Set.mem_singleton_iff.mp member
    calc
      _ = other (.inr owner) := instantiate_generator other _
      _ = mapNames (Equiv.swap value (value + 1)) (candidate (.inr owner)) := by simp only [other,ite_true]
      _ = _ := congrArg (mapNames (Equiv.swap value (value + 1))) (instantiate_generator candidate (.inr owner)).symm

def remaining {Variables : Type} {decl : Variables → MetaArity spaceSignature}
    {problem : ContextualResidual.Problem decl} : ContextualFrameWorklist.Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem the_actual_worklist_solves_the_joined_problem :
    remaining (ContextualFrameWorklist.run 32 active (ContextualResidual.observeProblem problem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 32 (ContextualResidual.observeProblem problem)
    captures (solution captures (generator captures))
      ((ContextualResidual.models_observeProblem _ _).mpr (two_reads_accept_every_caller _ _))]
  decide +kernel

theorem schema_guard_matches_only_one_physical_row {Future : Type}
    (future : Future → MetaArity spaceSignature) (candidate : Assignment active future)
    {occurrence : Nat} (present : occurrence ∈ before.present) :
    ContextualGuardMatching.Matches locals candidate (place (name 1) (symbol 10))
      (ContextualGuardedStep.guardRows locals captures (placedRows locals captures addresses rows) occurrence) ↔
      occurrence = 7 := by
  have cases : occurrence = 7 ∨ occurrence = 11 := by simpa [before] using present
  rcases cases with rfl | rfl
  · constructor
    · intro _; rfl
    · intro _
      change ContextualGuardMatching.Matches locals candidate (place (name 1) (symbol 10))
        (.schema (place (name 1) (generator (ContextualSelectionViews.source locals active) (.inl 0))))
      refine ⟨ContextualGuardMatching.Extension.identity future,(fun _ => symbol 10),?_⟩
      with_unfolding_all rfl
  · constructor
    · intro matched
      change place (name 1) (symbol 10) = place (name 2)
        (instantiate candidate (generator active (.inr 0))) at matched
      have impossible : (1 : Nat) = 2 := name_injective (place_injective matched).1
      omega
    · intro impossible
      omega

theorem guard_region_is_one_row {Future : Type}
    (future : Future → MetaArity spaceSignature) (candidate : Assignment active future) :
    ContextualGuardSemantics.region locals candidate
      (ContextualGuardedStep.guardRows locals captures (placedRows locals captures addresses rows)) before.present
      (place (name 1) (symbol 10)) = {7} := by
  apply Finset.ext
  intro occurrence
  rw [ContextualGuardSemantics.mem_region]
  constructor
  · rintro ⟨present,matched⟩
    have same := (schema_guard_matches_only_one_physical_row future candidate present).mp matched
    simpa only [Finset.mem_singleton] using same
  · intro member
    obtain rfl := Finset.mem_singleton.mp member
    exact ⟨by decide,(schema_guard_matches_only_one_physical_row future candidate (by decide)).mpr rfl⟩

theorem two_read_views_still_count_as_one_stored_row :
    ContextualGuardSemantics.Ask locals problem
      (ContextualGuardedStep.guardRows locals captures (placedRows locals captures addresses rows)) before.present
      (.count (place (name 1) (symbol 10)) 1) := by
  intro Future future candidate _
  change (ContextualGuardSemantics.region locals candidate _ before.present (place (name 1) (symbol 10))).card = 1
  rw [guard_region_is_one_row future candidate]
  rfl

theorem counting_the_two_views_as_two_rows_is_refused :
    ¬ ContextualGuardSemantics.Ask locals problem
      (ContextualGuardedStep.guardRows locals captures (placedRows locals captures addresses rows)) before.present
      (.count (place (name 1) (symbol 10)) 2) := by
  intro asked
  have count := asked _ captures (solution captures (generator captures)) (two_reads_accept_every_caller _ _)
  change (ContextualGuardSemantics.region locals (solution captures (generator captures)) _ before.present
    (place (name 1) (symbol 10))).card = 2 at count
  rw [guard_region_is_one_row] at count
  cases count

private theorem known_fixed {a b : Nat} (fixesOne : Equiv.swap a b 1 = 1) :
    ∀ term ∈ known, mapNames (Equiv.swap a b) term = term := by
  intro term member
  simp only [known,Set.mem_insert_iff,Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · change (name (Equiv.swap a b 1) : Closed active) = name 1
    exact congrArg (name (decl := active)) fixesOne
  · rfl
  · rfl
  · rfl
  · change place (name (Equiv.swap a b 1)) (symbol 10) = (place (name 1) (symbol 10) : Closed active)
    exact congrArg (fun n => (place (name n) (symbol 10) : Closed active)) fixesOne
  · change place (name (Equiv.swap a b 1)) (symbol 20) = (place (name 1) (symbol 20) : Closed active)
    exact congrArg (fun n => (place (name n) (symbol 20) : Closed active)) fixesOne

private theorem knowledge_fixed {a b : Nat} (fixesOne : Equiv.swap a b 1 = 1) :
    ∀ term ∈ Knowledge known (storedViews locals captures ∅ selection addresses rows before)
      (fun n => n = 1), mapNames (Equiv.swap a b) term = term := by
  intro term member
  rcases member with knownTerm | ⟨n,rfl,occurrence,present,atName,scope,_,_,rfl⟩
  · exact known_fixed fixesOne term knownTerm
  · have cases : occurrence = 7 ∨ occurrence = 11 := by simpa [before] using present
    rcases cases with rfl | rfl
    · have schema : placedRows locals captures addresses rows 7 =
          .schema (place (name 1) (generator (ContextualSelectionViews.source locals captures) (.inl 0))) := by
        with_unfolding_all rfl
      rw [schema,mapNames_view]
      apply congrArg (ContextualStoredRows.viewAt locals captures scope)
      change ContextualStoredRows.Row.schema (place (name (Equiv.swap a b 1))
          (generator (ContextualSelectionViews.source locals captures) (.inl 0))) =
        (ContextualStoredRows.Row.schema (place (name 1)
          (generator (ContextualSelectionViews.source locals captures) (.inl 0))) :
            ContextualStoredRows.Row locals captures [] ())
      exact congrArg (fun n => (ContextualStoredRows.Row.schema (place (name n)
        (generator (ContextualSelectionViews.source locals captures) (.inl 0))) :
          ContextualStoredRows.Row locals captures [] ())) fixesOne
    · change ResolvesTo ([] : EquationStore (Closed active)) (name 2) 1 at atName
      have impossible : (2 : Nat) = 1 := ResolvesTo.unique
        (ContextualFrameUnifier.solvable_of_model
          (show ContextualFrameUnifier.Models (generator active) [] by simp [ContextualFrameUnifier.Models]))
        (resolves_name ([] : EquationStore (Closed active)) 2) atName
      omega

theorem reach_is_only_the_held_space {n : Nat}
    (reached : Reached locals captures ∅ selection known addresses rows before n) : n = 1 := by
  apply reached (fun n => n = 1)
  intro value possessed
  by_contra notOne
  let other := if value = 2 then 3 else 2
  have different : other ≠ value := by dsimp [other]; split <;> omega
  have otherNotOne : other ≠ 1 := by dsimp [other]; split <;> omega
  have fixesOne : Equiv.swap value other 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm notOne) (Ne.symm otherNotOne)
  exact possessed ⟨other,different,indistinguishable_of_invariant (knowledge_fixed fixesOne)
    (by intro equation member; change equation ∈ [] at member; cases member)⟩

theorem delivery_does_not_grant_read_access :
    ¬ Reached locals captures ∅ selection known addresses rows before 9 ∧
      resultAddresses locals captures selection addresses produced 8 = name 9 ∧
        8 ∈ (result locals captures ∅ selection addresses rows before rule).present := by
  refine ⟨fun reached => ?_,rfl,by decide⟩
  have impossible := reach_is_only_the_held_space reached
  omega

theorem the_unreached_occurrence_and_its_readings_survive (value : Nat) :
    11 ∈ (result locals captures ∅ selection addresses rows before rule).present ∧
      (Frame.Entails problem (generator active (.inr 0)) (symbol value) ↔
        Frame.Entails ([] : EquationStore (Closed active)) (generator active (.inr 0)) (symbol value)) := by
  refine ⟨admitted.unreached_survives (by decide) (n := 2) (resolves_name _ 2) ?_,
    every_retained_reference_equality_is_unchanged value⟩
  intro reached
  have impossible := reach_is_only_the_held_space reached
  omega

def rawRule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures)) :=
  ⟨[],[(name 1,symbol 10),(name 1,symbol 20)],[],[],[(name 9,pair (symbol 10) (symbol 20))]⟩

theorem fresh_raw_rule : freshLocated locals captures ∅ selection rawRule = rule := by
  with_unfolding_all rfl

theorem semantic_admission_uses_the_existing_execution :
    ContextualGuardedStep.Valid locals captures ∅ selection
      (rawRule.toRule (spaceTerms (ContextualSelectionViews.source locals captures)))
      (placedRows locals captures addresses rows) before outputs := by
  have fresh : Admits locals captures ∅ selection known written addresses rows before
      (freshLocated locals captures ∅ selection rawRule) outputs := by
    rw [fresh_raw_rule]
    exact admitted
  exact fresh.semantic_admission

theorem joined_problem_is_in_the_complete_fragment :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem problem) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  rw [problem_explicit]
  decide +kernel

theorem completed_execution_is_constructed :
    ∃ fuel update, ContextualTransportedActivation.FromRun locals captures fuel ∅ selection
      (rawRule.toRule (spaceTerms (ContextualSelectionViews.source locals captures)))
      (placedRows locals captures addresses rows) before outputs update := by
  have fresh : Admits locals captures ∅ selection known written addresses rows before
      (freshLocated locals captures ∅ selection rawRule) outputs := by
    rw [fresh_raw_rule]
    exact admitted
  apply fresh.completed_run
  rw [fresh_raw_rule]
  exact joined_problem_is_in_the_complete_fragment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach.Controls
