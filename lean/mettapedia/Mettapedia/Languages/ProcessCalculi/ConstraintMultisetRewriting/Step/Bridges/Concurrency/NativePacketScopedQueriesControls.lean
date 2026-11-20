import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketScopedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedAdmissionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualModels

/-!
# Scoped count queries: a serial round and an atomic own bag

The store is a bag of physical occurrences, the commit is a bag of matches,
each guard is asked after that member's own tells, the program is fixed,
and knowledge is one store. Two quiet count-one events form a serial round.
Two count-one events emitting zero at distinct fresh ports instead admit an
atomic own bag. An actual returned-frame solution witnesses at least two
matches after either event, refusing the other's actual residual in both
orders. No refusal is inferred from a failed sufficient independence test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedQueriesControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualNonprincipalCountControls
open NativePacketGuardedAdmissionControls (state quietCount)
open NativePacketStep (Terms Ports packetAction)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open RuleSyntax RuleSyntax.JointFirings
open RuleSyntax.StepWeb.ObservedBags

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

abbrev A := packetAction (S := base) (O := Nat) (Γ := []) (sort := ())
abbrev X := OneFrame.frames A

theorem quiet_scoped_round :
    (scopedStep X (NativePacketScopedQueries.scopedQueries [quietCount,quietCount])).Admits
      (s := NativePacketRounds.source [quietCount,quietCount])
      (bagOf A (NativePacketScopedQueries.memberList [quietCount,quietCount])) :=
  NativePacketScopedRounds.scoped_of_clear (by simp) NativePacketGuardedAdmissionControls.two_count_events_clear

theorem malformed_scope_rejects :
    NativePacketScopedQueries.reject (S := base) ∈
      NativePacketScopedQueries.decode [NativePacketScopedQueries.QueryCode.count 1]
        ([] : List (Terms base Nat [] ())) :=
  NativePacketScopedQueries.decode_bad_length _ _ (by decide)

def emitter (port : Nat) : LiveFiring state :=
  { NativePacketGuardedAdmissionControls.counted 1 with
    rule := { (NativePacketGuardedAdmissionControls.counted 1).rule with produce := [literal 0] }
    selection := ⟨[],[],[port]⟩
    outputs := fun _ => literal 0 }

theorem emitter_information (port : Nat) : FamilyInformation.memberInformation (emitter port) = information := rfl

theorem emitter_checks (port : Nat) : (emitter port).toNative.prepared.rule.checks = [.count pattern 1] := rfl

theorem emitter_shapes (port : Nat) :
    (native (S := base) (O := Nat) (Γ := []) (sort := ())).Shapes (emitter port).toNative :=
  ⟨List.nodup_nil,List.nodup_singleton _,rfl,rfl,rfl⟩

theorem emitter_enabled (port : Nat) (fresh : port = 2 ∨ port = 3) :
    Enabled (fun _ : Nat => ()) state.state.present ((emitter port).selection.commit (T := Unit)) := by
  rcases fresh with rfl | rfl <;>
    exact ⟨by decide,by decide,by decide,by decide,fun _ inside => by cases inside⟩

theorem emitter_realized (port : Nat) (fresh : port = 2 ∨ port = 3) : (emitter port).toNative.Realized := by
  apply (native_admits_iff (emitter port).toNative).mpr
  refine ⟨emitter_shapes port,emitter_enabled port fresh,?_,?_⟩
  · exact ⟨⟨Empty,locals⟩,model locals (literal 0),constant_model locals⟩
  · intro target candidate solved
    refine ⟨?_,fun _ inside => by cases inside⟩
    intro check inside
    rw [emitter_checks] at inside
    obtain rfl := List.mem_singleton.mp inside
    exact count_guard target.Names target.arity candidate solved

def members : List (LiveFiring state) := [emitter 2,emitter 3]
def source := NativePacketRounds.source members
def atomicBag := bagOf A (NativePacketScopedQueries.memberList members)

theorem each_enabled (index : Fin members.length) :
    Enabled (fun _ : Nat => ()) state.state.present (members[index].selection.commit (T := Unit)) := by
  fin_cases index
  · exact emitter_enabled 2 (.inl rfl)
  · exact emitter_enabled 3 (.inr rfl)

theorem each_realized (index : Fin members.length) : members[index].toNative.Realized := by
  fin_cases index
  · exact emitter_realized 2 (.inl rfl)
  · exact emitter_realized 3 (.inr rfl)

def constantData : FamilyInformation.SolutionData state members ⟨Empty,locals⟩ where
  shared := Assignment.compose (model locals (literal 0)) (ContextualSelectionViews.capturedTarget locals functions)
  member _ := model locals (literal 0)
  agrees _ := rfl
  models index := by fin_cases index <;> exact constant_model locals

theorem atomic_own : atomicBag.AdmitsOwn X source := by
  refine ⟨⟨NativePacketScopedQueries.bag_fresh members,by decide,by decide,?_⟩,?_,?_,?_⟩
  · intro selected inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    fin_cases index <;> exact ⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨by decide,by decide,by decide,by decide,fun _ inside => by cases inside⟩
  · refine ⟨PUnit.unit,NativePacketRounds.fitData constantData,?_⟩
    have solved := NativePacketRounds.fitData_joint constantData (by simp [members]) each_enabled
    exact (congrArg (fun equations => A.Models (NativePacketRounds.fitData constantData) equations)
      (NativePacketScopedQueries.joint_information members)).mpr solved
  · intro selected inside target substitution solved
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    fin_cases index <;> exact ⟨(fun _ inside => by cases inside),(fun _ inside => by cases inside)⟩

theorem atomic_scoped :
    (scopedStep X (NativePacketScopedQueries.scopedQueries members)).Admits (s := source) atomicBag := by
  apply (NativePacketScopedQueries.scoped_admits_iff_queries members).mpr
  refine ⟨by simp [NativePacketScopedQueries.memberList,members],atomic_own,?_⟩
  intro index
  have actual := ((native_admits_iff members[index].toNative).mp (each_realized index)).2.2.2
  exact ((NativePacketGuardedAdmission.asks_iff members index (each_enabled index)).mpr
    ((NativePacketGuardedAdmission.native_asks_iff members[index]).mp actual)).2

section ReturnedFrame

variable (port other : Nat) (execution : ContextualConditionalExecution.Firing state.locals state.state)
  (selectionEq : execution.selection = (emitter port).selection)
  (ruleEq : execution.rule = (emitter port).rule)
  (outputsEq : execution.outputs = (emitter port).outputs)
  (reusableEq : execution.reusable = fun _ => false)

def returnedJoint : NativeResidual.Joint state (emitter other).toNative.information
    (NativeResidual.problemOf state execution.selection execution.rule) ⟨Empty,locals⟩ where
  left := model locals (literal 0)
  right := model locals (literal 0)
  left_models := constant_model locals
  right_models := by rw [selectionEq,ruleEq]; exact constant_model locals
  agree := rfl

noncomputable def returnedCounter := ResidualModels.amalgam (s := state) execution
  (returnedJoint port other execution selectionEq ruleEq)

theorem returned_model : ContextualResidual.Models (returnedCounter port other execution selectionEq ruleEq)
    ((emitter other).residualAt execution).toNative.information :=
  ResidualModels.models_amalgam (s := state) execution (emitter other) (fun _ inside => by cases inside)
    (returnedJoint port other execution selectionEq ruleEq)

theorem carried_pattern_zero :
    instantiate (returnedCounter port other execution selectionEq ruleEq)
      (instantiate (NativeResidual.carry execution) pattern) = literal 0 :=
  (ResidualModels.read_left (s := state) execution (returnedJoint port other execution selectionEq ruleEq) pattern).trans rfl

include selectionEq in
theorem returned_old_zero_present : 0 ∈ execution.target.present := by
  change 0 ∈ fire state.state.present (execution.selection.commit (T := Unit))
  rw [selectionEq]
  change 0 ∈ fire ({0,1} : Finset Nat) ((emitter port).selection.commit (T := Unit))
  simp [emitter,Selection.commit,MeTTaCalculus.OccurrenceCommits.fire]

include selectionEq in
theorem returned_new_present : port ∈ execution.target.present := by
  change port ∈ fire state.state.present (execution.selection.commit (T := Unit))
  rw [selectionEq]
  simp [emitter,Selection.commit,MeTTaCalculus.OccurrenceCommits.fire]

include outputsEq reusableEq in
theorem returned_two_matches (nonzero : port ≠ 0) :
    2 ≤ (ContextualConditionalGuards.region
      (ContextualPublication.privateFamily state.locals execution.update.declaration)
      (returnedCounter port other execution selectionEq ruleEq)
      (ContextualConditionalExecution.guardRows
        (ContextualPublication.privateFamily state.locals execution.update.declaration)
        execution.target.declarations execution.target.rows)
      execution.target.present (instantiate (NativeResidual.carry execution) pattern)).card := by
  let region := ContextualConditionalGuards.region
    (ContextualPublication.privateFamily state.locals execution.update.declaration)
    (returnedCounter port other execution selectionEq ruleEq)
    (ContextualConditionalExecution.guardRows
      (ContextualPublication.privateFamily state.locals execution.update.declaration)
      execution.target.declarations execution.target.rows)
    execution.target.present (instantiate (NativeResidual.carry execution) pattern)
  have zero : 0 ∈ region := by
    apply (ContextualConditionalGuards.mem_region _ _ _ _ _ 0).mpr
    refine ⟨returned_old_zero_present port execution selectionEq,?_⟩
    rw [carried_pattern_zero]
    apply (NativeResidual.matches_retained (s := state) execution
      (returnedCounter port other execution selectionEq ruleEq)
      (by rw [selectionEq]; simpa [emitter] using nonzero.symm) (literal 0)).mpr
    change ContextualConditionalRows.Matches locals active _ (literal 0)
      (ContextualConditionalRows.ofStored locals active (.shared (literal 0)))
    exact (ContextualConditionalRows.ofStored_matches_iff locals active
      (Assignment.compose (returnedCounter port other execution selectionEq ruleEq) (NativeResidual.carry execution))
      (literal 0) (.shared (literal 0))).mpr
      ((ContextualGuardMatching.shared_matches_iff locals _ (literal 0) (literal 0)).mpr rfl)
  have made : port ∈ region := by
    apply (ContextualConditionalGuards.mem_region _ _ _ _ _ port).mpr
    refine ⟨returned_new_present port execution selectionEq,?_⟩
    rw [carried_pattern_zero]
    apply (NativeResidual.matches_made (s := state) execution
      (returnedCounter port other execution selectionEq ruleEq)
      (by rw [selectionEq]; exact List.mem_singleton_self _)
      (by rw [reusableEq]) (literal 0)).mpr
    rw [outputsEq]
    rfl
  have subset : ({0,port} : Finset Nat) ⊆ region := by
    intro occurrence inside
    rcases Finset.mem_insert.mp inside with rfl | inside
    · exact zero
    · obtain rfl := Finset.mem_singleton.mp inside
      exact made
  have lower := Finset.card_le_card subset
  simpa [nonzero.symm] using lower

omit selectionEq ruleEq outputsEq reusableEq in
theorem returned_checks : ((emitter other).residualAt execution).toNative.prepared.rule.checks =
    [.count (instantiate (NativeResidual.carry execution) pattern) 1] := by
  have carried := NativeResidual.prepared_rule_carried (s := state) execution (emitter other).selection (emitter other).rule
    (fun occurrence => (state.state.rows occurrence).value) (fun occurrence => (execution.target.rows occurrence).value)
  have checks := congrArg RuleInstance.checks carried
  change (emitter other).toNative.prepared.rule.checks.map (Check.map (instantiate (NativeResidual.carry execution))) =
    ((emitter other).residualAt execution).toNative.prepared.rule.checks at checks
  rw [emitter_checks] at checks
  exact checks.symm

include selectionEq ruleEq outputsEq reusableEq in
theorem returned_refused (nonzero : port ≠ 0) : ¬ ((emitter other).residualAt execution).toNative.Realized := by
  intro admitted
  have asked := ((native_admits_iff ((emitter other).residualAt execution).toNative).mp admitted).2.2.2
  have held := (asked (ResidualModels.extended (s := state) execution ⟨Empty,locals⟩)
    (returnedCounter port other execution selectionEq ruleEq) (returned_model port other execution selectionEq ruleEq)).1
    (.count (instantiate (NativeResidual.carry execution) pattern) 1)
    (by rw [returned_checks]; exact List.mem_singleton_self _)
  change (ContextualConditionalGuards.region _ _ _ _ _).card = 1 at held
  have lower := returned_two_matches port other execution selectionEq ruleEq outputsEq reusableEq nonzero
  have impossible : 2 ≤ 1 := Nat.le_trans lower (Nat.le_of_eq held)
  omega

end ReturnedFrame

theorem actual_residual_refused (port other : Nat) (admitted : (emitter port).toNative.Realized) (nonzero : port ≠ 0) :
    ¬ (NativeIterated.residualAfter (s := state) admitted (emitter other)).toNative.Realized := by
  have data := LiveFiring.execution_data (s := state) admitted
  exact returned_refused port other (LiveFiring.execution (s := state) admitted)
    data.2.1 data.1 data.2.2.1 data.2.2.2 nonzero

theorem no_sequential (port other : Nat) (nonzero : port ≠ 0) (last : NativeState base Nat [] ()) :
    ¬ NativeIterated.Sequential state [emitter port,emitter other] last := by
  intro sequence
  obtain ⟨first,later⟩ := (NativeIterated.sequential_cons_iff (S := base)).mp sequence
  obtain ⟨second,_⟩ := (NativeIterated.sequential_singleton_iff (S := base)).mp later
  exact actual_residual_refused port other first nonzero second

theorem neither_order_runs (last : NativeState base Nat [] ()) :
    ¬ NativeIterated.Sequential state [emitter 2,emitter 3] last ∧
      ¬ NativeIterated.Sequential state [emitter 3,emitter 2] last :=
  ⟨no_sequential 2 3 (by decide) last,no_sequential 3 2 (by decide) last⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedQueriesControls
