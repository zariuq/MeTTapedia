import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution
import Mettapedia.Logic.LP.TermEquality

/-!
# Executed open aliases, captured thunks and shared demand

The native heads in these controls carry explicit first-order symbolic data.
The observer returns that data together with the persistent tell store; a
solution interprets it. This is not a formation or conversion claim for native
mathematical terms. The underlying lambdas, thunk captures and shared-force
operations are the existing first-class source and machine.
-/

open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution.Controls

open Presentation NeedReference PolarizedNeed PolarizedNeedMachine
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

abbrev signature : Mettapedia.Logic.LP.LPSignature where
  constants := Bool
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

abbrev LogicTerm := Mettapedia.Logic.LP.Term signature
abbrev Assignment := Mettapedia.Logic.LP.Subst signature
abbrev Source := Computation LogicTerm Unit (Equation LogicTerm) 0 0 0
abbrev Runtime := NeedMachine LogicTerm Unit (Equation LogicTerm) Empty Empty 0

def x : LogicTerm := .var 0
def y : LogicTerm := .var 1
def a : LogicTerm := .const false
def b : LogicTerm := .const true
def openAlias : Equation LogicTerm := (x, y)
def chooseA : Equation LogicTerm := (y, a)
def chooseB : Equation LogicTerm := (x, b)
def contradiction : Equation LogicTerm := (a, b)

def check := FirstOrderProfile.check signature
def action := FirstOrder.action signature

theorem check_exact (store : EquationStore LogicTerm) :
    check store = true ↔ action.Consistent store := FirstOrderProfile.check_exact signature store

theorem alias_allows_each_future_value (value : Bool) :
    action.Models (fun _ => .const value) [openAlias] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  rfl

theorem alias_is_still_open :
    action.Models (fun _ => a) [openAlias] ∧ action.Models (fun _ => b) [openAlias] ∧ a ≠ b :=
  ⟨alias_allows_each_future_value false, alias_allows_each_future_value true,
    by intro equality; cases equality⟩

theorem later_tell_resolves_both (assignment : Assignment)
    (models : action.Models assignment [openAlias, chooseA]) :
    assignment.applyTerm x = a ∧ assignment.applyTerm y = a := by
  have joined := models openAlias (by simp)
  have fixed := models chooseA (by simp)
  change assignment.applyTerm x = assignment.applyTerm y at joined
  change assignment.applyTerm y = a at fixed
  exact ⟨joined.trans fixed, fixed⟩

theorem inconsistent_later_tell : ¬ action.Consistent [openAlias, chooseA, chooseB] := by
  rintro ⟨assignment, models⟩
  have joined := models openAlias (by simp)
  have fixedA := models chooseA (by simp)
  have fixedB := models chooseB (by simp)
  change assignment.applyTerm x = assignment.applyTerm y at joined
  change assignment.applyTerm y = a at fixedA
  change assignment.applyTerm x = b at fixedB
  have impossible : a = b := fixedA.symm.trans (joined.symm.trans fixedB)
  cases impossible

theorem contradiction_rejected : check [contradiction] = false := by
  cases checked : check [contradiction] with
  | false => rfl
  | true =>
    obtain ⟨assignment, models⟩ := (check_exact _).mp checked
    have impossible := models contradiction (by simp)
    change a = b at impossible
    cases impossible

theorem alias_accepted : check [openAlias] = true :=
  (check_exact _).mpr ⟨fun _ => a, alias_allows_each_future_value false⟩

theorem refined_alias_accepted : check [openAlias, chooseA] = true := by
  apply (check_exact _).mpr
  refine ⟨fun _ => a, ?_⟩
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem captured_refinement_accepted : check [chooseA, openAlias] = true := by
  apply (check_exact _).mpr
  refine ⟨fun _ => a, ?_⟩
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem other_refinement_accepted : check [openAlias, chooseB] = true := by
  apply (check_exact _).mpr
  refine ⟨fun _ => b, ?_⟩
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem contradictory_refinement_rejected : check [openAlias, chooseA, chooseB] = false := by
  cases checked : check [openAlias, chooseA, chooseB] with
  | false => rfl
  | true => exact False.elim (inconsistent_later_tell ((check_exact _).mp checked))

def primitive (_ : Unit) (value : Tm LogicTerm 0) : Produced (Tm LogicTerm 0) Empty Empty :=
  .value value

def world : NeedWorld LogicTerm Unit (Equation LogicTerm) Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

def capture (code : Source) : Closure LogicTerm Unit (Equation LogicTerm) 0 :=
  ⟨0, 0, 0, code, ids, Fin.elim0, Fin.elim0⟩

def observe (state : Runtime) : Option LogicTerm × EquationStore LogicTerm :=
  ((match haltedOutcome state with
    | some (.value (.returned (.native (.head term)))) => some term
    | _ => none), state.world.receipts.effects)

def rawOutputs (fuel : Nat) (code : Source) :=
  ((NeedConstraintEffects.rawCore (extension primitive)).answerOccurrences fuel
    (initial (capture code) world)).map observe

def outputs (fuel : Nat) (code : Source) :=
  ((machine primitive [] check).answerOccurrences fuel (initial (capture code) world)).map observe

theorem outputs_exact (fuel : Nat) (code : Source) :
    outputs fuel code = (rawOutputs fuel code).filter (fun observation => check observation.2) := by
  unfold outputs
  rw [ordered_occurrences_exact action primitive [] check check_exact]
  simpa only [rawOutputs, List.nil_append, Function.comp_def, observe] using
    (List.filter_map (f := observe) (p := fun observation => check observation.2)
      (l := (NeedConstraintEffects.rawCore (extension primitive)).answerOccurrences fuel
        (initial (capture code) world))).symm

def passedThunk : Source :=
  .valueApply (.valueLambda (.forceThunk (.variable 0)))
    (.thunk (.emit openAlias (.returnValue (.native (.head x)))))

theorem passed_thunk_raw : rawOutputs 10 passedThunk = [(some x, [openAlias])] := by
  decide +kernel

theorem passed_thunk_checked : outputs 10 passedThunk = [(some x, [openAlias])] := by
  rw [outputs_exact, passed_thunk_raw]
  simp [alias_accepted]

/-- The thunk is captured before refinement, then forced in the current
world. Capturing code does not capture and restore an older equation store. -/
def capturedBeforeTell : Source :=
  .bindValue (.returnValue (.thunk (.emit openAlias (.returnValue (.native (.head x))))))
    (.emit chooseA (.forceThunk (.variable 0)))

theorem captured_before_refinement_raw :
    rawOutputs 30 capturedBeforeTell = [(some x, [chooseA, openAlias])] := by
  decide +kernel

theorem captured_before_refinement_checked :
    outputs 30 capturedBeforeTell = [(some x, [chooseA, openAlias])] := by
  rw [outputs_exact, captured_before_refinement_raw]
  simp [captured_refinement_accepted]

def sharedAcrossTell : Source :=
  .letNeed (.emit openAlias (.returnValue (.native (.head x))))
    (.bindValue (.forceNeed 0) (.emit chooseA (.forceNeed 0)))

theorem shared_cached_value_keeps_one_producer_tell :
    rawOutputs 40 sharedAcrossTell = [(some x, [openAlias, chooseA])] := by
  decide +kernel

theorem shared_refined_value_checked : outputs 40 sharedAcrossTell = [(some x, [openAlias, chooseA])] := by
  rw [outputs_exact, shared_cached_value_keeps_one_producer_tell]
  simp [refined_alias_accepted]

def independentRefinementsOfSharedValue : Source :=
  .letNeed (.emit openAlias (.returnValue (.native (.head x))))
    (.bindValue (.forceNeed 0)
      (.choose (.emit chooseA (.forceNeed 0)) (.emit chooseB (.forceNeed 0))))

/-- The shared symbolic value does not choose a ground value at birth.
Different later branches may consistently refine it differently. -/
theorem shared_open_value_has_two_consistent_future_refinements :
    outputs 45 independentRefinementsOfSharedValue =
      [(some x, [openAlias, chooseA]), (some x, [openAlias, chooseB])] := by
  rw [outputs_exact]
  have raw : rawOutputs 45 independentRefinementsOfSharedValue =
      [(some x, [openAlias, chooseA]), (some x, [openAlias, chooseB])] := by
    decide +kernel
  rw [raw]
  simp [refined_alias_accepted, other_refinement_accepted]

def conflictAfterSharing : Source :=
  .letNeed (.emit openAlias (.returnValue (.native (.head x))))
    (.bindValue (.forceNeed 0) (.emit chooseA (.emit chooseB (.forceNeed 0))))

theorem conflicting_source_would_otherwise_return :
    rawOutputs 40 conflictAfterSharing = [(some x, [openAlias, chooseA, chooseB])] := by
  decide +kernel

theorem conflicting_shared_branch_is_rejected : outputs 40 conflictAfterSharing = [] := by
  rw [outputs_exact, conflicting_source_would_otherwise_return]
  simp [contradictory_refinement_rejected]

theorem duplicate_valid_branches_survive :
    outputs 45 (.choose sharedAcrossTell sharedAcrossTell) =
      [(some x, [openAlias, chooseA]), (some x, [openAlias, chooseA])] := by
  rw [outputs_exact]
  have raw : rawOutputs 45 (.choose sharedAcrossTell sharedAcrossTell) =
      [(some x, [openAlias, chooseA]), (some x, [openAlias, chooseA])] := by decide +kernel
  rw [raw]
  simp [refined_alias_accepted]

/-- Refusing the earlier inconsistent branch retains the later alternative.
No successful occurrence is invented to stand in for the refused branch. -/
theorem rejected_earlier_branch_keeps_later_answer :
    outputs 45 (.choose conflictAfterSharing sharedAcrossTell) =
      [(some x, [openAlias, chooseA])] := by
  rw [outputs_exact]
  have raw : rawOutputs 45 (.choose conflictAfterSharing sharedAcrossTell) =
      [(some x, [openAlias, chooseA, chooseB]), (some x, [openAlias, chooseA])] := by
    decide +kernel
  rw [raw]
  simp [contradictory_refinement_rejected, refined_alias_accepted]

/-- The cached open value is interpreted by the same final solution as its
producer's alias and its consumer's later tell. It is not an old ground copy. -/
theorem shared_observation_resolves_under_joint_store
    (term : LogicTerm) (store : EquationStore LogicTerm)
    (returned : (some term, store) ∈ outputs 40 sharedAcrossTell)
    (assignment : Assignment) (models : action.Models assignment store) :
    assignment.applyTerm term = a ∧ assignment.applyTerm y = a := by
  rw [shared_refined_value_checked] at returned
  simp only [List.mem_singleton, Prod.mk.injEq, Option.some.injEq] at returned
  obtain ⟨rfl, rfl⟩ := returned
  exact later_tell_resolves_both assignment models

/-- A contradictory tell is refused at its first transition; the following
return is never scheduled in this logical-effect profile. -/
theorem contradictory_tell_refused_before_continuation :
    (machine primitive [] check).next
      (initial (capture (.emit contradiction (.returnValue (.native (.head x))))) world) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro next selected
  obtain ⟨selected, consistent⟩ :=
    (NeedConstraintEffects.checked_successor_iff action (extension primitive) [] check check_exact _ _).mp selected
  have stores :
      ((NeedLocalSteps.step (extension primitive)
        (initial (capture (.emit contradiction (.returnValue (.native (.head x))))) world)).map
          (fun state => state.world.receipts.effects)) = [[contradiction]] := by
    decide +kernel
  have member : next.world.receipts.effects ∈
      (NeedLocalSteps.step (extension primitive)
        (initial (capture (.emit contradiction (.returnValue (.native (.head x))))) world)).map
          (fun state => state.world.receipts.effects) := List.mem_map.mpr ⟨next, selected, rfl⟩
  rw [stores] at member
  have same := List.mem_singleton.mp member
  have accepted := (check_exact _).mpr consistent
  simp only [NeedConstraintEffects.equations, List.nil_append, same, contradiction_rejected] at accepted
  cases accepted

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution.Controls
