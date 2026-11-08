import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveBoundaries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveRefusal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViewControls
import Mathlib.Tactic.FinCases

/-!
# Shared query variables, fresh row uses and empty-query controls

The two unary tags are rigid constructor shapes. The same local query key
occurs in both patterns. Stored-schema locals open per use; caller captures
do not become query locals. All executable checks use the actual worklist.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching
open ContextualConjunctiveQueries
open ContextualConjunctiveAbsence
open ContextualSelectionViews.Controls (base atom pair)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

abbrev queries (_ : Nat) : MetaArity base := ([], ())
abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev Pattern := Term (signature base (queryFamily queries captures)) [] ()
abbrev Captured := Term (signature base captures) [] ()
abbrev Raw := Term (signature base (ContextualSelectionViews.source locals captures)) [] ()
abbrev Stored := ContextualStoredRows.Row locals captures [] ()

def p {V : Type} {declaration : V → MetaArity base} (value : Term (signature base declaration) [] ()) :=
  pair value (atom declaration)
def q {V : Type} {declaration : V → MetaArity base} (value : Term (signature base declaration) [] ()) :=
  pair value (pair (atom declaration) (atom declaration))

def a : Captured := atom captures
def b : Captured := pair a a
def patternA : Pattern := atom (queryFamily queries captures)
def patternB : Pattern := pair patternA patternA
def x : Pattern := generator (queryFamily queries captures) (.inl 0)
def shared : Pattern := generator (queryFamily queries captures) (.inr 0)
def patterns : List Pattern := [p x, q x]

def rows (occurrence : Nat) : Stored :=
  if occurrence = 10 then .shared (p a)
  else if occurrence = 20 then .shared (q b)
  else .shared (q a)
def world : Finset Nat := {10, 20}
def enlarged : Finset Nat := {10, 20, 30}

def chosenRows (first second : Nat) (port : Fin patterns.length) : Nat := if port.val = 0 then first else second

def shapeA {Next : Type} : ContextualShapeErasure.ShapeTerm base Next :=
  .app ⟨(), .constant⟩ (fun impossible => Fin.elim0 impossible)
def shapeB {Next : Type} : ContextualShapeErasure.ShapeTerm base Next :=
  .app ⟨(), .pair⟩ (Fin.cases shapeA (fun tail => Fin.cases shapeA (fun impossible => Fin.elim0 impossible) tail))

def shapeRootIsPair {Next : Type} : ContextualShapeErasure.ShapeTerm base Next → Bool
  | .app ⟨(), .pair⟩ _ => true
  | _ => false
def shapeFirst {Next : Type} : ContextualShapeErasure.ShapeTerm base Next → Option (ContextualShapeErasure.ShapeTerm base Next)
  | .app ⟨(), .pair⟩ children => some (children ⟨0, by change 0 < 2; decide +kernel⟩)
  | _ => none
def shapeSecond {Next : Type} : ContextualShapeErasure.ShapeTerm base Next → Option (ContextualShapeErasure.ShapeTerm base Next)
  | .app ⟨(), .pair⟩ children => some (children ⟨1, by change 1 < 2; decide +kernel⟩)
  | _ => none

theorem the_two_rigid_shapes_are_distinct {Next : Type} : (shapeA : ContextualShapeErasure.ShapeTerm base Next) ≠ shapeB := by
  intro same
  have impossible := congrArg shapeRootIsPair same
  change false = true at impossible
  cases impossible

theorem every_occupied_tuple_is_structural (first second : Nat)
    (firstPresent : first = 10 ∨ first = 20) (secondPresent : second = 10 ∨ second = 20) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (joint queries locals captures [] patterns rows (chosenRows first second))) := by
  rw [← ContextualPatternFragment.checkProblem_iff]
  rcases firstPresent with rfl | rfl <;> rcases secondPresent with rfl | rfl <;> decide +kernel

theorem every_occupied_tuple_has_inconsistent_shapes (first second : Nat)
    (firstPresent : first = 10 ∨ first = 20) (secondPresent : second = 10 ∨ second = 20)
    (Next : Type) (images : ContextualShapeErasure.ShapeAssignment base
      (Nat ⊕ (ScopedVar Nat ⊕ Nat)) Next) :
    ¬ ContextualShapeErasure.ShapeModels images (ContextualResidual.observeProblem
      (joint queries locals captures [] patterns rows (chosenRows first second))) := by
  intro models
  have firstEq := models ((ContextualResidual.observeProblem
    (joint queries locals captures [] patterns rows (chosenRows first second))).get ⟨0, by change 0 < 2; decide +kernel⟩) (List.get_mem _ _)
  have secondEq := models ((ContextualResidual.observeProblem
    (joint queries locals captures [] patterns rows (chosenRows first second))).get ⟨1, by change 1 < 2; decide +kernel⟩) (List.get_mem _ _)
  rcases firstPresent with rfl | rfl
  · rcases secondPresent with rfl | rfl
    · have different := Option.some.inj (congrArg shapeSecond secondEq)
      change shapeA = shapeB at different
      exact the_two_rigid_shapes_are_distinct different
    · have firstValue := Option.some.inj (congrArg shapeFirst firstEq)
      have secondValue := Option.some.inj (congrArg shapeFirst secondEq)
      change shapeA = images (.inl 0) at firstValue
      change shapeB = images (.inl 0) at secondValue
      exact the_two_rigid_shapes_are_distinct (firstValue.trans secondValue.symm)
  · have different := Option.some.inj (congrArg shapeSecond firstEq)
    change shapeB = shapeA at different
    exact the_two_rigid_shapes_are_distinct different.symm

theorem the_actual_tuple_refuses (first second : Nat)
    (firstPresent : first = 10 ∨ first = 20) (secondPresent : second = 10 ∨ second = 20) :
    certifiesTuple queries locals captures 2 [] patterns rows (chosenRows first second) = true :=
  ContextualConjunctiveRefusal.of_shape_inconsistency queries locals captures 1 [] patterns rows
    (chosenRows first second) (every_occupied_tuple_is_structural first second firstPresent secondPresent)
    (every_occupied_tuple_has_inconsistent_shapes first second firstPresent secondPresent)

theorem p_has_an_individual_witness :
    ContextualConjunctiveQueries.Matches queries locals captures (generator captures) [p x] rows (fun _ => 10) := by
  refine ⟨Extension.identity captures, (fun _ => a), (fun _ => a), ?_⟩
  intro port
  have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
  subst port
  with_unfolding_all rfl

theorem q_has_an_individual_witness :
    ContextualConjunctiveQueries.Matches queries locals captures (generator captures) [q x] rows (fun _ => 20) := by
  refine ⟨Extension.identity captures, (fun _ => b), (fun _ => a), ?_⟩
  intro port
  have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
  subst port
  with_unfolding_all rfl

theorem every_present_pair_is_enumerated (chosen : Fin 2 → Nat) (present : ∀ port, chosen port ∈ world) :
    chosen ∈ candidates world 2 := (mem_candidates world chosen).mpr present

theorem repeated_reads_of_one_physical_row_are_enumerated :
    (fun _ : Fin 2 => 10) ∈ candidates world 2 :=
  (mem_candidates world _).mpr (fun _ => by decide +kernel)

theorem the_shared_variable_conjunction_is_certifiably_absent :
    certifies queries locals captures 2 [] patterns rows world = true := by
  apply decide_eq_true
  intro chosen member
  have first := (mem_candidates world chosen).mp member ⟨0, by decide +kernel⟩
  have second := (mem_candidates world chosen).mp member ⟨1, by decide +kernel⟩
  have shape : chosen = fun port => if port.val = 0 then chosen ⟨0, by decide +kernel⟩ else chosen ⟨1, by decide +kernel⟩ := by
    funext port
    change Fin 2 at port
    fin_cases port <;> rfl
  simp only [world, Finset.mem_insert, Finset.mem_singleton] at first second
  rw [shape]
  exact the_actual_tuple_refuses _ _ first second

theorem the_executable_result_proves_the_all_future_absence :
    Ask queries locals captures [] patterns rows world :=
  certifies_sound queries locals captures 2 [] patterns rows world the_shared_variable_conjunction_is_certifiably_absent

def addedChoice (port : Fin patterns.length) : Nat := if port.val = 0 then 10 else 30

theorem q_at_the_shared_value_defeats_the_conjunction_absence :
    ContextualConjunctiveQueries.Matches queries locals captures (generator captures) patterns rows addedChoice := by
  refine ⟨Extension.identity captures, (fun _ => a), (fun _ => a), ?_⟩
  intro port
  change Fin 2 at port
  have cases : port.val = 0 ∨ port.val = 1 := by have := port.isLt; omega
  rcases cases with first | second
  · have only : port = 0 := Fin.ext first
    subst port
    with_unfolding_all rfl
  · have only : port = 1 := Fin.ext second
    subst port
    with_unfolding_all rfl

theorem adding_that_row_invalidates_the_guard :
    ¬ Ask queries locals captures [] patterns rows enlarged := by
  intro absent
  exact absent Nat captures (generator captures) (by intro equation member; cases member) addedChoice
    (fun port => by unfold addedChoice; split <;> decide +kernel)
    q_at_the_shared_value_defeats_the_conjunction_absence

theorem an_existing_join_is_not_certified_absent :
    certifies queries locals captures 2 [] patterns rows enlarged = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact adding_that_row_invalidates_the_guard (certifies_sound queries locals captures 2 [] patterns rows enlarged accepted)

def universalRow : Raw := p (generator (ContextualSelectionViews.source locals captures) (.inl 0))
def schemaRows (_ : Nat) : Stored := .schema universalRow
def independentPatterns : List Pattern := [p patternA, p patternB]

theorem one_schema_row_may_be_read_at_two_independent_instances :
    ContextualConjunctiveQueries.Matches queries locals captures (generator captures)
      independentPatterns schemaRows (fun _ => 7) := by
  refine ⟨Extension.identity captures, (fun _ => a),
    (fun name => if name.scope = 2 then a else b), ?_⟩
  intro port
  change Fin 2 at port
  have cases : port.val = 0 ∨ port.val = 1 := by have := port.isLt; omega
  rcases cases with first | second
  · have only : port = 0 := Fin.ext first
    subst port
    with_unfolding_all rfl
  · have only : port = 1 := Fin.ext second
    subst port
    with_unfolding_all rfl

theorem those_repeated_schema_reads_are_never_certified_absent (fuel : Nat) :
    certifies queries locals captures fuel [] independentPatterns schemaRows {7} = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact certifies_sound queries locals captures fuel [] independentPatterns schemaRows {7} accepted
    Nat captures (generator captures) (by intro equation member; cases member) (fun _ => 7)
    (fun _ => by decide +kernel) one_schema_row_may_be_read_at_two_independent_instances

def repeatedRow : Raw := pair (generator (ContextualSelectionViews.source locals captures) (.inl 0))
  (generator (ContextualSelectionViews.source locals captures) (.inl 0))
def aliasRows (_ : Nat) : Stored := .schema repeatedRow

theorem alias_tuple_shapes_conflict (Next : Type)
    (images : ContextualShapeErasure.ShapeAssignment base (Nat ⊕ (ScopedVar Nat ⊕ Nat)) Next) :
    ¬ ContextualShapeErasure.ShapeModels images (ContextualResidual.observeProblem
      (joint queries locals captures [] [pair patternA patternB] aliasRows (fun _ => 7))) := by
  intro models
  have same := models ((ContextualResidual.observeProblem
    (joint queries locals captures [] [pair patternA patternB] aliasRows (fun _ => 7))).get ⟨0, by decide +kernel⟩) (List.get_mem _ _)
  have firstValue := Option.some.inj (congrArg shapeFirst same)
  have secondValue := Option.some.inj (congrArg shapeSecond same)
  change images (.inr (.inl (ScopedVar.at 2 0))) = shapeA at firstValue
  change images (.inr (.inl (ScopedVar.at 2 0))) = shapeB at secondValue
  exact the_two_rigid_shapes_are_distinct (firstValue.symm.trans secondValue)

theorem aliases_inside_one_row_are_not_freshened_per_hole :
    certifies queries locals captures 2 [] [pair patternA patternB] aliasRows {7} = true := by
  apply decide_eq_true
  intro chosen member
  have fixed : chosen = fun _ => 7 := by
    funext port
    exact Finset.mem_singleton.mp ((mem_candidates {7} chosen).mp member port)
  rw [fixed]
  exact ContextualConjunctiveRefusal.of_shape_inconsistency queries locals captures 1 [] [pair patternA patternB]
    aliasRows (fun _ => 7) (by rw [← ContextualPatternFragment.checkProblem_iff]; decide +kernel) alias_tuple_shapes_conflict

def boundLater : Assignment captures captures := fun _ => a

theorem later_binding_of_a_caller_variable_can_make_a_join :
    ContextualConjunctiveQueries.Matches queries locals captures boundLater [p shared] rows (fun _ => 10) := by
  refine ⟨Extension.identity captures, (fun _ => a), (fun _ => a), ?_⟩
  intro port
  have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
  subst port
  with_unfolding_all rfl

theorem the_check_cannot_manufacture_or_forget_the_caller_binding :
    ¬ Ask queries locals captures [] [p shared] rows {10} := by
  intro absent
  exact absent Nat captures boundLater (by intro equation member; cases member) (fun _ => 10)
    (fun _ => by decide +kernel) later_binding_of_a_caller_variable_can_make_a_join

theorem a_shared_caller_variable_prevents_absence_certification (fuel : Nat) :
    certifies queries locals captures fuel [] [p shared] rows {10} = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact the_check_cannot_manufacture_or_forget_the_caller_binding
    (certifies_sound queries locals captures fuel [] [p shared] rows {10} accepted)

def binderQueries (_ : Nat) : MetaArity base := ([()], ())
def binderPattern : Term (signature base (queryFamily binderQueries captures)) [] () :=
  .op (.inl .lam) (.cons
    (.op (.inr (Operator.mk (declaration := queryFamily binderQueries captures) (.inl 0)))
      (.cons (.var .zero) .nil)) .nil)
def boundIdentity : Captured := .op (.inl .lam) (.cons (.var .zero) .nil)
def binderRows (_ : Nat) : Stored := .shared boundIdentity

theorem a_declared_query_parameter_can_refer_to_its_bound_variable :
    ContextualConjunctiveQueries.Matches binderQueries locals captures (generator captures)
      [binderPattern] binderRows (fun _ => 7) := by
  refine ⟨Extension.identity captures, (fun _ => .var .zero), (fun _ => a), ?_⟩
  intro port
  have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
  subst port
  with_unfolding_all rfl

def forbiddenBinderPattern : Pattern := .op (.inl .lam)
  (.cons (.op (.inr (Operator.mk (declaration := queryFamily queries captures) (.inl 0))) .nil) .nil)

theorem a_nullary_query_local_cannot_capture_the_same_bound_variable :
    certifies queries locals captures 2 [] [forbiddenBinderPattern] binderRows {7} = true := by
  apply decide_eq_true
  intro chosen member
  have fixed : chosen = fun _ => 7 := by
    funext port
    exact Finset.mem_singleton.mp ((mem_candidates {7} chosen).mp member port)
  rw [fixed]
  decide +kernel

theorem zero_fuel_does_not_refute_any_of_the_nonempty_candidate_set :
    certifies queries locals captures 0 [] patterns rows world = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have all := of_decide_eq_true accepted
  have contradiction := all (fun _ : Fin patterns.length => 10)
    ((mem_candidates world _).mpr (fun _ => by decide +kernel))
  cases contradiction

theorem empty_conjunction_has_its_empty_candidate_even_in_an_empty_world :
    ContextualConjunctiveBoundaries.emptyChoice (O := Nat) ∈ candidates (∅ : Finset Nat) 0 :=
  ContextualConjunctiveBoundaries.the_empty_tuple_is_enumerated ∅

theorem empty_conjunction_is_not_absent (fuel : Nat) :
    certifies queries locals captures fuel [] ([] : List Pattern) rows ∅ = false :=
  ContextualConjunctiveBoundaries.no_fuel_can_certify_absence_of_a_consistent_empty_conjunction
    queries locals captures (generator captures) fuel [] rows ∅ (by intro equation member; cases member)

theorem nonempty_conjunction_is_absent_in_an_empty_world :
    certifies queries locals captures 0 [] patterns rows ∅ = true :=
  ContextualConjunctiveBoundaries.empty_world_certifies_a_nonempty_query queries locals captures 0 [] patterns (by decide +kernel) rows

theorem the_inconsistent_background_has_no_model {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment captures next) : ¬ ContextualFrameUnifier.Models candidate [(a, b)] := by
  intro models
  have same := models (a, b) (List.mem_singleton_self _)
  have sizes := congrArg termSize same
  change 1 = 3 at sizes
  omega

theorem an_inconsistent_background_makes_even_empty_absence_vacuous :
    Ask queries locals captures [(a, b)] ([] : List Pattern) rows world := by
  intro Next next candidate impossible
  exact False.elim (the_inconsistent_background_has_no_model next candidate impossible)

theorem that_vacuous_guard_does_not_supply_step_consistency :
    ¬ (ContextualFamilies.action captures [] ()).Consistent [(a, b)] := by
  rintro ⟨candidate, models⟩
  exact the_inconsistent_background_has_no_model captures candidate models

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls
