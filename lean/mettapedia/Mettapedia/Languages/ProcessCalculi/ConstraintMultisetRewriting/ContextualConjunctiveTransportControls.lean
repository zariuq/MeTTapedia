import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAskTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls

/-!
# Joined absence, independent schema instances and empty tuples retain their scopes

The semantic transport keeps every physical port. The actual finite
worklist certifier is also exercised on the transported conjunction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveTransportControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels ContextualConjunctiveQueries ContextualConjunctiveAbsence
open ContextualSelectionViews.Controls (base)
open ContextualConjunctiveControls
  (queries locals captures patterns rows world enlarged independentPatterns schemaRows
    one_schema_row_may_be_read_at_two_independent_instances shapeA shapeB shapeFirst shapeSecond
    the_two_rigid_shapes_are_distinct)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

abbrev unused (_ : Unit) : MetaArity base := ([()], ())
abbrev wide := extended unused captures
def grow := inclusion unused captures
def grownPatterns := mapPatterns queries grow patterns
def grownRows (occurrence : Nat) := (rows occurrence).map locals grow
def grownChoice (first second : Nat) (port : Fin grownPatterns.length) : Nat :=
  if port.val = 0 then first else second

theorem grown_tuple_shapes_conflict (first second : Nat)
    (firstPresent : first = 10 ∨ first = 20) (secondPresent : second = 10 ∨ second = 20)
    (Next : Type) (images : ContextualShapeErasure.ShapeAssignment base
      (Nat ⊕ (Mettapedia.Logic.LP.ScopedVar Nat ⊕ (Unit ⊕ Nat))) Next) :
    ¬ ContextualShapeErasure.ShapeModels images (ContextualResidual.observeProblem
      (joint queries locals wide [] grownPatterns grownRows (grownChoice first second))) := by
  intro models
  have firstEq := models ((ContextualResidual.observeProblem
    (joint queries locals wide [] grownPatterns grownRows (grownChoice first second))).get
      ⟨0, by change 0 < 2; decide +kernel⟩) (List.get_mem _ _)
  have secondEq := models ((ContextualResidual.observeProblem
    (joint queries locals wide [] grownPatterns grownRows (grownChoice first second))).get
      ⟨1, by change 1 < 2; decide +kernel⟩) (List.get_mem _ _)
  rcases firstPresent with rfl | rfl
  · rcases secondPresent with rfl | rfl
    · have different := Option.some.inj (congrArg shapeSecond secondEq)
      change shapeA = shapeB at different
      exact the_two_rigid_shapes_are_distinct different
    · have one := Option.some.inj (congrArg shapeFirst firstEq)
      have two := Option.some.inj (congrArg shapeFirst secondEq)
      change shapeA = images (.inl 0) at one
      change shapeB = images (.inl 0) at two
      exact the_two_rigid_shapes_are_distinct (one.trans two.symm)
  · have different := Option.some.inj (congrArg shapeSecond firstEq)
    change shapeB = shapeA at different
    exact the_two_rigid_shapes_are_distinct different.symm

theorem grown_tuple_is_certified (first second : Nat)
    (firstPresent : first = 10 ∨ first = 20) (secondPresent : second = 10 ∨ second = 20) :
    certifiesTuple queries locals wide 2 [] grownPatterns grownRows (grownChoice first second) = true := by
  apply ContextualConjunctiveRefusal.of_shape_inconsistency queries locals wide 1 [] grownPatterns grownRows
    (grownChoice first second) ?_ (grown_tuple_shapes_conflict first second firstPresent secondPresent)
  rw [← ContextualPatternFragment.checkProblem_iff]
  rcases firstPresent with rfl | rfl <;> rcases secondPresent with rfl | rfl <;> decide +kernel

theorem original_shared_query_absence_transports :
    Ask queries locals wide (ContextualFrameUnifier.mapProblem grow []) grownPatterns grownRows world :=
  (Ask.unused_extension_iff queries locals captures unused [] patterns rows world).mpr
    ContextualConjunctiveControls.the_executable_result_proves_the_all_future_absence

theorem the_added_shared_value_still_defeats_absence :
    ¬ Ask queries locals wide (ContextualFrameUnifier.mapProblem grow []) grownPatterns grownRows enlarged := by
  intro absent
  exact ContextualConjunctiveControls.adding_that_row_invalidates_the_guard
    ((Ask.unused_extension_iff queries locals captures unused [] patterns rows enlarged).mp absent)

theorem actual_transported_conjunction_is_certified :
    certifies queries locals wide 2 [] grownPatterns grownRows world = true := by
  apply decide_eq_true
  intro chosen member
  have first := (mem_candidates world chosen).mp member ⟨0, by change 0 < 2; decide +kernel⟩
  have second := (mem_candidates world chosen).mp member ⟨1, by change 1 < 2; decide +kernel⟩
  have shape : chosen = grownChoice (chosen ⟨0, by change 0 < 2; decide +kernel⟩)
      (chosen ⟨1, by change 1 < 2; decide +kernel⟩) := by
    funext port
    change Fin 2 at port
    fin_cases port <;> rfl
  simp only [world, Finset.mem_insert, Finset.mem_singleton] at first second
  rw [shape]
  exact grown_tuple_is_certified _ _ first second

theorem the_empty_query_keeps_its_empty_candidate :
    certifies queries locals wide 0 [] [] grownRows ∅ = false := by decide +kernel

theorem the_two_independent_instances_survive_capture_transport :
    Matches queries locals wide (ContextualStoredRows.liftCaptures unused (generator captures))
      (mapPatterns queries grow independentPatterns)
      (fun occurrence => (schemaRows occurrence).map locals grow)
      (mapChoice queries grow independentPatterns (fun _ => 7)) := by
  apply (ContextualConjunctiveQueries.matches_after_capture_transport queries locals grow
    (ContextualStoredRows.liftCaptures unused (generator captures)) independentPatterns schemaRows (fun _ => 7)).mpr
  have grown := (ContextualConjunctiveQueries.matches_inclusion_iff queries locals unused captures (generator captures)
    independentPatterns schemaRows (fun _ => 7)).mpr one_schema_row_may_be_read_at_two_independent_instances
  exact (lifted_capture_assignment unused (generator captures)).symm ▸ grown

theorem repeated_physical_ports_are_still_seven
    (port : Fin (mapPatterns queries grow independentPatterns).length) :
    mapChoice queries grow independentPatterns (fun _ : Fin independentPatterns.length => 7) port = 7 := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveTransportControls
