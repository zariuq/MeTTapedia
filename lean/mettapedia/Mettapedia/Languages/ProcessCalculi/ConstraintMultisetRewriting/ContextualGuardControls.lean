import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRefutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViewControls

/-!
# Scoped guards distinguish private instances from future caller bindings

A schematic row counts once under every model. A shared unknown does not
license absence from its identity instance. The bounded absence checker
requires actual refutation and never treats exhausted fuel as absence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm atom pair p
  a b rawA rawB privateVariable universalRow sharedValue)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

abbrev CapturedTerm := Term (signature base captures) [] ()
abbrev Stored := ContextualStoredRows.Row locals captures [] ()
def capturedAtom : CapturedTerm := atom captures
def query : CapturedTerm := p capturedAtom
def world : Finset Nat := {7}
def schemaRows (_ : Nat) : Stored := .schema universalRow
def sharedRows (_ : Nat) : Stored := .shared (p sharedValue)

theorem schema_matches_every_supplied_model {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment captures next) :
    Matches locals candidate (instantiate candidate query) (schemaRows 7) := by
  let extension := Extension.withLocals locals next
  let localBodies : Assignment locals extension.declarations := fun _ => atom extension.declarations
  refine ⟨extension, localBodies, ?_⟩
  with_unfolding_all rfl

theorem singleton_region {Next : Type} (next : Next → MetaArity base)
    (candidate : Assignment captures next) (rows : Nat → Stored) (pattern : CapturedTerm)
    (matched : Matches locals candidate (instantiate candidate pattern) (rows 7)) :
    region locals candidate rows world pattern = {7} := by
  classical
  ext occurrence
  constructor
  · intro member
    exact ((mem_region locals candidate rows world pattern occurrence).mp member).1
  · intro member
    have same : occurrence = 7 := Finset.mem_singleton.mp member
    subst occurrence
    exact (mem_region locals candidate rows world pattern 7).mpr ⟨by decide, matched⟩

theorem a_schematic_row_entails_count_one :
    Ask locals ([] : EquationStore CapturedTerm) schemaRows world (.count query 1) := by
  intro Next next candidate _
  exact (congrArg Finset.card
    (singleton_region next candidate schemaRows query (schema_matches_every_supplied_model next candidate))).trans
    (by decide : ({7} : Finset Nat).card = 1)

def localOne : Assignment locals raw := fun _ => rawA
def localTwo : Assignment locals raw := fun identity => if identity = 0 then rawA else rawB
def localExtension := Extension.withLocals locals captures

theorem distinct_local_witnesses_have_the_same_observed_instance :
    instantiate (instanceAssignment locals localOne localExtension.assignment (generator captures)) universalRow =
        instantiate localExtension.assignment query ∧
      instantiate (instanceAssignment locals localTwo localExtension.assignment (generator captures)) universalRow =
        instantiate localExtension.assignment query := by
  constructor <;> with_unfolding_all rfl

theorem the_local_witnesses_are_not_the_same_assignment : localOne ≠ localTwo := by
  intro same
  have different := congrArg (fun assignment : Assignment locals raw => termSize (assignment 1)) same
  change 1 = 3 at different
  omega

theorem equivalent_local_witnesses_still_count_one_occurrence :
    Holds locals (generator captures) schemaRows world (.count query 1) :=
  a_schematic_row_entails_count_one Nat captures (generator captures)
    (fun _ member => False.elim (List.not_mem_nil member))

theorem changing_private_witnesses_cannot_change_a_capture :
    instanceAssignment locals localOne localExtension.assignment (generator captures) (.inr 0) =
      instanceAssignment locals localTwo localExtension.assignment (generator captures) (.inr 0) := rfl

private theorem query_ne_live_unknown : query ≠ p sharedValue := by
  intro same
  have fields := eq_of_heq (Term.op.inj same).2
  have first := (Args.cons.inj fields).1
  have heads := (Term.op.inj first).1
  cases heads

theorem identity_absence_of_a_shared_unknown_is_only_pointwise :
    Holds locals (generator captures) sharedRows world (.absent query) := by
  intro _ _ matched
  exact query_ne_live_unknown matched

def assignedA : Assignment captures captures := fun _ => capturedAtom

theorem later_binding_makes_the_shared_row_match :
    Matches locals assignedA (instantiate assignedA query) (sharedRows 7) := by
  with_unfolding_all rfl

theorem pointwise_identity_absence_does_not_admit_the_guard :
    ¬ Ask locals ([] : EquationStore CapturedTerm) sharedRows world (.absent query) := by
  intro admitted
  have absent := admitted Nat captures assignedA (fun _ member => False.elim (List.not_mem_nil member))
  exact absent 7 (by decide) later_binding_makes_the_shared_row_match

theorem an_unknown_shared_row_does_not_entail_count_zero :
    ¬ Ask locals ([] : EquationStore CapturedTerm) sharedRows world (.count query 0) := by
  intro admitted
  have zero := admitted Nat captures assignedA (fun _ member => False.elim (List.not_mem_nil member))
  have one := congrArg Finset.card
    (singleton_region captures assignedA sharedRows query later_binding_makes_the_shared_row_match)
  change (region locals assignedA sharedRows world query).card = 0 at zero
  have one' : (region locals assignedA sharedRows world query).card = 1 := one.trans (by decide)
  omega

theorem an_unknown_shared_row_does_not_entail_count_one :
    ¬ Ask locals ([] : EquationStore CapturedTerm) sharedRows world (.count query 1) := by
  intro admitted
  have one := admitted Nat captures (generator captures) (fun _ member => False.elim (List.not_mem_nil member))
  have empty := (absent_iff_empty locals (generator captures) sharedRows world query).mp
    identity_absence_of_a_shared_unknown_is_only_pointwise
  have zero : (region locals (generator captures) sharedRows world query).card = 0 :=
    (congrArg Finset.card empty).trans rfl
  change (region locals (generator captures) sharedRows world query).card = 1 at one
  omega

def rigidOtherRows (_ : Nat) : Stored := .shared (p (pair capturedAtom capturedAtom))

theorem zero_fuel_is_not_an_absence_certificate :
    ContextualGuardRefutation.certifiesAbsence locals captures 0
      ([] : EquationStore CapturedTerm) rigidOtherRows world query = false := by decide

theorem an_actual_rigid_refutation_certifies_absence :
    ContextualGuardRefutation.certifiesAbsence locals captures 1
      ([] : EquationStore CapturedTerm) rigidOtherRows world query = true := by decide +kernel

theorem the_executable_certificate_proves_the_future_absence_ask :
    Ask locals ([] : EquationStore CapturedTerm) rigidOtherRows world (.absent query) :=
  ContextualGuardRefutation.certifiesAbsence_sound locals captures 1 [] rigidOtherRows world query
    an_actual_rigid_refutation_certifies_absence

theorem a_compatible_schema_does_not_certify_absence :
    ContextualGuardRefutation.certifiesAbsence locals captures 2
      ([] : EquationStore CapturedTerm) schemaRows world query = false := by
  cases computed : ContextualGuardRefutation.certifiesAbsence locals captures 2
      ([] : EquationStore CapturedTerm) schemaRows world query with
  | false => rfl
  | true =>
      have admitted := ContextualGuardRefutation.certifiesAbsence_sound locals captures 2 [] schemaRows world query computed
      have absent := admitted Nat captures (generator captures)
        (fun _ member => False.elim (List.not_mem_nil member))
      exact False.elim (absent 7 (by decide) (schema_matches_every_supplied_model captures (generator captures)))

theorem absence_after_consuming_the_matching_schema_keeps_count_one :
    Holds locals assignedA schemaRows (world.erase 7) (.absent query) ↔
      Holds locals assignedA schemaRows world (.count query 1) :=
  absent_after_erase_iff_count_one locals assignedA schemaRows world query 7 (by decide)
    (schema_matches_every_supplied_model captures assignedA)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics.Controls
