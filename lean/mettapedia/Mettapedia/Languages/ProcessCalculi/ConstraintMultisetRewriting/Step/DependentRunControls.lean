import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunRearrangement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBlockControls

/-!
# Actual dependent executions in the witnessed comparison groupoid

One event publishes a dependent path helper; the other publishes an
independent point helper. Both complete orders are executions of the actual
dependent full step. Their raw de Bruijn rows differ, while the canonical
block exchange preserves the typed rows and their occurrence identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open DependentFull.Controls TelescopeControls

def first : HelperFiring setting.levels Nat baseState := ⟨pathHelpers, fData⟩
def second : HelperFiring setting.levels Nat baseState := ⟨pointHelpers, gData⟩

theorem diamond : Diamond first second firstAdmitted secondAdmitted :=
  Classical.choice (diamond_exists first second firstAdmitted secondAdmitted independentAtJoint)

def firstOrder : (step setting.levels Nat).toStep.Run baseState := toFull diamond.forward
def secondOrder : (step setting.levels Nat).toStep.Run baseState := toFull diamond.backward

theorem actual_executions : firstOrder.word.length = 2 ∧ secondOrder.word.length = 2 := ⟨rfl, rfl⟩

theorem different_raw_rows :
    (firstOrder.last.label 1).2.code ≠ (secondOrder.last.label 1).2.code :=
  TelescopeControls.composites_differ diamond.afterFirst diamond.afterSecond

theorem actual_present_occurrences : firstOrder.last.present = secondOrder.last.present :=
  diamond.occurrences_kept

theorem actual_typed_row_transport (occurrence : Nat) :
    secondOrder.last.label occurrence =
      (firstOrder.last.label occurrence).reindex (exchange pointHelpers pathHelpers) :=
  diamond.typed_rows_kept occurrence

theorem existing_trace_recovered :
    (helperTransport setting.levels Nat).TraceEquiv baseState diamond.forward diamond.backward :=
  diamond.existing_trace

theorem witnessed_comparison_exists :
    Nonempty (Transport.RunRearrangement.Cell (helperTransport setting.levels Nat)
      diamond.forward diamond.backward) := ⟨diamond.cell⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls.actual_typed_row_transport
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls.different_raw_rows
