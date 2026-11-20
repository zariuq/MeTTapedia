import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.RootDeterminism

/-!
# Harmless and harmful completion of an actual declared definition

Adding addition's successor row preserves the already completed numeral one.
The old stuck call add one zero ceases to be an answer. Checked footprints
license the former and reject reuse for the latter. Forged and stale context
caches are refused independently of the requested name.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ComputationSyntax ComputationSupport
open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.RootDeterminism
open NativeTypesOnTheStep.VectorAppend
open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one)

theorem inclusion : RulesSub prules vrules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := id
  computation := by
    intro n left right step
    rcases step with inherited | half
    · exact Or.inl inherited
    · exact Or.inr (half_sub_complete half)

theorem added_roots_use_add {n : Nat} {left right : Tower.Tm n} (step : vrules.computation.step left right) :
    prules.computation.step left right ∨ Uses addN left := by
  rcases step with inherited | added
  · exact Or.inl (Or.inl inherited)
  · cases added with
    | zero argument => exact Or.inl (Or.inr (HalfStep.zero _))
    | succ first second => exact Or.inr (by simp [Uses])

def cache : Cache Tower.Head 0 0 := ⟨.hole, ∅⟩

theorem cache_valid : cache.check = true := by decide
theorem numeral_scope : cache.scope one addN = true := by decide
theorem changed_call_scope_refused : cache.scope stuckCall addN = false := by decide

theorem numeral_license : RootAgreementAt (old := prules) (next := vrules) (one : Tower.Tm 0) :=
  cache.licenses_roots cache_valid one addN numeral_scope added_roots_use_add

theorem harmless_update : Answer prules (one : Tower.Tm 0) one ∧ Answer vrules (one : Tower.Tm 0) one := by
  have old : Answer prules (one : Tower.Tm 0) one := ⟨.refl, one_normal_half⟩
  exact ⟨old, answer_preserved inclusion NativeTypesOnTheStep.DeclaredConfluence.addPresentation
    (fun same => same) numeral_license old⟩

theorem old_stuck_answer : Answer prules stuckCall stuckCall := ⟨.refl, stuck_normal⟩

theorem new_step : vrules.computation.step stuckCall
    (.app (.const succN) (.app (.app (.const addN) (.const zeroN)) (.const zeroN))) :=
  Or.inr (AddStep.succ (.const zeroN) (.const zeroN))

theorem harmful_update : ¬ Answer vrules stuckCall stuckCall := fun answer => answer.2 (.root new_step)

theorem missing_root_license : ¬ RootAgreementAt (old := prules) (next := vrules) stuckCall := by
  intro license
  exact stuck_normal (.root (license 0 .hole stuckCall rfl _ new_step))

def forged : Cache Tower.Head 0 0 := ⟨.pairFst .hole (.const zeroN), ∅⟩
def stale : Cache Tower.Head 0 0 := ⟨.pairFst .hole (.const addN), {zeroN}⟩

theorem forged_refused : forged.check = false := by decide
theorem stale_refused : stale.check = false := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.Controls.harmless_update
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.Controls.harmful_update
