import Mettapedia.GSLT.Core.OperationalNormalization
import Mettapedia.GSLT.Core.OperationalRealization

/-!
# Positive forward blocks do not exclude added implementation divergence

The existing source has one transition from `false` to `true`. The implementation
performs that transition and can then keep taking a step at `true`. The actual
operational correspondence has positive forward blocks and aligns the Boolean
readout exactly. Its reverse readback treats the extra loop as administration.

This separates preservation of source divergence from exclusion of target-only
divergence. It complements the existing empty-block control: no source transition
is erased here. A target-side progress certificate is an additional obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

abbrev source := OperationalRealization.FusionCanary.source

def spinning : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ after => after = true
  rewrites_resp_left := by
    intro before other after _ step
    exact ⟨after, step, rfl⟩
  rewrites_resp_right := by
    intro before after other step same
    exact same ▸ step

/-- Readback relates the actual committed Boolean states. -/
def correspondence : OperationalCorrespondence source spinning where
  related := Eq
  readStep := by
    intro origin current next related step
    subst current
    change next = true at step
    subst next
    cases origin with
    | false => exact .inr ⟨true, ⟨rfl, rfl⟩, rfl⟩
    | true => exact .inl rfl
  forward := by
    rintro origin after current related ⟨before, finished⟩
    subst origin
    subst after
    subst current
    exact ⟨true, ⟨.cons ⟨rfl⟩ (.refl true)⟩, rfl⟩

/-- Every source transition has a nonempty implementation from every related state. -/
theorem positive_forward :
    ∀ {origin after : source.Term} {current : spinning.Term},
      correspondence.related origin current → source.Step origin after →
      ∃ final, ∃ path : ExecutionPath spinning current final,
        0 < path.length ∧ correspondence.related after final := by
  rintro origin after current related ⟨before, finished⟩
  subst origin
  subst after
  subst current
  exact ⟨true, .cons ⟨rfl⟩ (.refl true), by decide, rfl⟩

theorem source_normalizes : Acc (fun next state => source.Step state next) false := by
  refine .intro false ?_
  rintro after ⟨_, rfl⟩
  refine .intro true ?_
  rintro later ⟨impossible, _⟩
  cases impossible

/-- The implementation has a genuine infinite execution after its first commit. -/
def execution : Nat → spinning.Term
  | 0 => false
  | _ + 1 => true

theorem execution_steps (index : Nat) : spinning.Step (execution index) (execution (index + 1)) := rfl

theorem target_does_not_normalize : ¬ Acc (fun next state => spinning.Step state next) false :=
  not_acc_iff_exists_descending_chain.mpr ⟨execution, rfl, execution_steps⟩

/-- Positive forward blocks do not provide the converse normalization theorem. -/
theorem positive_blocks_allow_added_divergence :
    correspondence.related false false ∧
      Acc (fun next state => source.Step state next) false ∧
      ¬ Acc (fun next state => spinning.Step state next) false :=
  ⟨rfl, source_normalizes, target_does_not_normalize⟩

/-- The finite observation law still holds for every Boolean readout predicate. -/
theorem finite_observations_agree (observe : Bool → Prop) :
    (∃ after, source.MultiStep false after ∧ observe after) ↔
      ∃ after, spinning.MultiStep false after ∧ observe after :=
  correspondence.reachable_iff observe observe (fun same => same ▸ Iff.rfl) rfl

/-- No strictly decreasing natural-number rank can certify this target's silent readback steps. -/
theorem no_administrative_rank :
    ¬ ∃ rank : spinning.Term → Nat,
      ∀ {origin current next}, correspondence.related origin current →
        spinning.Step current next → correspondence.related origin next →
        rank next < rank current := by
  rintro ⟨rank, decreases⟩
  exact Nat.lt_irrefl (rank true) (decreases (origin := true) (current := true) (next := true) rfl rfl rfl)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks.positive_forward
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks.positive_blocks_allow_added_divergence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks.finite_observations_agree
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.PositiveBlocks.no_administrative_rank
