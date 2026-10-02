import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction

/-!
# A pi process with no unguarded output does not reduce

Communication consumes an output that is not beneath an input or a
replication.  The number of such outputs is invariant under structural
congruence, including the unfolding of a replication, whose copy stays
beneath its input.  Every reducing process has one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

namespace Process

/-- The outputs not beneath an input or a replication. -/
def unguardedOutputs : Process → Nat
  | .nil => 0
  | .par left right => left.unguardedOutputs + right.unguardedOutputs
  | .input _ _ _ => 0
  | .output _ _ => 1
  | .nu _ body => body.unguardedOutputs
  | .replicate _ _ _ => 0

/-- Renaming a name does not change the unguarded outputs. -/
theorem unguardedOutputs_substitute (old new : Name) :
    ∀ process : Process,
      (process.substitute old new).unguardedOutputs = process.unguardedOutputs
  | .nil => rfl
  | .par left right => by
      simp only [substitute, unguardedOutputs, unguardedOutputs_substitute old new left,
        unguardedOutputs_substitute old new right]
  | .input channel bound body => by
      simp only [substitute]
      split_ifs <;> rfl
  | .output _ _ => rfl
  | .nu bound body => by
      simp only [substitute]
      split_ifs
      · rfl
      · simp only [unguardedOutputs, unguardedOutputs_substitute old new body]
  | .replicate channel bound body => by
      simp only [substitute]
      split_ifs <;> rfl

end Process

/-- Structural congruence preserves the unguarded outputs. -/
theorem unguardedOutputs_SC {left right : Process} (related : left ≡ right) :
    left.unguardedOutputs = right.unguardedOutputs := by
  induction related with
  | refl _ => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second
  | par_cong _ _ _ _ _ _ first second => simp only [Process.unguardedOutputs, first, second]
  | input_cong _ _ _ _ _ _ => rfl
  | nu_cong _ _ _ _ recurse => simpa only [Process.unguardedOutputs] using recurse
  | replicate_cong _ _ _ _ _ _ => rfl
  | par_comm _ _ => simp only [Process.unguardedOutputs]; omega
  | par_assoc _ _ _ => simp only [Process.unguardedOutputs]; omega
  | par_nil_left _ => simp only [Process.unguardedOutputs]; omega
  | par_nil_right _ => simp only [Process.unguardedOutputs]; omega
  | nu_nil _ => rfl
  | nu_par _ _ _ _ => rfl
  | nu_swap _ _ _ => rfl
  | alpha_input _ _ _ _ _ _ => rfl
  | alpha_nu _ _ body _ =>
      simp only [Process.unguardedOutputs, Process.unguardedOutputs_substitute]
  | alpha_replicate _ _ _ _ _ _ => rfl
  | replicate_unfold _ _ _ => rfl

/-- **Every reducing process has an unguarded output.** -/
theorem unguardedOutputs_pos_of_reduces {source target : Process} (step : source ⇝ target) :
    0 < source.unguardedOutputs := by
  induction step with
  | comm _ _ _ _ => simp [Process.unguardedOutputs]
  | par_left _ _ _ _ recurse => simp only [Process.unguardedOutputs]; omega
  | par_right _ _ _ _ recurse => simp only [Process.unguardedOutputs]; omega
  | res _ _ _ _ recurse => simpa only [Process.unguardedOutputs] using recurse
  | struct _ _ _ _ sourceRelated _ _ recurse =>
      rw [unguardedOutputs_SC sourceRelated]
      exact recurse

/-- A process with no unguarded output has no reduction. -/
theorem not_reduces_of_unguardedOutputs_eq_zero {source : Process}
    (silent : source.unguardedOutputs = 0) (target : Process) : IsEmpty (source ⇝ target) :=
  ⟨fun step => absurd (unguardedOutputs_pos_of_reduces step) (by omega)⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus
