import Mettapedia.OSLF.PiCalculus.Reduction

/-!
# Multi-Step Reduction for π-Calculus

Defines reflexive-transitive closure of reduction.
-/

namespace Mettapedia.OSLF.PiCalculus

/-- Reflexive-transitive closure of reduction -/
inductive MultiStep : Process → Process → Type where
  | refl (P : Process) :
      MultiStep P P
  | step (P Q R : Process) (h : Reduces P Q) (rest : MultiStep Q R) :
      MultiStep P R

notation:50 P " ⇝* " Q => MultiStep P Q

/-- Transitivity -/
noncomputable def MultiStep.trans {P Q R : Process} :
    MultiStep P Q → MultiStep Q R → MultiStep P R := by
  intro h1 h2
  induction h1 with
  | refl _ => exact h2
  | step _ _ _ h_red _ ih => exact MultiStep.step _ _ _ h_red (ih h2)

/-- Single step embeds into multi-step -/
def MultiStep.single {P Q : Process} (h : P ⇝ Q) : MultiStep P Q :=
  MultiStep.step P Q Q h (MultiStep.refl Q)

/-- Parallel left congruence -/
noncomputable def MultiStep.par_left {P P' Q : Process} (h : MultiStep P P') : MultiStep (P ||| Q) (P' ||| Q) := by
  induction h with
  | refl _ => exact MultiStep.refl _
  | step _ _ _ h_red _ ih =>
      exact MultiStep.trans (MultiStep.single (Reduces.par_left _ _ _ h_red)) ih

/-- Parallel right congruence -/
noncomputable def MultiStep.par_right {P Q Q' : Process} (h : MultiStep Q Q') : MultiStep (P ||| Q) (P ||| Q') := by
  induction h with
  | refl _ => exact MultiStep.refl _
  | step _ _ _ h_red _ ih =>
      exact MultiStep.trans (MultiStep.single (Reduces.par_right _ _ _ h_red)) ih

/-- Restriction congruence -/
noncomputable def MultiStep.nu {x : Name} {P P' : Process} (h : MultiStep P P') : MultiStep (Process.nu x P) (Process.nu x P') := by
  induction h with
  | refl _ => exact MultiStep.refl _
  | step _ _ _ h_red _ ih =>
      exact MultiStep.trans (MultiStep.single (Reduces.res _ _ _ h_red)) ih

end Mettapedia.OSLF.PiCalculus
