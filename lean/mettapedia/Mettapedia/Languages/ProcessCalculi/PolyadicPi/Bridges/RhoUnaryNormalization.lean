import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mathlib.Order.WellFounded

/-!
# No infinite implementation work for a strongly normalizing source

An arbitrary authored rho firing either advances the retained unary source
or strictly decreases its finite administrative credit. Source accessibility
and induction on that credit therefore prove accessibility of every related
runtime state. The proof covers all schedules and intermediate states; it
does not identify source communications with implementation instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalization

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryReadback RhoUnaryWorld

/-- Every implementation firing is justified by either actual source
progress or a decrease in the existing exact work balance. -/
theorem strongly_normalizing {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess}
    (normalizing : Acc (fun after before => (NativeTypes.operationalTheory Γ).Step before after) origin)
    (before : Witness initialWorld origin current) :
    Acc (fun next state => Target.Step state next) current := by
  induction normalizing generalizing current with
  | intro origin _ sourceIH =>
      have solve : ∀ amount : Nat, ∀ (state : TargetProcess)
          (witness : Witness initialWorld origin state), witness.credit = amount →
          Acc (fun next state => Target.Step state next) state := by
        intro amount
        induction amount using Nat.strong_induction_on with
        | h amount creditIH =>
            intro state witness credit
            apply Acc.intro state
            intro next actualStep
            obtain ⟨after, nextWitness, charge, status, balance⟩ := readOne witness actualStep
            rcases status with ⟨zero, same⟩ | ⟨_, advanced⟩
            · subst after
              have less : nextWitness.credit < amount := by omega
              exact creditIH nextWitness.credit less next nextWitness rfl
            · exact sourceIH after advanced nextWitness
      exact solve before.credit current before rfl

/-- A failure of implementation accessibility cannot be introduced solely
by an infinite sequence of administrative firings. -/
theorem nonnormalizing_reflected {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (divergent : ¬ Acc (fun next state => Target.Step state next) current) :
    ¬ Acc (fun after before => (NativeTypes.operationalTheory Γ).Step before after) origin :=
  fun normalizing => divergent (strongly_normalizing normalizing before)

/-- An infinite supplied execution of the actual runtime entails an
infinite actual source execution starting at the same retained source.
The source sequence is obtained by dependent choice after the exact
credit argument rules out infinite administrative work. -/
theorem infinite_execution_reflected {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (runtime : Nat → TargetProcess) (starts : runtime 0 = current)
    (firings : ∀ index, Target.Step (runtime index) (runtime (index + 1))) :
    ∃ source : Nat → Proc Γ, source 0 = origin ∧
      ∀ index, (NativeTypes.operationalTheory Γ).Step (source index) (source (index + 1)) := by
  have divergent : ¬ Acc (fun next state => Target.Step state next) current :=
    not_acc_iff_exists_descending_chain.mpr ⟨runtime, starts, firings⟩
  exact not_acc_iff_exists_descending_chain.mp (nonnormalizing_reflected before divergent)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalization
