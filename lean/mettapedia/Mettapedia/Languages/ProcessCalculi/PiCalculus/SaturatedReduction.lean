import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceToolkit

/-!
# Saturated reduction bisimilarity

Two processes are saturated reduction bisimilar when, beside every process, a reduction of either is matched by a
reduction of the other, to processes again so related. The contexts are the parallel compositions.

- Every process is bisimilar to itself (`SaturatedReductionBisimilar.refl`), and the relation is symmetric
  (`SaturatedReductionBisimilar.symm`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- **A saturated reduction bisimulation**: beside every process, a reduction of either side is matched by one of the
other, to related processes. -/
def IsSaturatedReduction (relation : Process → Process → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ context : Process,
    (∀ next, Nonempty ((first ||| context) ⇝ next) →
      ∃ matched, Nonempty ((second ||| context) ⇝ matched) ∧ relation next matched) ∧
    (∀ next, Nonempty ((second ||| context) ⇝ next) →
      ∃ matched, Nonempty ((first ||| context) ⇝ matched) ∧ relation matched next)

/-- **Saturated reduction bisimilarity.** -/
def SaturatedReductionBisimilar (first second : Process) : Prop :=
  ∃ relation, IsSaturatedReduction relation ∧ relation first second

theorem SaturatedReductionBisimilar.refl (process : Process) : SaturatedReductionBisimilar process process :=
  ⟨Eq, fun _ _ same context => by
    subst same
    exact ⟨fun next step => ⟨next, step, rfl⟩, fun next step => ⟨next, step, rfl⟩⟩, rfl⟩

theorem SaturatedReductionBisimilar.symm {first second : Process} (bisimilar : SaturatedReductionBisimilar first second) :
    SaturatedReductionBisimilar second first := by
  obtain ⟨relation, saturated, related⟩ := bisimilar
  refine ⟨fun left right => relation right left, fun left right related context => ?_, related⟩
  obtain ⟨forth, back⟩ := saturated related context
  exact ⟨back, forth⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus
