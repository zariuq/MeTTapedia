import Mettapedia.InformationTheory.FiniteProbability

/-!
# Strong lumpability of finite controlled stochastic kernels

A state observation admits an exact stochastic dynamics when states with the
same observation have the same total transition mass into each observation
class. The quotient kernel is constructed by aggregation and is independent
of the chosen representatives. Probability prediction commutes with the
observation. This is a law about future updates, stronger than agreement of
the current readout.
-/

namespace Mettapedia.ProbabilityTheory.FiniteLumpability

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S C A : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-- The controlled kernel cannot distinguish states inside an observation fibre. -/
def StrongLumpability (view : S → C) (kernel : A → S → Prob S) : Prop :=
  ∀ a s t, view s = view t → coarsen (kernel a s) view = coarsen (kernel a t) view

/-- The aggregated stochastic kernel, computed from representatives of observation classes. -/
noncomputable def lumpedKernel (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) : A → C → Prob C :=
  fun a c => coarsen (kernel a (representative c)) view

/-- With a right inverse and lumpability, the aggregate of every source state is the quotient row. -/
theorem lumpedKernel_correct (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (a : A) (s : S) :
    lumpedKernel view kernel representative a (view s) = coarsen (kernel a s) view :=
  lumpable a (representative (view s)) s (sectionLaw (view s))

theorem lumpedKernel_independent (view : S → C) (kernel : A → S → Prob S)
    (first second : C → S) (firstLaw : Function.RightInverse first view)
    (secondLaw : Function.RightInverse second view)
    (lumpable : StrongLumpability view kernel) :
    lumpedKernel view kernel first = lumpedKernel view kernel second := by
  funext a c
  exact lumpable a (first c) (second c) ((firstLaw c).trans (secondLaw c).symm)

/-- Predicting and then observing equals predicting with the genuinely aggregated kernel. -/
theorem coarsen_predict (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (prior : Prob S) (a : A) :
    coarsen (Prob.bind prior (kernel a)) view =
      Prob.bind (coarsen prior view) (lumpedKernel view kernel representative a) := by
  rw [coarsen_bind]
  apply Subtype.ext
  funext c
  simp only [bind_apply]
  rw [coarsen_expectation]
  apply Finset.sum_congr rfl
  intro s _
  rw [lumpedKernel_correct view kernel representative sectionLaw lumpable]

/-- Every reward of the observed state has the same expected next-state value. -/
theorem next_reward_preserved (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (prior : Prob S) (a : A) (reward : C → ℝ) :
    (∑ s, (Prob.bind prior (kernel a)).1 s * reward (view s)) =
      ∑ c, (Prob.bind (coarsen prior view) (lumpedKernel view kernel representative a)).1 c * reward c := by
  rw [← coarsen_expectation, coarsen_predict view kernel representative sectionLaw lumpable]

end Mettapedia.ProbabilityTheory.FiniteLumpability
