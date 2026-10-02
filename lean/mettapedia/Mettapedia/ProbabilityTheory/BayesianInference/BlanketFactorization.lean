import Mettapedia.ProbabilityTheory.BayesianInference.MarkovBlanket
import Mettapedia.ProbabilityTheory.FiniteLumpability

/-!
# Factorized statistical interfaces and their temporal boundary

A fork-shaped finite law factors as a blanket prior times two independent
conditional kernels. The blanket is a separate coordinate, so conditioning
does not include the queried external or internal variable. Its statistical
independence theorem is inherited from the finite factorization theorem.

Temporal sufficiency is a further kernel condition: the control demonstrates
two equal current views with different future views.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.Prob

variable {E B I : Type*} [Fintype E] [Fintype B] [Fintype I]
  [DecidableEq E] [DecidableEq B] [DecidableEq I]

/-- A normalized finite fork law, with genuinely distinct conditioning coordinates. -/
noncomputable def forkLaw (blanket : Prob B) (external : B → Prob E)
    (internal : B → Prob I) : Prob (E × B × I) :=
  ⟨fun x => blanket.1 x.2.1 * (external x.2.1).1 x.1 * (internal x.2.1).1 x.2.2,
    (fun x => mul_nonneg (mul_nonneg (blanket.2.1 x.2.1)
      ((external x.2.1).2.1 x.1)) ((internal x.2.1).2.1 x.2.2)), by
      simp only [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, fun b => (internal b).2.2, mul_one]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, fun b => (external b).2.2, mul_one]
      exact blanket.2.2⟩

theorem fork_conditionalIndependent (blanket : Prob B) (external : B → Prob E)
    (internal : B → Prob I) :
    CondIndep (forkLaw blanket external internal).1 Prod.fst
      (fun x => x.2.1) (fun x => x.2.2) := by
  exact condIndep_of_factorization
    (fun e b => blanket.1 b * (external b).1 e) (fun b i => (internal b).1 i)

theorem fork_conditionalInformation_zero (blanket : Prob B) (external : B → Prob E)
    (internal : B → Prob I) :
    condMutualInfo (forkLaw blanket external internal).1 Prod.fst
      (fun x => x.2.1) (fun x => x.2.2) = 0 :=
  (conditionalInformation_eq_zero_iff _ _ _ _).mpr
    (fork_conditionalIndependent blanket external internal)

namespace TemporalControl

noncomputable def kernel (_ : Unit) (state : Bool × Bool) : Prob (Bool × Bool) :=
  Prob.dirac (state.2, state.2)

theorem equal_current_views : (false, false).1 = (false, true).1 := rfl

/-- A hidden internal bit changes the next observation despite equal current observations. -/
theorem different_future_views :
    coarsen (kernel () (false, false)) Prod.fst ≠
      coarsen (kernel () (false, true)) Prod.fst := by
  rw [kernel, kernel, coarsen_dirac, coarsen_dirac]
  intro equal
  have at_false := congrArg (fun p : Prob Bool => p.1 false) equal
  simp [Prob.dirac] at at_false

theorem not_lumpable :
    ¬ Mettapedia.ProbabilityTheory.FiniteLumpability.StrongLumpability Prod.fst kernel := by
  intro sufficient
  exact different_future_views (sufficient () (false, false) (false, true) equal_current_views)

end TemporalControl

end Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket
