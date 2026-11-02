import Mettapedia.Algebra.RuleAlgebra.SingleSpecies
import Mettapedia.Algebra.RuleAlgebra.MultiSpecies
import Mettapedia.Algebra.RuleAlgebra.OwnershipGluing
import Mettapedia.Algebra.RuleAlgebra.MomentEquations

/-!
# Behr–Krivine Rule Algebra, Regional Ownership Gluing, and Exact Moment Equations

Umbrella entry point for `Mettapedia.Algebra.RuleAlgebra`:

* `SingleSpecies`: 3-color occurrence representation `occRho1`, faithfulness
  (`occRho1_injective`), homomorphism (`occRho1_mul`), intertwining with uncolored
  bags (`forgetColors_occRho1`), associativity (`mul1_assoc`), and `Semiring SingleRuleAlgebra`.
* `MultiSpecies`: restricted tensor product (`tensorRules`), multi-species associativity
  (`mul_assoc`), `Semiring (MultiRuleAlgebra R)`, `Ring (SignedRuleAlgebra R)`,
  Z-set representation (`rhoZ_mul`), and positive/negative controls (`rho_churn_eq_keep`,
  `compose1_pureAbsent_take`, `naiveDropMul1_not_assoc`).
* `OwnershipGluing` (`Q3.3`): necessary & sufficient regional boundary framing
  (`Rule.matchesBag_frame_iff_exhaust_subset`), closure under rule fusion with outbound
  transfers (`Rule.ReadsWithin.of_compose`), operator frame equivariance
  (`rhoZ_comm_shiftBagZ`), and disjoint-region commutation
  (`commutator_eq_zero_of_disjoint_regions`).
* `MomentEquations` (`Q3.2`): continuous-time Markov generator (`generator`), mass
  conservation (`totalMass_comp_generator`), syntactic Ehrenfest moment equation
  (`syntactic_ehrenfest`), Leibniz derivation (`commutator_mul_right`), closed-form
  reactive commutators (`commutator_pureAbsent_take`, `commutator_count_autocatalytic`,
  `commutator_lock_mutexAcquire`), and mutating-operator negative control
  (`ehrenfest_fails_for_non_observable`).
-/
