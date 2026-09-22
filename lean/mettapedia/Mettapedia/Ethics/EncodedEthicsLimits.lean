import Mettapedia.Ethics.MoralUndecidability
import Mettapedia.Computability.KolmogorovComplexity.Uncomputability
import Foundation.FirstOrder.Incompleteness.First
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.Löb

/-!
# Limits that apply to ethics as far as it is encoded

The results below are standard theorems of computability and proof theory,
stated for the objects this development uses to encode ethical systems.  They
hold of an ethical system exactly to the extent the system is encoded by those
objects: actions as partial recursive codes, exemplar records as binary strings,
and moral sentences as sentences of an arithmetic theory.

**Actions as partial recursive codes.**

* No computable reform changes what every agent does: some agent behaves
  exactly as its reformed version (`reform_leaves_some_behavior`, Kleene's
  recursion theorem).  Computability is load-bearing: a noncomputable reform
  changes every agent's behavior (`noncomputable_reform_changes_everyone`).
* Every partial recursive way of acting on one's own code is realized by an
  agent: some agent computes exactly what that policy prescribes for it
  (`self_referential_agent`).

**Exemplar records as binary strings.**

* The length of the shortest description of an exemplar record by the optimal
  machine is not computable (`exemplarDescriptionLength_not_computable`).

**Moral sentences in an arithmetic theory.**

* **Self-trust permits everything it covers.**  If a theory proves, for each
  action, that its own proof of the action's permissibility makes the action
  permissible, then it proves every such action permissible
  (`selfTrust_permits`, Löb's theorem).  Consistently, it then prohibits none of
  them (`selfTrust_prohibits_nothing`).  The hypothesis cannot be had for free:
  a consistent theory does not trust itself about falsity
  (`no_selfTrust_about_falsity`).
* A sound, computably axiomatized theory containing enough arithmetic leaves
  some of its own sentences undecided (`ethical_theory_incomplete`, Gödel's first
  theorem), and cannot prove its own consistency
  (`ethical_theory_cannot_prove_own_consistency`, the second).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EncodedEthicsLimits

open Nat.Partrec (Code)
open Mettapedia.Ethics.MoralUndecidability

/-! ## Actions as partial recursive codes -/

/-- **No computable reform changes every agent's behavior.** -/
theorem reform_leaves_some_behavior {reform : ActionCode → ActionCode} (computable : Computable reform) :
    ∃ agent, consequences (reform agent) = consequences agent :=
  Code.fixed_point computable

open Classical in
/-- A reform that sends the zero agent's behavior elsewhere and everything else to
the zero agent. -/
noncomputable def contrarianReform (agent : ActionCode) : ActionCode :=
  if agent.eval = Code.zero.eval then Code.succ else Code.zero

/-- **Computability is load-bearing**: the contrarian reform changes every agent's
behavior. -/
theorem noncomputable_reform_changes_everyone (agent : ActionCode) :
    consequences (contrarianReform agent) ≠ consequences agent := by
  unfold contrarianReform consequences
  split_ifs with same
  · rw [same]
    intro equal
    have values := congrFun equal 0
    simp only [Code.eval] at values
    have ones : (1 : ℕ) = 0 :=
      Part.some_injective (values.trans (rfl : (pure 0 : ℕ →. ℕ) 0 = Part.some 0))
    exact absurd ones (by decide)
  · exact fun equal => same equal.symm

/-- **Agents acting on their own code exist for every partial recursive policy.** -/
theorem self_referential_agent {policy : ActionCode → ℕ →. ℕ} (partrec : Partrec₂ policy) :
    ∃ agent, consequences agent = policy agent :=
  Code.fixed_point₂ partrec

/-! ## Exemplar records as binary strings -/

open KolmogorovComplexity in
/-- The length of the shortest description of an exemplar record by the optimal
machine. -/
noncomputable def exemplarDescriptionLength (record : BinString) : ℕ :=
  kolmogorovComplexity record

open KolmogorovComplexity Mettapedia.Computability.Hutter in
/-- **The shortest description of an exemplar record is not computable.** -/
theorem exemplarDescriptionLength_not_computable :
    ¬ FinitelyComputable exemplarDescriptionLength :=
  kolmogorovComplexity_not_finitelyComputable

/-! ## Moral sentences in an arithmetic theory -/

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

section SelfTrust

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {Action : Type*}

/-- **Self-trust permits everything it covers** (Löb's theorem). -/
theorem selfTrust_permits (permitted : Action → ArithmeticSentence)
    (selfTrust : ∀ action, T ⊢ T.standardProvability (permitted action) ➝ permitted action)
    (action : Action) : T ⊢ permitted action :=
  löb_theorem (selfTrust action)

/-- **And a consistent self-trusting theory prohibits none of it.** -/
theorem selfTrust_prohibits_nothing [Consistent T] (permitted : Action → ArithmeticSentence)
    (selfTrust : ∀ action, T ⊢ T.standardProvability (permitted action) ➝ permitted action)
    (action : Action) : T ⊬ ∼permitted action := by
  intro prohibited
  exact not_consistent_iff_inconsistent.mpr
    (inconsistent_of_provable_of_unprovable (selfTrust_permits permitted selfTrust action) prohibited)
    inferInstance

/-- **Self-trust is not free**: a consistent theory does not trust its own proofs
of falsity. -/
theorem no_selfTrust_about_falsity [Consistent T] :
    T ⊬ T.standardProvability ⊥ ➝ ⊥ := fun trusted =>
  not_consistent_iff_inconsistent.mpr (inconsistent_iff_provable_bot.mpr (löb_theorem trusted))
    inferInstance

end SelfTrust

/-- **An ethical theory containing enough arithmetic is incomplete** (Gödel's
first theorem). -/
theorem ethical_theory_incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : Incomplete T :=
  Arithmetic.incomplete T

/-- **And cannot prove its own consistency** (Gödel's second theorem). -/
theorem ethical_theory_cannot_prove_own_consistency (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [Consistent T] : T ⊬ ↑T.consistent :=
  consistent_unprovable T

#print axioms reform_leaves_some_behavior
#print axioms noncomputable_reform_changes_everyone
#print axioms self_referential_agent
#print axioms exemplarDescriptionLength_not_computable
#print axioms selfTrust_permits
#print axioms selfTrust_prohibits_nothing
#print axioms no_selfTrust_about_falsity
#print axioms ethical_theory_incomplete
#print axioms ethical_theory_cannot_prove_own_consistency

end Mettapedia.Ethics.EncodedEthicsLimits
