import Mettapedia.Logic.ProofSearch.PlanExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Displayed accounting of the same branching proof plan

The existing refinement's `Stage.Cost` supplies the selected local charge on
its actual reconstruction evidence. The same free plan folds into a proof and
an account. Forgetting the account recovers the existing proof algebra.
Independent premise totals use commutative addition; no execution order or
search policy is selected. These are declared accounts, not runtime measures.

The account is not a semantic rule grade. Expansion preserves an account only when its local composite charge equals
the actual inner-plus-outer charges. Equality of proofs alone does not imply
equality of accounts.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch
namespace ProofObligations.PolynomialPlans

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open scoped BigOperators

variable {Goal : Type} {Solution : Goal → Type} {Routes : Goal → Type}
variable {Grade : Type} [AddCommMonoid Grade]

abbrev Charges (methods : ∀ goal, Routes goal → Refinement Solution goal) (Grade : Type)
    [AddCommMonoid Grade] :=
  ∀ goal route, Stage.Cost (methods goal route).stage Grade

/-- Read the existing stage charge on this very reconstruction receipt. -/
def localCharge (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) (goal : Goal) (route : Routes goal)
    (answers : ∀ premise, Solution ((methods goal route).query premise)) : Grade :=
  (charges goal route).charge
    (input := answers) (output := (methods goal route).rebuild answers) ⟨rfl⟩

/-- A writer-valued instance of the existing refinement. Its premise family and
query map are unchanged, so its polynomial is definitionally the same one. -/
def withCost (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) (goal : Goal) (route : Routes goal) :
    Refinement (fun goal => Solution goal × Grade) goal where
  Premise := (methods goal route).Premise
  query := (methods goal route).query
  rebuild answers :=
    ((methods goal route).rebuild (fun premise => (answers premise).1),
      (∑ premise, (answers premise).2) +
        localCharge methods charges goal route (fun premise => (answers premise).1))

def accountedAlgebra (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) :
    (polynomial methods).Algebra (fun _ goal => Solution goal × Grade) :=
  reconstruction (withCost methods charges)

/-- The proof projection is an algebra homomorphism, not a second checker. -/
def forgetAccount (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) :
    Algebra.Hom (accountedAlgebra methods charges) (reconstruction methods) where
  toFun := fun _ _ value => value.1
  commutes := by intros; rfl

noncomputable def account (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Solution goal × Grade) :
    ∀ base goal, (polynomial methods).Free Holes base goal → Solution goal × Grade :=
  Free.fold (polynomial methods) interpret (accountedAlgebra methods charges)

/-- Proof and accounting are projections of one fold over the retained plan. -/
theorem account_proof (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Solution goal × Grade)
    {base : Unit} {goal : Goal} (plan : (polynomial methods).Free Holes base goal) :
    (account methods charges interpret base goal plan).1 =
      Free.fold (polynomial methods) (fun base goal h => (interpret base goal h).1)
        (reconstruction methods) base goal plan :=
  Free.fold_unique (polynomial methods) _ _
    (fun base goal plan => (account methods charges interpret base goal plan).1)
    (by intros; rfl) (by intros; rfl) base goal plan

theorem account_fill (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) {Holes NextHoles : Unit → Goal → Type}
    (replacement : ∀ base goal, Holes base goal → (polynomial methods).Free NextHoles base goal)
    (interpret : ∀ base goal, NextHoles base goal → Solution goal × Grade)
    {base : Unit} {goal : Goal} (plan : (polynomial methods).Free Holes base goal) :
    account methods charges interpret base goal
        (Free.bind (polynomial methods) replacement base goal plan) =
      account methods charges
        (fun base goal h => account methods charges interpret base goal (replacement base goal h))
        base goal plan :=
  Free.fold_bind (polynomial methods) replacement interpret (accountedAlgebra methods charges) plan

/-- The primitive charges of a composite refinement, computed from its actual
inner reconstructions and their supplied proofs. -/
def expansionCharges (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) : Charges (compositeMethods methods) Grade :=
  fun goal route => Refinement.cost (compositeMethods methods goal route)
    (fun answers =>
      (∑ premise, localCharge methods charges _ (route.2 premise)
        (fun leaf => answers ⟨premise, leaf⟩)) +
      localCharge methods charges goal route.1
        (fun premise => (methods _ (route.2 premise)).rebuild
          (fun leaf => answers ⟨premise, leaf⟩)))

/-- The local accounting condition concerns only primitive reconstruction
charges, not the desired conclusion about entire plan folds. -/
theorem withCost_comp (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) (goal : Goal) (route : CompositeRoutes methods goal)
    (answers : ∀ premise, Solution ((compositeMethods methods goal route).query premise) × Grade) :
    ((withCost methods charges goal route.1).comp
      (fun premise => withCost methods charges _ (route.2 premise))).rebuild answers =
      (withCost (compositeMethods methods) (expansionCharges methods charges) goal route).rebuild
        answers := by
  apply Prod.ext
  · rfl
  · dsimp [compositeMethods, Refinement.comp] at answers
    change (∑ p, ((∑ q, (answers ⟨p, q⟩).2) +
        localCharge methods charges _ (route.2 p) (fun q => (answers ⟨p, q⟩).1))) +
        localCharge methods charges goal route.1
          (fun p => (methods _ (route.2 p)).rebuild (fun q => (answers ⟨p, q⟩).1)) =
      (∑ p, (answers p).2) +
        ((∑ p, localCharge methods charges _ (route.2 p) (fun q => (answers ⟨p, q⟩).1)) +
          localCharge methods charges goal route.1
            (fun p => (methods _ (route.2 p)).rebuild (fun q => (answers ⟨p, q⟩).1)))
    rw [Finset.sum_add_distrib, Fintype.sum_sigma]
    simp only [add_assoc]

/-- Expansion preserves the combined proof/account when the source account is
the sum of the actual inner and outer method charges. -/
theorem account_expansion (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Solution goal × Grade)
    {base : Unit} {goal : Goal}
    (plan : (polynomial (compositeMethods methods)).Free Holes base goal) :
    account methods charges interpret base goal ((expansion methods).run base goal plan) =
      account (compositeMethods methods) (expansionCharges methods charges) interpret
        base goal plan := by
  apply (expansion methods).reconstruct _ _ (fun _ _ value => value) interpret interpret
  · intros; rfl
  · intro base goal route values plans ih
    change ((withCost methods charges goal route.1).comp
        (fun premise => withCost methods charges _ (route.2 premise))).rebuild
          (fun premise => account methods charges interpret base _ (plans premise)) = _
    have same : (fun premise => account methods charges interpret base _ (plans premise)) =
        values := funext ih
    exact (congrArg
      (((withCost methods charges goal route.1).comp
        (fun premise => withCost methods charges _ (route.2 premise))).rebuild) same).trans
      (withCost_comp methods charges goal route values)

/-- An independently supplied source account is valid for account preservation
only after its local receipt charges have been compared with the primitives. -/
theorem account_expansion_of_charges
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (targetCharges : Charges methods Grade)
    (sourceCharges : Charges (compositeMethods methods) Grade)
    (agrees : ∀ goal route answers,
      localCharge (compositeMethods methods) sourceCharges goal route answers =
        localCharge (compositeMethods methods) (expansionCharges methods targetCharges)
          goal route answers)
    {Holes : Unit → Goal → Type}
    (interpret : ∀ base goal, Holes base goal → Solution goal × Grade)
    {base : Unit} {goal : Goal}
    (plan : (polynomial (compositeMethods methods)).Free Holes base goal) :
    account methods targetCharges interpret base goal ((expansion methods).run base goal plan) =
      account (compositeMethods methods) sourceCharges interpret base goal plan := by
  rw [account_expansion]
  have same : accountedAlgebra (compositeMethods methods) (expansionCharges methods targetCharges) =
      accountedAlgebra (compositeMethods methods) sourceCharges := by
    apply congrArg IndexedPolynomial.Algebra.mk
    funext base goal input
    rcases input with ⟨route, answers⟩
    apply Prod.ext
    · rfl
    · exact congrArg ((∑ premise : (compositeMethods methods goal route).Premise,
          (answers premise).2) + ·)
        (agrees goal route (fun premise => (answers premise).1)).symm
  exact congrArg (fun algebra => Free.fold _ interpret algebra base goal plan) same

/-- Successful accounting of a partial tree uses the existing partial
reconstruction of the same refinement family; one absent receipt is not success. -/
theorem missing_account_keeps_open
    (methods : ∀ goal, Routes goal → Refinement Solution goal)
    (charges : Charges methods Grade) {goal : Goal} (route : Routes goal)
    (answers : ∀ premise, Option (Solution ((methods goal route).query premise) × Grade))
    (missing : ∃ premise, answers premise = none) :
    reconstruct? (withCost methods charges)
      (applyMethod (withCost methods charges) route
        (fun premise => hole (withCost methods charges) (answers premise))) = none :=
  open_child_keeps_root_open (withCost methods charges) route answers missing

end ProofObligations.PolynomialPlans
end Mettapedia.Logic.ProofSearch
