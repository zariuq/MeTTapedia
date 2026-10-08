import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSObservation
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A natural infinite-action law beyond finite GSOS observation

The independently specified law returns a stopped term exactly when one
child has no transition at any natural-number action. Direct images preserve
each emptiness test, so the law is natural under all variable maps. A fresh
enabled action outside any finite observation set changes its output.
Consequently no finite rule family per operator and output action denotes
this law. The separator concerns finite-premise reconstruction, not finite
successor sets or existence of the operational lifting.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.InfiniteBoundary

open _root_.CategoryTheory Mettapedia.TypeTheory
open Classical GSOSControls

theorem rename_stopped {X Y : signature.Families} (mapping : X ⟶ Y) :
    signature.rename mapping (stopped (X := X)) = stopped (X := Y) := by
  unfold stopped Mettapedia.OSLF.DeterministicGSOS.Signature.rename
  rw [IndexedPolynomial.Free.map_node]
  congr 1
  funext position
  exact position.elim

/-- An actual natural law with a complete, infinitely supported absence test. -/
def law : Law signature actions where
  app X := fun base sort => match base, sort with
    | .unit, () => ↾(fun layer => match layer with
      | ⟨.stopped, _⟩ => fun _ => ∅
      | ⟨.choose, children⟩ => fun _ =>
        if ∀ action, (children false).2 action = ∅ then {stopped (X := X)} else ∅)
  naturality {X Y} mapping := by
    funext base sort
    cases base
    cases sort
    apply ConcreteCategory.hom_ext
    intro layer
    rcases layer with ⟨operator, children⟩
    cases operator with
    | stopped =>
        funext action
        exact (Mettapedia.CategoryTheory.FinitePowerset.map_empty _).symm
    | choose =>
        funext action
        have emptiness : (∀ action, behaviourMap signature actions mapping PUnit.unit ()
            (children false).2 action = ∅) ↔ ∀ action, (children false).2 action = ∅ :=
          forall_congr' (fun action => availability_preserved signature actions mapping PUnit.unit ()
            (children false).2 action)
        by_cases disabled : ∀ action, (children false).2 action = ∅
        · have mapped := emptiness.mpr disabled
          change (if ∀ action, behaviourMap signature actions mapping PUnit.unit ()
            (children false).2 action = ∅ then {stopped (X := Y)} else ∅) =
              Mettapedia.CategoryTheory.FinitePowerset.map (signature.rename mapping)
                (if ∀ action, (children false).2 action = ∅ then {stopped (X := X)} else ∅)
          rw [if_pos mapped, if_pos disabled, Mettapedia.CategoryTheory.FinitePowerset.map_singleton,
            rename_stopped]
        · have mapped := fun held => disabled (emptiness.mp held)
          change (if ∀ action, behaviourMap signature actions mapping PUnit.unit ()
            (children false).2 action = ∅ then {stopped (X := Y)} else ∅) =
              Mettapedia.CategoryTheory.FinitePowerset.map (signature.rename mapping)
                (if ∀ action, (children false).2 action = ∅ then {stopped (X := X)} else ∅)
          rw [if_neg mapped, if_neg disabled, Mettapedia.CategoryTheory.FinitePowerset.map_empty]

def disabled : Offered naturals := fun position =>
  (if position then 20 else 10, fun _ => ∅)

def enabled (fresh : Nat) : Offered naturals := fun position =>
  (if position then 20 else 10, fun action => if position = false ∧ action = fresh then {99} else ∅)

theorem disabled_readout :
    law.app naturals PUnit.unit () ⟨Operator.choose, disabled⟩ 0 = {stopped} := by
  change (if ∀ action : Nat, (∅ : Finset Nat) = ∅ then {stopped} else ∅) = _
  rw [if_pos (fun _ => rfl)]

theorem enabled_readout (fresh : Nat) :
    law.app naturals PUnit.unit () ⟨Operator.choose, enabled fresh⟩ 0 = ∅ := by
  change (if ∀ action, (enabled fresh false).2 action = ∅ then {stopped} else ∅) = ∅
  apply if_neg
  intro none
  have impossible := none fresh
  simp only [enabled, and_self, if_true] at impossible
  exact Finset.singleton_ne_empty _ impossible

theorem not_uniform : ¬ UniformFiniteObservation law := by
  intro uniform
  obtain ⟨observed, determines⟩ := uniform () Operator.choose 0
  let fresh := observed.sup (fun address => address.2) + 1
  have outside : ∀ address ∈ observed, address.2 ≠ fresh := by
    intro address member same
    have bound : address.2 ≤ observed.sup (fun address => address.2) := Finset.le_sup member
    dsimp only [fresh] at same
    exact (Nat.ne_of_lt (Nat.lt_succ_of_le bound)) same
  have same := determines naturals disabled (enabled fresh) (fun _ => rfl)
    (fun address member => by
      have differs := outside address member
      simp [disabled, enabled, differs])
  rw [disabled_readout, enabled_readout] at same
  exact Finset.singleton_ne_empty _ same

/-- Finiteness per output action cannot hide an infinite negative guard. -/
theorem no_finite_presentation :
    ¬ ∃ presentation : Presentation signature actions, Presentation.Denotes presentation law := by
  rintro ⟨presentation, denotes⟩
  exact not_uniform (presentation.uniform_of_denotes law denotes)

end Mettapedia.OSLF.FiniteBranching.Premises.InfiniteBoundary
