import Mettapedia.GSLT.Causality.ResourceLinearHorn
import Mettapedia.Logic.LinearLogic.TensorHornEquivalence

/-!
# Exact resource schedules and tensor-sequent proofs

The no-read consume/produce resource system has exactly the proofs of the
positive tensor sequent calculus with its transition instances as declared
rules. Arbitrary tensor/unit cut formulas preserve the same atomic boundary
and transition-use list. A planning query which asks for only part of the
final bag corresponds to a proof with an explicit residual tensor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.System

open Mettapedia.Logic.LinearLogic

universe uAtom uRule
variable {Atom : Type uAtom} [DecidableEq Atom] (system : System.{uAtom, uRule} Atom)

abbrev TensorProof (context : Multiset (TensorSequent.Formula Atom)) (goal : TensorSequent.Formula Atom) :=
  TensorSequent.Derives (fun entry : system.Entry => system.consume entry.2)
    (fun entry : system.Entry => system.produce entry.2) context goal

theorem tensor_sequent_iff_fires (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (context : Multiset (TensorSequent.Formula Atom)) (goal : TensorSequent.Formula Atom)
    (trace : List system.Entry) :
    (∃ proof : system.TensorProof context goal, proof.uses = trace) ↔
      system.Fires trace (TensorSequent.contextAtoms context) goal.atoms := by
  rw [TensorSequent.derives_iff_horn]
  exact (system.linear_fires_iff_horn_proof noReads trace _ _).symm

theorem fires_iff_tensor_sequent (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (trace : List system.Entry) (before after : Multiset Atom) :
    system.Fires trace before after ↔
      ∃ proof : system.TensorProof (TensorSequent.atomContext before) (TensorSequent.Formula.ofMultiset after),
        proof.uses = trace := by
  simpa only [TensorSequent.contextAtoms_atomContext, TensorSequent.Formula.atoms_ofMultiset] using
    (system.tensor_sequent_iff_fires noReads (TensorSequent.atomContext before)
      (TensorSequent.Formula.ofMultiset after) trace).symm

/-- The planning terminal condition accepts a subbag of the final state.
The corresponding linear proof keeps every leftover occurrence explicitly;
it does not prove the smaller exact sequent by weakening. -/
theorem partial_goal_iff_residual_tensor (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (trace : List system.Entry) (before goal : Multiset Atom) :
    (∃ after, system.Fires trace before after ∧ goal ≤ after) ↔
      ∃ residual, ∃ proof : system.TensorProof (TensorSequent.atomContext before)
          (TensorSequent.Formula.ofMultiset (goal + residual)), proof.uses = trace := by
  constructor
  · rintro ⟨after, runs, containsGoal⟩
    have boundary : after = goal + (after - goal) := by
      rw [add_comm, Multiset.sub_add_cancel containsGoal]
    refine ⟨after - goal, ?_⟩
    apply (system.fires_iff_tensor_sequent noReads trace before _).mp
    exact boundary ▸ runs
  · rintro ⟨residual, proof, uses⟩
    exact ⟨goal + residual, (system.fires_iff_tensor_sequent noReads trace before _).mpr ⟨proof, uses⟩,
      Multiset.le_add_right _ _⟩

end Mettapedia.GSLT.Causality.ResourceInteraction.System
