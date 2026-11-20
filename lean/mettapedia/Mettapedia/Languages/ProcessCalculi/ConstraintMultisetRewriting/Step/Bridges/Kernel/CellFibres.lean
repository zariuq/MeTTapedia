import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellProposals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellCorrespondence

/-!
# Infinite raw firings with one operational result

The actual checked-cell step accepts infinitely many total proposal functions
that differ only on unused keys. They all have the same canonical proposal
and the same complete resulting state. Finite successor-state semantics does
not therefore establish a bijection of raw firing fibres with runtime words.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellFibres

open Mettapedia.Machines.TIsa Cells CellEffects Control
open CellOccurrences CellProposals
open CheckedCells.Controls (edge keys initial proposal)

def state : State Nat := CellCorrespondence.Controls.state

def family (index : Nat) : Firing [edge] where
  ordinal := ⟨0, by decide⟩
  candidate key := if key = 0 then 14 else if key = index + 2 then 42 else 7

theorem family_outputs (index : Nat) : outputWords edge (family index).candidate = outputWords edge proposal := rfl

theorem family_admitted (index : Nat) : (step [edge]).Admits (s := state) (family index) := by
  exact (eligible_iff_outputs edge keys initial (family_outputs index)).mpr CellCorrespondence.Controls.admitted

theorem family_injective : Function.Injective family := by
  intro first second same
  by_contra different
  have nonzero : first + 2 ≠ 0 := by omega
  have values := congrArg (fun firing : Firing [edge] => firing.candidate (first + 2)) same
  have sameIndex : first = second := by simpa [family, nonzero] using values
  exact different sameIndex

theorem raw_admitted_firings_infinite :
    Infinite {firing : Firing [edge] // (step [edge]).Admits (s := state) firing} := by
  apply Infinite.of_injective (fun index : Nat => (⟨family index, family_admitted index⟩ :
    {firing : Firing [edge] // (step [edge]).Admits (s := state) firing}))
  intro first second same
  exact family_injective (congrArg Subtype.val same)

theorem canonical_family_equal (first second : Nat) : normalize (family first) = normalize (family second) := by
  apply congrArg (Firing.mk (⟨0, by decide⟩ : Fin [edge].length))
  exact (canonical_eq_iff edge _ _).mpr ((family_outputs first).trans (family_outputs second).symm)

theorem family_result_equal (first second : Nat) : result state (family first) = result state (family second) :=
  (result_normalize [edge] state (family first)).symm.trans
    ((congrArg (result state) (canonical_family_equal first second)).trans
      (result_normalize [edge] state (family second)))

#print axioms raw_admitted_firings_infinite
#print axioms canonical_family_equal
#print axioms family_result_equal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellFibres
