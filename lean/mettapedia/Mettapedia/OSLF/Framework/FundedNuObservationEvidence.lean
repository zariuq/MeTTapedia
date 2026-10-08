import Mettapedia.OSLF.Framework.FundedNuBudgetDiagram
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Dependent evidence over actual funded observations

The independently proved finite classes identify the complete actual profile
image. Families on those classes therefore give genuine families on observed
execution answers and spending. Their full supplied witnesses are retained.

A varying family on the unobserved state need not descend, even up to fibre
equivalence: the persistent loop and a long finite chain have identical
funded profiles but can support fibres of different cardinalities.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.FundedNuObservationEvidence

open FundedNuObservationClasses FundedNuBudgetSeparation
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

def actualView (budget : Nat) (state : Option Nat) : ActualProfile budget :=
  ⟨view budget state, state, rfl⟩

theorem actualView_eq_realize (budget : Nat) (state : Option Nat) :
    actualView budget state = realize budget (classify budget state) :=
  Subtype.ext (representative_profiles budget state).symm

theorem observed_class_readout (budget : Nat) (state : Option Nat) :
    (imageEquivalence budget).symm (actualView budget state) = classify budget state := by
  rw [actualView_eq_realize]
  exact (imageEquivalence budget).symm_apply_apply (classify budget state)

universe u

/-- The target family reads only the complete actual profile. The domain
family depends on the earned observable class, with no hidden-state read. -/
def familyFactorization (budget : Nat) (family : Class budget → Type u) :
    FamilyFactorization (actualView budget) (fun state => family (classify budget state)) where
  targetFamily observed := family ((imageEquivalence budget).symm observed)
  identify state := Equiv.cast (congrArg family (observed_class_readout budget state).symm)

theorem supplied_witness_recovered (budget : Nat) (family : Class budget → Type u)
    (state : Option Nat) (witness : family (classify budget state)) :
    ((familyFactorization budget family).identify state).symm
      ((familyFactorization budget family).identify state witness) = witness :=
  ((familyFactorization budget family).identify state).symm_apply_apply witness

def visibleCertificate (budget : Nat) : Class budget → Type
  | none => Unit
  | some length => Fin (length.val + 1)

def visibleWitness (budget : Nat) (code : Class budget) : visibleCertificate budget code :=
  match code with
  | none => ()
  | some length => ⟨length.val, Nat.lt_succ_self length.val⟩

theorem visible_witness_value (budget : Nat) (length : Fin budget) :
    (visibleWitness budget (some length)).val = length.val := rfl

/-- This family deliberately depends on a hidden finite-chain length. -/
def hiddenCertificate : Option Nat → Type
  | none => PUnit
  | some length => Fin (length + 2)

theorem loop_finite_fibres_not_equivalent (length : Nat) :
    ¬ Nonempty (hiddenCertificate none ≃ hiddenCertificate (some length)) := by
  change ¬ Nonempty (PUnit ≃ Fin (length + 2))
  rintro ⟨equivalence⟩
  let zero : Fin (length + 2) := ⟨0, by omega⟩
  let one : Fin (length + 2) := ⟨1, by omega⟩
  have identical : equivalence.symm zero = equivalence.symm one := Subsingleton.elim _ _
  have collision := congrArg Fin.val (equivalence.symm.injective identical)
  change (0 : Nat) = 1 at collision
  omega

theorem hidden_certificate_does_not_descend (budget : Nat) :
    ¬ Nonempty (FamilyFactorization (actualView budget) hiddenCertificate) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres (left := none) (right := some budget)
  · exact Subtype.ext (bounded_views_agree budget budget le_rfl).symm
  · exact loop_finite_fibres_not_equivalent budget

end Mettapedia.OSLF.Framework.FundedNuObservationEvidence
