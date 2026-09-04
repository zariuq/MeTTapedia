import Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutation

/-!
# Positive and negative controls for premise-permutation replay

The positive interface reads premises only through permutation-invariant
summaries.  Swapping two distinct accepted children therefore preserves exact
replay.  Two negative controls show that premise multiplicity cannot be
contracted and that an ordered rule interface does not acquire exchange for
free.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutationCanary

open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem
open Mettapedia.Logic.FinitaryRuleSystem.Derivation
open Mettapedia.Logic.FinitaryRuleSystem.Derivation.PremisePermutationPlan

/-! ## A genuinely permutation-invariant interface -/

inductive Witness where
  | leafZero
  | leafOne
  | combine
deriving DecidableEq

def expectedArity : Witness → Nat
  | .leafZero | .leafOne => 0
  | .combine => 2

def expectedConclusion : Witness → Nat
  | .leafZero => 0
  | .leafOne => 1
  | .combine => 2

def premiseAllowed : Witness → Nat → Bool
  | .leafZero, _ | .leafOne, _ => true
  | .combine, premise => decide (premise < 2)

def symmetricIsInstance (witness : Witness) (premises : List Nat)
    (conclusion : Nat) : Bool :=
  decide (premises.length = expectedArity witness ∧
    conclusion = expectedConclusion witness) &&
      premises.all (premiseAllowed witness)

def SymmetricRules (premises : List Nat) (conclusion : Nat) : Prop :=
  ∃ witness, symmetricIsInstance witness premises conclusion = true

def symmetricInterface : RuleWitness SymmetricRules where
  W := Witness
  isInstance := symmetricIsInstance
  sound witness _premises _conclusion accepted := ⟨witness, accepted⟩
  complete _premises _conclusion rule := rule

theorem symmetricInterface_invariant :
    PremisePermutationInvariant symmetricInterface := by
  intro witness conclusion arity premises permutation
  have permutes :
      (List.ofFn (premises ∘ permutation)).Perm (List.ofFn premises) :=
    Equiv.Perm.ofFn_comp_perm permutation premises
  simp only [symmetricInterface, symmetricIsInstance]
  rw [permutes.length_eq,
    boolAll_eq_of_perm permutes (premiseAllowed witness)]

def leafZeroCertificate : Derivation Nat Witness :=
  .node 0 .leafZero 0 (fun i => Fin.elim0 i)

def leafOneCertificate : Derivation Nat Witness :=
  .node 1 .leafOne 0 (fun i => Fin.elim0 i)

def pairChildren : Fin 2 → Derivation Nat Witness :=
  Fin.cases leafZeroCertificate (fun _ => leafOneCertificate)

def pairCertificate : Derivation Nat Witness :=
  .node 2 .combine 2 pairChildren

def swapTwo : Equiv.Perm (Fin 2) :=
  Equiv.swap (0 : Fin 2) (1 : Fin 2)

def swapPlan : PremisePermutationPlan pairCertificate :=
  .node swapTwo (fun i => identity (pairChildren (swapTwo i)))

theorem pairCertificate_valid :
    pairCertificate.valid symmetricInterface = true := by
  rfl

theorem reordered_pair_valid :
    (reorder swapPlan).valid symmetricInterface = true := by
  exact (reorder_valid symmetricInterface symmetricInterface_invariant
    swapPlan).trans pairCertificate_valid

theorem pair_permutationEquivalent :
    PermutationEquivalent pairCertificate (reorder swapPlan) :=
  Relation.EqvGen.rel _ _ ⟨swapPlan, rfl⟩

/-- Read the first child conclusion when a root has at least one child. -/
def firstChildConclusion : Derivation Nat Witness → Option Nat
  | .node _ _ 0 _ => none
  | .node _ _ (_ + 1) children => some (children 0).concl

/-- The positive control is non-vacuous: the first child changes from the
zero leaf to the one leaf. -/
theorem reorder_changes_first_child_conclusion :
    firstChildConclusion (reorder swapPlan) = some 1 := by
  rfl

/-! ## Multiplicity is not permutation bureaucracy -/

def oneChildCertificate : Derivation Nat Witness :=
  .node 2 .combine 1 (fun _ => leafZeroCertificate)

theorem oneChildCertificate_invalid :
    oneChildCertificate.valid symmetricInterface = false := by
  rfl

theorem multiplicity_contraction_not_permutationEquivalent :
    ¬ PermutationEquivalent pairCertificate oneChildCertificate := by
  intro equivalent
  have sameValidity := equivalent.valid_eq symmetricInterface
    symmetricInterface_invariant
  rw [pairCertificate_valid, oneChildCertificate_invalid] at sameValidity
  cases sameValidity

/-! ## An order-sensitive rule does not receive exchange -/

def orderedIsInstance (witness : Witness) (premises : List Nat)
    (conclusion : Nat) : Bool :=
  match witness with
  | .leafZero => decide (premises = [] ∧ conclusion = 0)
  | .leafOne => decide (premises = [] ∧ conclusion = 1)
  | .combine => decide (premises = [0, 1] ∧ conclusion = 2)

def OrderedRules (premises : List Nat) (conclusion : Nat) : Prop :=
  ∃ witness, orderedIsInstance witness premises conclusion = true

def orderedInterface : RuleWitness OrderedRules where
  W := Witness
  isInstance := orderedIsInstance
  sound witness _premises _conclusion accepted := ⟨witness, accepted⟩
  complete _premises _conclusion rule := rule

def swappedPairCertificate : Derivation Nat Witness :=
  .node 2 .combine 2 (pairChildren ∘ swapTwo)

theorem ordered_pair_valid :
    pairCertificate.valid orderedInterface = true := by
  rfl

theorem ordered_swapped_pair_invalid :
    swappedPairCertificate.valid orderedInterface = false := by
  rfl

theorem ordered_reordered_pair_invalid :
    (reorder swapPlan).valid orderedInterface = false := by
  rfl

theorem orderedInterface_not_invariant :
    ¬ PremisePermutationInvariant orderedInterface := by
  intro invariant
  have sameValidity := reorder_valid orderedInterface invariant swapPlan
  have impossible : false = true :=
    ordered_reordered_pair_invalid.symm.trans
      (sameValidity.trans ordered_pair_valid)
  cases impossible

end Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutationCanary
