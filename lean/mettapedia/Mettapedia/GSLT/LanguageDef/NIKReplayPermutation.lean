import Mettapedia.GSLT.LanguageDef.NIKFinitaryReplayInitiality
import Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutation
import Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutationCanary

/-!
# Premise-permutation invariance at an external replay boundary

The generic external-certificate replay checker, its initial finite-tree fold,
and every exact wire refinement give identical results on structurally
permutation-equivalent certificates whenever the selected rule interface
explicitly validates premise exchange.  This theorem concerns that boundary
service only, not native NIK services in general.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKReplayPermutation

open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKFinitaryReplayInitiality
open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem
open Mettapedia.Logic.FinitaryRuleSystem.Derivation.PremisePermutationPlan
open Mettapedia.OSLF.Framework.InitialModalSchema

universe u v

/-- Abstract external replay is constant on the qualified premise-permutation
equivalence classes. -/
theorem replayChecker_check_eq_of_permutationEquivalent
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (invariant : PremisePermutationInvariant interface)
    (claim : Judgment)
    {left right : Derivation Judgment interface.W}
    (equivalent : PermutationEquivalent left right) :
    (replayChecker interface).check claim left =
      (replayChecker interface).check claim right := by
  simp only [replayChecker]
  rw [equivalent.valid_eq interface invariant, equivalent.concl_eq]

/-- The canonical initial replay fold itself factors through the qualified
premise-permutation quotient. -/
theorem foldedReplay_eq_of_permutationEquivalent
    {Judgment : Type u}
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (invariant : PremisePermutationInvariant interface)
    {left right : Derivation Judgment interface.W}
    (equivalent : PermutationEquivalent left right) :
    foldedReplay interface left = foldedReplay interface right := by
  rw [foldedReplay_eq, foldedReplay_eq, equivalent.concl_eq,
    equivalent.valid_eq interface invariant]

/-- Every exact physical wire refinement returns the same result on canonical
encodings of qualified permutation-equivalent certificates. -/
theorem exactWireRefinement_check_eq_of_permutationEquivalent
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (invariant : PremisePermutationInvariant interface)
    {ClaimWire CertificateWire : Type*}
    (claimCodec : Checker.PartialCodec Judgment ClaimWire)
    (certificateCodec :
      Checker.PartialCodec (Derivation Judgment interface.W) CertificateWire)
    (target : Checker ClaimWire CertificateWire)
    (refinement : ExactWireRefinement
      (replayChecker interface) claimCodec certificateCodec target)
    (claim : Judgment)
    {left right : Derivation Judgment interface.W}
    (equivalent : PermutationEquivalent left right) :
    target.check (claimCodec.encode claim) (certificateCodec.encode left) =
      target.check (claimCodec.encode claim)
        (certificateCodec.encode right) := by
  rw [refinement.canonical_check_commutes,
    refinement.canonical_check_commutes]
  exact replayChecker_check_eq_of_permutationEquivalent interface invariant
    claim equivalent

namespace Canary

open Mettapedia.Logic.FinitaryRuleSystem.ReplayPermutationCanary

theorem replay_accepts_pair :
    (replayChecker symmetricInterface).check 2 pairCertificate = true := by
  rfl

theorem replay_accepts_permuted_pair :
    (replayChecker symmetricInterface).check 2 (reorder swapPlan) = true := by
  calc
    (replayChecker symmetricInterface).check 2 (reorder swapPlan) =
        (replayChecker symmetricInterface).check 2 pairCertificate :=
      (replayChecker_check_eq_of_permutationEquivalent symmetricInterface
        symmetricInterface_invariant 2 pair_permutationEquivalent).symm
    _ = true := replay_accepts_pair

theorem replay_rejects_multiplicity_contraction :
    (replayChecker symmetricInterface).check 2 oneChildCertificate = false := by
  rfl

theorem ordered_replay_rejects_swapped_pair :
    (replayChecker orderedInterface).check 2 swappedPairCertificate = false := by
  rfl

end Canary

end Mettapedia.GSLT.LanguageDef.NIKReplayPermutation
