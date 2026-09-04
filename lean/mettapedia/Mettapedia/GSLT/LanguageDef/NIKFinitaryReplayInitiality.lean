import Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority
import Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
import Mettapedia.Logic.FinitaryRuleSystem

/-!
# Initial finite-tree factorization of an external replay service

The profile-blind external-certificate replay service factors through the
unique fold from the initial algebra of finite derivation trees into the
algebra computing root conclusion and replay validity.  Comparing the folded
conclusion with the requested claim is a separate final observation.  This is
one NIK boundary service; it is not the canonical description of native NIK
decision, proof, construction, transformation, or search.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKFinitaryReplayInitiality

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
open Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority
open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem
open Mettapedia.OSLF.Framework.InitialModalSchema

universe u v

/-- The paired result of the canonical finite-tree replay fold. -/
def foldedReplay
    {Judgment : Type u} {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (certificate : Derivation Judgment interface.W) : Judgment × Bool :=
  (NodeAlgebra.fold (NodeAlgebra.replayAlgebra interface) certificate).down

theorem foldedReplay_eq
    {Judgment : Type u} {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (certificate : Derivation Judgment interface.W) :
    foldedReplay interface certificate =
      (certificate.concl, certificate.valid interface) :=
  NodeAlgebra.fold_replay interface certificate

/-- This replay service is the unique finite-tree fold computing validity and root
conclusion, followed by equality with the requested claim. -/
theorem replayChecker_check_eq_initialFold
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (claim : Judgment) (certificate : Derivation Judgment interface.W) :
    (replayChecker interface).check claim certificate =
      ((foldedReplay interface certificate).2 &&
        decide ((foldedReplay interface certificate).1 = claim)) := by
  rw [foldedReplay_eq]
  rfl

/-- Any node-preserving implementation of the paired replay computation is
equal to the canonical fold. -/
theorem replayNodeHom_unique
    {Judgment : Type u} {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    (candidate :
      NodeAlgebra.derivationAlgebra ⟶
        NodeAlgebra.replayAlgebra interface) :
    candidate = NodeAlgebra.foldHom (NodeAlgebra.replayAlgebra interface) :=
  NodeAlgebra.hom_eq_fold _ candidate

/-- The generic factorization specializes definitionally to every qualified
rule system used as a NIK authority. -/
theorem qualifiedChecker_check_eq_initialFold
    {Judgment : Type u} [DecidableEq Judgment]
    (ruleSystem : QualifiedRuleSystem.{u, v} Judgment)
    (claim : Judgment)
    (certificate : Derivation Judgment ruleSystem.witness.W) :
    (ruleSystem.checker).check claim certificate =
      ((foldedReplay ruleSystem.witness certificate).2 &&
        decide ((foldedReplay ruleSystem.witness certificate).1 = claim)) :=
  replayChecker_check_eq_initialFold ruleSystem.witness claim certificate

/-! ## Exact physical implementations -/

/-- An exact implementation of encoded external replay inherits authority for
least rule closure on every decodable claim wire.  Malformed inputs are
covered by the refinement contract rather than excluded from the theorem. -/
theorem exactWireRefinement_authority
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    {ClaimWire CertificateWire : Type*}
    (claimCodec : Checker.PartialCodec Judgment ClaimWire)
    (certificateCodec :
      Checker.PartialCodec (Derivation Judgment interface.W) CertificateWire)
    (target : Checker ClaimWire CertificateWire)
    (refinement : ExactWireRefinement
      (replayChecker interface) claimCodec certificateCodec target) :
    target.Authority (DecodedMeaning claimCodec (Derives rules)) :=
  refinement.authority (replayChecker_authority interface)

/-- An independently supplied interpretation of the rules remains sound for
an exact encoded implementation.  No semantic predicate enters the target
checker. -/
theorem exactWireRefinement_sound_in_model
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    {ClaimWire CertificateWire : Type*}
    (claimCodec : Checker.PartialCodec Judgment ClaimWire)
    (certificateCodec :
      Checker.PartialCodec (Derivation Judgment interface.W) CertificateWire)
    (target : Checker ClaimWire CertificateWire)
    (refinement : ExactWireRefinement
      (replayChecker interface) claimCodec certificateCodec target)
    (meaning : Judgment → Prop)
    (rulesSound : ∀ premises conclusion, rules premises conclusion →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion) :
    target.Sound (DecodedMeaning claimCodec meaning) :=
  refinement.sound
    (replay_sound_in_every_model interface meaning rulesSound)

/-- If an independent sound interpretation rejects a judgment, every physical
certificate wire is rejected for that judgment's canonical encoding. -/
theorem exactWireRefinement_rejects_outside_model
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    {ClaimWire CertificateWire : Type*}
    (claimCodec : Checker.PartialCodec Judgment ClaimWire)
    (certificateCodec :
      Checker.PartialCodec (Derivation Judgment interface.W) CertificateWire)
    (target : Checker ClaimWire CertificateWire)
    (refinement : ExactWireRefinement
      (replayChecker interface) claimCodec certificateCodec target)
    (meaning : Judgment → Prop)
    (rulesSound : ∀ premises conclusion, rules premises conclusion →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    {claim : Judgment} (outsideMeaning : ¬ meaning claim)
    (wireCertificate : CertificateWire) :
    target.check (claimCodec.encode claim) wireCertificate = false :=
  refinement.rejects_encoded_claim_outside_meaning
    (replay_sound_in_every_model interface meaning rulesSound)
    outsideMeaning wireCertificate

/-- On canonical encodings, exact physical replay is the initial finite-tree
fold followed by comparison of the folded root with the requested claim. -/
theorem exactWireRefinement_check_eq_initialFold
    {Judgment : Type u} [DecidableEq Judgment]
    {rules : List Judgment → Judgment → Prop}
    (interface : RuleWitness.{u, v} rules)
    {ClaimWire CertificateWire : Type*}
    (claimCodec : Checker.PartialCodec Judgment ClaimWire)
    (certificateCodec :
      Checker.PartialCodec (Derivation Judgment interface.W) CertificateWire)
    (target : Checker ClaimWire CertificateWire)
    (refinement : ExactWireRefinement
      (replayChecker interface) claimCodec certificateCodec target)
    (claim : Judgment) (certificate : Derivation Judgment interface.W) :
    target.check (claimCodec.encode claim)
        (certificateCodec.encode certificate) =
      ((foldedReplay interface certificate).2 &&
        decide ((foldedReplay interface certificate).1 = claim)) := by
  rw [refinement.canonical_check_commutes]
  exact replayChecker_check_eq_initialFold interface claim certificate

namespace Canary

/-- One nullary rule deriving the sole judgment. -/
inductive Rules : List Unit → Unit → Prop where
  | unit : Rules [] ()

/-- The Boolean witness is deliberately proof-relevant: only `true` names the
real rule instance. -/
def isInstance (witness : Bool) (premises : List Unit)
    (conclusion : Unit) : Bool :=
  witness && decide (premises = [] ∧ conclusion = ())

def interface : RuleWitness Rules where
  W := Bool
  isInstance := isInstance
  sound witness premises conclusion accepted := by
    simp only [isInstance, Bool.and_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with ⟨_witnessTrue, premisesEmpty, _conclusionUnit⟩
    subst premises
    cases conclusion
    exact Rules.unit
  complete premises conclusion rule := by
    cases rule
    exact ⟨true, by decide⟩

def acceptedCertificate : Derivation Unit Bool :=
  .node () true 0 (fun i => Fin.elim0 i)

def rejectedCertificate : Derivation Unit Bool :=
  .node () false 0 (fun i => Fin.elim0 i)

theorem certificates_same_conclusion :
    acceptedCertificate.concl = rejectedCertificate.concl := rfl

theorem acceptedCertificate_valid :
    acceptedCertificate.valid interface = true := rfl

theorem rejectedCertificate_invalid :
    rejectedCertificate.valid interface = false := rfl

theorem replay_accepts_valid_certificate :
    (replayChecker interface).check () acceptedCertificate = true := rfl

theorem replay_rejects_invalid_same_conclusion :
    (replayChecker interface).check () rejectedCertificate = false := rfl

/-- A conclusion-only observer cannot distinguish the accepted and rejected
certificates, so it cannot replace the replay fold. -/
theorem conclusionOnly_cannot_characterize_replay :
    decide (acceptedCertificate.concl = ()) =
        decide (rejectedCertificate.concl = ()) ∧
      (replayChecker interface).check () acceptedCertificate ≠
        (replayChecker interface).check () rejectedCertificate := by
  decide

end Canary

/-! ## Axiom audit -/

#print axioms exactWireRefinement_authority
#print axioms exactWireRefinement_sound_in_model
#print axioms exactWireRefinement_rejects_outside_model
#print axioms exactWireRefinement_check_eq_initialFold

end Mettapedia.GSLT.LanguageDef.NIKFinitaryReplayInitiality
