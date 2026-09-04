import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

/-!
# Exact semantic reductions and the decidability frontier

Decidability belongs to a meaning predicate on a specified claim language.
It is not implied or refuted merely by naming an ambient mathematical
structure.  The load-bearing obstruction is an effective exact reduction from
an undecidable meaning predicate.

This module formalizes that boundary and gives a concrete NIK-shaped example.
A decidable Boolean fragment is extended disjointly by fixed-input halting
claims.  The Boolean fragment retains direct decision.  The full extension has
no computable direct decision kernel, because halting embeds effectively and
truth-reflectingly.  Nevertheless, the extension has exact finite-certificate
authority: Boolean claims use a thin receipt, while halting claims use a step
budget checked by bounded evaluation.

Consequently, adding expressive claims need not invalidate a decidable ground
fragment, but it may force the larger authority from direct decision to
proof-relevant replay.  No claim about natural-number objects, categorical
exponentials, or a particular real-field expansion follows without a separate
exact encoding theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKSemanticGroundDecidabilityFrontier

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uSource uTarget

/-! ## Exact reductions of semantic decision problems -/

/-- An effective claim translation which preserves and reflects meaning. -/
structure ComputableExactMeaningReduction
    (SourceClaim : Type uSource) (TargetClaim : Type uTarget)
    [Primcodable SourceClaim] [Primcodable TargetClaim]
    (SourceMeaning : SourceClaim -> Prop)
    (TargetMeaning : TargetClaim -> Prop) where
  encode : SourceClaim -> TargetClaim
  encode_computable : Computable encode
  meaning_iff : forall claim,
    TargetMeaning (encode claim) <-> SourceMeaning claim

/-- A direct decision procedure pulls back along an exact semantic
reduction. -/
def pullbackDecisionKernel
    {SourceClaim : Type uSource} {TargetClaim : Type uTarget}
    [Primcodable SourceClaim] [Primcodable TargetClaim]
    {SourceMeaning : SourceClaim -> Prop}
    {TargetMeaning : TargetClaim -> Prop}
    (reduction : ComputableExactMeaningReduction SourceClaim TargetClaim
      SourceMeaning TargetMeaning)
    (targetKernel : Checker.DecisionKernel TargetClaim TargetMeaning) :
    Checker.DecisionKernel SourceClaim SourceMeaning where
  decide := fun claim => targetKernel.decide (reduction.encode claim)
  correct := by
    intro claim
    exact (targetKernel.correct (reduction.encode claim)).trans
      (reduction.meaning_iff claim)

/-- Pullback also preserves computability of the decision function. -/
theorem pullbackDecisionKernel_computable
    {SourceClaim : Type uSource} {TargetClaim : Type uTarget}
    [Primcodable SourceClaim] [Primcodable TargetClaim]
    {SourceMeaning : SourceClaim -> Prop}
    {TargetMeaning : TargetClaim -> Prop}
    (reduction : ComputableExactMeaningReduction SourceClaim TargetClaim
      SourceMeaning TargetMeaning)
    (targetKernel : Checker.DecisionKernel TargetClaim TargetMeaning)
    (targetComputable : Computable targetKernel.decide) :
    Computable (pullbackDecisionKernel reduction targetKernel).decide :=
  targetComputable.comp reduction.encode_computable

/-- Any meaning which effectively and exactly contains fixed-input halting has
no computable direct decision kernel. -/
theorem no_computableDecisionKernel_of_halting_reduction
    {TargetClaim : Type uTarget} [Primcodable TargetClaim]
    {TargetMeaning : TargetClaim -> Prop}
    (reduction : ComputableExactMeaningReduction Nat.Partrec.Code TargetClaim
      Checker.HaltingMeaning TargetMeaning) :
    Not (exists targetKernel : Checker.DecisionKernel TargetClaim TargetMeaning,
      Computable targetKernel.decide) := by
  rintro ⟨targetKernel, targetComputable⟩
  apply Checker.no_computableDecisionKernel_for_halting
  exact ⟨pullbackDecisionKernel reduction targetKernel,
    pullbackDecisionKernel_computable reduction targetKernel
      targetComputable⟩

/-! ## A disjoint decidable/halting extension -/

/-- A minimal decidable ground meaning with both a positive and a negative
claim. -/
def BooleanMeaning (claim : Bool) : Prop := claim = true

def booleanDecisionKernel : Checker.DecisionKernel Bool BooleanMeaning where
  decide := id
  correct := by
    intro claim
    rfl

theorem booleanDecisionKernel_computable :
    Computable booleanDecisionKernel.decide := by
  simpa [booleanDecisionKernel] using
    (Computable.id : Computable (fun claim : Bool => claim))

/-- The extension retains the decidable fragment on the left and adds halting
claims on the right. -/
abbrev ExpandedClaim := Sum Bool Nat.Partrec.Code

def ExpandedMeaning : ExpandedClaim -> Prop :=
  Sum.elim BooleanMeaning Checker.HaltingMeaning

/-- Halting is an effective exact semantic subproblem of the extension. -/
def haltingReduction :
    ComputableExactMeaningReduction Nat.Partrec.Code ExpandedClaim
      Checker.HaltingMeaning ExpandedMeaning where
  encode := fun code => (Sum.inr code : ExpandedClaim)
  encode_computable := Computable.sumInr
  meaning_iff := fun _code => Iff.rfl

theorem expandedMeaning_has_no_computableDecisionKernel :
    Not (exists kernel : Checker.DecisionKernel ExpandedClaim ExpandedMeaning,
      Computable kernel.decide) :=
  no_computableDecisionKernel_of_halting_reduction haltingReduction

/-- Certificates retain which authority lane supplied the evidence. -/
abbrev ExpandedCertificate := Sum Unit Nat

/-- Exact replay for the extension.  Crossed lane tags fail closed. -/
def expandedChecker : Checker ExpandedClaim ExpandedCertificate :=
  Checker.sum booleanDecisionKernel.toChecker
    Checker.haltingTrustBoundaryChecker

/-- The disjoint extension is an executable checker, not merely a
set-theoretic authority relation. -/
theorem expandedChecker_computable :
    Computable (fun input : ExpandedClaim × ExpandedCertificate =>
      expandedChecker.check input.1 input.2) := by
  simpa [expandedChecker] using
    (Checker.sum_computable
      booleanDecisionKernel.toChecker
      Checker.haltingTrustBoundaryChecker
      (booleanDecisionKernel.toChecker_computable
        booleanDecisionKernel_computable)
      Checker.haltingTrustBoundaryChecker_computable)

theorem expandedChecker_sound :
    expandedChecker.Sound ExpandedMeaning := by
  simpa [expandedChecker, ExpandedMeaning] using
    (Checker.sum_sound
      booleanDecisionKernel.authority.sound
      Checker.haltingTrustBoundaryChecker_sound)

theorem expandedChecker_complete :
    expandedChecker.CertificateComplete ExpandedMeaning := by
  simpa [expandedChecker, ExpandedMeaning] using
    (Checker.sum_complete
      booleanDecisionKernel.authority.complete
      Checker.haltingTrustBoundaryChecker_complete)

def expandedAuthority : expandedChecker.Authority ExpandedMeaning where
  sound := expandedChecker_sound
  complete := expandedChecker_complete

/-! ## Exact NIK authority routes -/

def booleanTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Bool
  Scope := fun _kind => BooleanMeaning
  Meaning := fun _kind => BooleanMeaning
  scope_sound := by
    intro _kind _claim meaningful
    exact meaningful

def booleanContract : AuthorityContract booleanTheory where
  Certificate := fun _kind => Unit
  checker := fun _kind => booleanDecisionKernel.toChecker
  scopeAuthority := fun _kind => booleanDecisionKernel.authority

def haltingTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => Nat.Partrec.Code
  Scope := fun _kind => Checker.HaltingMeaning
  Meaning := fun _kind => Checker.HaltingMeaning
  scope_sound := by
    intro _kind _claim meaningful
    exact meaningful

def haltingContract : AuthorityContract haltingTheory where
  Certificate := fun _kind => Nat
  checker := fun _kind => Checker.haltingTrustBoundaryChecker
  scopeAuthority := fun _kind => Checker.haltingTrustBoundaryAuthority

def expandedTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _kind => ()
  Claim := fun _kind => ExpandedClaim
  Scope := fun _kind => ExpandedMeaning
  Meaning := fun _kind => ExpandedMeaning
  scope_sound := by
    intro _kind _claim meaningful
    exact meaningful

def expandedContract : AuthorityContract expandedTheory where
  Certificate := fun _kind => ExpandedCertificate
  checker := fun _kind => expandedChecker
  scopeAuthority := fun _kind => expandedAuthority

/-- The decidable fragment enters the larger authority without losing or
gaining meaning or accepted evidence on its image. -/
def booleanInclusion : AuthorityTranslation booleanContract expandedContract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind claim => .inl claim
  mapCertificate := fun _kind _certificate => .inl ()
  check_commutes := by
    intro kind claim certificate
    cases kind
    cases certificate
    rfl
  meaning_preserved := by
    intro _kind _claim meaningful
    exact meaningful

theorem booleanInclusion_conservative :
    booleanInclusion.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro _kind _claim meaningful
    exact meaningful
  meaning_reflecting := by
    intro _kind _claim meaningful
    exact meaningful

/-- The proof-relevant halting lane also enters by exact replay. -/
def haltingInclusion : AuthorityTranslation haltingContract expandedContract where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind code => .inr code
  mapCertificate := fun _kind budget => .inr budget
  check_commutes := by
    intro kind _code _budget
    cases kind
    rfl
  meaning_preserved := by
    intro _kind _code meaningful
    exact meaningful

theorem haltingInclusion_conservative :
    haltingInclusion.toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro _kind _code meaningful
    exact meaningful
  meaning_reflecting := by
    intro _kind _code meaningful
    exact meaningful

/-! ## Positive and negative controls -/

theorem true_fragment_accepted :
    expandedChecker.check (.inl true) (.inl ()) = true := by
  rfl

theorem false_fragment_rejected :
    expandedChecker.check (.inl false) (.inl ()) = false := by
  rfl

theorem halting_certificate_rejected_at_boolean_claim (budget : Nat) :
    expandedChecker.check (.inl true) (.inr budget) = false := by
  rfl

theorem boolean_certificate_rejected_at_halting_claim
    (code : Nat.Partrec.Code) :
    expandedChecker.check (.inr code) (.inl ()) = false := by
  rfl

theorem zero_program_has_finite_certificate :
    exists budget,
      expandedChecker.check (.inr Nat.Partrec.Code.zero)
        (.inr budget) = true := by
  have halts : Checker.HaltingMeaning Nat.Partrec.Code.zero := by
    change (Part.some 0).Dom
    exact Part.some_dom 0
  obtain ⟨budget, accepted⟩ :=
    Checker.haltingTrustBoundaryChecker_complete
      Nat.Partrec.Code.zero halts
  exact ⟨budget, accepted⟩

/-- The decidable left fragment remains exactly decidable even though the
whole extension is not computably decidable. -/
theorem boolean_fragment_decision_exact (claim : Bool) :
    booleanDecisionKernel.decide claim = true <->
      ExpandedMeaning (.inl claim) :=
  booleanDecisionKernel.correct claim

#print axioms pullbackDecisionKernel
#print axioms pullbackDecisionKernel_computable
#print axioms no_computableDecisionKernel_of_halting_reduction
#print axioms expandedMeaning_has_no_computableDecisionKernel
#print axioms expandedChecker_computable
#print axioms expandedChecker_sound
#print axioms expandedChecker_complete
#print axioms expandedAuthority
#print axioms booleanInclusion_conservative
#print axioms haltingInclusion_conservative
#print axioms zero_program_has_finite_certificate

end Mettapedia.GSLT.LanguageDef.NIKSemanticGroundDecidabilityFrontier
