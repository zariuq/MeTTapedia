import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Basic
import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Certificate replay and kernel authority

Finite evidence, executable replay, theoremhood decision, and trusted
computation are different properties.  They must not be arranged into a
single ladder merely because several familiar systems happen to occupy
different corners of the resulting space.

This module isolates the reusable distinctions.

* A `Checker` is an executable Boolean replay function.
* Soundness and certificate completeness together form `Checker.Authority`.
  This identifies semantic truth with the existence of accepted evidence; it
  does not by itself decide whether such evidence exists.
* A `DecisionKernel` decides the semantic judgment directly.
* A `CompleteProducer` composed with a sound checker yields a decision kernel.
* Explicit conversion evidence and kernel-recomputed conversion both support
  complete proof checking, but only the former retains the conversion path.
* A family may require certificates of unbounded depth while every individual
  certificate remains finite.

Infinitary claims require an additional, orthogonal global condition.  The
ProofGSLT recurrent-trace development supplies the concrete Buechi instance;
cyclic local replay alone is deliberately not treated as authority here.
-/

namespace Mettapedia.GSLT.LanguageDef.KernelAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization

universe uClaim uCertificate uJudgment uAxiom uConversion

/-! ## Executable replay and exact authority -/

/-- A structurally total executable checker for untrusted evidence. -/
structure Checker (Claim : Type uClaim) (Certificate : Type uCertificate) where
  check : Claim -> Certificate -> Bool

namespace Checker

/-- Accepted evidence never establishes a false semantic claim. -/
def Sound {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (Meaning : Claim -> Prop) : Prop :=
  forall claim certificate, checker.check claim certificate = true ->
    Meaning claim

/-- Every true semantic claim has some accepted certificate. -/
def CertificateComplete {Claim : Type uClaim}
    {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (Meaning : Claim -> Prop) : Prop :=
  forall claim, Meaning claim ->
    exists certificate, checker.check claim certificate = true

/-- Exact replay authority is the two-sided certificate-existence law. -/
structure Authority {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (Meaning : Claim -> Prop) : Prop where
  sound : checker.Sound Meaning
  complete : checker.CertificateComplete Meaning

/-- Exact authority identifies meaning with existence of accepted evidence. -/
theorem Authority.meaning_iff_exists_certificate
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate} {Meaning : Claim -> Prop}
    (authority : checker.Authority Meaning) (claim : Claim) :
    Meaning claim <->
      exists certificate, checker.check claim certificate = true := by
  constructor
  · exact authority.complete claim
  · rintro ⟨certificate, accepted⟩
    exact authority.sound claim certificate accepted

/-! ## Composing independent checker obligations -/

/-- Replay two independent evidence components for the same claim.  This is
the generic shape used when local rule legality and a global acceptance
condition are checked separately. -/
def conjunction
    {Claim : Type uClaim} {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uJudgment}
    (left : Checker Claim LeftCertificate)
    (right : Checker Claim RightCertificate) :
    Checker Claim (LeftCertificate × RightCertificate) where
  check := fun claim evidence =>
    left.check claim evidence.1 && right.check claim evidence.2

theorem conjunction_sound
    {Claim : Type uClaim} {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uJudgment}
    {left : Checker Claim LeftCertificate}
    {right : Checker Claim RightCertificate}
    {LeftMeaning RightMeaning : Claim -> Prop}
    (leftSound : left.Sound LeftMeaning)
    (rightSound : right.Sound RightMeaning) :
    (conjunction left right).Sound
      (fun claim => LeftMeaning claim /\ RightMeaning claim) := by
  intro claim evidence accepted
  have acceptedParts :
      left.check claim evidence.1 = true /\
        right.check claim evidence.2 = true := by
    simpa only [conjunction, Bool.and_eq_true] using accepted
  exact ⟨leftSound claim evidence.1 acceptedParts.1,
    rightSound claim evidence.2 acceptedParts.2⟩

theorem conjunction_complete
    {Claim : Type uClaim} {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uJudgment}
    {left : Checker Claim LeftCertificate}
    {right : Checker Claim RightCertificate}
    {LeftMeaning RightMeaning : Claim -> Prop}
    (leftComplete : left.CertificateComplete LeftMeaning)
    (rightComplete : right.CertificateComplete RightMeaning) :
    (conjunction left right).CertificateComplete
      (fun claim => LeftMeaning claim /\ RightMeaning claim) := by
  intro claim meaningful
  obtain ⟨leftMeaning, rightMeaning⟩ := meaningful
  obtain ⟨leftEvidence, leftAccepted⟩ := leftComplete claim leftMeaning
  obtain ⟨rightEvidence, rightAccepted⟩ :=
    rightComplete claim rightMeaning
  exact ⟨⟨leftEvidence, rightEvidence⟩, by
    simp [conjunction, leftAccepted, rightAccepted]⟩

/-- Exact authorities compose without merging their certificate languages. -/
theorem conjunction_authority
    {Claim : Type uClaim} {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uJudgment}
    {left : Checker Claim LeftCertificate}
    {right : Checker Claim RightCertificate}
    {LeftMeaning RightMeaning : Claim -> Prop}
    (leftAuthority : left.Authority LeftMeaning)
    (rightAuthority : right.Authority RightMeaning) :
    (conjunction left right).Authority
      (fun claim => LeftMeaning claim /\ RightMeaning claim) where
  sound := conjunction_sound leftAuthority.sound rightAuthority.sound
  complete := conjunction_complete leftAuthority.complete
    rightAuthority.complete

/-! ## Combining distinct judgment families -/

/-- Tagged dispatch between two distinct claim and certificate languages.
Cross-family evidence is rejected rather than guessed or coerced. -/
def sum
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    (left : Checker LeftClaim LeftCertificate)
    (right : Checker RightClaim RightCertificate) :
    Checker (Sum LeftClaim RightClaim)
      (Sum LeftCertificate RightCertificate) where
  check
    | .inl claim, .inl certificate => left.check claim certificate
    | .inr claim, .inr certificate => right.check claim certificate
    | .inl _, .inr _ => false
    | .inr _, .inl _ => false

@[simp] theorem sum_check_left
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    (left : Checker LeftClaim LeftCertificate)
    (right : Checker RightClaim RightCertificate)
    (claim : LeftClaim) (certificate : LeftCertificate) :
    (sum left right).check (.inl claim) (.inl certificate) =
      left.check claim certificate := rfl

@[simp] theorem sum_check_right
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    (left : Checker LeftClaim LeftCertificate)
    (right : Checker RightClaim RightCertificate)
    (claim : RightClaim) (certificate : RightCertificate) :
    (sum left right).check (.inr claim) (.inr certificate) =
      right.check claim certificate := rfl

@[simp] theorem sum_rejects_left_claim_right_certificate
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    (left : Checker LeftClaim LeftCertificate)
    (right : Checker RightClaim RightCertificate)
    (claim : LeftClaim) (certificate : RightCertificate) :
    (sum left right).check (.inl claim) (.inr certificate) = false := rfl

@[simp] theorem sum_rejects_right_claim_left_certificate
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    (left : Checker LeftClaim LeftCertificate)
    (right : Checker RightClaim RightCertificate)
    (claim : RightClaim) (certificate : LeftCertificate) :
    (sum left right).check (.inr claim) (.inl certificate) = false := rfl

theorem sum_sound
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    {left : Checker LeftClaim LeftCertificate}
    {right : Checker RightClaim RightCertificate}
    {LeftMeaning : LeftClaim -> Prop} {RightMeaning : RightClaim -> Prop}
    (leftSound : left.Sound LeftMeaning)
    (rightSound : right.Sound RightMeaning) :
    (sum left right).Sound (Sum.elim LeftMeaning RightMeaning) := by
  intro claim certificate accepted
  cases claim <;> cases certificate
  · exact leftSound _ _ accepted
  · simp at accepted
  · simp at accepted
  · exact rightSound _ _ accepted

theorem sum_complete
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    {left : Checker LeftClaim LeftCertificate}
    {right : Checker RightClaim RightCertificate}
    {LeftMeaning : LeftClaim -> Prop} {RightMeaning : RightClaim -> Prop}
    (leftComplete : left.CertificateComplete LeftMeaning)
    (rightComplete : right.CertificateComplete RightMeaning) :
    (sum left right).CertificateComplete
      (Sum.elim LeftMeaning RightMeaning) := by
  intro claim meaningful
  cases claim with
  | inl claim =>
      obtain ⟨certificate, accepted⟩ := leftComplete claim meaningful
      exact ⟨.inl certificate, accepted⟩
  | inr claim =>
      obtain ⟨certificate, accepted⟩ := rightComplete claim meaningful
      exact ⟨.inr certificate, accepted⟩

/-- Exact authorities for distinct judgment families form one tagged
authority without conflating their evidence. -/
theorem sum_authority
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    {left : Checker LeftClaim LeftCertificate}
    {right : Checker RightClaim RightCertificate}
    {LeftMeaning : LeftClaim -> Prop} {RightMeaning : RightClaim -> Prop}
    (leftAuthority : left.Authority LeftMeaning)
    (rightAuthority : right.Authority RightMeaning) :
    (sum left right).Authority (Sum.elim LeftMeaning RightMeaning) where
  sound := sum_sound leftAuthority.sound rightAuthority.sound
  complete := sum_complete leftAuthority.complete rightAuthority.complete

/-- Sound evidence for a stronger property remains sound after a semantic
projection.  Completeness is deliberately not preserved by this operation. -/
theorem Sound.map
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Strong Weak : Claim -> Prop}
    (sound : checker.Sound Strong)
    (projection : forall claim, Strong claim -> Weak claim) :
    checker.Sound Weak := by
  intro claim certificate accepted
  exact projection claim (sound claim certificate accepted)

/-! ## Exact certificate scopes and semantic projections -/

/-- A certificate language may be exact for a declared semantic scope while
that scope only projects soundly into a broader guest-language meaning.  This
is the reusable shape for finite global witnesses whose completeness at the
broader meaning has not been established. -/
structure AuthorityProjection
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (Certified Meaning : Claim -> Prop) : Prop where
  authority : checker.Authority Certified
  project : forall claim, Certified claim -> Meaning claim

/-- Every authority projection is sound for its projected meaning. -/
theorem AuthorityProjection.sound
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Certified Meaning : Claim -> Prop}
    (projection : checker.AuthorityProjection Certified Meaning) :
    checker.Sound Meaning :=
  projection.authority.sound.map projection.project

/-- Exact authority is the special case whose certificate scope and guest
meaning coincide. -/
def Authority.toProjection
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate} {Meaning : Claim -> Prop}
    (authority : checker.Authority Meaning) :
    checker.AuthorityProjection Meaning Meaning where
  authority := authority
  project := fun _ meaningful => meaningful

/-- A separating claim proves that a projected authority is not exact for
the broader guest meaning. -/
theorem AuthorityProjection.not_target_authority_of_gap
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Certified Meaning : Claim -> Prop}
    (projection : checker.AuthorityProjection Certified Meaning)
    {claim : Claim} (meaningful : Meaning claim)
    (notCertified : ¬ Certified claim) :
    ¬ checker.Authority Meaning := by
  intro targetAuthority
  obtain ⟨certificate, accepted⟩ :=
    targetAuthority.complete claim meaningful
  exact notCertified
    (projection.authority.sound claim certificate accepted)

/-- Independent authority projections compose by pairing their evidence and
conjoining both their exact and projected meanings. -/
def AuthorityProjection.conjunction
    {Claim : Type uClaim} {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uJudgment}
    {left : Checker Claim LeftCertificate}
    {right : Checker Claim RightCertificate}
    {LeftCertified RightCertified LeftMeaning RightMeaning : Claim -> Prop}
    (leftProjection :
      left.AuthorityProjection LeftCertified LeftMeaning)
    (rightProjection :
      right.AuthorityProjection RightCertified RightMeaning) :
    (Checker.conjunction left right).AuthorityProjection
      (fun claim => LeftCertified claim /\ RightCertified claim)
      (fun claim => LeftMeaning claim /\ RightMeaning claim) where
  authority := Checker.conjunction_authority
    leftProjection.authority rightProjection.authority
  project := by
    intro claim certified
    exact ⟨leftProjection.project claim certified.1,
      rightProjection.project claim certified.2⟩

/-- Authority projections for distinct judgment families compose through the
same fail-closed tagged dispatch. -/
def AuthorityProjection.sum
    {LeftClaim : Type uClaim} {RightClaim : Type uJudgment}
    {LeftCertificate : Type uCertificate}
    {RightCertificate : Type uAxiom}
    {left : Checker LeftClaim LeftCertificate}
    {right : Checker RightClaim RightCertificate}
    {LeftCertified LeftMeaning : LeftClaim -> Prop}
    {RightCertified RightMeaning : RightClaim -> Prop}
    (leftProjection :
      left.AuthorityProjection LeftCertified LeftMeaning)
    (rightProjection :
      right.AuthorityProjection RightCertified RightMeaning) :
    (Checker.sum left right).AuthorityProjection
      (Sum.elim LeftCertified RightCertified)
      (Sum.elim LeftMeaning RightMeaning) where
  authority := Checker.sum_authority
    leftProjection.authority rightProjection.authority
  project := by
    intro claim certified
    cases claim with
    | inl claim => exact leftProjection.project claim certified
    | inr claim => exact rightProjection.project claim certified

/-! ## Transporting semantic certificates to a finite wire carrier -/

/-- A fail-closed wire codec.  Decoding need only be partial, but every
canonical encoding must decode to the original certificate. -/
structure PartialCodec (Certificate : Type uCertificate)
    (Wire : Type uJudgment) where
  encode : Certificate -> Wire
  decode : Wire -> Option Certificate
  decode_encode : forall certificate, decode (encode certificate) = some certificate

/-- A left-invertible encoder cannot identify distinct certificates. -/
theorem PartialCodec.encode_injective
    {Certificate : Type uCertificate} {Wire : Type uJudgment}
    (codec : PartialCodec Certificate Wire) :
    Function.Injective codec.encode := by
  intro left right sameEncoding
  have decoded : codec.decode (codec.encode left) =
      codec.decode (codec.encode right) := congrArg codec.decode sameEncoding
  simpa [codec.decode_encode] using decoded

/-- Replay a semantic checker after fail-closed wire decoding. -/
def onWire
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Wire : Type uJudgment}
    (checker : Checker Claim Certificate)
    (codec : PartialCodec Certificate Wire) : Checker Claim Wire where
  check := fun claim wire =>
    match codec.decode wire with
    | none => false
    | some certificate => checker.check claim certificate

theorem onWire_sound
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Wire : Type uJudgment}
    {checker : Checker Claim Certificate}
    (codec : PartialCodec Certificate Wire)
    {Meaning : Claim -> Prop} (sound : checker.Sound Meaning) :
    (onWire checker codec).Sound Meaning := by
  intro claim wire accepted
  unfold onWire at accepted
  cases decoded : codec.decode wire with
  | none => simp [decoded] at accepted
  | some certificate =>
      exact sound claim certificate (by simpa [decoded] using accepted)

theorem onWire_complete
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Wire : Type uJudgment}
    {checker : Checker Claim Certificate}
    (codec : PartialCodec Certificate Wire)
    {Meaning : Claim -> Prop}
    (complete : checker.CertificateComplete Meaning) :
    (onWire checker codec).CertificateComplete Meaning := by
  intro claim meaningful
  obtain ⟨certificate, accepted⟩ := complete claim meaningful
  exact ⟨codec.encode certificate, by
    simp [onWire, codec.decode_encode, accepted]⟩

/-- A faithful codec transports exact authority to untrusted wire input. -/
theorem onWire_authority
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Wire : Type uJudgment}
    {checker : Checker Claim Certificate}
    (codec : PartialCodec Certificate Wire)
    {Meaning : Claim -> Prop} (authority : checker.Authority Meaning) :
    (onWire checker codec).Authority Meaning where
  sound := onWire_sound codec authority.sound
  complete := onWire_complete codec authority.complete

/-- Fail-closed wire decoding preserves both the exact certificate scope and
its semantic projection. -/
def AuthorityProjection.onWire
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Wire : Type uJudgment}
    {checker : Checker Claim Certificate}
    (codec : PartialCodec Certificate Wire)
    {Certified Meaning : Claim -> Prop}
    (projection : checker.AuthorityProjection Certified Meaning) :
    (Checker.onWire checker codec).AuthorityProjection Certified Meaning where
  authority := Checker.onWire_authority codec projection.authority
  project := projection.project

/-- A checker that rejects every certificate. -/
def rejectAll (Claim : Type uClaim) (Certificate : Type uCertificate) :
    Checker Claim Certificate where
  check := fun _ _ => false

/-- Rejecting everything is sound for every meaning. -/
theorem rejectAll_sound (Claim : Type uClaim) (Certificate : Type uCertificate)
    (Meaning : Claim -> Prop) :
    (rejectAll Claim Certificate).Sound Meaning := by
  intro claim certificate accepted
  simp [rejectAll] at accepted

/-- Soundness alone is not authority whenever at least one claim is true. -/
theorem rejectAll_not_authority
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Meaning : Claim -> Prop} {claim : Claim} (meaningful : Meaning claim) :
    ¬ (rejectAll Claim Certificate).Authority Meaning := by
  intro authority
  obtain ⟨certificate, accepted⟩ := authority.complete claim meaningful
  simp [rejectAll] at accepted

/-! ## Authority is not automatically decision -/

/-- A kernel which directly decides a semantic judgment. -/
structure DecisionKernel (Claim : Type uClaim) (Meaning : Claim -> Prop) where
  decide : Claim -> Bool
  correct : forall claim, decide claim = true <-> Meaning claim

/-- A decision kernel can be viewed as a replay checker with a trivial
certificate.  This representation intentionally carries no proof details. -/
def DecisionKernel.toChecker {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : DecisionKernel Claim Meaning) : Checker Claim Unit where
  check := fun claim _ => kernel.decide claim

/-- Every decision kernel induces exact certificate authority. -/
theorem DecisionKernel.authority
    {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (kernel : DecisionKernel Claim Meaning) :
    kernel.toChecker.Authority Meaning where
  sound := by
    intro claim _ accepted
    exact (kernel.correct claim).mp accepted
  complete := by
    intro claim meaningful
    exact ⟨(), (kernel.correct claim).mpr meaningful⟩

/-- Exhaustive certificate search is available when the whole certificate
space is finite.  This is much stronger than saying that each individual
certificate is a finite syntax tree. -/
def exhaustiveCheck
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    [Fintype Certificate] (checker : Checker Claim Certificate)
    (claim : Claim) : Bool :=
  decide (exists certificate, checker.check claim certificate = true)

theorem exhaustiveCheck_eq_true_iff
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    [Fintype Certificate] (checker : Checker Claim Certificate)
    (claim : Claim) :
    exhaustiveCheck checker claim = true <->
      exists certificate, checker.check claim certificate = true := by
  simp [exhaustiveCheck]

/-- Exact authority over a finite certificate space yields a decision kernel
by exhaustive search.  No such conclusion is drawn for an unbounded proof
syntax such as trees, DAGs, traces, or automata. -/
def decisionKernelOfFiniteCertificateSpace
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    [Fintype Certificate] {checker : Checker Claim Certificate}
    {Meaning : Claim -> Prop} (authority : checker.Authority Meaning) :
    DecisionKernel Claim Meaning where
  decide := exhaustiveCheck checker
  correct := by
    intro claim
    rw [exhaustiveCheck_eq_true_iff]
    exact authority.meaning_iff_exists_certificate claim |>.symm

/-- A producer is complete when every meaningful claim causes it to emit
accepted evidence.  It may emit rejected evidence on other inputs; replay,
not producer trust, determines acceptance. -/
structure CompleteProducer
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (Meaning : Claim -> Prop) where
  produce : Claim -> Option Certificate
  complete : forall claim, Meaning claim ->
    exists certificate,
      produce claim = some certificate /\
        checker.check claim certificate = true

/-- Run a producer and replay exactly the evidence it returned. -/
def checkProduced
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate} {Meaning : Claim -> Prop}
    (producer : CompleteProducer checker Meaning) (claim : Claim) : Bool :=
  match producer.produce claim with
  | none => false
  | some certificate => checker.check claim certificate

/-- A complete producer plus a sound independent replay checker is a decision
kernel.  This is the precise certifying-algorithm pattern. -/
def decisionKernelOfProducer
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate} {Meaning : Claim -> Prop}
    (sound : checker.Sound Meaning)
    (producer : CompleteProducer checker Meaning) :
    DecisionKernel Claim Meaning where
  decide := checkProduced producer
  correct := by
    intro claim
    constructor
    · intro accepted
      unfold checkProduced at accepted
      cases produced : producer.produce claim with
      | none => simp [produced] at accepted
      | some certificate =>
          exact sound claim certificate (by simpa [produced] using accepted)
    · intro meaningful
      obtain ⟨certificate, produced, accepted⟩ :=
        producer.complete claim meaningful
      simp [checkProduced, produced, accepted]

end Checker

/-! ## A theory with conversion -/

/-- The minimal semantic shape needed to separate inference from conversion. -/
structure Theory (Judgment : Type uJudgment) where
  axioms : Judgment -> Prop
  conversion : Judgment -> Judgment -> Prop

/-- A judgment is derivable from an axiom and zero or more conversions. -/
inductive Derivable {Judgment : Type uJudgment} (theory : Theory Judgment) :
    Judgment -> Prop
  | axiom' {judgment : Judgment} :
      theory.axioms judgment -> Derivable theory judgment
  | convert {source target : Judgment} :
      Derivable theory source -> theory.conversion source target ->
        Derivable theory target

/-- A binary claim used by an executable conversion checker. -/
structure ConversionClaim (Judgment : Type uJudgment) where
  source : Judgment
  target : Judgment

/-! ## Explicit, proof-relevant conversion -/

/-- A finite derivation article that retains evidence for every conversion. -/
inductive ExplicitCertificate
    (Judgment : Type uJudgment) (AxiomEvidence : Type uAxiom)
    (ConversionEvidence : Type uConversion) where
  | base (evidence : AxiomEvidence)
  | convert (source : Judgment)
      (prior : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence)
      (evidence : ConversionEvidence)
deriving Repr, DecidableEq

/-- Replay an explicit derivation article. -/
def checkExplicit
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion}
    (axiomChecker : Checker Judgment AxiomEvidence)
    (conversionChecker : Checker (ConversionClaim Judgment) ConversionEvidence) :
    Judgment ->
      ExplicitCertificate Judgment AxiomEvidence ConversionEvidence -> Bool
  | target, .base evidence => axiomChecker.check target evidence
  | target, .convert source prior evidence =>
      checkExplicit axiomChecker conversionChecker source prior &&
        conversionChecker.check ⟨source, target⟩ evidence
termination_by _ certificate => sizeOf certificate

/-- The explicit derivation checker as an ordinary checker value. -/
def explicitChecker
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion}
    (axiomChecker : Checker Judgment AxiomEvidence)
    (conversionChecker : Checker (ConversionClaim Judgment) ConversionEvidence) :
    Checker Judgment
      (ExplicitCertificate Judgment AxiomEvidence ConversionEvidence) where
  check := checkExplicit axiomChecker conversionChecker

/-- Local soundness composes into soundness of complete derivation replay. -/
theorem checkExplicit_sound
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion}
    {theory : Theory Judgment}
    {axiomChecker : Checker Judgment AxiomEvidence}
    {conversionChecker : Checker (ConversionClaim Judgment) ConversionEvidence}
    (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment}
    {certificate : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence}
    (accepted : checkExplicit axiomChecker conversionChecker target certificate = true) :
    Derivable theory target := by
  induction certificate generalizing target with
  | base evidence =>
      exact .axiom' (axiomSound target evidence (by
        simpa [checkExplicit] using accepted))
  | convert source prior evidence inductionHypothesis =>
      have acceptedParts :
          checkExplicit axiomChecker conversionChecker source prior = true /\
            conversionChecker.check ⟨source, target⟩ evidence = true := by
        simpa [checkExplicit, Bool.and_eq_true] using accepted
      exact .convert (inductionHypothesis acceptedParts.1)
        (conversionSound ⟨source, target⟩ evidence acceptedParts.2)

/-- Local certificate completeness composes into completeness of explicit
derivation articles. -/
theorem checkExplicit_complete
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion}
    {theory : Theory Judgment}
    {axiomChecker : Checker Judgment AxiomEvidence}
    {conversionChecker : Checker (ConversionClaim Judgment) ConversionEvidence}
    (axiomComplete : axiomChecker.CertificateComplete theory.axioms)
    (conversionComplete : conversionChecker.CertificateComplete
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment} (derivable : Derivable theory target) :
    exists certificate,
      checkExplicit axiomChecker conversionChecker target certificate = true := by
  induction derivable with
  | axiom' isAxiom =>
      obtain ⟨evidence, accepted⟩ := axiomComplete _ isAxiom
      exact ⟨.base evidence, by simpa [checkExplicit] using accepted⟩
  | @convert source target prior converted inductionHypothesis =>
      obtain ⟨priorEvidence, priorAccepted⟩ := inductionHypothesis
      obtain ⟨conversionEvidence, conversionAccepted⟩ :=
        conversionComplete ⟨source, target⟩ converted
      exact ⟨.convert source priorEvidence conversionEvidence, by
        simp [checkExplicit, priorAccepted, conversionAccepted]⟩

/-- Explicit local authorities generate an exact authority for derivability. -/
theorem explicitChecker_authority
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion}
    {theory : Theory Judgment}
    {axiomChecker : Checker Judgment AxiomEvidence}
    {conversionChecker : Checker (ConversionClaim Judgment) ConversionEvidence}
    (axiomAuthority : axiomChecker.Authority theory.axioms)
    (conversionAuthority : conversionChecker.Authority
      (fun claim => theory.conversion claim.source claim.target)) :
    (explicitChecker axiomChecker conversionChecker).Authority
      (Derivable theory) where
  sound := by
    intro target certificate accepted
    exact checkExplicit_sound axiomAuthority.sound conversionAuthority.sound accepted
  complete := by
    intro target derivable
    exact checkExplicit_complete axiomAuthority.complete
      conversionAuthority.complete derivable

/-! ## Kernel-recomputed conversion -/

/-- A finite derivation skeleton retains conversion endpoints but no evidence
for why those endpoints are convertible. -/
inductive KernelSkeleton (Judgment : Type uJudgment) where
  | base
  | convert (source : Judgment) (prior : KernelSkeleton Judgment)
deriving Repr, DecidableEq

/-- Replay a derivation skeleton while recomputing every semantic premise. -/
def checkSkeleton
    {Judgment : Type uJudgment} {theory : Theory Judgment}
    (axiomKernel : Checker.DecisionKernel Judgment theory.axioms)
    (conversionKernel : Checker.DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target)) :
    Judgment -> KernelSkeleton Judgment -> Bool
  | target, .base => axiomKernel.decide target
  | target, .convert source prior =>
      checkSkeleton axiomKernel conversionKernel source prior &&
        conversionKernel.decide ⟨source, target⟩
termination_by _ certificate => sizeOf certificate

def skeletonChecker
    {Judgment : Type uJudgment} {theory : Theory Judgment}
    (axiomKernel : Checker.DecisionKernel Judgment theory.axioms)
    (conversionKernel : Checker.DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target)) :
    Checker Judgment (KernelSkeleton Judgment) where
  check := checkSkeleton axiomKernel conversionKernel

theorem checkSkeleton_sound
    {Judgment : Type uJudgment} {theory : Theory Judgment}
    (axiomKernel : Checker.DecisionKernel Judgment theory.axioms)
    (conversionKernel : Checker.DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment} {certificate : KernelSkeleton Judgment}
    (accepted : checkSkeleton axiomKernel conversionKernel target certificate = true) :
    Derivable theory target := by
  induction certificate generalizing target with
  | base =>
      exact .axiom' ((axiomKernel.correct target).mp (by
        simpa [checkSkeleton] using accepted))
  | convert source prior inductionHypothesis =>
      have acceptedParts :
          checkSkeleton axiomKernel conversionKernel source prior = true /\
            conversionKernel.decide ⟨source, target⟩ = true := by
        simpa [checkSkeleton, Bool.and_eq_true] using accepted
      exact .convert (inductionHypothesis acceptedParts.1)
        ((conversionKernel.correct ⟨source, target⟩).mp acceptedParts.2)

theorem checkSkeleton_complete
    {Judgment : Type uJudgment} {theory : Theory Judgment}
    (axiomKernel : Checker.DecisionKernel Judgment theory.axioms)
    (conversionKernel : Checker.DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment} (derivable : Derivable theory target) :
    exists certificate,
      checkSkeleton axiomKernel conversionKernel target certificate = true := by
  induction derivable with
  | axiom' isAxiom =>
      exact ⟨.base, by
        simpa [checkSkeleton] using (axiomKernel.correct _).mpr isAxiom⟩
  | @convert source target prior converted inductionHypothesis =>
      obtain ⟨priorEvidence, priorAccepted⟩ := inductionHypothesis
      exact ⟨.convert source priorEvidence, by
        simp [checkSkeleton, priorAccepted,
          (conversionKernel.correct ⟨source, target⟩).mpr converted]⟩

/-- Recomputing conversion is a complete authority when the admitted kernels
really decide the two local semantic predicates.  The finite skeleton remains
a proof term, but it is not a self-contained conversion certificate. -/
theorem skeletonChecker_authority
    {Judgment : Type uJudgment} {theory : Theory Judgment}
    (axiomKernel : Checker.DecisionKernel Judgment theory.axioms)
    (conversionKernel : Checker.DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target)) :
    (skeletonChecker axiomKernel conversionKernel).Authority
      (Derivable theory) where
  sound := by
    intro target certificate accepted
    exact checkSkeleton_sound axiomKernel conversionKernel accepted
  complete := by
    intro target derivable
    exact checkSkeleton_complete axiomKernel conversionKernel derivable

/-! ## Erasing conversion evidence -/

/-- Forget all local evidence while retaining the derivation skeleton. -/
def ExplicitCertificate.erase
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion} :
    ExplicitCertificate Judgment AxiomEvidence ConversionEvidence ->
      KernelSkeleton Judgment
  | .base _ => .base
  | .convert source prior _ => .convert source prior.erase

/-- Number of inference/conversion nodes in an explicit article. -/
def ExplicitCertificate.depth
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion} :
    ExplicitCertificate Judgment AxiomEvidence ConversionEvidence -> Nat
  | .base _ => 0
  | .convert _ prior _ => prior.depth + 1

private def evidenceTheory : Theory Bool where
  axioms := fun judgment => judgment = false
  conversion := fun source target => source = false /\ target = true

private def evidenceAxiomChecker : Checker Bool Unit where
  check := fun judgment _ => decide (judgment = false)

private def evidenceConversionChecker : Checker (ConversionClaim Bool) Bool where
  check := fun claim _ => decide (claim.source = false /\ claim.target = true)

private theorem evidenceAxiomChecker_authority :
    evidenceAxiomChecker.Authority evidenceTheory.axioms where
  sound := by
    intro judgment _ accepted
    change judgment = false
    change decide (judgment = false) = true at accepted
    exact of_decide_eq_true accepted
  complete := by
    intro judgment isAxiom
    change judgment = false at isAxiom
    exact ⟨(), by
      change decide (judgment = false) = true
      exact decide_eq_true isAxiom⟩

private theorem evidenceConversionChecker_authority :
    evidenceConversionChecker.Authority
      (fun claim => evidenceTheory.conversion claim.source claim.target) where
  sound := by
    intro claim _ accepted
    change claim.source = false /\ claim.target = true
    change decide (claim.source = false /\ claim.target = true) = true at accepted
    exact of_decide_eq_true accepted
  complete := by
    intro claim converted
    change claim.source = false /\ claim.target = true at converted
    exact ⟨false, by
      change decide (claim.source = false /\ claim.target = true) = true
      exact decide_eq_true converted⟩

private theorem evidenceExplicitChecker_authority :
    (explicitChecker evidenceAxiomChecker evidenceConversionChecker).Authority
      (Derivable evidenceTheory) :=
  explicitChecker_authority evidenceAxiomChecker_authority
    evidenceConversionChecker_authority

private def evidenceCertificate (evidence : Bool) :
    ExplicitCertificate Bool Unit Bool :=
  .convert false (.base ()) evidence

theorem evidenceCertificates_accepted (evidence : Bool) :
    checkExplicit evidenceAxiomChecker evidenceConversionChecker true
      (evidenceCertificate evidence) = true := by
  simp [evidenceCertificate, checkExplicit, evidenceAxiomChecker,
    evidenceConversionChecker]

theorem evidenceCertificates_derivable (evidence : Bool) :
    Derivable evidenceTheory true :=
  evidenceExplicitChecker_authority.sound true (evidenceCertificate evidence)
    (evidenceCertificates_accepted evidence)

/-- Two distinct conversion witnesses have the same evidence-erased proof. -/
theorem evidenceErasure_noninjective :
    ¬ Function.Injective
      (ExplicitCertificate.erase :
        ExplicitCertificate Bool Unit Bool -> KernelSkeleton Bool) := by
  intro injective
  have equal : evidenceCertificate false = evidenceCertificate true :=
    injective rfl
  cases equal

/-- Loss of conversion evidence is an explicit nontrivial fibre. -/
def evidenceErasureFiber :
    NonTrivialFiber
      (ExplicitCertificate.erase :
        ExplicitCertificate Bool Unit Bool -> KernelSkeleton Bool)
      id where
  left := evidenceCertificate false
  right := evidenceCertificate true
  sameShadow := rfl
  differentValue := by decide

/-- Additive valuation of an explicit proof article.  Different applications
may instantiate this with work, span, provenance weight, evidential weight,
or another declared additive observation. -/
def ExplicitCertificate.valuation
    {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
    {ConversionEvidence : Type uConversion} {Value : Type*} [AddMonoid Value]
    (axiomValue : AxiomEvidence -> Value)
    (conversionValue : ConversionEvidence -> Value) :
    ExplicitCertificate Judgment AxiomEvidence ConversionEvidence -> Value
  | .base evidence => axiomValue evidence
  | .convert _ prior evidence =>
      prior.valuation axiomValue conversionValue + conversionValue evidence

private def evidenceCost : ExplicitCertificate Bool Unit Bool -> Nat :=
  ExplicitCertificate.valuation (fun _ => 0) (fun evidence => if evidence then 1 else 0)

private theorem evidenceCosts_differ :
    evidenceCost (evidenceCertificate false) ≠
      evidenceCost (evidenceCertificate true) := by
  decide

/-- Two explicit conversion paths with the same erased skeleton can carry
different costs. -/
def evidenceCostFiber :
    NonTrivialFiber
      (ExplicitCertificate.erase :
        ExplicitCertificate Bool Unit Bool -> KernelSkeleton Bool)
      evidenceCost where
  left := evidenceCertificate false
  right := evidenceCertificate true
  sameShadow := rfl
  differentValue := evidenceCosts_differ

/-- Cost or provenance retained on conversion evidence cannot in general be
reconstructed from an ordinary proof skeleton. -/
theorem evidenceCost_not_determined_by_erasure :
    ¬ Factors
      (ExplicitCertificate.erase :
        ExplicitCertificate Bool Unit Bool -> KernelSkeleton Bool)
      evidenceCost :=
  evidenceCostFiber.not_factors

/-! ## Unbounded certificate depth is not absence of finite certificates -/

private def successorTheory : Theory Nat where
  axioms := fun judgment => judgment = 0
  conversion := fun source target => target = source + 1

private def successorAxiomChecker : Checker Nat Unit where
  check := fun judgment _ => decide (judgment = 0)

private def successorConversionChecker : Checker (ConversionClaim Nat) Unit where
  check := fun claim _ => decide (claim.target = claim.source + 1)

/-- The certificate for `n` has exactly `n` conversion nodes. -/
def successorCertificate : (n : Nat) -> ExplicitCertificate Nat Unit Unit
  | 0 => .base ()
  | n + 1 => .convert n (successorCertificate n) ()

theorem successorCertificate_accepted (n : Nat) :
    checkExplicit successorAxiomChecker successorConversionChecker n
      (successorCertificate n) = true := by
  induction n with
  | zero => simp [successorCertificate, checkExplicit, successorAxiomChecker]
  | succ n inductionHypothesis =>
      simp only [successorCertificate, checkExplicit, Bool.and_eq_true]
      exact ⟨inductionHypothesis, by simp [successorConversionChecker]⟩

@[simp] theorem successorCertificate_depth (n : Nat) :
    (successorCertificate n).depth = n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp [successorCertificate, ExplicitCertificate.depth,
        inductionHypothesis]

/-- Arbitrarily deep computations have accepted finite certificates. -/
theorem accepted_certificates_have_unbounded_depth (bound : Nat) :
    exists target certificate,
      checkExplicit successorAxiomChecker successorConversionChecker target
        certificate = true /\
      bound <= certificate.depth :=
  ⟨bound, successorCertificate bound,
    successorCertificate_accepted bound, by simp⟩

/-! ## Equations and rewrites are independent checking obligations -/

/-- A GSLT whose two terms are equated although it has no rewrite edges. -/
def equationOnlyGSLT : GSLT where
  Term := Bool
  equations :=
    { r := fun _ _ => True
      iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ }
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

theorem equationOnlyGSLT_false_true_equivalent :
    equationOnlyGSLT.Equiv false true :=
  trivial

private def equationOnlyGSLT_reachable_eq :
    {source target : Bool} ->
      equationOnlyGSLT.MultiStep source target -> source = target
  | _, _, .refl _ => rfl
  | _, _, .step first _ => first.elim

theorem equationOnlyGSLT_false_true_not_reachable :
    ¬ equationOnlyGSLT.MultiStep false true := by
  intro path
  exact Bool.false_ne_true (equationOnlyGSLT_reachable_eq path)

/-- Checkable equations need not be generated by the operational rewrite
relation.  Therefore `E = closure(R)` is not a general checker-tier
classification for GSLTs. -/
theorem executable_equation_not_generated_by_rewrites :
    Nonempty (Checker.DecisionKernel (Bool × Bool)
      (fun pair => equationOnlyGSLT.Equiv pair.1 pair.2)) /\
    ¬ (forall source target,
      equationOnlyGSLT.Equiv source target <->
        equationOnlyGSLT.MultiStep source target) := by
  constructor
  · refine ⟨
      { decide := fun _ => true
        correct := by
          intro pair
          change true = true <-> True
          simp }⟩
  · intro generated
    exact equationOnlyGSLT_false_true_not_reachable
      ((generated false true).mp equationOnlyGSLT_false_true_equivalent)

/-! ## A generic blindness theorem -/

/-- One checker cannot be sound for one meaning and certificate-complete for
a different meaning when a claim separates them.  The theorem concerns what
the checker can observe; it does not imply that finite evidence is impossible
for either meaning separately. -/
theorem no_straddling_authority
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {smaller larger : Claim -> Prop} {claim : Claim}
    (soundForSmaller : checker.Sound smaller)
    (completeForLarger : checker.CertificateComplete larger)
    (largeMeaning : larger claim) (notSmall : ¬ smaller claim) : False := by
  obtain ⟨certificate, accepted⟩ := completeForLarger claim largeMeaning
  exact notSmall (soundForSmaller claim certificate accepted)

end Mettapedia.GSLT.LanguageDef.KernelAuthority
