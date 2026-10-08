import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mettapedia.Logic.HostingStyles.Admissibility
import Mettapedia.Logic.HostingStyles.ComputingEncoding

/-!
# The three hostings as observers

A hosting observes a proof system.  The points observed are the *claims*: a
judgment together with a derivation of it.  What a map of theories reports
about a claim is the judgment and the image of the derivation up to the
static equivalence of the target (`report`).

* **Native**: the claim itself.
* **Judgments as types**: the judgment and the encoding of the derivation up
  to the framework's conversion (`frameworkReport`).
* **Shallow semantic**: the judgment and the one host proof of its validity
  (`shallowReport`); equivalently the judgment's denotation.

## The chain

In the sense of `Mettapedia.GSLT.Core.NonFactorization`:

* the framework report factors through the native one
  (`frameworkReport_factors_native`), with no hypothesis beyond the encoding
  being defined;
* the shallow report factors through the framework report
  (`shallowReport_factors_framework`).  The recovery is defined on *every*
  term of the framework, and it uses exactly two things: adequacy, to read a
  term back as a derivation, and soundness, to read a derivation as a truth.

## When a step forgets nothing

* A map of theories into a theory without reduction is hosting exactly when
  its report is injective (`hosting_iff_report_injective`): hosting says that
  the observer has trivial fibres.
* The rules-as-constants encoding has trivial fibres
  (`native_factors_frameworkReport`): the claim is recovered from the
  framework report.  The computing encoding does not
  (`computingReport_fibre`, `size_not_factors_computingReport`).
* A shallow report has trivial fibres only if every judgment has at most one
  derivation (`shallowReport_injective_iff`).  For the worked logic it does
  not (`shallowReport_fibre`), and the size of a derivation is not a function
  of it (`size_not_factors_shallowReport`), while it is a function of the
  framework report (`size_factors_frameworkReport`).

## The Distinction Calculus reading

Each report is a crisp observer (`observer`), two claims being
indistinguishable when their reports agree.  Factoring is coarsening
(`observer_extends_of_factors`), so the three observers are ordered: native
refines judgments as types, which refines shallow (`native_refines_framework`,
`framework_refines_shallow`).  The two derivations of `φ ➝ φ` are apart for
the framework observer and indistinguishable for the shallow one
(`identity_detour_observed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus
open Framework

universe v

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-- A claim with its evidence: a judgment and a derivation of it. -/
abbrev Claim : Type := Σ j : J, P.Proof j

/-- **What a map of theories reports about a claim**: the judgment, and the
image of the derivation up to the static equivalence of the target. -/
def report {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target) (claim : P.Claim) :
    Σ j : J, Quotient (target.equations (map.interface j)) :=
  ⟨claim.1, Quotient.mk _ (map.term claim.2)⟩

/-- Every report factors through the claim. -/
theorem report_factors_native {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target) :
    Factors (fun claim : P.Claim => claim) (P.report map) :=
  ⟨P.report map, fun _ => rfl⟩

/-- **A map reflects the identity of derivations exactly when its report is
injective.** -/
theorem reflectsEquations_iff_report_injective {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target) :
    map.ReflectsEquations ↔ Function.Injective (P.report map) := by
  constructor
  · rintro reflects ⟨j, first⟩ ⟨j', second⟩ same
    obtain ⟨rfl, images⟩ := Sigma.mk.inj_iff.mp same
    have related := Quotient.exact (eq_of_heq images)
    have equal : first = second := reflects related
    rw [equal]
  · intro injective origin first second related
    have same : P.report map ⟨origin, first⟩ = P.report map ⟨origin, second⟩ :=
      congrArg (Sigma.mk origin) (Quotient.sound related)
    exact eq_of_heq (Sigma.mk.inj_iff.mp (injective same)).2

/-- **Hosting is having trivial fibres**: for a target without reduction, a
map is hosting exactly when its report is injective. -/
theorem hosting_iff_report_injective {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target)
    (static : ∀ {interface : target.Interface} (term next : target.Term interface),
      ¬ target.rewrites term next) :
    map.Hosting ↔ Function.Injective (P.report map) :=
  (P.hosting_iff_static _ map static).trans (P.reflectsEquations_iff_report_injective map)

/-- The same statement in the vocabulary of factorization: the claim is
constant on the fibres of the report. -/
theorem hosting_iff_constantOnFibers {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target)
    (static : ∀ {interface : target.Interface} (term next : target.Term interface),
      ¬ target.rewrites term next) :
    map.Hosting ↔ ConstantOnFibers (P.report map) (fun claim : P.Claim => claim) :=
  P.hosting_iff_report_injective map static

/-- A map that identifies two derivations has a fibre on which the claim is
not constant. -/
def fibreOfIdentified {target : ContextTheory.{0}}
    (map : ContextMap (P.proofTheory (ProofCongruence.identity P)) target) {j : J}
    {first second : P.Proof j} (distinct : first ≠ second)
    (identified : (target.equations (map.interface j)).r (map.term first) (map.term second)) :
    NonTrivialFiber (P.report map) (fun claim : P.Claim => claim) where
  left := ⟨j, first⟩
  right := ⟨j, second⟩
  sameShadow := congrArg (Sigma.mk j) (Quotient.sound identified)
  differentValue := fun same => distinct (eq_of_heq (Sigma.mk.inj_iff.mp same).2)

/-! ## The reports of the judgments-as-types and shallow hostings -/

variable {P} (finitary : P.Finitary)

/-- The report of the rules-as-constants encoding: the judgment and the term
up to conversion. -/
noncomputable abbrev Finitary.frameworkReport : P.Claim →
    Σ j : J, Quotient ((frameworkTheory finitary.signature).equations (.base j)) :=
  P.report finitary.encodingMap

/-- **The framework report factors through the native one.** -/
theorem Finitary.frameworkReport_factors_native :
    Factors (fun claim : P.Claim => claim) finitary.frameworkReport :=
  P.report_factors_native _

/-- **The native report factors through the framework report**: the encoding
has trivial fibres, and a claim is recovered from its report by adequacy. -/
theorem Finitary.native_factors_frameworkReport :
    Factors finitary.frameworkReport (fun claim : P.Claim => claim) :=
  ⟨fun shadow => ⟨shadow.1, finitary.adequacy shadow.1 shadow.2⟩, fun claim =>
    congrArg (Sigma.mk claim.1) (finitary.readback_encodeTerm claim.2)⟩

/-- The framework report is injective. -/
theorem Finitary.frameworkReport_injective : Function.Injective finitary.frameworkReport :=
  (P.hosting_iff_report_injective _ (fun _ _ step => step)).mp finitary.encodingMap_hosting

/-- The size of a derivation is a function of the framework report. -/
theorem Finitary.size_factors_frameworkReport :
    Factors finitary.frameworkReport (fun claim : P.Claim => size finitary claim.2) := by
  obtain ⟨recover, recovers⟩ := finitary.native_factors_frameworkReport
  exact ⟨fun shadow => size finitary (recover shadow).2, fun claim =>
    congrArg (fun claim : P.Claim => size finitary claim.2) (recovers claim)⟩

section Shallow

variable {Point : Type v} {holds : Point → J → Prop} (sound : LocallySound holds P)

/-- The report of a shallow embedding: the judgment and the host proof of its
validity. -/
noncomputable abbrev shallowReport : P.Claim →
    Σ j : J, Quotient ((shallowTheory holds).equations j) :=
  P.report (shallowMap sound finitary (ProofCongruence.identity P))

/-- **The shallow report factors through the framework report.**  The
recovery reads any term of the framework back as a derivation, by adequacy,
and a derivation as a truth, by soundness. -/
theorem shallowReport_factors_framework :
    Factors finitary.frameworkReport (shallowReport finitary sound) :=
  ⟨fun shadow => ⟨shadow.1, Quotient.mk _ ⟨sound.valid (finitary.adequacy shadow.1 shadow.2)⟩⟩,
    fun claim => congrArg (Sigma.mk claim.1) (Quotient.sound trivial)⟩

/-- Two claims have the same shallow report exactly when they are claims of
the same judgment. -/
theorem shallowReport_eq_iff (first second : P.Claim) :
    shallowReport finitary sound first = shallowReport finitary sound second ↔
      first.1 = second.1 := by
  constructor
  · intro same
    exact (Sigma.mk.inj_iff.mp same).1
  · obtain ⟨j, first⟩ := first
    obtain ⟨j', second⟩ := second
    rintro rfl
    exact congrArg (Sigma.mk j) (Quotient.sound trivial)

/-- **A shallow report has trivial fibres exactly when every judgment has at
most one derivation.** -/
theorem shallowReport_injective_iff :
    Function.Injective (shallowReport finitary sound) ↔ ∀ j : J, Subsingleton (P.Proof j) := by
  constructor
  · intro injective j
    refine ⟨fun first second => ?_⟩
    have same := injective ((shallowReport_eq_iff finitary sound ⟨j, first⟩ ⟨j, second⟩).mpr rfl)
    exact eq_of_heq (Sigma.mk.inj_iff.mp same).2
  · rintro unique ⟨j, first⟩ ⟨j', second⟩ same
    obtain rfl := (shallowReport_eq_iff finitary sound _ _).mp same
    rw [(unique j).elim first second]

end Shallow

end RuleSignature

/-! ## The observers of the Distinction Calculus -/

/-- **The crisp observer of a report**: two points are indistinguishable when
their reports agree. -/
noncomputable def observer {V W : Type} (report : V → W) : Tolerance V := by
  classical
  exact Tolerance.ofReport report

theorem observer_indistinguishable {V W : Type} (report : V → W) (first second : V) :
    (observer report).Indistinguishable first second ↔ report first = report second := by
  classical
  exact Tolerance.ofReport_indistinguishable report first second

theorem observer_apart {V W : Type} (report : V → W) (first second : V) :
    (observer report).Apart first second ↔ report first ≠ report second := by
  constructor
  · intro apart same
    exact (Tolerance.not_apart_iff_indistinguishable _ _ _).mpr
      ((observer_indistinguishable report first second).mpr same) apart
  · intro different
    by_contra notApart
    exact different ((observer_indistinguishable report first second).mp
      ((Tolerance.not_apart_iff_indistinguishable _ _ _).mp notApart))

/-- **Factoring is coarsening**: an observer whose report is a function of
another's distinguishes no more. -/
theorem observer_extends_of_factors {V W W' : Type} {fine : V → W} {coarse : V → W'}
    (factors : Factors fine coarse) : (observer fine).Extends (observer coarse) := by
  classical
  intro first second
  change (if fine first = fine second then (1 : ℚ) else 0) ≤
    (if coarse first = coarse second then 1 else 0)
  by_cases same : fine first = fine second
  · rw [if_pos same, if_pos (factors.constantOnFibers first second same)]
  · rw [if_neg same]
    split_ifs <;> norm_num

namespace RuleSignature

variable {J : Type} {P : RuleSignature J} (finitary : P.Finitary)

/-- **Native refines judgments as types.** -/
theorem Finitary.native_refines_framework :
    (observer fun claim : P.Claim => claim).Extends (observer finitary.frameworkReport) :=
  observer_extends_of_factors finitary.frameworkReport_factors_native

/-- For the rules-as-constants encoding the refinement is an equality of
distinctions: the framework observer distinguishes whatever the native one
does. -/
theorem Finitary.framework_refines_native :
    (observer finitary.frameworkReport).Extends (observer fun claim : P.Claim => claim) :=
  observer_extends_of_factors finitary.native_factors_frameworkReport

/-- **Judgments as types refines shallow.** -/
theorem framework_refines_shallow {Point : Type v} {holds : Point → J → Prop}
    (sound : LocallySound holds P) :
    (observer finitary.frameworkReport).Extends (observer (shallowReport finitary sound)) :=
  observer_extends_of_factors (shallowReport_factors_framework finitary sound)

end RuleSignature

/-! ## The worked logic -/

/-- The claim of `p ➝ p` by the short derivation. -/
def identityClaim : intSignature.Claim := ⟨_, identityProof (.atom 0)⟩

/-- The claim of `p ➝ p` by the long derivation. -/
def detourClaim : intSignature.Claim := ⟨_, detourProof (.atom 0)⟩

theorem identityClaim_ne_detourClaim : identityClaim ≠ detourClaim := fun same =>
  identityProof_ne_detourProof (.atom 0) (eq_of_heq (Sigma.mk.inj_iff.mp same).2)

/-- **A fibre of the shallow report**: two different claims that the Kripke
embedding does not tell apart. -/
noncomputable def shallowReport_fibre :
    NonTrivialFiber (RuleSignature.shallowReport intFinitary kripke_locallySound)
      (fun claim : intSignature.Claim => claim) :=
  intSignature.fibreOfIdentified _ (identityProof_ne_detourProof (.atom 0)) trivial

/-- **The size of a derivation is not a function of the shallow report.** -/
theorem size_not_factors_shallowReport :
    ¬ Factors (RuleSignature.shallowReport intFinitary kripke_locallySound)
      (fun claim : intSignature.Claim => RuleSignature.size intFinitary claim.2) :=
  NonTrivialFiber.not_factors
    { left := identityClaim
      right := detourClaim
      sameShadow := (RuleSignature.shallowReport_eq_iff intFinitary kripke_locallySound _ _).mpr rfl
      differentValue := by
        change RuleSignature.size intFinitary (identityProof (.atom 0)) ≠
          RuleSignature.size intFinitary (detourProof (.atom 0))
        rw [size_identityProof, size_detourProof]
        decide }

/-- The framework report tells the two claims apart. -/
theorem frameworkReport_identity_ne_detour :
    intFinitary.frameworkReport identityClaim ≠ intFinitary.frameworkReport detourClaim :=
  fun same => identityClaim_ne_detourClaim (intFinitary.frameworkReport_injective same)

/-- **The two derivations of `p ➝ p` under the three observers**: apart
natively and for judgments as types, indistinguishable shallowly. -/
theorem identity_detour_observed :
    (observer fun claim : intSignature.Claim => claim).Apart identityClaim detourClaim ∧
      (observer intFinitary.frameworkReport).Apart identityClaim detourClaim ∧
        (observer (RuleSignature.shallowReport intFinitary kripke_locallySound)).Indistinguishable
          identityClaim detourClaim :=
  ⟨(observer_apart _ _ _).mpr identityClaim_ne_detourClaim,
    (observer_apart _ _ _).mpr frameworkReport_identity_ne_detour,
    (observer_indistinguishable _ _ _).mpr
      ((RuleSignature.shallowReport_eq_iff intFinitary kripke_locallySound _ _).mpr rfl)⟩

/-! ## The computing encoding -/

/-- **A fibre of the computing encoding's report**: two different derivations
that the framework's conversion identifies. -/
noncomputable def computingReport_fibre :
    NonTrivialFiber (minimalSignature.report computingMap)
      (fun claim : minimalSignature.Claim => claim) :=
  minimalSignature.fibreOfIdentified computingMap (discardTower_ne (.atom 0) 0)
    (discardTower_conv (.atom 0) 1)

/-- **The size of a derivation is not a function of the computing encoding's
report.** -/
theorem size_not_factors_computingReport :
    ¬ Factors (minimalSignature.report computingMap)
      (fun claim : minimalSignature.Claim => RuleSignature.size minimalFinitary claim.2) :=
  NonTrivialFiber.not_factors
    { left := ⟨_, discardTower (.atom 0) 1⟩
      right := ⟨_, minIdentity (.atom 0)⟩
      sameShadow := congrArg (Sigma.mk _) (Quotient.sound (discardTower_conv (.atom 0) 1))
      differentValue := by
        change RuleSignature.size minimalFinitary (discardTower (.atom 0) 1) ≠
          RuleSignature.size minimalFinitary (minIdentity (.atom 0))
        rw [size_discardTower, size_minIdentity]
        decide }

#print axioms RuleSignature.hosting_iff_report_injective
#print axioms RuleSignature.Finitary.native_factors_frameworkReport
#print axioms RuleSignature.shallowReport_factors_framework
#print axioms RuleSignature.shallowReport_injective_iff
#print axioms observer_extends_of_factors
#print axioms size_not_factors_shallowReport
#print axioms identity_detour_observed
#print axioms size_not_factors_computingReport

end Mettapedia.Logic.HostingStyles
