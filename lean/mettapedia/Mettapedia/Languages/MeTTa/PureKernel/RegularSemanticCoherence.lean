import Mettapedia.Languages.MeTTa.PureKernel.RegularSemanticUniverse

/-!
# Conversion coherence for the regular semantic universe

The semantic universe retains contextual candidates rather than erasing them
to normalization.  A fundamental lemma therefore needs a coherence theorem:
convertible semantic type codes must select extensionally equivalent meanings.

This module builds the exact infrastructure for that theorem.  Constructor
heads are invariant under conversion, dependent-function and dependent-pair
codes inherit the existing Church--Rosser injectivity theorems, and equivalent
domain meanings induce the identity substitution between their contextual
extensions.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.Confluence

/-! ## Constructor-head coherence -/

/-- The four code constructors interpreted by the present semantic universe.
All other term heads are intentionally outside this finite observation. -/
def semanticCodeHead : PureTm n → Option Nat
  | .u0 => some 0
  | .pi _ _ => some 1
  | .sigma _ _ => some 2
  | .id _ _ _ => some 3
  | .u1 => some 4
  | _ => none

/-- Reduction cannot change an observed semantic code constructor head. -/
theorem semanticCodeHead_red {source target : PureTm n}
    (step : Red source target) {head : Nat}
    (observed : semanticCodeHead source = some head) :
    semanticCodeHead target = some head := by
  cases step <;> simp [semanticCodeHead] at observed ⊢
  all_goals assumption

/-- Finite reduction cannot change an observed semantic code constructor
head. -/
theorem semanticCodeHead_redStar {source target : PureTm n}
    (steps : RedStar source target) {head : Nat}
    (observed : semanticCodeHead source = some head) :
    semanticCodeHead target = some head := by
  induction steps with
  | refl => exact observed
  | tail earlier finalStep ih =>
      exact semanticCodeHead_red finalStep ih

/-- Church--Rosser makes the observed constructor head invariant under
conversion. -/
theorem semanticCodeHead_eq_of_conv
    {left right : PureTm n} {leftHead rightHead : Nat}
    (leftObserved : semanticCodeHead left = some leftHead)
    (rightObserved : semanticCodeHead right = some rightHead)
    (conversion : Conv left right) : leftHead = rightHead := by
  rcases church_rosser_conv conversion with ⟨common, leftSteps, rightSteps⟩
  have leftCommon := semanticCodeHead_redStar leftSteps leftObserved
  have rightCommon := semanticCodeHead_redStar rightSteps rightObserved
  exact Option.some.inj (leftCommon.symm.trans rightCommon)

/-! ## Candidate congruence at a fixed dependent base -/

/-- Dependent function formation respects extensional equivalence of its
codomain candidate when the domain candidate is fixed. -/
theorem ContextualCandidateType.pi_codomain_equivalent
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    {left right : ContextualCandidateType
      (context.extendContextual domain)}
    (equivalent : left.Equivalent right) :
    (domain.pi left).Equivalent (domain.pi right) := by
  intro m environment function
  constructor
  · intro covered k rho argument argumentCovered
    exact (equivalent
      (consSub argument (renameEnvironment rho environment))
      (.app (rename rho function) argument)).1
        (covered rho argument argumentCovered)
  · intro covered k rho argument argumentCovered
    exact (equivalent
      (consSub argument (renameEnvironment rho environment))
      (.app (rename rho function) argument)).2
        (covered rho argument argumentCovered)

/-- Dependent pair formation respects extensional equivalence of its codomain
candidate when the domain candidate is fixed. -/
theorem ContextualCandidateType.sigma_codomain_equivalent
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    {left right : ContextualCandidateType
      (context.extendContextual domain)}
    (equivalent : left.Equivalent right) :
    (domain.sigma left).Equivalent (domain.sigma right) := by
  intro m environment pair
  constructor
  · intro covered
    exact ⟨covered.1,
      (equivalent (consSub (.fst pair) environment) (.snd pair)).1 covered.2⟩
  · intro covered
    exact ⟨covered.1,
      (equivalent (consSub (.fst pair) environment) (.snd pair)).2 covered.2⟩

/-! ## Meaning coherence under conversion -/

namespace SemanticType

/-- Convertible semantic type codes select extensionally equivalent candidate
meanings.  Dependent codomains are compared after pulling the right-hand
meaning across the semantic identity map induced by domain equivalence. -/
theorem meaning_equivalent_of_conv
    {context : CoherentCandidateContext n}
    {left right : PureTm n}
    {leftMeaning rightMeaning : ContextualCandidateType context}
    (leftSemantic : SemanticType context left leftMeaning)
    (rightSemantic : SemanticType context right rightMeaning)
    (conversion : Conv left right) :
    leftMeaning.Equivalent rightMeaning := by
  induction leftSemantic with
  | u0 =>
      induction rightSemantic with
      | u0 => exact ContextualCandidateType.Equivalent.refl _
      | pi =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 0) (rightHead := 1) rfl rfl conversion
          omega
      | sigma =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 0) (rightHead := 2) rfl rfl conversion
          omega
      | identity =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 0) (rightHead := 3) rfl rfl conversion
          omega
      | convert sourceSemantic rightConversion rightIH =>
          exact rightIH (Relation.EqvGen.trans _ _ _ conversion
            (Relation.EqvGen.symm _ _ rightConversion.converts.toConv))
  | @pi nPi contextPi leftDomainCode leftCodomainCode leftDomain leftCodomain
      leftDomainSemantic leftCodomainSemantic domainIH codomainIH =>
      induction rightSemantic with
      | u0 =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 1) (rightHead := 0) rfl rfl conversion
          omega
      | @pi _ _ rightDomainCode rightCodomainCode rightDomain rightCodomain
          rightDomainSemantic rightCodomainSemantic _ _ =>
          have componentConversions := pi_injectivity conversion
          have domainEquivalent : leftDomain.Equivalent rightDomain :=
            domainIH rightDomainSemantic componentConversions.1
          have domainPullback : leftDomain.Equivalent
              (rightDomain.reindex (SemanticSubstitution.id _).maps) :=
            ContextualCandidateType.Equivalent.trans domainEquivalent
              (ContextualCandidateType.Equivalent.symm
                (ContextualCandidateType.reindex_id_equivalent rightDomain))
          let lifted := SemanticSubstitution.lift rightDomain leftDomain
            (SemanticSubstitution.id _) domainPullback
          rcases rightCodomainSemantic.subst_exists lifted with
            ⟨pulledCodomain, pulledSemantic, pulledEquivalent⟩
          have pulledSemantic' : SemanticType _ rightCodomainCode
              pulledCodomain := by
            simpa only [liftSub_ids, subst_ids] using pulledSemantic
          have codomainEquivalent : leftCodomain.Equivalent pulledCodomain :=
            codomainIH pulledSemantic' componentConversions.2
          have sameDomain : (leftDomain.pi leftCodomain).Equivalent
              (leftDomain.pi pulledCodomain) :=
            leftDomain.pi_codomain_equivalent codomainEquivalent
          have assembled : (leftDomain.pi pulledCodomain).Equivalent
              ((rightDomain.pi rightCodomain).reindex
                (SemanticSubstitution.id _).maps) :=
            SemanticSubstitution.reindex_pi_equivalent
              rightDomain leftDomain rightCodomain pulledCodomain
              (SemanticSubstitution.id _)
              domainPullback pulledEquivalent
          intro m environment function
          exact (sameDomain environment function).trans
            ((assembled environment function).trans
              (ContextualCandidateType.reindex_id_equivalent
                (rightDomain.pi rightCodomain) environment function))
      | sigma =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 1) (rightHead := 2) rfl rfl conversion
          omega
      | identity =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 1) (rightHead := 3) rfl rfl conversion
          omega
      | @convert nRight contextRight sourceRight targetRight meaningRight
          rightSourceSemantic rightConversion rightSourceIH =>
          exact rightSourceIH leftDomainSemantic leftCodomainSemantic domainIH
            codomainIH (Relation.EqvGen.trans _ _ _ conversion
              (Relation.EqvGen.symm _ _ rightConversion.converts.toConv))
  | @sigma nSigma contextSigma leftDomainCode leftCodomainCode leftDomain leftCodomain
      leftDomainSemantic leftCodomainSemantic domainIH codomainIH =>
      induction rightSemantic with
      | u0 =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 2) (rightHead := 0) rfl rfl conversion
          omega
      | pi =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 2) (rightHead := 1) rfl rfl conversion
          omega
      | @sigma _ _ rightDomainCode rightCodomainCode rightDomain rightCodomain
          rightDomainSemantic rightCodomainSemantic _ _ =>
          have componentConversions := sigma_injectivity conversion
          have domainEquivalent : leftDomain.Equivalent rightDomain :=
            domainIH rightDomainSemantic componentConversions.1
          have domainPullback : leftDomain.Equivalent
              (rightDomain.reindex (SemanticSubstitution.id _).maps) :=
            ContextualCandidateType.Equivalent.trans domainEquivalent
              (ContextualCandidateType.Equivalent.symm
                (ContextualCandidateType.reindex_id_equivalent rightDomain))
          let lifted := SemanticSubstitution.lift rightDomain leftDomain
            (SemanticSubstitution.id _) domainPullback
          rcases rightCodomainSemantic.subst_exists lifted with
            ⟨pulledCodomain, pulledSemantic, pulledEquivalent⟩
          have pulledSemantic' : SemanticType _ rightCodomainCode
              pulledCodomain := by
            simpa only [liftSub_ids, subst_ids] using pulledSemantic
          have codomainEquivalent : leftCodomain.Equivalent pulledCodomain :=
            codomainIH pulledSemantic' componentConversions.2
          have sameDomain : (leftDomain.sigma leftCodomain).Equivalent
              (leftDomain.sigma pulledCodomain) :=
            leftDomain.sigma_codomain_equivalent codomainEquivalent
          have assembled : (leftDomain.sigma pulledCodomain).Equivalent
              ((rightDomain.sigma rightCodomain).reindex
                (SemanticSubstitution.id _).maps) :=
            SemanticSubstitution.reindex_sigma_equivalent
              rightDomain leftDomain rightCodomain pulledCodomain
              (SemanticSubstitution.id _)
              domainPullback pulledEquivalent
          intro m environment pair
          exact (sameDomain environment pair).trans
            ((assembled environment pair).trans
              (ContextualCandidateType.reindex_id_equivalent
                (rightDomain.sigma rightCodomain) environment pair))
      | identity =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 2) (rightHead := 3) rfl rfl conversion
          omega
      | @convert nRight contextRight sourceRight targetRight meaningRight
          rightSourceSemantic rightConversion rightSourceIH =>
          exact rightSourceIH leftDomainSemantic leftCodomainSemantic domainIH
            codomainIH (Relation.EqvGen.trans _ _ _ conversion
              (Relation.EqvGen.symm _ _ rightConversion.converts.toConv))
  | @identity nId contextId typeCodeId leftId rightId typeId
      typeSemanticId leftSemanticId rightSemanticId typeIHId =>
      induction rightSemantic with
      | u0 =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 3) (rightHead := 0) rfl rfl conversion
          omega
      | pi =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 3) (rightHead := 1) rfl rfl conversion
          omega
      | sigma =>
          have heads := semanticCodeHead_eq_of_conv
            (leftHead := 3) (rightHead := 2) rfl rfl conversion
          omega
      | identity => exact ContextualCandidateType.Equivalent.refl _
      | @convert nRight contextRight sourceRight targetRight meaningRight
          rightSourceSemantic rightConversion rightSourceIH =>
          exact rightSourceIH typeSemanticId leftSemanticId rightSemanticId
            typeIHId (Relation.EqvGen.trans _ _ _ conversion
              (Relation.EqvGen.symm _ _ rightConversion.converts.toConv))
  | convert sourceSemantic leftConversion leftIH =>
      exact leftIH rightSemantic (Relation.EqvGen.trans _ _ _
        leftConversion.converts.toConv conversion)

/-- Candidate meaning is unique up to extensional equivalence for a fixed
semantic type code. -/
theorem meaning_unique
    {context : CoherentCandidateContext n} {code : PureTm n}
    {left right : ContextualCandidateType context}
    (leftSemantic : SemanticType context code left)
    (rightSemantic : SemanticType context code right) :
    left.Equivalent right :=
  meaning_equivalent_of_conv leftSemantic rightSemantic (.refl code)

/-- No interpreted type code is convertible to the untyped top sort.  This is
the semantic form of predicativity used to distinguish formation judgments
from ordinary term judgments in the fundamental lemma. -/
theorem not_conv_u1
    {context : CoherentCandidateContext n} {code : PureTm n}
    {meaning : ContextualCandidateType context}
    (semantic : SemanticType context code meaning) : ¬ Conv code .u1 := by
  induction semantic with
  | u0 =>
      intro conversion
      have heads := semanticCodeHead_eq_of_conv
        (leftHead := 0) (rightHead := 4) rfl rfl conversion
      omega
  | pi _ _ domainIH codomainIH =>
      intro conversion
      have heads := semanticCodeHead_eq_of_conv
        (leftHead := 1) (rightHead := 4) rfl rfl conversion
      omega
  | sigma _ _ domainIH codomainIH =>
      intro conversion
      have heads := semanticCodeHead_eq_of_conv
        (leftHead := 2) (rightHead := 4) rfl rfl conversion
      omega
  | identity _ _ _ typeIH =>
      intro conversion
      have heads := semanticCodeHead_eq_of_conv
        (leftHead := 3) (rightHead := 4) rfl rfl conversion
      omega
  | convert sourceSemantic semanticConversion sourceIH =>
      intro targetConversion
      exact sourceIH (Relation.EqvGen.trans _ _ _
        semanticConversion.converts.toConv targetConversion)

end SemanticType

/-! ## Axiom audit -/

#print axioms semanticCodeHead_red
#print axioms semanticCodeHead_redStar
#print axioms semanticCodeHead_eq_of_conv
#print axioms ContextualCandidateType.pi_codomain_equivalent
#print axioms ContextualCandidateType.sigma_codomain_equivalent
#print axioms SemanticType.meaning_equivalent_of_conv
#print axioms SemanticType.meaning_unique
#print axioms SemanticType.not_conv_u1

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
