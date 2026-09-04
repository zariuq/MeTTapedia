import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.TypeTheory.TarskiUniverseCapabilities

/-!
# Tarski code families over observations

An observation of universe levels can preserve the carrier of codes while
failing to preserve what those codes decode to.  A complete factorization of
a Tarski code family therefore has two displayed stages:

1. the code family factors through the level observation; and
2. the decoding family factors through the induced observation on the total
   space of levels and codes.

The second stage is a real semantic obligation.  The negative control has the
same singleton code carrier at two observationally identical levels, but its
unique code decodes to a singleton at one level and a Boolean at the other.
Its code syntax factors; its decoding semantics cannot.

This module does not select a universe hierarchy, cumulativity policy,
self-coding policy, or object-language calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.TarskiUniverseCapabilities

universe uLevel uCode uEl uTarget

/-- A Tarski code family factors through a level observation when both its
code carrier and its decoding family factor through the corresponding
displayed observations. -/
structure CodeDecodingFactorization
    (source : TarskiCodeFamily.{uLevel, uCode, uEl})
    {TargetLevel : Type uTarget}
    (observeLevel : source.Level → TargetLevel) where
  code : FamilyFactorization observeLevel source.Code
  decoding :
    FamilyFactorization code.totalObservation
      (fun point : Sigma source.Code => source.El point.1 point.2)

namespace CodeDecodingFactorization

variable {source : TarskiCodeFamily.{uLevel, uCode, uEl}}
variable {TargetLevel : Type uTarget}
variable {observeLevel : source.Level → TargetLevel}

/-- A full code-and-decoding factorization retains the code-carrier
factorization as its syntactic stage. -/
def codeOnly
    (factorization : CodeDecodingFactorization source observeLevel) :
    FamilyFactorization observeLevel source.Code :=
  factorization.code

/-- Equal observations of level-code pairs force equivalence of their decoded
source types. -/
def decodedFibreEquiv
    (factorization : CodeDecodingFactorization source observeLevel)
    {left right : Sigma source.Code}
    (sameObservation :
      factorization.code.totalObservation left =
        factorization.code.totalObservation right) :
    source.El left.1 left.2 ≃ source.El right.1 right.2 :=
  factorization.decoding.fibreEquiv sameObservation

/-- The total family of a code paired with one decoded inhabitant factors
through the level observation. -/
def decodedSigma
    (factorization : CodeDecodingFactorization source observeLevel) :
    FamilyFactorization observeLevel
      (fun level =>
        Sigma fun code : source.Code level => source.El level code) :=
  factorization.code.dependentSigma factorization.decoding

/-- The family assigning a section through every code at one level also
factors through the level observation. -/
def decodedPi
    (factorization : CodeDecodingFactorization source observeLevel) :
    FamilyFactorization observeLevel
      (fun level =>
        forall code : source.Code level, source.El level code) :=
  factorization.code.dependentPi factorization.decoding

end CodeDecodingFactorization

/-! ## Positive and negative controls -/

namespace Canary

/-- A coarse level observation identifying two source levels. -/
def coarseLevel : Bool → PUnit := fun _ => PUnit.unit

/-- Both levels have one code, and that code always decodes to a singleton. -/
abbrev constantDecoding : TarskiCodeFamily.{0, 0, 0} where
  Level := Bool
  Code := fun _ => PUnit
  El := fun _ _ => PUnit

def constantCodeFactorization :
    FamilyFactorization coarseLevel constantDecoding.Code :=
  FamilyFactorization.constant coarseLevel PUnit

def constantElFactorization :
    FamilyFactorization constantCodeFactorization.totalObservation
      (fun point : Sigma constantDecoding.Code =>
        constantDecoding.El point.1 point.2) :=
  FamilyFactorization.constant
    constantCodeFactorization.totalObservation PUnit

/-- Positive control: constant codes and constant decoding both factor. -/
def constantFactorization :
    CodeDecodingFactorization constantDecoding coarseLevel where
  code := constantCodeFactorization
  decoding := constantElFactorization

/-- The code carrier remains constant, but its unique code has genuinely
different decoding semantics at the two source levels. -/
abbrev varyingDecoding : TarskiCodeFamily.{0, 0, 0} where
  Level := Bool
  Code := fun _ => PUnit
  El := fun level _ => if level then Bool else PUnit

/-- The syntactic code family still factors through the coarse level
observation. -/
def varyingCodeFactors :
    FamilyFactorization coarseLevel varyingDecoding.Code :=
  FamilyFactorization.constant coarseLevel PUnit

/-- Nevertheless no full code-and-decoding factorization exists: the common
target code fibre is a singleton, so the unique codes at the identified
levels must have the same target observation, which would force `PUnit` and
`Bool` to be equivalent. -/
theorem varyingDecoding_does_not_factor :
    ¬ Nonempty
      (CodeDecodingFactorization varyingDecoding coarseLevel) := by
  rintro ⟨factorization⟩
  let left : Sigma varyingDecoding.Code := ⟨false, PUnit.unit⟩
  let right : Sigma varyingDecoding.Code := ⟨true, PUnit.unit⟩
  have sameTargetCode :
      factorization.code.identify false PUnit.unit =
        factorization.code.identify true PUnit.unit := by
    apply (factorization.code.identify false).symm.injective
    exact Subsingleton.elim _ _
  have sameObservation :
      factorization.code.totalObservation left =
        factorization.code.totalObservation right := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq sameTargetCode
  have impossible : PUnit ≃ Bool := by
    simpa [left, right, varyingDecoding] using
      factorization.decodedFibreEquiv sameObservation
  exact
    DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool
      ⟨impossible⟩

/-- Paired semantic boundary: code-carrier factorization is inhabited for the
varying example while code-and-decoding factorization is impossible. -/
theorem code_syntax_does_not_determine_decoding_factorization :
    Nonempty
        (FamilyFactorization coarseLevel varyingDecoding.Code) ∧
      ¬ Nonempty
        (CodeDecodingFactorization varyingDecoding coarseLevel) :=
  ⟨⟨varyingCodeFactors⟩, varyingDecoding_does_not_factor⟩

/-- Positive compositional control: a full factorization yields actual Pi and
Sigma factorizations of the decoded families. -/
theorem constant_decoding_pi_sigma_control :
    Nonempty
        (FamilyFactorization coarseLevel
          (fun level =>
            Sigma fun code : constantDecoding.Code level =>
              constantDecoding.El level code)) ∧
      Nonempty
        (FamilyFactorization coarseLevel
          (fun level =>
            forall code : constantDecoding.Code level,
              constantDecoding.El level code)) :=
  ⟨⟨constantFactorization.decodedSigma⟩,
    ⟨constantFactorization.decodedPi⟩⟩

end Canary

#print axioms CodeDecodingFactorization.decodedFibreEquiv
#print axioms CodeDecodingFactorization.decodedSigma
#print axioms CodeDecodingFactorization.decodedPi
#print axioms Canary.varyingDecoding_does_not_factor
#print axioms Canary.code_syntax_does_not_determine_decoding_factorization
#print axioms Canary.constant_decoding_pi_sigma_control

end Mettapedia.TypeTheory.TarskiCodeFamilyObserverFactorization
