import Mettapedia.TypeTheory.FamilyEnclosingUniverseTower
import Mettapedia.TypeTheory.TarskiClosureRankObstruction
import Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mathlib.SetTheory.Cardinal.Defs

/-!
# Cumulative formation routes need code-level coherence

Forming a dependent product or sum and then lifting its code, versus lifting
its input codes before formation, always yields equivalent decoded carriers
in the existing enclosing tower. Its interface does not require the resulting
codes to be equal.

A full-interface tag adapter makes the distinction explicit. It retains every
original enclosing/closure operation and exactly the projected decoding, but
uses different tags for fibre-code lifts and Pi/Sigma formation. Applied to
any independently supplied small operator, it produces another small operator
whose two formation routes have different codes at every successor edge.

A semantic motive into the same lower universe chooses its unit or empty code
by that tag. Its fibres on the two routes are not equivalent, so it cannot
factor through any observation identifying those routes. Decoded cardinality
is one explicit such observation, justified by the actual decoding equivalence.

This is non-entailment of code/motive coherence from the current interface.
The arbitrary semantic motive is not claimed to be definable or admitted in
the native language. No native unsoundness, necessary observer policy, full
model existence, or change of assembly/profile follows from this result.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiCumulativeCodeCoherenceBoundary

open FamilyEnclosingUniverse UniverseClosureProfiles TarskiUniverseCapabilities
open TarskiDecodedFamilyCoherence DependentFamilyObserverFactorization

universe uCode uEl u uObservation

/-! ## A closure-preserving tag adapter, not a new universe model -/

/-- Fibre codes use true; ordinary type formers use false. All original
decoding equivalences and full dependent closure are preserved by projection.
The selected family and its genuinely dependent fibres are unchanged. -/
def tagEnvelope {A : Type uEl} {B : A → Type uEl}
    (original : ClosedTarskiUniverseOver.{uCode, uEl} A B) :
    ClosedTarskiUniverseOver.{uCode, uEl} A B where
  Code := Bool × original.Code
  El code := original.El code.2
  baseCode := (true, original.baseCode)
  elBase := original.elBase
  fibreCode index := (true, original.fibreCode index)
  elFibre := original.elFibre
  emptyCode := (false, original.emptyCode)
  elEmpty := original.elEmpty
  unitCode := (false, original.unitCode)
  elUnit := original.elUnit
  natCode := (false, original.natCode)
  elNat := original.elNat
  sumCode left right := (false, original.sumCode left.2 right.2)
  elSum left right := original.elSum left.2 right.2
  piCode domain codomain := (false, original.piCode domain.2 (fun value => (codomain value).2))
  elPi domain codomain := original.elPi domain.2 (fun value => (codomain value).2)
  sigmaCode domain codomain :=
    (false, original.sigmaCode domain.2 (fun value => (codomain value).2))
  elSigma domain codomain := original.elSigma domain.2 (fun value => (codomain value).2)
  identityCode domain left right := (false, original.identityCode domain.2 left right)
  elIdentity domain left right := original.elIdentity domain.2 left right
  wCode shape position := (false, original.wCode shape.2 (fun value => (position value).2))
  elW shape position := original.elW shape.2 (fun value => (position value).2)

/-- This transformation uses a supplied operator; it does not manufacture
an inhabitant of the small-operator interface. -/
def tagOperator (operator : SmallFamilyEnclosingUniverseOperator.{u}) :
    SmallFamilyEnclosingUniverseOperator.{u} where
  enclose A B := tagEnvelope (operator.enclose A B)

/-- The retained tag changes no decoded carrier of the original envelope. -/
theorem tag_decoding {A : Type uEl} {B : A → Type uEl}
    (original : ClosedTarskiUniverseOver.{uCode, uEl} A B)
    (tag : Bool) (code : original.Code) :
    (tagEnvelope original).El (tag, code) = original.El code := rfl

/-! ## The two actual semantic formation routes -/

namespace Routes

variable (operator : SmallFamilyEnclosingUniverseOperator.{u})
variable (A : Type u) (B : A → Type u)
variable (level : Nat)
variable (domain : (FamilyEnclosingUniverseTower.family operator A B).Code level)
variable (codomain : (FamilyEnclosingUniverseTower.family operator A B).El level domain →
  (FamilyEnclosingUniverseTower.family operator A B).Code level)

def liftedPi : (FamilyEnclosingUniverseTower.family operator A B).Code (level + 1) :=
  FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level)
    (FamilyEnclosingUniverseTower.piCode operator A B level domain codomain)

def liftedSigma : (FamilyEnclosingUniverseTower.family operator A B).Code (level + 1) :=
  FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level)
    (FamilyEnclosingUniverseTower.sigmaCode operator A B level domain codomain)

/-- The existing mixed-level operation, with its actual dependent argument
reindexing through decodeLift. -/
def upperPi : PiCoding (FamilyEnclosingUniverseTower.family operator A B)
    level level (level + 1) :=
  (show PiCoding (FamilyEnclosingUniverseTower.family operator A B)
      (level + 1) (level + 1) (level + 1) from
    ⟨FamilyEnclosingUniverseTower.piCode operator A B (level + 1),
      FamilyEnclosingUniverseTower.decodePi operator A B (level + 1)⟩).mapInputs
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level))

def upperSigma : SigmaCoding (FamilyEnclosingUniverseTower.family operator A B)
    level level (level + 1) :=
  (show SigmaCoding (FamilyEnclosingUniverseTower.family operator A B)
      (level + 1) (level + 1) (level + 1) from
    ⟨FamilyEnclosingUniverseTower.sigmaCode operator A B (level + 1),
      FamilyEnclosingUniverseTower.decodeSigma operator A B (level + 1)⟩).mapInputs
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.liftCode operator A B (Nat.le_succ level))
    (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level))

/-- Both routes decode to the same full dependent function space. -/
def piAgreement :
    (FamilyEnclosingUniverseTower.family operator A B).El (level + 1)
        (liftedPi operator A B level domain codomain) ≃
      (FamilyEnclosingUniverseTower.family operator A B).El (level + 1)
        ((upperPi operator A B level).code domain codomain) :=
  (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level)
    (FamilyEnclosingUniverseTower.piCode operator A B level domain codomain)).trans
      ((FamilyEnclosingUniverseTower.decodePi operator A B level domain codomain).trans
        ((upperPi operator A B level).decode domain codomain).symm)

def sigmaAgreement :
    (FamilyEnclosingUniverseTower.family operator A B).El (level + 1)
        (liftedSigma operator A B level domain codomain) ≃
      (FamilyEnclosingUniverseTower.family operator A B).El (level + 1)
        ((upperSigma operator A B level).code domain codomain) :=
  (FamilyEnclosingUniverseTower.decodeLift operator A B (Nat.le_succ level)
    (FamilyEnclosingUniverseTower.sigmaCode operator A B level domain codomain)).trans
      ((FamilyEnclosingUniverseTower.decodeSigma operator A B level domain codomain).trans
        ((upperSigma operator A B level).decode domain codomain).symm)

end Routes

/-! ## A conditional full-interface counterexample, at every successor edge -/

variable (operator : SmallFamilyEnclosingUniverseOperator.{u})
variable (A : Type u) (B : A → Type u)
variable (level : Nat)
variable (domain : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code level)
variable (codomain :
  (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El level domain →
    (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code level)

theorem pi_route_tags :
    (Routes.liftedPi (tagOperator operator) A B level domain codomain).1 = true ∧
      ((Routes.upperPi (tagOperator operator) A B level).code domain codomain).1 = false := by
  constructor
  · rw [Routes.liftedPi, FamilyEnclosingUniverseTower.liftCode_successor]
    rfl
  · rfl

theorem sigma_route_tags :
    (Routes.liftedSigma (tagOperator operator) A B level domain codomain).1 = true ∧
      ((Routes.upperSigma (tagOperator operator) A B level).code domain codomain).1 = false := by
  constructor
  · rw [Routes.liftedSigma, FamilyEnclosingUniverseTower.liftCode_successor]
    rfl
  · rfl

theorem pi_routes_ne :
    Routes.liftedPi (tagOperator operator) A B level domain codomain ≠
      (Routes.upperPi (tagOperator operator) A B level).code domain codomain := by
  intro equal
  have tags := congrArg Prod.fst equal
  rw [(pi_route_tags operator A B level domain codomain).1,
    (pi_route_tags operator A B level domain codomain).2] at tags
  cases tags

theorem sigma_routes_ne :
    Routes.liftedSigma (tagOperator operator) A B level domain codomain ≠
      (Routes.upperSigma (tagOperator operator) A B level).code domain codomain := by
  intro equal
  have tags := congrArg Prod.fst equal
  rw [(sigma_route_tags operator A B level domain codomain).1,
    (sigma_route_tags operator A B level domain codomain).2] at tags
  cases tags

/-- The motive returns actual codes in the same lower universe. This is an
arbitrary semantic family, not an asserted native term defining a tag test. -/
def motiveCode
    (code : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1)) :
    (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code level :=
  if code.1 then (FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).unitCode
  else (FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).emptyCode

def motive
    (code : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1)) :
    Type u :=
  (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El level
    (motiveCode operator A B level code)

private theorem motive_fibres_ne
    (left right : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1))
    (leftTag : left.1 = true) (rightTag : right.1 = false) :
    ¬ Nonempty (motive operator A B level left ≃ motive operator A B level right) := by
  rintro ⟨equivalence⟩
  have source : motive operator A B level left := by
    simp only [motive, motiveCode, leftTag, ↓reduceIte]
    exact (FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).elUnit.symm
      PUnit.unit
  have target := equivalence source
  simp only [motive, motiveCode, rightTag, Bool.false_eq_true, ↓reduceIte] at target
  exact Empty.elim
    ((FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).elEmpty target)

theorem pi_motive_fibres_not_equivalent :
    ¬ Nonempty
      (motive operator A B level (Routes.liftedPi (tagOperator operator) A B level domain codomain) ≃
        motive operator A B level
          ((Routes.upperPi (tagOperator operator) A B level).code domain codomain)) :=
  motive_fibres_ne operator A B level _ _
    (pi_route_tags operator A B level domain codomain).1
    (pi_route_tags operator A B level domain codomain).2

theorem sigma_motive_fibres_not_equivalent :
    ¬ Nonempty
      (motive operator A B level (Routes.liftedSigma (tagOperator operator) A B level domain codomain) ≃
        motive operator A B level
          ((Routes.upperSigma (tagOperator operator) A B level).code domain codomain)) :=
  motive_fibres_ne operator A B level _ _
    (sigma_route_tags operator A B level domain codomain).1
    (sigma_route_tags operator A B level domain codomain).2

/-- Any observation identifying the routes loses this dependent semantic
family, even when it retains their decoded carriers up to equivalence. -/
theorem pi_motive_no_factorization {Observation : Type uObservation}
    (observe : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1) →
      Observation)
    (identifies : observe (Routes.liftedPi (tagOperator operator) A B level domain codomain) =
      observe ((Routes.upperPi (tagOperator operator) A B level).code domain codomain)) :
    ¬ Nonempty (FamilyFactorization observe (motive operator A B level)) :=
  FamilyFactorization.not_nonempty_of_nonEquivalent_fibres identifies
    (pi_motive_fibres_not_equivalent operator A B level domain codomain)

theorem sigma_motive_no_factorization {Observation : Type uObservation}
    (observe : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1) →
      Observation)
    (identifies : observe (Routes.liftedSigma (tagOperator operator) A B level domain codomain) =
      observe ((Routes.upperSigma (tagOperator operator) A B level).code domain codomain)) :
    ¬ Nonempty (FamilyFactorization observe (motive operator A B level)) :=
  FamilyFactorization.not_nonempty_of_nonEquivalent_fibres identifies
    (sigma_motive_fibres_not_equivalent operator A B level domain codomain)

/-- A concrete observation of decoded carriers up to their cardinality.
This observer is not adopted as a native semantic or evaluation policy. -/
def decodedCardinality
    (code : (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).Code (level + 1)) :
    Cardinal.{u} :=
  Cardinal.mk ((FamilyEnclosingUniverseTower.family (tagOperator operator) A B).El (level + 1) code)

theorem pi_motive_no_decodedCardinality_factorization :
    ¬ Nonempty (FamilyFactorization (decodedCardinality operator A B level)
      (motive operator A B level)) := by
  let natural := (FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).natCode
  exact pi_motive_no_factorization operator A B level natural (fun _ => natural) _
    (Cardinal.mk_congr
      (Routes.piAgreement (tagOperator operator) A B level natural (fun _ => natural)))

theorem sigma_motive_no_decodedCardinality_factorization :
    ¬ Nonempty (FamilyFactorization (decodedCardinality operator A B level)
      (motive operator A B level)) := by
  let natural := (FamilyEnclosingUniverseTower.envelope (tagOperator operator) A B level).natCode
  exact sigma_motive_no_factorization operator A B level natural (fun _ => natural) _
    (Cardinal.mk_congr
      (Routes.sigmaAgreement (tagOperator operator) A B level natural (fun _ => natural)))

/-- The counter-operator retains the entire enclosing interface, full
formation/closure package, and derived predicative ranks. The obstruction
therefore is not caused by deleting an existing universe capability. -/
theorem counter_tower_retains_closure_and_ranks :
    (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).PiClosed ∧
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).SigmaClosed ∧
      (FamilyEnclosingUniverseTower.family (tagOperator operator) A B).PredicativeRanks ∧
      (∀ level : Nat, Nonempty (UniverseEmbedding
        (TarskiUniverseEmbedding.universeAt
          (FamilyEnclosingUniverseTower.family (tagOperator operator) A B) (level + 1))
        (TarskiUniverseEmbedding.universeAt
          (FamilyEnclosingUniverseTower.family (tagOperator operator) A B) level))) :=
  ⟨FamilyEnclosingUniverseTower.piClosed (tagOperator operator) A B,
    FamilyEnclosingUniverseTower.sigmaClosed (tagOperator operator) A B,
    TarskiClosureRankObstruction.tower_predicativeRanks (tagOperator operator) A B,
    fun level => ⟨FamilyEnclosingUniverseTower.successorEmbedding (tagOperator operator) A B level⟩⟩

#print axioms tagEnvelope
#print axioms tagOperator
#print axioms Routes.piAgreement
#print axioms Routes.sigmaAgreement
#print axioms pi_routes_ne
#print axioms sigma_routes_ne
#print axioms pi_motive_fibres_not_equivalent
#print axioms sigma_motive_fibres_not_equivalent
#print axioms pi_motive_no_decodedCardinality_factorization
#print axioms sigma_motive_no_decodedCardinality_factorization
#print axioms counter_tower_retains_closure_and_ranks

end Mettapedia.TypeTheory.TarskiCumulativeCodeCoherenceBoundary
