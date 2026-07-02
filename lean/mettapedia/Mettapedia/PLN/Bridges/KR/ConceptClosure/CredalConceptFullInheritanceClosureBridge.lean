import Mettapedia.KR.ConceptOntology.CredalFormation
import Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility

/-!
# Credal Lower-Formed Concept ↔ Full-Inheritance Fixpoint Closure Bridge

This module is the full-strength analogue of
`CredalConceptFixpointClosureBridge`.

The older bridge transports the exact extensional proxy already present in the
generated-table infrastructure. This file instead transports the new
`fullInheritanceStrength` directly through the same WM fixpoint-closure
calculus, so credal concept formation can drive closure/admissibility results
without collapsing back to the older extensional-only slice.
-/

namespace Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.Hyperseed
open scoped ENNReal

universe u v w x y z

section LowerFormedConceptClosure

variable {State : Type u} {Query : Type v} {Obj : Type w} {Attr : Type x}
variable {Q : Type y} {Gate : Type z}
variable [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State] [BinaryWorldModel State Query]
variable [Preorder Q] [Fintype Obj] [Fintype Attr]

/-- A seed family of robust credal inheritance obligations, viewed as ordered
pairs of lower formed subconcepts and superconcepts. -/
abbrev LowerFormedConceptPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M × _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M

/-- Query set obtained by encoding a robust credal seed family into a
world-model query language. -/
def lowerFormedConceptQuerySet
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M)) :
    Set Query :=
  { q | ∃ p : LowerFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 }

@[simp] theorem mem_lowerFormedConceptQuerySet_iff
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (q : Query) :
    q ∈ lowerFormedConceptQuerySet Γ M encode seed ↔
      ∃ p : LowerFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 := by
  rfl

/-- If a query encoding exposes the supported robust lower-formed inheritance
slice at the new full-strength level, and every seed obligation is already
above threshold in that exact full-strength semantics, then the encoded seed
query set is threshold-valid in the world model. -/
theorem thresholdValid_lowerFormedConceptQuerySet_of_exactFullInheritanceStrength
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (lowerFormedConceptQuerySet Γ M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  simpa [hEncode p.1 p.2] using hSeed p hp

/-- The same exact robust seed obligations remain threshold-valid after
closing under any state-indexed WM consequence rule set. -/
theorem leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (lowerFormedConceptQuerySet Γ M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_lowerFormedConceptQuerySet_of_exactFullInheritanceStrength
    (State := State) (Query := Query) Γ M W τ encode seed hEncode hSeed

section Admissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/-- If the available region is covered by the least WM closure of exact robust
lower-formed full-inheritance obligations, then every available query becomes
WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_exactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) :
    availableRegionAt P W B guard ⊆
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure (State := State) (Query := Query) R W
      (lowerFormedConceptQuerySet Γ M encode seed))
  · exact leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed
  · exact hAvail

/-- If the available region is exactly covered by the least WM closure of
exact robust lower-formed full-inheritance obligations, the admissible region
collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_exactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    hAvail
    (leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed)

end Admissibility

end LowerFormedConceptClosure

section UpperFormedConceptClosure

variable {State : Type u} {Query : Type v} {Obj : Type w} {Attr : Type x}
variable {Q : Type y} {Gate : Type z}
variable [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State] [BinaryWorldModel State Query]
variable [Preorder Q] [Fintype Obj] [Fintype Attr]

/-- A seed family of permissive credal inheritance obligations, viewed as
ordered pairs of upper formed subconcepts and superconcepts. -/
abbrev UpperFormedConceptPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M × _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M

/-- Query set obtained by encoding a permissive credal seed family into a
world-model query language. -/
def upperFormedConceptQuerySet
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M)) :
    Set Query :=
  { q | ∃ p : UpperFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 }

@[simp] theorem mem_upperFormedConceptQuerySet_iff
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (q : Query) :
    q ∈ upperFormedConceptQuerySet Γ M encode seed ↔
      ∃ p : UpperFormedConceptPair Γ M, p ∈ seed ∧ q = encode p.1 p.2 := by
  rfl

section LowerToUpperTransport

variable [Fintype Gate] [Nonempty Gate]

/-- Embed a robust lower-formed obligation into the permissive upper-formed
carrier using the canonical lower-to-upper concept transport. -/
def lowerPairToUpperPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :
    LowerFormedConceptPair Γ M → UpperFormedConceptPair Γ M :=
  fun p =>
    (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M p.1,
      _root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M p.2)

/-- The permissive upper seed obtained from a robust lower seed by canonical
lower-to-upper transport. -/
def lowerSeedAsUpper
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (seed : Set (LowerFormedConceptPair Γ M)) :
    Set (UpperFormedConceptPair Γ M) :=
  { pU | ∃ pL : LowerFormedConceptPair Γ M, pL ∈ seed ∧ pU = lowerPairToUpperPair Γ M pL }

omit [Fintype Gate] in
@[simp] theorem mem_lowerSeedAsUpper_iff
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (seed : Set (LowerFormedConceptPair Γ M))
    (pU : UpperFormedConceptPair Γ M) :
    pU ∈ lowerSeedAsUpper Γ M seed ↔
      ∃ pL : LowerFormedConceptPair Γ M, pL ∈ seed ∧ pU = lowerPairToUpperPair Γ M pL := by
  rfl

omit [Fintype Gate] in
/-- If a lower-query encoder is just the upper-query encoder after canonical
lower-to-upper transport, then every encoded robust seed query is present in
the transported permissive seed query set. -/
theorem lowerFormedConceptQuerySet_subset_upperFormedConceptQuerySet_of_liftEncode
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        encodeLower subConcept superConcept =
          encodeUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) :
    lowerFormedConceptQuerySet Γ M encodeLower seed ⊆
      upperFormedConceptQuerySet Γ M encodeUpper (lowerSeedAsUpper Γ M seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  refine ⟨lowerPairToUpperPair Γ M p, ?_, ?_⟩
  · exact ⟨p, hp, rfl⟩
  · exact hEncode p.1 p.2

omit [Fintype Gate] in
/-- The canonical lower-to-upper query-set inclusion is preserved by the same
WM consequence closure. -/
theorem leastRuleClosure_lowerFormedConceptQuerySet_subset_upperFormedConceptQuerySet_of_liftEncode
    (R : RuleSet State Query) (W : State)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        encodeLower subConcept superConcept =
          encodeUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) :
    leastRuleClosure (State := State) (Query := Query) R W
        (lowerFormedConceptQuerySet Γ M encodeLower seed) ⊆
      leastRuleClosure (State := State) (Query := Query) R W
        (upperFormedConceptQuerySet Γ M encodeUpper (lowerSeedAsUpper Γ M seed)) := by
  apply leastRuleClosure_least_of_seed_and_rules
  · intro q hq
    exact seed_subset_leastRuleClosure (State := State) (Query := Query) R W
      (upperFormedConceptQuerySet Γ M encodeUpper (lowerSeedAsUpper Γ M seed))
      (lowerFormedConceptQuerySet_subset_upperFormedConceptQuerySet_of_liftEncode
        Γ M encodeLower encodeUpper seed hEncode hq)
  · intro r hr hside hprem
    exact leastRuleClosure_rule_closed (State := State) (Query := Query) R W
      (upperFormedConceptQuerySet Γ M encodeUpper (lowerSeedAsUpper Γ M seed))
      hr hside hprem

end LowerToUpperTransport

section DeterminedUpperToLowerTransport

/-- A permissively formed concept becomes robustly lower-formed once the
gate-credal process determines its formation gamble.  This is the closure-side
collapse of upper/permissive formation back to lower/robust formation. -/
def upperToLowerFormedConceptOfDetermines
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (A : _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M)
    (hDet :
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M A.1)) :
    _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M := by
  refine ⟨A.1, ?_⟩
  have hNotMixed :
      ¬ (A.1 ∈ _root_.Mettapedia.KR.ConceptOntology.upperConceptFamily Γ M ∧
          A.1 ∉ _root_.Mettapedia.KR.ConceptOntology.lowerConceptFamily Γ M) :=
    (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec_determinesGlobalGamble_conceptFormationGamble_iff
        (Γ := Γ) (M := M) (A := A.1)).1 hDet
  by_contra hNotLower
  exact hNotMixed ⟨A.2, hNotLower⟩

@[simp] theorem upperToLowerFormedConceptOfDetermines_val
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (A : _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M)
    (hDet :
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M A.1)) :
    (upperToLowerFormedConceptOfDetermines Γ M A hDet).1 = A.1 := rfl

/-- Reclassify a permissive upper seed pair as a robust lower seed pair when
both endpoint concepts are determined by the gate-credal process. -/
def upperPairToLowerPairOfDetermines
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (p : UpperFormedConceptPair Γ M)
    (hLeft :
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1))
    (hRight :
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) :
    LowerFormedConceptPair Γ M :=
  (upperToLowerFormedConceptOfDetermines Γ M p.1 hLeft,
    upperToLowerFormedConceptOfDetermines Γ M p.2 hRight)

/-- Lower seed generated by reclassifying every determined permissive upper
seed obligation. -/
def determinedUpperSeedAsLower
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) :
    Set (LowerFormedConceptPair Γ M) :=
  { pL | ∃ pU : UpperFormedConceptPair Γ M, ∃ hp : pU ∈ seed,
      pL = upperPairToLowerPairOfDetermines Γ M pU (hDet pU hp).1 (hDet pU hp).2 }

@[simp] theorem mem_determinedUpperSeedAsLower_iff
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (pL : LowerFormedConceptPair Γ M) :
    pL ∈ determinedUpperSeedAsLower Γ M seed hDet ↔
      ∃ pU : UpperFormedConceptPair Γ M, ∃ hp : pU ∈ seed,
        pL = upperPairToLowerPairOfDetermines Γ M pU (hDet pU hp).1 (hDet pU hp).2 := by
  rfl

/-- If every permissive upper seed obligation is determined, and the upper
query encoder agrees with the lower encoder after reclassification, then the
upper query set embeds into the robust lower query set. -/
theorem upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      encodeUpper p.1 p.2 =
        encodeLower
          (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
          (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) :
    upperFormedConceptQuerySet Γ M encodeUpper seed ⊆
      lowerFormedConceptQuerySet Γ M encodeLower
        (determinedUpperSeedAsLower Γ M seed hDet) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  refine ⟨upperPairToLowerPairOfDetermines Γ M p (hDet p hp).1 (hDet p hp).2, ?_, ?_⟩
  · exact ⟨p, hp, rfl⟩
  · exact hEncode p hp

/-- The determined upper-to-lower reclassification is preserved by the same
WM consequence closure.  Once permissive upper seed concepts are projectively
determined, closing the upper query set cannot escape the corresponding robust
lower closure. -/
theorem leastRuleClosure_upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
    (R : RuleSet State Query) (W : State)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      encodeUpper p.1 p.2 =
        encodeLower
          (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
          (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) :
    leastRuleClosure (State := State) (Query := Query) R W
        (upperFormedConceptQuerySet Γ M encodeUpper seed) ⊆
      leastRuleClosure (State := State) (Query := Query) R W
        (lowerFormedConceptQuerySet Γ M encodeLower
          (determinedUpperSeedAsLower Γ M seed hDet)) := by
  apply leastRuleClosure_least_of_seed_and_rules
  · intro q hq
    exact seed_subset_leastRuleClosure (State := State) (Query := Query) R W
      (lowerFormedConceptQuerySet Γ M encodeLower
        (determinedUpperSeedAsLower Γ M seed hDet))
      (upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
        Γ M encodeUpper encodeLower seed hDet hEncode hq)
  · intro r hr hside hprem
    exact leastRuleClosure_rule_closed (State := State) (Query := Query) R W
      (lowerFormedConceptQuerySet Γ M encodeLower
        (determinedUpperSeedAsLower Γ M seed hDet))
      hr hside hprem

/-- Determined permissive upper seeds inherit robust lower closure validity.

This is the operational collapse theorem for the upper-to-lower transport:
once every permissive seed concept is projectively determined, and its query
encoder agrees with the robust lower encoder after reclassification, threshold
validity of the reclassified lower closure is enough to validate the original
upper closure. -/
theorem leastRuleClosure_thresholdValid_of_determinedUpperExactFullInheritanceStrength
    (R : RuleSet State Query) (W : State)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (τ : ℝ≥0∞)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      encodeUpper p.1 p.2 =
        encodeLower
          (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
          (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (upperFormedConceptQuerySet Γ M encodeUpper seed)) := by
  apply thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    (leastRuleClosure_upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
      (State := State) (Query := Query)
      R W Γ M encodeUpper encodeLower seed hDet hEncode)
  exact
    leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Query)
      R Γ M W τ encodeLower
      (determinedUpperSeedAsLower Γ M seed hDet)
      hLowerEncode hLowerSeed

section DeterminedUpperAdmissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/-- If the available region is covered by the least WM closure of determined
permissive upper obligations, every available query becomes WM-admissible using
the reclassified robust lower exact-strength proof. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_determinedUpperExactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      encodeUpper p.1 p.2 =
        encodeLower
          (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
          (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed)) :
    availableRegionAt P W B guard ⊆
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure (State := State) (Query := Query) R W
      (upperFormedConceptQuerySet Γ M encodeUpper seed))
  · exact
      leastRuleClosure_thresholdValid_of_determinedUpperExactFullInheritanceStrength
        (State := State) (Query := Query)
        R W Γ M τ encodeUpper encodeLower seed hDet hEncode hLowerEncode hLowerSeed
  · exact hAvail

/-- If the available region is covered by the least WM closure of determined
permissive upper obligations, WM-admissibility collapses back to availability
once the reclassified robust lower closure supplies threshold validity. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_determinedUpperExactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encodeUpper :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (encodeLower :
      _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      encodeUpper p.1 p.2 =
        encodeLower
          (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
          (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed)) :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    hAvail
    (leastRuleClosure_thresholdValid_of_determinedUpperExactFullInheritanceStrength
      (State := State) (Query := Query)
      R W Γ M τ encodeUpper encodeLower seed hDet hEncode hLowerEncode hLowerSeed)

end DeterminedUpperAdmissibility

end DeterminedUpperToLowerTransport

/-- If a query encoding exposes the permissive upper-formed inheritance slice
at the full-strength level, and every seed obligation is already above
threshold in that semantics, then the encoded seed query set is threshold-valid
in the world model. -/
theorem thresholdValid_upperFormedConceptQuerySet_of_exactFullInheritanceStrength
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (upperFormedConceptQuerySet Γ M encode seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  simpa [hEncode p.1 p.2] using hSeed p hp

/-- The same permissive upper-formed seed obligations remain threshold-valid
after closing under any state-indexed WM consequence rule set. -/
theorem leastRuleClosure_thresholdValid_of_upperExactFullInheritanceStrength
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W
        (upperFormedConceptQuerySet Γ M encode seed)) := by
  apply leastRuleClosure_thresholdValid
  exact thresholdValid_upperFormedConceptQuerySet_of_exactFullInheritanceStrength
    (State := State) (Query := Query) Γ M W τ encode seed hEncode hSeed

section Admissibility

variable {Signal : Type*} {Cost : Type*} [Preorder Cost]

/-- If the available region is covered by the least WM closure of exact
permissive upper-formed full-inheritance obligations, then every available
query becomes WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_upperExactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encode seed)) :
    availableRegionAt P W B guard ⊆
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.availableRegionAt_subset_wmAdmissibleRegionAt_of_thresholdValid
    (S := leastRuleClosure (State := State) (Query := Query) R W
      (upperFormedConceptQuerySet Γ M encode seed))
  · exact leastRuleClosure_thresholdValid_of_upperExactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed
  · exact hAvail

/-- If the available region is exactly covered by the least WM closure of
exact permissive upper-formed full-inheritance obligations, the admissible
region collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_upperExactFullInheritanceStrength
    (P : StatefulPerspective State Query Signal Cost)
    (R : RuleSet State Query)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set Query) (τ : ℝ≥0∞)
    (encode :
      _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encode seed)) :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Query) P W B guard τ =
      availableRegionAt P W B guard := by
  apply Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt_eq_availableRegionAt_of_thresholdValid
  exact thresholdValid_mono
    (State := State) (Query := Query) (W := W) (τ := τ)
    hAvail
    (leastRuleClosure_thresholdValid_of_upperExactFullInheritanceStrength
      (State := State) (Query := Query) R Γ M W τ encode seed hEncode hSeed)

end Admissibility

end UpperFormedConceptClosure

/-- Proof-carrying profile for the shared credal formed-concept
full-inheritance closure bridge.

This is the PLN/KR closure layer beneath the ASSOC/PAT semantic-layer
consumer: robust lower seeds, permissive upper seeds, and determined
upper-to-lower reclassification all route through the same WM closure and
threshold-validity surface. -/
structure CredalConceptFullInheritanceClosureBridgeProfile where
  lowerClosureThresholdValid :
    ∀ {State Query Obj Attr Q Gate : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr],
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      thresholdValid (State := State) (Query := Query) W τ
        (leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed))
  lowerAvailableRegionAdmissible :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) →
      availableRegionAt P W B guard ⊆
        Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ
  lowerAdmissibleRegionEqualsAvailable :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encode seed)) →
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ =
        availableRegionAt P W B guard
  upperClosureThresholdValid :
    ∀ {State Query Obj Attr Q Gate : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr],
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      thresholdValid (State := State) (Query := Query) W τ
        (leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encode seed))
  upperAvailableRegionAdmissible :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encode seed)) →
      availableRegionAt P W B guard ⊆
        Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ
  upperAdmissibleRegionEqualsAvailable :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encode :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encode subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encode seed)) →
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ =
        availableRegionAt P W B guard
  lowerClosureEmbedsUpperClosure :
    ∀ {State Query Obj Attr Q Gate : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Nonempty Gate],
      (R : RuleSet State Query) → (W : State) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encodeLower :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (encodeUpper :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        encodeLower subConcept superConcept =
          encodeUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) →
      leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encodeLower seed) ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper (lowerSeedAsUpper Γ M seed))
  determinedUpperClosureEmbedsLowerClosure :
    ∀ {State Query Obj Attr Q Gate : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr],
      (R : RuleSet State Query) → (W : State) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encodeUpper :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (encodeLower :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        encodeUpper p.1 p.2 =
          encodeLower
            (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
            (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) →
      leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed) ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (lowerFormedConceptQuerySet Γ M encodeLower
            (determinedUpperSeedAsLower Γ M seed hDet))
  determinedUpperClosureThresholdValid :
    ∀ {State Query Obj Attr Q Gate : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr],
      (R : RuleSet State Query) → (W : State) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (τ : ℝ≥0∞) →
      (encodeUpper :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (encodeLower :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        encodeUpper p.1 p.2 =
          encodeLower
            (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
            (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      thresholdValid (State := State) (Query := Query) W τ
        (leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed))
  determinedUpperAvailableRegionAdmissible :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encodeUpper :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (encodeLower :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        encodeUpper p.1 p.2 =
          encodeLower
            (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
            (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed)) →
      availableRegionAt P W B guard ⊆
        Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ
  determinedUpperAdmissibleRegionEqualsAvailable :
    ∀ {State Query Obj Attr Q Gate Signal Cost : Type}
      [_root_.Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State Query] [Preorder Q] [Fintype Obj] [Fintype Attr]
      [Preorder Cost],
      (P : StatefulPerspective State Query Signal Cost) →
      (R : RuleSet State Query) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set Query) → (τ : ℝ≥0∞) →
      (encodeUpper :
        _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M → Query) →
      (encodeLower :
        _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M →
          _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M → Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        encodeUpper p.1 p.2 =
          encodeLower
            (upperToLowerFormedConceptOfDetermines Γ M p.1 (hDet p hp).1)
            (upperToLowerFormedConceptOfDetermines Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W
            (encodeLower subConcept superConcept) =
          ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ determinedUpperSeedAsLower Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      (availableRegionAt P W B guard ⊆
        leastRuleClosure (State := State) (Query := Query) R W
          (upperFormedConceptQuerySet Γ M encodeUpper seed)) →
      Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Query) P W B guard τ =
        availableRegionAt P W B guard

/-- Public handle for the shared credal concept-closure bridge. -/
def credalConceptFullInheritanceClosureBridgeProfile :
    CredalConceptFullInheritanceClosureBridgeProfile where
  lowerClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
  lowerAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_exactFullInheritanceStrength
  lowerAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_exactFullInheritanceStrength
  upperClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_upperExactFullInheritanceStrength
  upperAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_upperExactFullInheritanceStrength
  upperAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_upperExactFullInheritanceStrength
  lowerClosureEmbedsUpperClosure :=
    leastRuleClosure_lowerFormedConceptQuerySet_subset_upperFormedConceptQuerySet_of_liftEncode
  determinedUpperClosureEmbedsLowerClosure :=
    leastRuleClosure_upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
  determinedUpperClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_determinedUpperExactFullInheritanceStrength
  determinedUpperAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_determinedUpperExactFullInheritanceStrength
  determinedUpperAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_determinedUpperExactFullInheritanceStrength

end Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge
