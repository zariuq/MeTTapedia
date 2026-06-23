import Mettapedia.Logic.ConceptOntology.BenchmarkControl

/-!
# Loop-Conjecture Scrutability

This module isolates the FCA reading of the conjecturing pipeline:

* a candidate implication is membership in an attribute closure,
* restricting to a finite/sample object population yields a larger closure,
* the conjecture frontier is the gap between a smaller-sample closure and a
  fuller closure.

The name is loop-facing because this is exactly the shape used by the loop
benchmark, but the theorems are generic over any FCA-style relation.
-/

namespace Mettapedia.Logic.ConceptOntology

universe u v

section Generic

variable {Obj : Type u} {Attr : Type v}

/-- The attribute closure induced by a sampled object population: attributes that
hold of every sampled object satisfying all premise attributes. This is the FCA
closure on the attribute side, read relative to a designated sample of objects. -/
def sampledAttributeClosure
    (sample : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) : Set Attr :=
  _root_.upperPolar r (sample ∩ _root_.lowerPolar r premise)

/-- A sampled attribute implication holds exactly when the conclusion lies in the
sampled FCA closure of the premise. -/
def sampledImplicationHolds
    (sample : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) (conclusion : Attr) : Prop :=
  conclusion ∈ sampledAttributeClosure sample r premise

/-- The full-context closure is the sampled closure at `Set.univ`. -/
def fullAttributeClosure
    (r : Obj → Attr → Prop) (premise : Set Attr) : Set Attr :=
  sampledAttributeClosure Set.univ r premise

/-- The sample-vs-full scrutability frontier: attributes supported by the smaller
sample closure but absent from the fuller closure. This is the closure-side
analogue of the conjecture residue. -/
def attributeScrutabilityFrontier
    (sampleApprox sampleFull : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) : Set Attr :=
  sampledAttributeClosure sampleApprox r premise \ sampledAttributeClosure sampleFull r premise

theorem mem_sampledAttributeClosure_iff
    (sample : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) (a : Attr) :
    a ∈ sampledAttributeClosure sample r premise ↔
      ∀ x, x ∈ sample → (∀ b, b ∈ premise → r x b) → r x a := by
  constructor
  · intro ha x hxsample hpremise
    exact ha ⟨hxsample, hpremise⟩
  · intro ha x hx
    exact ha x hx.1 hx.2

theorem sampledImplicationHolds_iff
    (sample : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) (conclusion : Attr) :
    sampledImplicationHolds sample r premise conclusion ↔
      ∀ x, x ∈ sample → (∀ b, b ∈ premise → r x b) → r x conclusion :=
  mem_sampledAttributeClosure_iff sample r premise conclusion

theorem mem_fullAttributeClosure_iff
    (r : Obj → Attr → Prop) (premise : Set Attr) (a : Attr) :
    a ∈ fullAttributeClosure r premise ↔
      ∀ x, (∀ b, b ∈ premise → r x b) → r x a := by
  simpa [fullAttributeClosure] using
    (mem_sampledAttributeClosure_iff (sample := (Set.univ : Set Obj)) r premise a)

/-- Enlarging the object sample can only shrink the attribute closure: more objects
means more potential counterexamples. -/
theorem sampledAttributeClosure_antitone
    {sampleSmall sampleLarge : Set Obj} (r : Obj → Attr → Prop) (premise : Set Attr)
    (hSamples : sampleSmall ⊆ sampleLarge) :
    sampledAttributeClosure sampleLarge r premise ⊆
      sampledAttributeClosure sampleSmall r premise := by
  intro a ha
  rw [mem_sampledAttributeClosure_iff] at ha ⊢
  intro x hx hprem
  exact ha x (hSamples hx) hprem

theorem fullAttributeClosure_subset_sampled
    (sample : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) :
    fullAttributeClosure r premise ⊆ sampledAttributeClosure sample r premise := by
  simpa [fullAttributeClosure] using
    sampledAttributeClosure_antitone r premise (sampleSmall := sample) (sampleLarge := Set.univ)
      (by intro x _; simp)

theorem mem_attributeScrutabilityFrontier_iff
    (sampleApprox sampleFull : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr) (a : Attr) :
    a ∈ attributeScrutabilityFrontier sampleApprox sampleFull r premise ↔
      a ∈ sampledAttributeClosure sampleApprox r premise ∧
        a ∉ sampledAttributeClosure sampleFull r premise := Iff.rfl

theorem attributeScrutabilityFrontier_eq_empty_of_eq
    (sampleApprox sampleFull : Set Obj) (r : Obj → Attr → Prop) (premise : Set Attr)
    (hEq : sampledAttributeClosure sampleApprox r premise =
      sampledAttributeClosure sampleFull r premise) :
    attributeScrutabilityFrontier sampleApprox sampleFull r premise = ∅ := by
  ext a
  simp [attributeScrutabilityFrontier, hEq]

end Generic

namespace LoopBenchmark

/-- The loop-identity vocabulary used by the current conjecturing benchmark. -/
inductive LoopProperty where
  | commutative
  | associative
  | flexible
  | leftAlternative
  | rightAlternative
  | leftBol
  | rightBol
  | moufang
  | cIdentity
  | lip
  | rip
  | twoSidedInverses
  | xCubedAssociative
  deriving DecidableEq, Repr, Fintype

/-- A finite loop-benchmark population with order labels and property
incidence. This matches the benchmark surface used by the Python loop miner:
objects are finite loops, attributes are named loop identities, and gates are
order-bounded samples of the same population. -/
structure LoopBenchmarkContext where
  LoopObj : Type u
  objFintype : Fintype LoopObj
  orderOf : LoopObj → ℕ
  satisfies : LoopObj → LoopProperty → Prop

attribute [instance] LoopBenchmarkContext.objFintype

/-- The FCA incidence relation of the loop benchmark. -/
def relation (B : LoopBenchmarkContext) : B.LoopObj → LoopProperty → Prop :=
  B.satisfies

/-- The conjunction antecedent used by the benchmark miner, presented as an
attribute set. -/
def premiseSet (premise : Finset LoopProperty) : Set LoopProperty :=
  {p | p ∈ premise}

@[simp] theorem mem_premiseSet_iff
    (premise : Finset LoopProperty) (p : LoopProperty) :
    p ∈ premiseSet premise ↔ p ∈ premise := Iff.rfl

/-- The order-bounded sample used for gate-indexed loop closures. -/
def sampleUpTo (B : LoopBenchmarkContext) (maxOrder : ℕ) : Set B.LoopObj :=
  {x | B.orderOf x ≤ maxOrder}

@[simp] theorem mem_sampleUpTo_iff
    (B : LoopBenchmarkContext) (maxOrder : ℕ) (x : B.LoopObj) :
    x ∈ sampleUpTo B maxOrder ↔ B.orderOf x ≤ maxOrder := Iff.rfl

/-- FCA closure of a premise within the loop population up to a given order. -/
def closureUpTo
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) : Set LoopProperty :=
  sampledAttributeClosure (sampleUpTo B maxOrder) (relation B) (premiseSet premise)

/-- FCA closure over the whole finite benchmark population. -/
def fullClosure
    (B : LoopBenchmarkContext) (premise : Finset LoopProperty) : Set LoopProperty :=
  fullAttributeClosure (relation B) (premiseSet premise)

/-- The actual benchmark notion of a mined implication at a given order bound:
the consequent lies in the sampled FCA closure of the antecedent. -/
def minedImplicationHoldsUpTo
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) (conclusion : LoopProperty) : Prop :=
  conclusion ∈ closureUpTo B maxOrder premise

/-- The full-population benchmark implication predicate. -/
def minedImplicationHolds
    (B : LoopBenchmarkContext)
    (premise : Finset LoopProperty) (conclusion : LoopProperty) : Prop :=
  conclusion ∈ fullClosure B premise

/-- Sample-vs-sample scrutability frontier for the order-gated loop benchmark. -/
def frontierBetweenOrders
    (B : LoopBenchmarkContext) (maxOrderApprox maxOrderFull : ℕ)
    (premise : Finset LoopProperty) : Set LoopProperty :=
  attributeScrutabilityFrontier
    (sampleUpTo B maxOrderApprox)
    (sampleUpTo B maxOrderFull)
    (relation B)
    (premiseSet premise)

/-- Sample-vs-full scrutability frontier for the loop benchmark. -/
def frontierToFull
    (B : LoopBenchmarkContext) (maxOrderApprox : ℕ)
    (premise : Finset LoopProperty) : Set LoopProperty :=
  attributeScrutabilityFrontier
    (sampleUpTo B maxOrderApprox)
    Set.univ
    (relation B)
    (premiseSet premise)

theorem mem_closureUpTo_iff
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) (a : LoopProperty) :
    a ∈ closureUpTo B maxOrder premise ↔
      ∀ x, B.orderOf x ≤ maxOrder →
        (∀ b, b ∈ premise → B.satisfies x b) →
        B.satisfies x a := by
  simpa [closureUpTo, relation, premiseSet, sampleUpTo] using
    (mem_sampledAttributeClosure_iff
      (sample := sampleUpTo B maxOrder)
      (r := relation B)
      (premise := premiseSet premise)
      a)

theorem minedImplicationHoldsUpTo_iff
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) (conclusion : LoopProperty) :
    minedImplicationHoldsUpTo B maxOrder premise conclusion ↔
      ∀ x, B.orderOf x ≤ maxOrder →
        (∀ b, b ∈ premise → B.satisfies x b) →
        B.satisfies x conclusion :=
  mem_closureUpTo_iff B maxOrder premise conclusion

theorem mem_fullClosure_iff
    (B : LoopBenchmarkContext)
    (premise : Finset LoopProperty) (a : LoopProperty) :
    a ∈ fullClosure B premise ↔
      ∀ x, (∀ b, b ∈ premise → B.satisfies x b) → B.satisfies x a := by
  simpa [fullClosure, relation, premiseSet] using
    (mem_fullAttributeClosure_iff
      (r := relation B)
      (premise := premiseSet premise)
      a)

theorem minedImplicationHolds_iff
    (B : LoopBenchmarkContext)
    (premise : Finset LoopProperty) (conclusion : LoopProperty) :
    minedImplicationHolds B premise conclusion ↔
      ∀ x, (∀ b, b ∈ premise → B.satisfies x b) → B.satisfies x conclusion :=
  mem_fullClosure_iff B premise conclusion

theorem sampleUpTo_mono
    (B : LoopBenchmarkContext) {small large : ℕ}
    (h : small ≤ large) :
    sampleUpTo B small ⊆ sampleUpTo B large := by
  intro x hx
  exact le_trans hx h

/-- As the order cap grows, the sampled closure can only shrink: more loops
mean more potential counterexamples. -/
theorem closureUpTo_antitone
    (B : LoopBenchmarkContext) {small large : ℕ}
    (premise : Finset LoopProperty) (h : small ≤ large) :
    closureUpTo B large premise ⊆ closureUpTo B small premise := by
  simpa [closureUpTo, relation, premiseSet] using
    sampledAttributeClosure_antitone
      (r := relation B)
      (premise := premiseSet premise)
      (sampleSmall := sampleUpTo B small)
      (sampleLarge := sampleUpTo B large)
      (sampleUpTo_mono B h)

theorem fullClosure_subset_closureUpTo
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) :
    fullClosure B premise ⊆ closureUpTo B maxOrder premise := by
  simpa [fullClosure, closureUpTo, relation, premiseSet] using
    fullAttributeClosure_subset_sampled
      (sample := sampleUpTo B maxOrder)
      (r := relation B)
      (premise := premiseSet premise)

theorem mem_frontierBetweenOrders_iff
    (B : LoopBenchmarkContext) (maxOrderApprox maxOrderFull : ℕ)
    (premise : Finset LoopProperty) (a : LoopProperty) :
    a ∈ frontierBetweenOrders B maxOrderApprox maxOrderFull premise ↔
      a ∈ closureUpTo B maxOrderApprox premise ∧
        a ∉ closureUpTo B maxOrderFull premise := by
  simpa [frontierBetweenOrders, closureUpTo, relation, premiseSet, sampleUpTo] using
    (mem_attributeScrutabilityFrontier_iff
      (sampleApprox := sampleUpTo B maxOrderApprox)
      (sampleFull := sampleUpTo B maxOrderFull)
      (r := relation B)
      (premise := premiseSet premise)
      a)

theorem mem_frontierToFull_iff
    (B : LoopBenchmarkContext) (maxOrderApprox : ℕ)
    (premise : Finset LoopProperty) (a : LoopProperty) :
    a ∈ frontierToFull B maxOrderApprox premise ↔
      a ∈ closureUpTo B maxOrderApprox premise ∧
        a ∉ fullClosure B premise := by
  exact
    (mem_attributeScrutabilityFrontier_iff
      (sampleApprox := sampleUpTo B maxOrderApprox)
      (sampleFull := (Set.univ : Set B.LoopObj))
      (r := relation B)
      (premise := premiseSet premise)
      a)

end LoopBenchmark

section CredalScrutability

variable {Obj : Type u} {Attr : Type v} {Q : Type} {Gate : Type}
variable [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

attribute [local instance] Classical.propDecidable

/-- The credal scrutability frontier: concepts formed under at least one
admissible gate but not robustly under all of them. -/
def credalScrutabilityGap
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    Set (AbstractInheritance.DualConcept Obj Attr) :=
  upperConceptFamily Γ M \ lowerConceptFamily Γ M

omit [Fintype Gate] [Nonempty Gate] in
theorem mem_credalScrutabilityGap_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    A ∈ credalScrutabilityGap Γ M ↔
      A ∈ upperConceptFamily Γ M ∧
        A ∉ lowerConceptFamily Γ M := Iff.rfl

theorem globalEnvelopeWidth_conceptFormationGamble_eq_indicator_credalScrutabilityGap
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
        (conceptFormationGamble Γ M A) =
      if A ∈ credalScrutabilityGap Γ M then 1 else 0 := by
  simp [credalScrutabilityGap, globalEnvelopeWidth_conceptFormationGamble_eq]

theorem mem_credalScrutabilityGap_iff_globalEnvelopeWidth_eq_one
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    A ∈ credalScrutabilityGap Γ M ↔
      (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
          (conceptFormationGamble Γ M A) = 1 := by
  simp [globalEnvelopeWidth_conceptFormationGamble_eq_indicator_credalScrutabilityGap]

end CredalScrutability

namespace ControlExample

open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-- The exact crisp relation used by the control benchmark. -/
def contextRel : Animal → Trait → Prop :=
  crispRelation BinaryFcaBenchmarkContext.exactGate context.evidence

/-- The smaller sampled population consisting only of robin and bat. -/
def robinBatSample : Set Animal := {x | x = .robin ∨ x = .bat}

/-- Winged as a singleton premise set. -/
def wingedPremise : Set Trait := {Trait.winged}

theorem flies_mem_robinBat_winged_closure :
    Trait.flies ∈ sampledAttributeClosure robinBatSample contextRel wingedPremise := by
  rw [mem_sampledAttributeClosure_iff]
  intro x hxsample hprem
  cases x with
  | robin =>
      simp [contextRel, crispRelation,
        BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
        context, BinaryFcaBenchmarkContext.supportToken]
  | penguin =>
      simp [robinBatSample] at hxsample
  | bat =>
      simp [contextRel, crispRelation,
        BinaryFcaBenchmarkContext.exactGate, EvidenceGate.positiveThreshold,
        context, BinaryFcaBenchmarkContext.supportToken]

theorem flies_not_mem_full_winged_closure :
    Trait.flies ∉ fullAttributeClosure contextRel wingedPremise := by
  intro hflies
  rw [mem_fullAttributeClosure_iff] at hflies
  have hpenguin : contextRel Animal.penguin Trait.flies := by
    apply hflies Animal.penguin
    intro b hb
    have hb' : b = Trait.winged := by simpa [wingedPremise] using hb
    subst b
    simp [contextRel, crispRelation, BinaryFcaBenchmarkContext.exactGate,
      EvidenceGate.positiveThreshold, context, BinaryFcaBenchmarkContext.supportToken]
  have hnotPenguin : ¬ contextRel Animal.penguin Trait.flies := by
    simp [contextRel, crispRelation, BinaryFcaBenchmarkContext.exactGate,
      EvidenceGate.positiveThreshold, context]
    change (0 : ℝ≥0∞) < 1
    norm_num
  exact hnotPenguin hpenguin

theorem flies_mem_winged_scrutability_frontier :
    Trait.flies ∈ attributeScrutabilityFrontier robinBatSample Set.univ contextRel wingedPremise := by
  exact ⟨flies_mem_robinBat_winged_closure, flies_not_mem_full_winged_closure⟩

end ControlExample

namespace ControlCredalExample

open ControlExample

/-- The control benchmark's credal frontier under the exact/strict gate family:
concepts visible under some gate but not robust across all gates. -/
def controlCredalScrutabilityGap : Set (AbstractInheritance.DualConcept Animal Trait) :=
  credalScrutabilityGap gateFamily context.evidence

theorem flyingFamilyConcept_mem_controlCredalScrutabilityGap :
    flyingFamilyConcept ∈ controlCredalScrutabilityGap := by
  exact ⟨flyingFamilyConcept_mem_upper, flyingFamilyConcept_not_mem_lower⟩

theorem batOnlyFlyingConcept_not_mem_controlCredalScrutabilityGap :
    batOnlyFlyingConcept ∉ controlCredalScrutabilityGap := by
  intro hGap
  exact batOnlyFlyingConcept_not_mem_upper hGap.1

theorem flyingFamilyConcept_globalEnvelopeWidth_eq_one :
    (gateCredalProjectiveSpec (Gate := Bool)).globalEnvelopeWidth
        (conceptFormationGamble gateFamily context.evidence flyingFamilyConcept) = 1 := by
  exact
    (mem_credalScrutabilityGap_iff_globalEnvelopeWidth_eq_one
      (Γ := gateFamily)
      (M := context.evidence)
      (A := flyingFamilyConcept)).mp
        flyingFamilyConcept_mem_controlCredalScrutabilityGap

end ControlCredalExample

end Mettapedia.Logic.ConceptOntology
