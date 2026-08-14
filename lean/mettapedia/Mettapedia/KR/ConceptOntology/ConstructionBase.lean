import Mettapedia.KR.ConceptOntology.LoopConjectureScrutability

/-!
# Construction Base

This module packages the existing closure and credal machinery into a thin
`Abstract / Phenomena / Indexicality` interface.

The intent is not to create a parallel theory. Instead, it gives a higher-level
reframing layer:

* `Abstract` = attributes / intents / conceptual side
* `Phenomena` = objects / extents / observed side
* `Indexicality` = the vantage or window determining which phenomena are visible
* `thatsAllAt` = the current vantage is already closure-complete
* `openWorldAt` = there remains a nonempty closure frontier beyond the current
  vantage

On the credal side, `thatsAllConcept` and `openWorldConcept` repackage the
already-proved lower/upper concept-family gap and its envelope-width theorem.
-/

namespace Mettapedia.KR.ConceptOntology

universe u v w

/-- A thin API-layer base for construction from `Abstract`, `Phenomena`, and an
`Indexicality`-dependent window into the phenomena. The finite observer is not
hard-coded: the indexicality may be time, budget, order bound, viewpoint, or
any other sampling regime. -/
structure ConstructionBase where
  Phenomena : Type u
  Abstract : Type v
  Indexicality : Type w
  incidence : Phenomena → Abstract → Prop
  visibleAt : Indexicality → Set Phenomena

namespace ConstructionBase

variable (B : ConstructionBase)

/-- The closure computed from what is visible at a particular indexical
vantage. -/
def closureAt (ι : B.Indexicality) (premise : Set B.Abstract) : Set B.Abstract :=
  sampledAttributeClosure (B.visibleAt ι) B.incidence premise

/-- The full closure over all phenomena, independent of any finite vantage. -/
def fullClosure (premise : Set B.Abstract) : Set B.Abstract :=
  fullAttributeClosure B.incidence premise

/-- The current closure frontier: abstract content supported by the present
vantage but absent from the full closure. -/
def frontierAt (ι : B.Indexicality) (premise : Set B.Abstract) : Set B.Abstract :=
  attributeScrutabilityFrontier (B.visibleAt ι) Set.univ B.incidence premise

/-- Refinement of viewpoint: `j` sees at least everything `i` sees. -/
def Refines (i j : B.Indexicality) : Prop :=
  B.visibleAt i ⊆ B.visibleAt j

/-- "That's all" at vantage `ι`: the current closure already matches the full
closure. -/
def thatsAllAt (ι : B.Indexicality) (premise : Set B.Abstract) : Prop :=
  B.closureAt ι premise = B.fullClosure premise

/-- Open-world at vantage `ι`: the current closure frontier is still nonempty. -/
def openWorldAt (ι : B.Indexicality) (premise : Set B.Abstract) : Prop :=
  B.frontierAt ι premise ≠ ∅

theorem mem_closureAt_iff
    (ι : B.Indexicality) (premise : Set B.Abstract) (a : B.Abstract) :
    a ∈ B.closureAt ι premise ↔
      ∀ x, x ∈ B.visibleAt ι → (∀ b, b ∈ premise → B.incidence x b) → B.incidence x a := by
  simpa [ConstructionBase.closureAt] using
    (mem_sampledAttributeClosure_iff
      (sample := B.visibleAt ι)
      (r := B.incidence)
      (premise := premise)
      a)

theorem mem_fullClosure_iff
    (premise : Set B.Abstract) (a : B.Abstract) :
    a ∈ B.fullClosure premise ↔
      ∀ x, (∀ b, b ∈ premise → B.incidence x b) → B.incidence x a := by
  simpa [ConstructionBase.fullClosure] using
    (mem_fullAttributeClosure_iff
      (r := B.incidence)
      (premise := premise)
      a)

theorem fullClosure_subset_closureAt
    (ι : B.Indexicality) (premise : Set B.Abstract) :
    B.fullClosure premise ⊆ B.closureAt ι premise := by
  simpa [ConstructionBase.fullClosure, ConstructionBase.closureAt] using
    (fullAttributeClosure_subset_sampled
      (sample := B.visibleAt ι)
      (r := B.incidence)
      (premise := premise))

theorem closureAt_antitone_of_refines
    {i j : B.Indexicality} (premise : Set B.Abstract)
    (h : B.Refines i j) :
    B.closureAt j premise ⊆ B.closureAt i premise := by
  simpa [ConstructionBase.closureAt, ConstructionBase.Refines] using
    (sampledAttributeClosure_antitone
      (r := B.incidence)
      (premise := premise)
      (sampleSmall := B.visibleAt i)
      (sampleLarge := B.visibleAt j)
      h)

/-- Once a vantage has reached the full closure, every refinement of that
vantage is also closure-complete.  Seeing more phenomena may discharge
over-strong conjectures; it cannot reopen a concept that was already equal to
the full context. -/
theorem thatsAllAt_of_refines
    {i j : B.Indexicality} (premise : Set B.Abstract)
    (h : B.Refines i j) (hAll : B.thatsAllAt i premise) :
    B.thatsAllAt j premise := by
  apply Set.Subset.antisymm
  · intro a ha
    have hji : a ∈ B.closureAt i premise :=
      B.closureAt_antitone_of_refines premise h ha
    simpa [ConstructionBase.thatsAllAt] using hAll ▸ hji
  · exact B.fullClosure_subset_closureAt j premise

theorem frontierAt_eq_empty_iff_thatsAllAt
    (ι : B.Indexicality) (premise : Set B.Abstract) :
    B.frontierAt ι premise = ∅ ↔ B.thatsAllAt ι premise := by
  constructor
  · intro hEmpty
    apply Set.Subset.antisymm
    · intro a ha
      by_contra hNot
      have hFrontier : a ∈ B.frontierAt ι premise := ⟨ha, hNot⟩
      simp [hEmpty] at hFrontier
    · exact B.fullClosure_subset_closureAt ι premise
  · intro hAll
    exact attributeScrutabilityFrontier_eq_empty_of_eq
      (sampleApprox := B.visibleAt ι)
      (sampleFull := Set.univ)
      (r := B.incidence)
      (premise := premise)
      hAll

theorem openWorldAt_iff_not_thatsAllAt
    (ι : B.Indexicality) (premise : Set B.Abstract) :
    B.openWorldAt ι premise ↔ ¬ B.thatsAllAt ι premise := by
  constructor
  · intro hOpen hAll
    exact hOpen ((B.frontierAt_eq_empty_iff_thatsAllAt ι premise).2 hAll)
  · intro hNot hEmpty
    exact hNot ((B.frontierAt_eq_empty_iff_thatsAllAt ι premise).1 hEmpty)

/-- If even a refined vantage is still open-world, then every coarser vantage
it refines was already open-world.  Equivalently, refinement can close a
frontier but cannot create one after the coarse view had reached the full
closure. -/
theorem openWorldAt_of_refines_of_openWorldAt
    {i j : B.Indexicality} (premise : Set B.Abstract)
    (h : B.Refines i j) (hOpen : B.openWorldAt j premise) :
    B.openWorldAt i premise := by
  rw [B.openWorldAt_iff_not_thatsAllAt] at hOpen ⊢
  intro hAll
  exact hOpen (B.thatsAllAt_of_refines premise h hAll)

end ConstructionBase

namespace LoopBenchmark

/-- Recast the loop benchmark as an `Abstract / Phenomena / Indexicality` base:
loop properties are the abstract side, loops are the phenomenal side, and the
indexicality parameter is the order bound. -/
def toConstructionBase (B : LoopBenchmarkContext) : ConstructionBase where
  Phenomena := B.LoopObj
  Abstract := LoopProperty
  Indexicality := ℕ
  incidence := B.satisfies
  visibleAt := sampleUpTo B

@[simp] theorem toConstructionBase_closureAt_eq
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) :
    ((toConstructionBase B).closureAt maxOrder (premiseSet premise)) =
      closureUpTo B maxOrder premise := rfl

@[simp] theorem toConstructionBase_fullClosure_eq
    (B : LoopBenchmarkContext) (premise : Finset LoopProperty) :
    ((toConstructionBase B).fullClosure (premiseSet premise)) =
      fullClosure B premise := rfl

@[simp] theorem toConstructionBase_frontierAt_eq
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) :
    ((toConstructionBase B).frontierAt maxOrder (premiseSet premise)) =
      frontierToFull B maxOrder premise := rfl

theorem toConstructionBase_thatsAllAt_iff
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) :
    (toConstructionBase B).thatsAllAt maxOrder (premiseSet premise) ↔
      closureUpTo B maxOrder premise = fullClosure B premise := Iff.rfl

theorem toConstructionBase_openWorldAt_iff
    (B : LoopBenchmarkContext) (maxOrder : ℕ)
    (premise : Finset LoopProperty) :
    (toConstructionBase B).openWorldAt maxOrder (premiseSet premise) ↔
      frontierToFull B maxOrder premise ≠ ∅ := Iff.rfl

theorem toConstructionBase_refines_of_le
    (B : LoopBenchmarkContext) {small large : ℕ} (h : small ≤ large) :
    (toConstructionBase B).Refines small large := by
  show sampleUpTo B small ⊆ sampleUpTo B large
  exact sampleUpTo_mono B h

theorem toConstructionBase_thatsAllAt_of_le
    (B : LoopBenchmarkContext) {small large : ℕ}
    (premise : Finset LoopProperty) (h : small ≤ large)
    (hAll : (toConstructionBase B).thatsAllAt small (premiseSet premise)) :
    (toConstructionBase B).thatsAllAt large (premiseSet premise) := by
  exact ConstructionBase.thatsAllAt_of_refines (toConstructionBase B)
    (premiseSet premise) (toConstructionBase_refines_of_le B h) hAll

theorem toConstructionBase_openWorldAt_of_le
    (B : LoopBenchmarkContext) {small large : ℕ}
    (premise : Finset LoopProperty) (h : small ≤ large)
    (hOpen : (toConstructionBase B).openWorldAt large (premiseSet premise)) :
    (toConstructionBase B).openWorldAt small (premiseSet premise) := by
  exact ConstructionBase.openWorldAt_of_refines_of_openWorldAt (toConstructionBase B)
    (premiseSet premise) (toConstructionBase_refines_of_le B h) hOpen

end LoopBenchmark

section CredalOT

variable {Obj : Type u} {Attr : Type v} {Q : Type} {Gate : Type}
variable [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

attribute [local instance] Classical.propDecidable

/-- Credal "that's all": this concept is robust across every admissible gate, so
there is no lower/upper closure disagreement left for it. -/
def thatsAllConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) : Prop :=
  A ∉ credalScrutabilityGap Γ M

/-- Credal open-world: this concept sits in the lower/upper gap, so some
admissible gates form it and some do not. -/
def openWorldConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) : Prop :=
  A ∈ credalScrutabilityGap Γ M

theorem openWorldConcept_iff_globalEnvelopeWidth_eq_one
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) :
    openWorldConcept Γ M A ↔
      (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
        (conceptFormationGamble Γ M A) = 1 := by
  simpa [openWorldConcept] using
    (mem_credalScrutabilityGap_iff_globalEnvelopeWidth_eq_one
      (Γ := Γ) (M := M) (A := A))

theorem thatsAllConcept_iff_globalEnvelopeWidth_eq_zero
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) :
    thatsAllConcept Γ M A ↔
      (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
        (conceptFormationGamble Γ M A) = 0 := by
  constructor
  · intro hT
    have hGap : A ∉ credalScrutabilityGap Γ M := hT
    have hIndicator :=
      globalEnvelopeWidth_conceptFormationGamble_eq_indicator_credalScrutabilityGap
        (Γ := Γ) (M := M) (A := A)
    simpa [hGap] using hIndicator
  · intro hWidth hGap
    have hOne :
        (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
          (conceptFormationGamble Γ M A) = 1 := by
      exact (openWorldConcept_iff_globalEnvelopeWidth_eq_one
        (Γ := Γ) (M := M) (A := A)).mp hGap
    exact zero_ne_one (hWidth.symm.trans hOne)

omit [Fintype Gate] [Nonempty Gate] in
theorem openWorldConcept_iff_hasStrictGlobalWidth
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) :
    openWorldConcept Γ M A ↔
      (gateCredalProjectiveSpec (Gate := Gate)).hasStrictGlobalWidth
        (conceptFormationGamble Γ M A) := by
  simpa [openWorldConcept] using
    (mem_credalScrutabilityGap_iff_hasStrictGlobalWidth
      (Γ := Γ) (M := M) (A := A))

omit [Fintype Gate] [Nonempty Gate] in
theorem thatsAllConcept_iff_determinesGlobalGamble
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept Obj Attr) :
    thatsAllConcept Γ M A ↔
      (gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (conceptFormationGamble Γ M A) := by
  simpa [thatsAllConcept] using
    (not_mem_credalScrutabilityGap_iff_determinesGlobalGamble
      (Γ := Γ) (M := M) (A := A))

end CredalOT

namespace ControlExample

open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

/-- A tiny exact-control base: the abstract side is `Trait`, the phenomenal
side is `Animal`, and the indexicality is whether we only see the robin/bat
sample or the whole tiny world. -/
inductive ControlIndexicality where
  | sampled
  | total
  deriving DecidableEq, Repr, Fintype

def constructionBase : ConstructionBase where
  Phenomena := Animal
  Abstract := Trait
  Indexicality := ControlIndexicality
  incidence := contextRel
  visibleAt
    | .sampled => robinBatSample
    | .total => Set.univ

theorem flies_mem_control_frontier :
    Trait.flies ∈ constructionBase.frontierAt ControlIndexicality.sampled wingedPremise := by
  exact flies_mem_winged_scrutability_frontier

theorem control_openWorldAt_sampled :
    constructionBase.openWorldAt ControlIndexicality.sampled wingedPremise := by
  intro hEmpty
  have hMember := flies_mem_control_frontier
  rw [hEmpty] at hMember
  exact (Set.mem_empty_iff_false _).mp hMember

theorem control_thatsAllAt_total :
    constructionBase.thatsAllAt ControlIndexicality.total wingedPremise := by
  rfl

theorem flyingFamilyConcept_openWorldConcept :
    openWorldConcept gateFamily context.evidence flyingFamilyConcept := by
  exact ControlCredalExample.flyingFamilyConcept_mem_controlCredalScrutabilityGap

theorem flyingFamilyConcept_thatsAllConcept_not :
    ¬ thatsAllConcept gateFamily context.evidence flyingFamilyConcept := by
  intro hT
  have hO : openWorldConcept gateFamily context.evidence flyingFamilyConcept :=
    flyingFamilyConcept_openWorldConcept
  exact hT hO

theorem batOnlyFlyingConcept_thatsAllConcept :
    thatsAllConcept gateFamily context.evidence batOnlyFlyingConcept := by
  exact ControlCredalExample.batOnlyFlyingConcept_not_mem_controlCredalScrutabilityGap

theorem control_credal_family_supports_both_world_assumptions :
    openWorldConcept gateFamily context.evidence flyingFamilyConcept ∧
      thatsAllConcept gateFamily context.evidence batOnlyFlyingConcept := by
  exact ⟨flyingFamilyConcept_openWorldConcept, batOnlyFlyingConcept_thatsAllConcept⟩

theorem flyingFamilyConcept_hasStrictGlobalWidth :
    (gateCredalProjectiveSpec (Gate := Bool)).hasStrictGlobalWidth
        (conceptFormationGamble gateFamily context.evidence flyingFamilyConcept) := by
  exact (openWorldConcept_iff_hasStrictGlobalWidth
    (Γ := gateFamily) (M := context.evidence) (A := flyingFamilyConcept)).mp
      flyingFamilyConcept_openWorldConcept

theorem flyingFamilyConcept_not_determinesGlobalGamble :
    ¬ (gateCredalProjectiveSpec (Gate := Bool)).determinesGlobalGamble
        (conceptFormationGamble gateFamily context.evidence flyingFamilyConcept) := by
  intro hDet
  have hThatsAll : thatsAllConcept gateFamily context.evidence flyingFamilyConcept :=
    (thatsAllConcept_iff_determinesGlobalGamble
      (Γ := gateFamily) (M := context.evidence) (A := flyingFamilyConcept)).mpr hDet
  exact flyingFamilyConcept_thatsAllConcept_not hThatsAll

theorem batOnlyFlyingConcept_determinesGlobalGamble :
    (gateCredalProjectiveSpec (Gate := Bool)).determinesGlobalGamble
        (conceptFormationGamble gateFamily context.evidence batOnlyFlyingConcept) := by
  exact (thatsAllConcept_iff_determinesGlobalGamble
    (Γ := gateFamily) (M := context.evidence) (A := batOnlyFlyingConcept)).mp
      batOnlyFlyingConcept_thatsAllConcept

theorem batOnlyFlyingConcept_not_hasStrictGlobalWidth :
    ¬ (gateCredalProjectiveSpec (Gate := Bool)).hasStrictGlobalWidth
        (conceptFormationGamble gateFamily context.evidence batOnlyFlyingConcept) := by
  intro hWidth
  have hOpen : openWorldConcept gateFamily context.evidence batOnlyFlyingConcept :=
    (openWorldConcept_iff_hasStrictGlobalWidth
      (Γ := gateFamily) (M := context.evidence) (A := batOnlyFlyingConcept)).mpr hWidth
  exact batOnlyFlyingConcept_thatsAllConcept hOpen

end ControlExample

namespace LoopToyExample

open LoopBenchmark

/-- Tiny explicit loop population for a benchmark-shaped canary. -/
inductive ToyLoopObj where
  | order1
  | order2
  | order3
  deriving DecidableEq, Repr, Fintype

def orderOf : ToyLoopObj → ℕ
  | .order1 => 1
  | .order2 => 2
  | .order3 => 3

def satisfies : ToyLoopObj → LoopProperty → Prop
  | .order1, .flexible => True
  | .order1, .leftAlternative => True
  | .order1, .lip => True
  | .order2, .flexible => True
  | .order2, .leftAlternative => True
  | .order3, .flexible => True
  | _, _ => False

def context : LoopBenchmarkContext where
  LoopObj := ToyLoopObj
  objFintype := inferInstance
  orderOf := orderOf
  satisfies := satisfies

def premise : Finset LoopProperty := {LoopProperty.flexible, LoopProperty.leftAlternative}

theorem lip_mem_closureUpTo_order1 :
    LoopProperty.lip ∈ closureUpTo context 1 premise := by
  rw [mem_closureUpTo_iff]
  intro x hxOrder hprem
  cases x with
  | order1 =>
      simp [context, satisfies]
  | order2 =>
      simp [context, orderOf] at hxOrder
  | order3 =>
      simp [context, orderOf] at hxOrder

theorem lip_not_mem_fullClosure :
    LoopProperty.lip ∉ fullClosure context premise := by
  intro h
  rw [mem_fullClosure_iff] at h
  have hprem : ∀ b, b ∈ premise → satisfies ToyLoopObj.order2 b := by
    intro b hb
    have hb' : b = LoopProperty.flexible ∨ b = LoopProperty.leftAlternative := by
      simpa [premise] using hb
    rcases hb' with rfl | rfl <;> simp [satisfies]
  have hlip : satisfies ToyLoopObj.order2 LoopProperty.lip := h ToyLoopObj.order2 hprem
  simp [satisfies] at hlip

theorem lip_mem_frontier_order1 :
    LoopProperty.lip ∈ frontierToFull context 1 premise := by
  exact ⟨lip_mem_closureUpTo_order1, lip_not_mem_fullClosure⟩

theorem openWorldAt_order1 :
    (toConstructionBase context).openWorldAt (1 : ℕ) (premiseSet premise) := by
  rw [toConstructionBase_openWorldAt_iff]
  intro hEmpty
  have hMember := lip_mem_frontier_order1
  have : LoopProperty.lip ∈ (∅ : Set LoopProperty) := hEmpty ▸ hMember
  simp at this

theorem closureUpTo_order2_eq_fullClosure :
    closureUpTo context 2 premise = fullClosure context premise := by
  apply Set.Subset.antisymm
  · intro a ha
    rw [mem_closureUpTo_iff] at ha
    rw [mem_fullClosure_iff]
    intro x hprem
    cases x with
    | order1 =>
        exact ha ToyLoopObj.order1 (by simp [context, orderOf]) (by simpa [context, satisfies] using hprem)
    | order2 =>
        exact ha ToyLoopObj.order2 (by simp [context, orderOf]) (by simpa [context, satisfies] using hprem)
    | order3 =>
        have hfalse : False := by
          have hleft : satisfies ToyLoopObj.order3 LoopProperty.leftAlternative := hprem LoopProperty.leftAlternative (by simp [premise])
          simp [satisfies] at hleft
        exact False.elim hfalse
  · exact fullClosure_subset_closureUpTo context 2 premise

theorem thatsAllAt_order2 :
    (toConstructionBase context).thatsAllAt (2 : ℕ) (premiseSet premise) := by
  rw [toConstructionBase_thatsAllAt_iff]
  exact closureUpTo_order2_eq_fullClosure

theorem thatsAllAt_order3 :
    (toConstructionBase context).thatsAllAt (3 : ℕ) (premiseSet premise) := by
  exact toConstructionBase_thatsAllAt_of_le context premise (by decide) thatsAllAt_order2

end LoopToyExample

end Mettapedia.KR.ConceptOntology
