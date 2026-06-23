import Mettapedia.Logic.ConceptOntology.Formation
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-!
# Credal Concept-Family Formation

This module lifts exact finite concept formation to a first imprecise surface by
allowing uncertainty over which admissible evidence gate is active.

The intended semantics is deliberately conservative:

- a concept is in the lower family if it is formed under every admissible gate
- a concept is in the upper family if it is formed under at least one gate
- the accompanying credal envelope lives over the finite gate index space
  itself, with Dirac precise completions standing for "this gate was the active
  one"

This keeps uncertainty native to the formation process rather than bolting
credal coordinates onto already-precise formed concepts after the fact.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic.AbstractInheritance
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
attribute [local instance] Classical.propDecidable

universe u v w z

/-- A lower/upper concept family over the same dual-concept carrier. -/
structure CredalConceptFamily (Obj : Type u) (Attr : Type v) where
  lower : Set (DualConcept Obj Attr)
  upper : Set (DualConcept Obj Attr)

section GateFamilies

variable {Obj : Type u} {Attr : Type v} {Q : Type w} {Gate : Type z}
variable [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

/-- Concepts formed under at least one admissible evidence gate. -/
def upperConceptFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    Set (DualConcept Obj Attr) :=
  fun A => ∃ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M

/-- Concepts formed under every admissible evidence gate. -/
def lowerConceptFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    Set (DualConcept Obj Attr) :=
  fun A => ∀ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M

/-- Bundle the lower and upper credal formation fronts into one public
surface. -/
def credalConceptFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    CredalConceptFamily Obj Attr where
  lower := lowerConceptFamily Γ M
  upper := upperConceptFamily Γ M

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_lowerConceptFamily_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ lowerConceptFamily Γ M ↔
      ∀ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M :=
  Iff.rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_upperConceptFamily_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ upperConceptFamily Γ M ↔
      ∃ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M :=
  Iff.rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_credalConceptFamily_lower_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ (credalConceptFamily Γ M).lower ↔
      ∀ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M :=
  Iff.rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_credalConceptFamily_upper_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ (credalConceptFamily Γ M).upper ↔
      ∃ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M :=
  Iff.rfl

omit [Fintype Gate] in
theorem lowerConceptFamily_subset_upperConceptFamily
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    lowerConceptFamily Γ M ⊆ upperConceptFamily Γ M := by
  intro A hA
  obtain ⟨g⟩ := ‹Nonempty Gate›
  exact ⟨g, hA g⟩

omit [Fintype Gate] in
theorem credalConceptFamily_lower_subset_upper
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    (credalConceptFamily Γ M).lower ⊆ (credalConceptFamily Γ M).upper :=
  lowerConceptFamily_subset_upperConceptFamily Γ M

omit [Fintype Gate] [Nonempty Gate] in
theorem not_mem_lowerConceptFamily_of_not_mem_at
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) (g : Gate) :
    A ∉ AbstractInheritance.finiteConceptFamily (Γ g) M →
      A ∉ lowerConceptFamily Γ M := by
  intro hNot hLower
  exact hNot (hLower g)

omit [Fintype Gate] [Nonempty Gate] in
theorem not_mem_upperConceptFamily_of_forall_not_mem
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    (∀ g : Gate, A ∉ AbstractInheritance.finiteConceptFamily (Γ g) M) →
      A ∉ upperConceptFamily Γ M := by
  intro hAll hUpper
  rcases hUpper with ⟨g, hg⟩
  exact hAll g hg

/-- The finite upper carrier of credally formed concepts. -/
noncomputable def upperConceptFamilyFinset
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    Finset (DualConcept Obj Attr) := by
  classical
  exact Finset.univ.filter fun A => A ∈ upperConceptFamily Γ M

/-- The finite lower carrier of credally robust concepts. -/
noncomputable def lowerConceptFamilyFinset
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    Finset (DualConcept Obj Attr) := by
  classical
  exact Finset.univ.filter fun A => A ∈ lowerConceptFamily Γ M

/-- Concepts that remain formed under every admissible gate. -/
abbrev LowerFormedConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :=
  { A : DualConcept Obj Attr // A ∈ lowerConceptFamily Γ M }

/-- Concepts that are formed under at least one admissible gate. -/
abbrev UpperFormedConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :=
  { A : DualConcept Obj Attr // A ∈ upperConceptFamily Γ M }

omit [Nonempty Gate] in
@[simp] theorem mem_upperConceptFamilyFinset_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ upperConceptFamilyFinset Γ M ↔
      A ∈ upperConceptFamily Γ M := by
  classical
  simp [upperConceptFamilyFinset]

omit [Nonempty Gate] in
@[simp] theorem mem_lowerConceptFamilyFinset_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ lowerConceptFamilyFinset Γ M ↔
      A ∈ lowerConceptFamily Γ M := by
  classical
  simp [lowerConceptFamilyFinset]

/-- Interpretation of robust credally formed concepts by forgetting the
robust-membership proof. -/
noncomputable def lowerFormedConceptInterpretation
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    AbstractInheritance.Interpretation (LowerFormedConcept Γ M) Obj Attr where
  meaning := fun A => A.1

/-- Interpretation of permissively credally formed concepts by forgetting the
upper-membership proof. -/
noncomputable def upperFormedConceptInterpretation
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    AbstractInheritance.Interpretation (UpperFormedConcept Γ M) Obj Attr where
  meaning := fun A => A.1

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem lowerFormedConceptInterpretation_meaning
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : LowerFormedConcept Γ M) :
    (lowerFormedConceptInterpretation Γ M).meaning A = A.1 := rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem upperFormedConceptInterpretation_meaning
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : UpperFormedConcept Γ M) :
    (upperFormedConceptInterpretation Γ M).meaning A = A.1 := rfl

/-- A robustly formed concept can be viewed as an exact formed concept under
any admissible gate. -/
def lowerFormedConceptAt
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (g : Gate) :
    LowerFormedConcept Γ M → AbstractInheritance.FormedConcept (Γ g) M :=
  fun A => ⟨A.1, A.2 g⟩

/-- An upper formed concept carries some exact gate witness. -/
noncomputable def upperFormedConceptWitness
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    UpperFormedConcept Γ M →
      Σ g : Gate, AbstractInheritance.FormedConcept (Γ g) M := by
  classical
  intro A
  refine ⟨Classical.choose A.2, ?_⟩
  exact ⟨A.1, Classical.choose_spec A.2⟩

/-- A robustly formed concept can always be viewed as a permissively formed
concept with the same underlying dual concept. -/
def lowerToUpperFormedConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q) :
    LowerFormedConcept Γ M → UpperFormedConcept Γ M :=
  fun A => ⟨A.1, lowerConceptFamily_subset_upperConceptFamily Γ M A.2⟩

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem lowerFormedConceptAt_val
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (g : Gate) (A : LowerFormedConcept Γ M) :
    (lowerFormedConceptAt Γ M g A).1 = A.1 := rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem upperFormedConceptWitness_val
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : UpperFormedConcept Γ M) :
    (upperFormedConceptWitness Γ M A).2.1 = A.1 := by
  classical
  simp [upperFormedConceptWitness]

omit [Fintype Gate] in
@[simp] theorem lowerToUpperFormedConcept_val
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : LowerFormedConcept Γ M) :
    (lowerToUpperFormedConcept Γ M A).1 = A.1 := rfl

section CrispRecovery

@[simp] theorem mem_upperConceptFamily_singleton_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ upperConceptFamily (Gate := PUnit) (fun _ => G) M ↔
      A ∈ AbstractInheritance.finiteConceptFamily G M := by
  simp

@[simp] theorem mem_lowerConceptFamily_singleton_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    A ∈ lowerConceptFamily (Gate := PUnit) (fun _ => G) M ↔
      A ∈ AbstractInheritance.finiteConceptFamily G M := by
  simp

theorem upperConceptFamilyFinset_singleton_eq
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    upperConceptFamilyFinset (Gate := PUnit) (fun _ => G) M =
      AbstractInheritance.finiteConceptFamily G M := by
  classical
  ext A
  simp

theorem lowerConceptFamilyFinset_singleton_eq
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    lowerConceptFamilyFinset (Gate := PUnit) (fun _ => G) M =
      AbstractInheritance.finiteConceptFamily G M := by
  classical
  ext A
  simp

/-- Singleton gate uncertainty collapses the robust credal carrier back to the
exact formed-concept carrier. -/
noncomputable def lowerFormedConceptSingletonEquiv
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    LowerFormedConcept (Gate := PUnit) (fun _ => G) M ≃
      AbstractInheritance.FormedConcept G M where
  toFun A :=
    ⟨A.1, (mem_lowerConceptFamily_singleton_iff (G := G) (M := M) A.1).mp A.2⟩
  invFun A :=
    ⟨A.1, (mem_lowerConceptFamily_singleton_iff (G := G) (M := M) A.1).mpr A.2⟩
  left_inv A := by
    cases A
    rfl
  right_inv A := by
    cases A
    rfl

/-- Singleton gate uncertainty collapses the permissive credal carrier back to
the exact formed-concept carrier. -/
noncomputable def upperFormedConceptSingletonEquiv
    (G : EvidenceGate Q) (M : Obj → Attr → Q) :
    UpperFormedConcept (Gate := PUnit) (fun _ => G) M ≃
      AbstractInheritance.FormedConcept G M where
  toFun A :=
    ⟨A.1, (mem_upperConceptFamily_singleton_iff (G := G) (M := M) A.1).mp A.2⟩
  invFun A :=
    ⟨A.1, (mem_upperConceptFamily_singleton_iff (G := G) (M := M) A.1).mpr A.2⟩
  left_inv A := by
    cases A
    rfl
  right_inv A := by
    cases A
    rfl

@[simp] theorem lowerFormedConceptSingletonEquiv_val
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : LowerFormedConcept (Gate := PUnit) (fun _ => G) M) :
    (lowerFormedConceptSingletonEquiv G M A).1 = A.1 := rfl

@[simp] theorem upperFormedConceptSingletonEquiv_val
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A : UpperFormedConcept (Gate := PUnit) (fun _ => G) M) :
    (upperFormedConceptSingletonEquiv G M A).1 = A.1 := rfl

end CrispRecovery

/-- The full credal set generated by all Dirac precise previsions on the finite
gate index space. -/
noncomputable def gateCredalSet : CredalPrevisionSet Gate :=
  Set.range PrecisePrevision.dirac

omit [Fintype Gate] in
theorem gateCredalSet_nonempty :
    (gateCredalSet (Gate := Gate)).Nonempty := by
  obtain ⟨g⟩ := ‹Nonempty Gate›
  exact ⟨PrecisePrevision.dirac g, ⟨g, rfl⟩⟩

/-- Query gamble: does the candidate dual concept remain formed under the
chosen admissible gate? -/
noncomputable def conceptFormationGamble
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) : Gamble Gate :=
  fun g =>
    if A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M then 1 else 0

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem conceptFormationGamble_apply
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) (g : Gate) :
    conceptFormationGamble Γ M A g =
      if A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M then 1 else 0 :=
  rfl

omit [Fintype Gate] [Nonempty Gate] in
theorem conceptFormationGamble_in_unit
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) (g : Gate) :
    conceptFormationGamble Γ M A g ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h :
      A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M <;>
    simp [conceptFormationGamble, h]

/-- Identity-window projective specification for gate uncertainty. -/
def gateCredalProjectiveSpec :
    ProjectiveLocalCredalSpec PUnit Gate :=
  identityCredalProjectiveSpec (gateCredalSet (Gate := Gate))

omit [Fintype Gate] in
theorem gateCredalProjectiveSpec_hasCompatibleCompletion :
    (gateCredalProjectiveSpec (Gate := Gate)).hasCompatibleCompletion := by
  rw [gateCredalProjectiveSpec, identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact gateCredalSet_nonempty (Gate := Gate)

theorem lowerEnvelope_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    lowerEnvelope (gateCredalSet (Gate := Gate))
        (conceptFormationGamble Γ M A) =
      if A ∈ lowerConceptFamily Γ M then 1 else 0 := by
  classical
  by_cases hLower : A ∈ lowerConceptFamily Γ M
  · apply le_antisymm
    · rw [if_pos hLower]
      obtain ⟨g₀⟩ := ‹Nonempty Gate›
      have hmem :
          PrecisePrevision.dirac g₀ ∈ gateCredalSet (Gate := Gate) :=
        ⟨g₀, rfl⟩
      have hle :=
        lowerEnvelope_le_of_mem (gateCredalSet (Gate := Gate))
          (conceptFormationGamble Γ M A)
          (finite_credalRange_bddBelow (gateCredalSet (Gate := Gate))
            (conceptFormationGamble Γ M A))
          hmem
      simpa [gateCredalSet, conceptFormationGamble, hLower g₀] using hle
    · apply le_lowerEnvelope_of_forall_le
        (gateCredalSet (Gate := Gate))
        (gateCredalSet_nonempty (Gate := Gate))
        (conceptFormationGamble Γ M A)
      intro P hP
      rcases hP with ⟨g, rfl⟩
      rw [if_pos hLower]
      simp [conceptFormationGamble, hLower g]
  · have hWitness :
        ∃ g : Gate, A ∉ AbstractInheritance.finiteConceptFamily (Γ g) M := by
      simpa [lowerConceptFamily] using hLower
    apply le_antisymm
    · rw [if_neg hLower]
      rcases hWitness with ⟨g₀, hg₀⟩
      have hmem :
          PrecisePrevision.dirac g₀ ∈ gateCredalSet (Gate := Gate) :=
        ⟨g₀, rfl⟩
      have hle :=
        lowerEnvelope_le_of_mem (gateCredalSet (Gate := Gate))
          (conceptFormationGamble Γ M A)
          (finite_credalRange_bddBelow (gateCredalSet (Gate := Gate))
            (conceptFormationGamble Γ M A))
          hmem
      simpa [gateCredalSet, conceptFormationGamble, hg₀] using hle
    · apply le_lowerEnvelope_of_forall_le
        (gateCredalSet (Gate := Gate))
        (gateCredalSet_nonempty (Gate := Gate))
        (conceptFormationGamble Γ M A)
      intro P hP
      rcases hP with ⟨g, rfl⟩
      rw [if_neg hLower]
      by_cases hg :
          A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M <;>
        simp [conceptFormationGamble, hg]

theorem upperEnvelope_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    upperEnvelope (gateCredalSet (Gate := Gate))
        (conceptFormationGamble Γ M A) =
      if A ∈ upperConceptFamily Γ M then 1 else 0 := by
  classical
  by_cases hUpper : A ∈ upperConceptFamily Γ M
  · rcases hUpper with ⟨g₁, hg₁⟩
    apply le_antisymm
    · apply upperEnvelope_le_of_forall_le
        (gateCredalSet (Gate := Gate))
        (gateCredalSet_nonempty (Gate := Gate))
        (conceptFormationGamble Γ M A)
      intro P hP
      rcases hP with ⟨g, rfl⟩
      rw [if_pos ⟨g₁, hg₁⟩]
      by_cases hg :
          A ∈ AbstractInheritance.finiteConceptFamily (Γ g) M <;>
        simp [conceptFormationGamble, hg]
    · have hmem :
          PrecisePrevision.dirac g₁ ∈ gateCredalSet (Gate := Gate) :=
        ⟨g₁, rfl⟩
      have hge :=
        le_upperEnvelope_of_mem (gateCredalSet (Gate := Gate))
          (conceptFormationGamble Γ M A)
          (finite_credalRange_bddAbove (gateCredalSet (Gate := Gate))
            (conceptFormationGamble Γ M A))
          hmem
      rw [if_pos ⟨g₁, hg₁⟩]
      simpa [gateCredalSet, conceptFormationGamble, hg₁] using hge
  · have hAll :
        ∀ g : Gate, A ∉ AbstractInheritance.finiteConceptFamily (Γ g) M := by
      simpa [upperConceptFamily] using hUpper
    apply le_antisymm
    · apply upperEnvelope_le_of_forall_le
        (gateCredalSet (Gate := Gate))
        (gateCredalSet_nonempty (Gate := Gate))
        (conceptFormationGamble Γ M A)
      intro P hP
      rcases hP with ⟨g, rfl⟩
      rw [if_neg hUpper]
      simp [conceptFormationGamble, hAll g]
    · obtain ⟨g₀⟩ := ‹Nonempty Gate›
      have hmem :
          PrecisePrevision.dirac g₀ ∈ gateCredalSet (Gate := Gate) :=
        ⟨g₀, rfl⟩
      have hge :=
        le_upperEnvelope_of_mem (gateCredalSet (Gate := Gate))
          (conceptFormationGamble Γ M A)
          (finite_credalRange_bddAbove (gateCredalSet (Gate := Gate))
            (conceptFormationGamble Γ M A))
          hmem
      rw [if_neg hUpper]
      simpa [gateCredalSet, conceptFormationGamble, hAll g₀] using hge

theorem credalEnvelopeWidth_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    credalEnvelopeWidth (gateCredalSet (Gate := Gate))
        (conceptFormationGamble Γ M A) =
      if A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M
      then 1 else 0 := by
  classical
  by_cases hLower : A ∈ lowerConceptFamily Γ M
  · have hUpper := lowerConceptFamily_subset_upperConceptFamily Γ M hLower
    rw [if_neg (show ¬ (A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M) by
      simp [hLower])]
    simp [credalEnvelopeWidth, lowerEnvelope_conceptFormationGamble_eq,
      upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]
  · by_cases hUpper : A ∈ upperConceptFamily Γ M
    · rw [if_pos ⟨hUpper, hLower⟩]
      simp [credalEnvelopeWidth, lowerEnvelope_conceptFormationGamble_eq,
        upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]
    · rw [if_neg (show ¬ (A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M) by
        simp [hUpper])]
      simp [credalEnvelopeWidth, lowerEnvelope_conceptFormationGamble_eq,
        upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]

theorem credalEnvelopeWidthComplement_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    credalEnvelopeWidthComplement (gateCredalSet (Gate := Gate))
        (conceptFormationGamble Γ M A) =
      if A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M
      then 0 else 1 := by
  classical
  by_cases hMixed : A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M
  · rw [if_pos hMixed]
    rw [credalEnvelopeWidthComplement,
      credalEnvelopeWidth_conceptFormationGamble_eq, if_pos hMixed]
    ring
  · rw [if_neg hMixed]
    rw [credalEnvelopeWidthComplement,
      credalEnvelopeWidth_conceptFormationGamble_eq, if_neg hMixed]
    ring

theorem credalEnvelopeMidpoint_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    credalEnvelopeMidpoint (gateCredalSet (Gate := Gate))
        (conceptFormationGamble Γ M A) =
      if A ∈ lowerConceptFamily Γ M then 1
      else if A ∈ upperConceptFamily Γ M then (1 / 2 : ℝ) else 0 := by
  classical
  by_cases hLower : A ∈ lowerConceptFamily Γ M
  · have hUpper := lowerConceptFamily_subset_upperConceptFamily Γ M hLower
    simp [credalEnvelopeMidpoint, lowerEnvelope_conceptFormationGamble_eq,
      upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]
  · by_cases hUpper : A ∈ upperConceptFamily Γ M
    · simp [credalEnvelopeMidpoint, lowerEnvelope_conceptFormationGamble_eq,
        upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]
    · simp [credalEnvelopeMidpoint, lowerEnvelope_conceptFormationGamble_eq,
        upperEnvelope_conceptFormationGamble_eq, hLower, hUpper]

theorem globalNaturalExtension_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalNaturalExtension
        (conceptFormationGamble Γ M A) =
      if A ∈ lowerConceptFamily Γ M then 1 else 0 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalNaturalExtension,
    lowerEnvelope_conceptFormationGamble_eq]

theorem globalEnvelopeWidth_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
        (conceptFormationGamble Γ M A) =
      if A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M
      then 1 else 0 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    credalEnvelopeWidth_conceptFormationGamble_eq]

theorem globalEnvelopeWidthComplement_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidthComplement
        (conceptFormationGamble Γ M A) =
      if A ∈ upperConceptFamily Γ M ∧ A ∉ lowerConceptFamily Γ M
      then 0 else 1 := by
  simp [gateCredalProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    credalEnvelopeWidthComplement_conceptFormationGamble_eq]

theorem globalEnvelopeMidpoint_conceptFormationGamble_eq
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeMidpoint
        (conceptFormationGamble Γ M A) =
      if A ∈ lowerConceptFamily Γ M then 1
      else if A ∈ upperConceptFamily Γ M then (1 / 2 : ℝ) else 0 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    credalEnvelopeMidpoint_conceptFormationGamble_eq]

end GateFamilies

namespace ObservationSurface

variable {Obs : Type u} {Obj : Type v} {Attr : Type w} {Q : Type z} {Gate : Type*}
variable [AddCommMonoid Q] [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

/-- Observation-level lower/upper credal concept family induced by a finite
family of admissible gates. -/
noncomputable def credalConceptFamily
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    Mettapedia.Logic.ConceptOntology.CredalConceptFamily Obj Attr :=
  Mettapedia.Logic.ConceptOntology.credalConceptFamily Γ (aggregate S σ)

def lowerConceptFamily
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    Set (DualConcept Obj Attr) :=
  Mettapedia.Logic.ConceptOntology.lowerConceptFamily Γ (aggregate S σ)

def upperConceptFamily
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    Set (DualConcept Obj Attr) :=
  Mettapedia.Logic.ConceptOntology.upperConceptFamily Γ (aggregate S σ)

/-- Robustly formed concepts induced by aggregated observations. -/
abbrev LowerFormedConcept
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :=
  Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ (aggregate S σ)

/-- Permissively formed concepts induced by aggregated observations. -/
abbrev UpperFormedConcept
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :=
  Mettapedia.Logic.ConceptOntology.UpperFormedConcept Γ (aggregate S σ)

noncomputable def lowerConceptFamilyFinset
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    Finset (DualConcept Obj Attr) :=
  Mettapedia.Logic.ConceptOntology.lowerConceptFamilyFinset Γ (aggregate S σ)

noncomputable def upperConceptFamilyFinset
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    Finset (DualConcept Obj Attr) :=
  Mettapedia.Logic.ConceptOntology.upperConceptFamilyFinset Γ (aggregate S σ)

/-- Interpretation of robust credally formed observation concepts. -/
noncomputable def lowerFormedConceptInterpretation
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    AbstractInheritance.Interpretation (LowerFormedConcept S Γ σ) Obj Attr :=
  Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ (aggregate S σ)

/-- Interpretation of permissively credally formed observation concepts. -/
noncomputable def upperFormedConceptInterpretation
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs) :
    AbstractInheritance.Interpretation (UpperFormedConcept S Γ σ) Obj Attr :=
  Mettapedia.Logic.ConceptOntology.upperFormedConceptInterpretation Γ (aggregate S σ)

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem lowerFormedConceptInterpretation_meaning
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : LowerFormedConcept S Γ σ) :
    (lowerFormedConceptInterpretation S Γ σ).meaning A = A.1 := rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem upperFormedConceptInterpretation_meaning
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : UpperFormedConcept S Γ σ) :
    (upperFormedConceptInterpretation S Γ σ).meaning A = A.1 := rfl

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_lowerConceptFamily_iff
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    A ∈ lowerConceptFamily S Γ σ ↔
      ∀ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) (aggregate S σ) := by
  simp [lowerConceptFamily]

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem mem_upperConceptFamily_iff
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    A ∈ upperConceptFamily S Γ σ ↔
      ∃ g : Gate, A ∈ AbstractInheritance.finiteConceptFamily (Γ g) (aggregate S σ) := by
  simp [upperConceptFamily]

@[simp] theorem mem_upperConceptFamily_singleton_iff
    (S : ObservationSurface Obs Obj Attr Q)
    (G : EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    A ∈ upperConceptFamily S (Gate := PUnit) (fun _ => G) σ ↔
      A ∈ finiteConceptFamily S G σ := by
  simp [upperConceptFamily, finiteConceptFamily]

@[simp] theorem mem_lowerConceptFamily_singleton_iff
    (S : ObservationSurface Obs Obj Attr Q)
    (G : EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    A ∈ lowerConceptFamily S (Gate := PUnit) (fun _ => G) σ ↔
      A ∈ finiteConceptFamily S G σ := by
  simp [lowerConceptFamily, finiteConceptFamily]

theorem upperConceptFamilyFinset_singleton_eq
    (S : ObservationSurface Obs Obj Attr Q)
    (G : EvidenceGate Q) (σ : Multiset Obs) :
    upperConceptFamilyFinset S (Gate := PUnit) (fun _ => G) σ =
      finiteConceptFamily S G σ := by
  classical
  ext A
  simp [upperConceptFamilyFinset, finiteConceptFamily]

theorem lowerConceptFamilyFinset_singleton_eq
    (S : ObservationSurface Obs Obj Attr Q)
    (G : EvidenceGate Q) (σ : Multiset Obs) :
    lowerConceptFamilyFinset S (Gate := PUnit) (fun _ => G) σ =
      finiteConceptFamily S G σ := by
  classical
  ext A
  simp [lowerConceptFamilyFinset, finiteConceptFamily]

noncomputable def conceptFormationGamble
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) : Gamble Gate :=
  Mettapedia.Logic.ConceptOntology.conceptFormationGamble Γ (aggregate S σ) A

theorem globalEnvelopeWidth_conceptFormationGamble_eq
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidth
        (conceptFormationGamble S Γ σ A) =
      if A ∈ upperConceptFamily S Γ σ ∧ A ∉ lowerConceptFamily S Γ σ then 1 else 0 := by
  simpa [conceptFormationGamble, lowerConceptFamily, upperConceptFamily] using
    Mettapedia.Logic.ConceptOntology.globalEnvelopeWidth_conceptFormationGamble_eq
      (Gate := Gate) Γ (aggregate S σ) A

theorem globalEnvelopeWidthComplement_conceptFormationGamble_eq
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeWidthComplement
        (conceptFormationGamble S Γ σ A) =
      if A ∈ upperConceptFamily S Γ σ ∧ A ∉ lowerConceptFamily S Γ σ then 0 else 1 := by
  simpa [conceptFormationGamble, lowerConceptFamily, upperConceptFamily] using
    Mettapedia.Logic.ConceptOntology.globalEnvelopeWidthComplement_conceptFormationGamble_eq
      (Gate := Gate) Γ (aggregate S σ) A

theorem globalEnvelopeMidpoint_conceptFormationGamble_eq
    (S : ObservationSurface Obs Obj Attr Q)
    (Γ : Gate → EvidenceGate Q) (σ : Multiset Obs)
    (A : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate)).globalEnvelopeMidpoint
        (conceptFormationGamble S Γ σ A) =
      if A ∈ lowerConceptFamily S Γ σ then 1
      else if A ∈ upperConceptFamily S Γ σ then (1 / 2 : ℝ) else 0 := by
  simpa [conceptFormationGamble, lowerConceptFamily, upperConceptFamily] using
    Mettapedia.Logic.ConceptOntology.globalEnvelopeMidpoint_conceptFormationGamble_eq
      (Gate := Gate) Γ (aggregate S σ) A

end ObservationSurface

end Mettapedia.Logic.ConceptOntology
