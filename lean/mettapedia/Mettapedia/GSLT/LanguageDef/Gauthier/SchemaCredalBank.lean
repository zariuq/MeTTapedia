import Mettapedia.GSLT.LanguageDef.Gauthier.PatternSourceSupport
import Mettapedia.KR.ConceptOntology.CredalFormation

/-!
# Credal banks of canonical program schemas

This module classifies role-indexed program schemas using the existing lower
and upper families of `CredalConceptFamily`.  A semantic interpretation maps a
canonical schema to an existing `DualConcept`; the three banks add no new
concept-formation semantics:

* robust schemas belong to the lower family;
* provisional schemas belong to the upper but not the lower family;
* rejected schemas do not belong to the upper family.

Raw patterns enter the classifier only through `canonicalSchema`.  Hence the
classification is invariant under concrete hole names and under swapping the
two inputs of anti-unification.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierPatternSupport
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptOntology

universe u v w z

variable {Obj : Type u} {Attr : Type v}

/-- Canonical schemas whose meanings survive every admissible credal gate. -/
def robustSchemaBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set SchemaPattern :=
  {schema | meaning schema ∈ family.lower}

/-- Canonical schemas whose meanings survive at least one, but not every,
admissible credal gate. -/
def provisionalSchemaBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set SchemaPattern :=
  {schema | meaning schema ∈ family.upper ∧ meaning schema ∉ family.lower}

/-- Canonical schemas whose meanings survive no admissible credal gate. -/
def rejectedSchemaBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set SchemaPattern :=
  {schema | meaning schema ∉ family.upper}

/-- Raw role-indexed patterns classified through their canonical schema
identity. -/
def robustPatternBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set Pattern :=
  {pattern | canonicalSchema pattern ∈ robustSchemaBank family meaning}

/-- Provisional raw patterns, classified through canonical identity. -/
def provisionalPatternBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set Pattern :=
  {pattern | canonicalSchema pattern ∈ provisionalSchemaBank family meaning}

/-- Rejected raw patterns, classified through canonical identity. -/
def rejectedPatternBank (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) : Set Pattern :=
  {pattern | canonicalSchema pattern ∈ rejectedSchemaBank family meaning}

@[simp] theorem mem_robustSchemaBank_iff
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ robustSchemaBank family meaning ↔
      meaning schema ∈ family.lower := Iff.rfl

@[simp] theorem mem_provisionalSchemaBank_iff
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ provisionalSchemaBank family meaning ↔
      meaning schema ∈ family.upper ∧ meaning schema ∉ family.lower := Iff.rfl

@[simp] theorem mem_rejectedSchemaBank_iff
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ rejectedSchemaBank family meaning ↔
      meaning schema ∉ family.upper := Iff.rfl

/-- The three schema banks exhaust all schemas. -/
theorem schema_bank_exhaustive (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ robustSchemaBank family meaning ∨
      schema ∈ provisionalSchemaBank family meaning ∨
      schema ∈ rejectedSchemaBank family meaning := by
  by_cases lower : meaning schema ∈ family.lower
  · exact Or.inl lower
  · by_cases upper : meaning schema ∈ family.upper
    · exact Or.inr (Or.inl ⟨upper, lower⟩)
    · exact Or.inr (Or.inr upper)

/-- Robust and provisional classifications are disjoint. -/
theorem robust_disjoint_provisional (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) :
    Disjoint (robustSchemaBank family meaning)
      (provisionalSchemaBank family meaning) := by
  rw [Set.disjoint_left]
  intro schema robust provisional
  exact provisional.2 robust

/-- Provisional and rejected classifications are disjoint. -/
theorem provisional_disjoint_rejected (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr) :
    Disjoint (provisionalSchemaBank family meaning)
      (rejectedSchemaBank family meaning) := by
  rw [Set.disjoint_left]
  intro schema provisional rejected
  exact rejected provisional.1

/-- If the credal lower family is contained in its upper family, robust and
rejected classifications are disjoint. -/
theorem robust_disjoint_rejected (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr)
    (lower_upper : family.lower ⊆ family.upper) :
    Disjoint (robustSchemaBank family meaning)
      (rejectedSchemaBank family meaning) := by
  rw [Set.disjoint_left]
  intro schema robust rejected
  exact rejected (lower_upper robust)

section GateFamily

variable {Q : Type w} {Gate : Type z}
variable [Preorder Q] [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

omit [Fintype Gate] [Nonempty Gate] in
/-- The robust bank is exactly lower credal concept formation under every
admissible gate. -/
theorem mem_robustSchemaBank_credal_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ robustSchemaBank (credalConceptFamily Γ M) meaning ↔
      ∀ gate : Gate,
        meaning schema ∈ finiteConceptFamily (Γ gate) M := by
  rfl

omit [Fintype Gate] [Nonempty Gate] in
/-- The provisional bank is exactly existential but not universal concept
formation over the admissible gate family. -/
theorem mem_provisionalSchemaBank_credal_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ provisionalSchemaBank (credalConceptFamily Γ M) meaning ↔
      (∃ gate : Gate, meaning schema ∈ finiteConceptFamily (Γ gate) M) ∧
      ¬ (∀ gate : Gate, meaning schema ∈ finiteConceptFamily (Γ gate) M) := by
  rfl

omit [Fintype Gate] [Nonempty Gate] in
/-- The rejected bank is exactly failure to form under every admissible
gate. -/
theorem mem_rejectedSchemaBank_credal_iff
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (meaning : SchemaPattern → DualConcept Obj Attr) (schema : SchemaPattern) :
    schema ∈ rejectedSchemaBank (credalConceptFamily Γ M) meaning ↔
      ¬ (∃ gate : Gate,
        meaning schema ∈ finiteConceptFamily (Γ gate) M) := by
  rfl

omit [Fintype Gate] in
/-- Every gate-induced credal schema family has three pairwise-disjoint
classifications. -/
theorem credal_schema_banks_pairwise_disjoint
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (meaning : SchemaPattern → DualConcept Obj Attr) :
    Disjoint (robustSchemaBank (credalConceptFamily Γ M) meaning)
        (provisionalSchemaBank (credalConceptFamily Γ M) meaning) ∧
      Disjoint (robustSchemaBank (credalConceptFamily Γ M) meaning)
        (rejectedSchemaBank (credalConceptFamily Γ M) meaning) ∧
      Disjoint (provisionalSchemaBank (credalConceptFamily Γ M) meaning)
        (rejectedSchemaBank (credalConceptFamily Γ M) meaning) := by
  exact ⟨robust_disjoint_provisional _ _,
    robust_disjoint_rejected _ _
      (credalConceptFamily_lower_subset_upper Γ M),
    provisional_disjoint_rejected _ _⟩

end GateFamily

/-! ## Canonical-representative invariance -/

/-- Equal canonical representatives have identical robust status. -/
theorem robustPatternBank_congr_of_canonicalSchema_eq
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr)
    {left right : Pattern}
    (equal : canonicalSchema left = canonicalSchema right) :
    left ∈ robustPatternBank family meaning ↔
      right ∈ robustPatternBank family meaning := by
  simp only [robustPatternBank, Set.mem_setOf_eq]
  rw [equal]

/-- Equal canonical representatives have identical provisional status. -/
theorem provisionalPatternBank_congr_of_canonicalSchema_eq
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr)
    {left right : Pattern}
    (equal : canonicalSchema left = canonicalSchema right) :
    left ∈ provisionalPatternBank family meaning ↔
      right ∈ provisionalPatternBank family meaning := by
  simp only [provisionalPatternBank, Set.mem_setOf_eq]
  rw [equal]

/-- Equal canonical representatives have identical rejected status. -/
theorem rejectedPatternBank_congr_of_canonicalSchema_eq
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr)
    {left right : Pattern}
    (equal : canonicalSchema left = canonicalSchema right) :
    left ∈ rejectedPatternBank family meaning ↔
      right ∈ rejectedPatternBank family meaning := by
  simp only [rejectedPatternBank, Set.mem_setOf_eq]
  rw [equal]

/-- Alpha-equivalent raw patterns have identical membership in all three
credal schema banks. -/
theorem alphaEquivalent_schema_bank_invariance
    (family : CredalConceptFamily Obj Attr)
    (meaning : SchemaPattern → DualConcept Obj Attr)
    {left right : Pattern} (alpha : AlphaEquivalent left right) :
    (left ∈ robustPatternBank family meaning ↔
        right ∈ robustPatternBank family meaning) ∧
      (left ∈ provisionalPatternBank family meaning ↔
        right ∈ provisionalPatternBank family meaning) ∧
      (left ∈ rejectedPatternBank family meaning ↔
        right ∈ rejectedPatternBank family meaning) := by
  have canonical : canonicalSchema left = canonicalSchema right :=
    (canonicalSchema_eq_iff_alphaEquivalent left right).2 alpha
  exact ⟨robustPatternBank_congr_of_canonicalSchema_eq _ _ canonical,
    provisionalPatternBank_congr_of_canonicalSchema_eq _ _ canonical,
    rejectedPatternBank_congr_of_canonicalSchema_eq _ _ canonical⟩

/-! ## Source support as an existing dual concept -/

/-- Interpret finite causal-root support as the extent of an existing
`DualConcept`; schema attributes supply its intent. -/
def sourceSupportConcept {pattern : Pattern} {Attr : Type v}
    (matchingRows : List (SourceMatch pattern)) (attributes : Set Attr) :
    DualConcept Nat Attr where
  extent := {root | root ∈ supportRoots matchingRows}
  intent := attributes

@[simp] theorem mem_sourceSupportConcept_extent_iff
    {pattern : Pattern} {Attr : Type v}
    (matchingRows : List (SourceMatch pattern)) (attributes : Set Attr)
    (root : Nat) :
    root ∈ (sourceSupportConcept matchingRows attributes).extent ↔
      root ∈ supportRoots matchingRows := Iff.rfl

@[simp] theorem sourceSupportConcept_intent
    {pattern : Pattern} {Attr : Type v}
    (matchingRows : List (SourceMatch pattern)) (attributes : Set Attr) :
    (sourceSupportConcept matchingRows attributes).intent = attributes := rfl

/-- Duplicating an authenticated matching row cannot change the extensional
meaning supplied to credal formation. -/
theorem sourceSupportConcept_duplicate {pattern : Pattern} {Attr : Type v}
    (matched : SourceMatch pattern) (rest : List (SourceMatch pattern))
    (attributes : Set Attr) :
    sourceSupportConcept (matched :: matched :: rest) attributes =
      sourceSupportConcept (matched :: rest) attributes := by
  apply DualConcept.ext
  · ext root
    simp [sourceSupportConcept, supportRoots_duplicate]
  · rfl

/-! ## Executable positive and negative bank controls -/

namespace Control

def robustConcept : DualConcept Bool Bool where
  extent := Set.univ
  intent := Set.univ

def provisionalConcept : DualConcept Bool Bool where
  extent := {true}
  intent := Set.univ

def rejectedConcept : DualConcept Bool Bool where
  extent := Set.univ
  intent := ∅

@[simp] theorem robustConcept_ne_provisionalConcept :
    robustConcept ≠ provisionalConcept := by
  intro equal
  have extentEqual := congrArg (fun concept => false ∈ concept.extent) equal
  simp [robustConcept, provisionalConcept] at extentEqual

@[simp] theorem robustConcept_ne_rejectedConcept :
    robustConcept ≠ rejectedConcept := by
  intro equal
  have intentEqual := congrArg (fun concept => true ∈ concept.intent) equal
  simp [robustConcept, rejectedConcept] at intentEqual

@[simp] theorem provisionalConcept_ne_rejectedConcept :
    provisionalConcept ≠ rejectedConcept := by
  intro equal
  have intentEqual := congrArg (fun concept => true ∈ concept.intent) equal
  simp [provisionalConcept, rejectedConcept] at intentEqual

@[simp] theorem provisionalConcept_ne_robustConcept :
    provisionalConcept ≠ robustConcept :=
  Ne.symm robustConcept_ne_provisionalConcept

@[simp] theorem rejectedConcept_ne_robustConcept :
    rejectedConcept ≠ robustConcept :=
  Ne.symm robustConcept_ne_rejectedConcept

@[simp] theorem rejectedConcept_ne_provisionalConcept :
    rejectedConcept ≠ provisionalConcept :=
  Ne.symm provisionalConcept_ne_rejectedConcept

/-- A small exact credal family used only to exercise all three bank outcomes. -/
def controlFamily : CredalConceptFamily Bool Bool where
  lower := {robustConcept}
  upper := {robustConcept, provisionalConcept}

/-- Executable interpretation with one robust, one provisional, and all other
schemas rejected. -/
def controlMeaning : SchemaPattern → DualConcept Bool Bool
  | .hole .root 0 => robustConcept
  | .hole .root 1 => provisionalConcept
  | _ => rejectedConcept

theorem root_zero_is_robust :
    SchemaPattern.hole .root 0 ∈
      robustSchemaBank controlFamily controlMeaning := by
  simp [robustSchemaBank, controlFamily, controlMeaning]

theorem root_one_is_provisional :
    SchemaPattern.hole .root 1 ∈
      provisionalSchemaBank controlFamily controlMeaning := by
  simp [provisionalSchemaBank, controlFamily, controlMeaning,
    provisionalConcept_ne_robustConcept]

theorem code_zero_is_rejected :
    SchemaPattern.hole .code 0 ∈
      rejectedSchemaBank controlFamily controlMeaning := by
  simp [rejectedSchemaBank, controlFamily, controlMeaning,
    rejectedConcept_ne_robustConcept, rejectedConcept_ne_provisionalConcept]

end Control

#print axioms schema_bank_exhaustive
#print axioms robust_disjoint_provisional
#print axioms provisional_disjoint_rejected
#print axioms robust_disjoint_rejected
#print axioms mem_robustSchemaBank_credal_iff
#print axioms mem_provisionalSchemaBank_credal_iff
#print axioms mem_rejectedSchemaBank_credal_iff
#print axioms credal_schema_banks_pairwise_disjoint
#print axioms alphaEquivalent_schema_bank_invariance
#print axioms sourceSupportConcept_duplicate
#print axioms Control.root_zero_is_robust
#print axioms Control.root_one_is_provisional
#print axioms Control.code_zero_is_rejected

end Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank
