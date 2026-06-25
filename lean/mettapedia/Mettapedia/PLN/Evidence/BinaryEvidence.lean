import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.PLN.Evidence.EvidenceClass
import Mettapedia.PLN.TruthValues.PLNWeightTV
import Mettapedia.Algebra.QuantaleWeakness

open scoped NNReal

/-!
# BinaryEvidence Quantale (BinaryEvidence Counts)

This file implements the **canonical quantale carrier** for evidence counts.

## The Key Insight (from GPT-5 Pro review)

Instead of trying to use `[0,1]` as the foundational carrier (where aggregating independent
evidence additively can exceed 1), we use **evidence counts**
`(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` as the carrier:

- `n⁺` = positive evidence (supports the proposition)
- `n⁻` = negative evidence (refutes the proposition)

This IS a proper quantale:
- Complete lattice: coordinatewise ≤ with sup/inf
- Monoid ⊗: coordinatewise multiplication
- Quantale law: ⊗ distributes over ⨆

Then `SimpleTruthValue (s, c)` becomes a **view** via the standard mapping:
- `s = n⁺ / (n⁺ + n⁻)`           (strength)
- `c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)` (confidence, with prior κ)

## Main Definitions

- `BinaryEvidence` : The evidence counts type
- `BinaryEvidence.tensor` : Quantale multiplication (sequential composition)
- `BinaryEvidence.hplus` : Parallel aggregation (independent evidence combination)
- `toSTV` / `ofSTV` : View functions to/from SimpleTruthValue

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter on truth-value formulas
- GPT-5 Pro review document (2025-12-09)
-/

namespace Mettapedia.PLN.Evidence.EvidenceQuantale

open scoped ENNReal
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction

/-! ## The BinaryEvidence Type

BinaryEvidence counts are pairs of extended non-negative reals representing
positive and negative support for a proposition.
-/

/-- BinaryEvidence counts: (positive support, negative support) -/
structure BinaryEvidence where
  pos : ℝ≥0∞  -- n⁺: positive evidence
  neg : ℝ≥0∞  -- n⁻: negative evidence
  deriving Inhabited

namespace BinaryEvidence

@[ext]
theorem ext' {e₁ e₂ : BinaryEvidence} (hp : e₁.pos = e₂.pos) (hn : e₁.neg = e₂.neg) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨hp, hn⟩

/-! ### Basic Operations -/

/-- Zero evidence: no support either way -/
def zero : BinaryEvidence := ⟨0, 0⟩

/-- Unit evidence for tensor product (multiplicative identity)
    Note: The unit is (1, 1) so that x ⊗ 1 = (x.pos * 1, x.neg * 1) = x -/
def one : BinaryEvidence := ⟨1, 1⟩

/-- Total evidence count: n⁺ + n⁻ -/
noncomputable def total (e : BinaryEvidence) : ℝ≥0∞ := e.pos + e.neg

/-! ### Lattice Structure (Coordinatewise)

The lattice order represents "information ordering" - more evidence is higher.
-/

instance : LE BinaryEvidence where
  le x y := x.pos ≤ y.pos ∧ x.neg ≤ y.neg

instance : LT BinaryEvidence where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

theorem le_def (x y : BinaryEvidence) : x ≤ y ↔ x.pos ≤ y.pos ∧ x.neg ≤ y.neg := Iff.rfl

/-- BinaryEvidence forms a partial order under coordinatewise ≤ -/
instance : PartialOrder BinaryEvidence where
  le := fun x y => x.pos ≤ y.pos ∧ x.neg ≤ y.neg
  le_refl := fun x => ⟨le_refl x.pos, le_refl x.neg⟩
  le_trans := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hyz_pos, hyz_neg⟩ =>
    ⟨le_trans hxy_pos hyz_pos, le_trans hxy_neg hyz_neg⟩
  le_antisymm := fun x y ⟨hxy_pos, hxy_neg⟩ ⟨hyx_pos, hyx_neg⟩ => by
    cases x; cases y
    simp at *
    exact ⟨le_antisymm hxy_pos hyx_pos, le_antisymm hxy_neg hyx_neg⟩

instance : Bot BinaryEvidence where
  bot := ⟨0, 0⟩

instance : Top BinaryEvidence where
  top := ⟨⊤, ⊤⟩

/-! ### Quantale Multiplication (Sequential Composition)

When evidence flows through a chain A → B → C, the evidence compounds multiplicatively.
This is the ⊗ operation in the quantale.
-/

/-- Tensor product: sequential composition of evidence
    (n⁺₁, n⁻₁) ⊗ (n⁺₂, n⁻₂) = (n⁺₁ * n⁺₂, n⁻₁ * n⁻₂)

    Interpretation: If A→B has evidence (n⁺₁, n⁻₁) and B→C has evidence (n⁺₂, n⁻₂),
    then the "direct path" A→B→C has evidence that compounds multiplicatively.
-/
noncomputable def tensor (x y : BinaryEvidence) : BinaryEvidence :=
  ⟨x.pos * y.pos, x.neg * y.neg⟩

noncomputable instance : Mul BinaryEvidence := ⟨tensor⟩

theorem tensor_def (x y : BinaryEvidence) : x * y = ⟨x.pos * y.pos, x.neg * y.neg⟩ := rfl

/-- Tensor is commutative -/
theorem tensor_comm (x y : BinaryEvidence) : x * y = y * x := by
  simp only [tensor_def, mul_comm]

/-- Tensor is associative -/
theorem tensor_assoc (x y z : BinaryEvidence) : (x * y) * z = x * (y * z) := by
  simp only [tensor_def, mul_assoc]

/-- One is the tensor unit -/
theorem tensor_one (x : BinaryEvidence) : x * one = x := by
  simp only [tensor_def, one, mul_one]

theorem one_tensor (x : BinaryEvidence) : one * x = x := by
  rw [tensor_comm, tensor_one]

noncomputable instance : CommMonoid BinaryEvidence where
  mul := tensor
  mul_assoc := tensor_assoc
  one := one
  one_mul := one_tensor
  mul_one := tensor_one
  mul_comm := tensor_comm

/-! ### Parallel Aggregation (Independent BinaryEvidence)

When we have independent sources of evidence, they combine additively.
This is the ⊕ operation (separate from the lattice join).
-/

/-- Parallel combination: independent evidence sources add
    (n⁺₁, n⁻₁) ⊕ (n⁺₂, n⁻₂) = (n⁺₁ + n⁺₂, n⁻₁ + n⁻₂)

    Interpretation: Two independent observations supporting/refuting a proposition
    contribute additively to the total evidence.
-/
noncomputable def hplus (x y : BinaryEvidence) : BinaryEvidence :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩

noncomputable instance : Add BinaryEvidence := ⟨hplus⟩

theorem hplus_def (x y : BinaryEvidence) : x + y = ⟨x.pos + y.pos, x.neg + y.neg⟩ := rfl

theorem hplus_comm (x y : BinaryEvidence) : x + y = y + x := by
  simp only [hplus_def, add_comm]

theorem hplus_assoc (x y z : BinaryEvidence) : (x + y) + z = x + (y + z) := by
  simp only [hplus_def, add_assoc]

theorem hplus_zero (x : BinaryEvidence) : x + zero = x := by
  simp only [hplus_def, zero, add_zero]

theorem zero_hplus (x : BinaryEvidence) : zero + x = x := by
  simp only [hplus_def, zero, zero_add]

instance : Zero BinaryEvidence := ⟨zero⟩

/-! ### EvidenceType / AddCommMonoid (Revision Algebra)

PLN revision combines independent evidence additively:
`(n⁺₁,n⁻₁) ⊕ (n⁺₂,n⁻₂) = (n⁺₁+n⁺₂, n⁻₁+n⁻₂)`.

Register this as an `AddCommMonoid` instance so it can be used uniformly via
`EvidenceClass.EvidenceType`.
-/

noncomputable instance : AddCommMonoid BinaryEvidence where
  add := (· + ·)
  add_assoc := hplus_assoc
  zero := (0 : BinaryEvidence)
  zero_add := zero_hplus
  add_zero := hplus_zero
  nsmul := nsmulRec
  nsmul_zero := by
    intro x
    rfl
  nsmul_succ := by
    intro n x
    rfl
  add_comm := hplus_comm

noncomputable instance : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType BinaryEvidence where

/-! ### Division (Quotient Operation)

Division is needed for conditional probability calculations like Inheritance.
Uses safe division: returns 0 when dividing by 0.
-/

/-- Division: coordinatewise quotient with safe zero handling
    (n⁺₁, n⁻₁) / (n⁺₂, n⁻₂) = (n⁺₁/n⁺₂, n⁻₁/n⁻₂)

    Returns 0 when dividing by 0 to avoid undefined behavior.

    Interpretation: Used for conditional probability calculations.
    For Inheritance(A,B), we compute weakness(A ∩ B) / weakness(A),
    giving P(B|A) - the conditional probability that a member of A is also in B.
-/
noncomputable def div (x y : BinaryEvidence) : BinaryEvidence :=
  ⟨if y.pos = 0 then 0 else x.pos / y.pos,
   if y.neg = 0 then 0 else x.neg / y.neg⟩

noncomputable instance : Div BinaryEvidence := ⟨div⟩

theorem div_def (x y : BinaryEvidence) :
    x / y = ⟨if y.pos = 0 then 0 else x.pos / y.pos,
             if y.neg = 0 then 0 else x.neg / y.neg⟩ := rfl

/-! ### Lattice Structure

BinaryEvidence forms a complete lattice with coordinatewise operations:
- Meet (⊓): coordinatewise min
- Join (⊔): coordinatewise max
- Inf (⨅): coordinatewise infimum
- Sup (⨆): coordinatewise supremum

This gives BinaryEvidence the structure of a Frame, which is needed for the
lambda theory fibration.
-/

/-- Meet: coordinatewise minimum -/
def inf (x y : BinaryEvidence) : BinaryEvidence :=
  ⟨min x.pos y.pos, min x.neg y.neg⟩

/-- Join: coordinatewise maximum -/
def sup (x y : BinaryEvidence) : BinaryEvidence :=
  ⟨max x.pos y.pos, max x.neg y.neg⟩

/-- Infimum of a set: coordinatewise infimum (using ENNReal's sInf) -/
noncomputable def evidenceSInf (S : Set BinaryEvidence) : BinaryEvidence :=
  ⟨sInf (BinaryEvidence.pos '' S), sInf (BinaryEvidence.neg '' S)⟩

/-- Supremum of a set: coordinatewise supremum (using ENNReal's sSup) -/
noncomputable def evidenceSSup (S : Set BinaryEvidence) : BinaryEvidence :=
  ⟨sSup (BinaryEvidence.pos '' S), sSup (BinaryEvidence.neg '' S)⟩

/-- BinaryEvidence is a complete lattice under coordinatewise operations -/
noncomputable instance : CompleteLattice BinaryEvidence where
  -- Binary operations
  inf := inf
  sup := sup
  -- Top and bottom
  top := ⟨⊤, ⊤⟩
  bot := ⟨0, 0⟩
  le_top := fun x => ⟨le_top, le_top⟩
  bot_le := fun x => ⟨bot_le, bot_le⟩
  -- Binary meet/join laws
  inf_le_left := fun x y => by
    show inf x y ≤ x
    simp [inf, le_def]
  inf_le_right := fun x y => by
    show inf x y ≤ y
    simp [inf, le_def]
  le_inf := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hxz_pos, hxz_neg⟩ => by
    show x ≤ inf y z
    simp [inf, le_def, *]
  le_sup_left := fun x y => by
    show x ≤ sup x y
    simp [sup, le_def]
  le_sup_right := fun x y => by
    show y ≤ sup x y
    simp [sup, le_def]
  sup_le := fun x y z ⟨hxy_pos, hxy_neg⟩ ⟨hyz_pos, hyz_neg⟩ => by
    show sup x y ≤ z
    simp [sup, le_def, *]
  -- Complete lattice operations
  sSup := evidenceSSup
  sInf := evidenceSInf
  -- 4.31 `CompleteLattice` field shape: `isLUB_sSup`/`isGLB_sInf` replace the four
  -- `le_sSup`/`sSup_le`/`sInf_le`/`le_sInf` fields.  An `IsLUB S a` bundles the
  -- upper-bound fact (`le_sSup`) and the least-upper-bound fact (`sSup_le`) as
  -- `a ∈ upperBounds S ∧ a ∈ lowerBounds (upperBounds S)`; dually for `IsGLB`.
  isLUB_sSup := fun S => by
    refine ⟨fun x hx => ?_, fun x h => ?_⟩
    · -- `evidenceSSup S` is an upper bound (former `le_sSup`).
      simp only [evidenceSSup, le_def]
      exact ⟨le_sSup (Set.mem_image_of_mem BinaryEvidence.pos hx),
             le_sSup (Set.mem_image_of_mem BinaryEvidence.neg hx)⟩
    · -- `evidenceSSup S` is below every upper bound (former `sSup_le`).
      simp only [evidenceSSup, le_def]
      refine ⟨?_, ?_⟩
      · apply sSup_le
        intro p hp
        simp only [Set.mem_image] at hp
        obtain ⟨e, heS, rfl⟩ := hp
        exact (h heS).1
      · apply sSup_le
        intro n hn
        simp only [Set.mem_image] at hn
        obtain ⟨e, heS, rfl⟩ := hn
        exact (h heS).2
  isGLB_sInf := fun S => by
    refine ⟨fun x hx => ?_, fun x h => ?_⟩
    · -- `evidenceSInf S` is a lower bound (former `sInf_le`).
      simp only [evidenceSInf, le_def]
      exact ⟨sInf_le (Set.mem_image_of_mem BinaryEvidence.pos hx),
             sInf_le (Set.mem_image_of_mem BinaryEvidence.neg hx)⟩
    · -- `evidenceSInf S` is above every lower bound (former `le_sInf`).
      simp only [evidenceSInf, le_def]
      refine ⟨?_, ?_⟩
      · apply le_sInf
        intro p hp
        simp only [Set.mem_image] at hp
        obtain ⟨e, heS, rfl⟩ := hp
        exact (h heS).1
      · apply le_sInf
        intro n hn
        simp only [Set.mem_image] at hn
        obtain ⟨e, heS, rfl⟩ := hn
        exact (h heS).2

/-! ### Heyting Algebra Structure

BinaryEvidence forms a Heyting algebra with coordinatewise operations.
Since ENNReal has Heyting structure, the product BinaryEvidence = ENNReal × ENNReal
inherits it coordinatewise.
-/

/-- Heyting implication: coordinatewise residuation
    For ENNReal: a ⇨ b = if a ≤ b then ⊤ else b (Gödel implication)

    Interpretation: (n⁺₁, n⁻₁) ⇨ (n⁺₂, n⁻₂) gives the "weakest" evidence
    that makes the first imply the second.
-/
noncomputable def himp (a b : BinaryEvidence) : BinaryEvidence :=
  ⟨if a.pos ≤ b.pos then ⊤ else b.pos,
   if a.neg ≤ b.neg then ⊤ else b.neg⟩

/-- Complement: negation via Heyting implication with ⊥
    ¬a = a ⇨ ⊥ = a ⇨ (0, 0)
-/
noncomputable def compl (a : BinaryEvidence) : BinaryEvidence :=
  himp a ⊥

/-- The residuation law (Frame signature): a ≤ b ⇨ c ↔ a ⊓ b ≤ c -/
theorem le_himp_iff (a b c : BinaryEvidence) : a ≤ himp b c ↔ a ⊓ b ≤ c := by
  simp only [himp, le_def]
  constructor
  · intro ⟨ha_pos, ha_neg⟩
    constructor
    · by_cases hbc_pos : b.pos ≤ c.pos
      · simp only [hbc_pos, ite_true] at ha_pos
        calc min a.pos b.pos ≤ b.pos := min_le_right a.pos b.pos
          _ ≤ c.pos := hbc_pos
      · simp only [hbc_pos, ite_false] at ha_pos
        calc min a.pos b.pos ≤ a.pos := min_le_left a.pos b.pos
          _ ≤ c.pos := ha_pos
    · by_cases hbc_neg : b.neg ≤ c.neg
      · simp only [hbc_neg, ite_true] at ha_neg
        calc min a.neg b.neg ≤ b.neg := min_le_right a.neg b.neg
          _ ≤ c.neg := hbc_neg
      · simp only [hbc_neg, ite_false] at ha_neg
        calc min a.neg b.neg ≤ a.neg := min_le_left a.neg b.neg
          _ ≤ c.neg := ha_neg
  · intro ⟨h_pos, h_neg⟩
    -- Rewrite (a ⊓ b).pos = min a.pos b.pos etc.
    have h_inf_pos : (a ⊓ b).pos = min a.pos b.pos := rfl
    have h_inf_neg : (a ⊓ b).neg = min a.neg b.neg := rfl
    rw [h_inf_pos] at h_pos
    rw [h_inf_neg] at h_neg
    constructor
    · by_cases hbc_pos : b.pos ≤ c.pos
      · simp only [hbc_pos, ite_true]
        exact le_top
      · simp only [hbc_pos, ite_false]
        -- When ¬(b.pos ≤ c.pos), i.e., c.pos < b.pos
        -- We have h_pos : min a.pos b.pos ≤ c.pos
        -- Since min a.pos b.pos ≤ c.pos < b.pos, min must equal a.pos
        -- Therefore a.pos ≤ c.pos
        push_neg at hbc_pos
        have h_min_lt : min a.pos b.pos < b.pos := lt_of_le_of_lt h_pos hbc_pos
        have h_min_eq : min a.pos b.pos = a.pos := by
          by_contra h_neq
          have := min_eq_right (le_of_not_ge (fun h => h_neq (min_eq_left h)))
          rw [this] at h_min_lt
          exact lt_irrefl b.pos h_min_lt
        rw [h_min_eq] at h_pos
        exact h_pos
    · by_cases hbc_neg : b.neg ≤ c.neg
      · simp only [hbc_neg, ite_true]
        exact le_top
      · simp only [hbc_neg, ite_false]
        -- Same reasoning for the negative component
        push_neg at hbc_neg
        have h_min_lt : min a.neg b.neg < b.neg := lt_of_le_of_lt h_neg hbc_neg
        have h_min_eq : min a.neg b.neg = a.neg := by
          by_contra h_neq
          have := min_eq_right (le_of_not_ge (fun h => h_neq (min_eq_left h)))
          rw [this] at h_min_lt
          exact lt_irrefl b.neg h_min_lt
        rw [h_min_eq] at h_neg
        exact h_neg

/-- a ⇨ ⊥ = ¬a (definition of complement) -/
theorem himp_bot (a : BinaryEvidence) : himp a ⊥ = compl a := by
  rfl  -- By definition: compl a = himp a ⊥

/-- BinaryEvidence is a Frame (complete Heyting algebra)! -/
noncomputable instance : Order.Frame BinaryEvidence where
  himp := himp
  le_himp_iff := le_himp_iff
  compl := compl
  himp_bot := himp_bot

/-! ### Mathlib Theorems Now Available

After the `Order.Frame BinaryEvidence` instance above, these Mathlib theorems apply automatically:
- `le_himp_iff` : `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` (Frame residuation)
- `himp_bot` : `a ⇨ ⊥ = aᶜ` (complement definition)
- `inf_sSup_eq` : `a ⊓ sSup S = ⨆ b ∈ S, a ⊓ b` (Frame distributivity)
- `compl_compl_le_compl` and other Heyting complement laws

Use these directly via typeclass inference rather than BinaryEvidence-specific versions.
The proofs above (`le_himp_iff`, `himp_bot`) establish that BinaryEvidence satisfies
the Frame axioms; after the instance, general Frame/Heyting theory applies.
-/

/-! ### Quantale Structure

BinaryEvidence forms a commutative quantale under tensor product.
The tensor distributes over suprema coordinatewise.
-/

lemma iSup_pos {ι} (f : ι → BinaryEvidence) :
    (⨆ i, f i).pos = ⨆ i, (f i).pos := by
  -- `iSup` is `sSup` of `Set.range`; project the positive coordinate.
  change (evidenceSSup (Set.range f)).pos = sSup (Set.range fun i => (f i).pos)
  have hset : Set.range (fun i => (f i).pos) = BinaryEvidence.pos '' Set.range f := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  -- use `hset` to rewrite the range to an image
  simp [evidenceSSup, hset]

lemma iSup_neg {ι} (f : ι → BinaryEvidence) :
    (⨆ i, f i).neg = ⨆ i, (f i).neg := by
  change (evidenceSSup (Set.range f)).neg = sSup (Set.range fun i => (f i).neg)
  have hset : Set.range (fun i => (f i).neg) = BinaryEvidence.neg '' Set.range f := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  simp [evidenceSSup, hset]

lemma iSup_image_ennreal {α β} (s : Set α) (f : α → β) (g : β → ℝ≥0∞) :
    (⨆ b ∈ f '' s, g b) = ⨆ a ∈ s, g (f a) := by
  classical
  refine le_antisymm ?h1 ?h2
  · refine iSup₂_le ?_
    intro b hb
    rcases hb with ⟨a, ha, rfl⟩
    exact le_iSup_of_le a (le_iSup_of_le ha (le_rfl))
  · refine iSup₂_le ?_
    intro a ha
    have hfa : f a ∈ f '' s := ⟨a, ha, rfl⟩
    exact le_iSup_of_le (f a) (le_iSup_of_le hfa (le_rfl))

lemma iSup_pos_mul_right (a : BinaryEvidence) (s : Set BinaryEvidence) :
    (⨆ b ∈ s, a * b).pos = ⨆ b ∈ s, a.pos * b.pos := by
  classical
  have h1 : (⨆ b : {b // b ∈ s}, a * b.1) = ⨆ b ∈ s, a * b := by
    simpa using (iSup_subtype'' s (fun b => a * b))
  calc
    (⨆ b ∈ s, a * b).pos
        = (⨆ b : {b // b ∈ s}, a * b.1).pos := by
            simpa using congrArg BinaryEvidence.pos h1.symm
    _ = ⨆ b : {b // b ∈ s}, (a * b.1).pos := by
            simpa using (iSup_pos (fun b : {b // b ∈ s} => a * b.1))
    _ = ⨆ b : {b // b ∈ s}, a.pos * b.1.pos := by
            simp [tensor_def]
    _ = ⨆ b ∈ s, a.pos * b.pos := by
            exact (iSup_subtype'' s (fun b => a.pos * b.pos))

lemma iSup_neg_mul_right (a : BinaryEvidence) (s : Set BinaryEvidence) :
    (⨆ b ∈ s, a * b).neg = ⨆ b ∈ s, a.neg * b.neg := by
  classical
  have h1 : (⨆ b : {b // b ∈ s}, a * b.1) = ⨆ b ∈ s, a * b := by
    simpa using (iSup_subtype'' s (fun b => a * b))
  calc
    (⨆ b ∈ s, a * b).neg
        = (⨆ b : {b // b ∈ s}, a * b.1).neg := by
            simpa using congrArg BinaryEvidence.neg h1.symm
    _ = ⨆ b : {b // b ∈ s}, (a * b.1).neg := by
            simpa using (iSup_neg (fun b : {b // b ∈ s} => a * b.1))
    _ = ⨆ b : {b // b ∈ s}, a.neg * b.1.neg := by
            simp [tensor_def]
    _ = ⨆ b ∈ s, a.neg * b.neg := by
            exact (iSup_subtype'' s (fun b => a.neg * b.neg))

lemma iSup_pos_mul_left (s : Set BinaryEvidence) (b : BinaryEvidence) :
    (⨆ a ∈ s, a * b).pos = ⨆ a ∈ s, a.pos * b.pos := by
  classical
  have h1 : (⨆ a : {a // a ∈ s}, a.1 * b) = ⨆ a ∈ s, a * b := by
    simpa using (iSup_subtype'' s (fun a => a * b))
  calc
    (⨆ a ∈ s, a * b).pos
        = (⨆ a : {a // a ∈ s}, a.1 * b).pos := by
            simpa using congrArg BinaryEvidence.pos h1.symm
    _ = ⨆ a : {a // a ∈ s}, (a.1 * b).pos := by
            simpa using (iSup_pos (fun a : {a // a ∈ s} => a.1 * b))
    _ = ⨆ a : {a // a ∈ s}, a.1.pos * b.pos := by
            simp [tensor_def]
    _ = ⨆ a ∈ s, a.pos * b.pos := by
            exact (iSup_subtype'' s (fun a => a.pos * b.pos))

lemma iSup_neg_mul_left (s : Set BinaryEvidence) (b : BinaryEvidence) :
    (⨆ a ∈ s, a * b).neg = ⨆ a ∈ s, a.neg * b.neg := by
  classical
  have h1 : (⨆ a : {a // a ∈ s}, a.1 * b) = ⨆ a ∈ s, a * b := by
    simpa using (iSup_subtype'' s (fun a => a * b))
  calc
    (⨆ a ∈ s, a * b).neg
        = (⨆ a : {a // a ∈ s}, a.1 * b).neg := by
            simpa using congrArg BinaryEvidence.neg h1.symm
    _ = ⨆ a : {a // a ∈ s}, (a.1 * b).neg := by
            simpa using (iSup_neg (fun a : {a // a ∈ s} => a.1 * b))
    _ = ⨆ a : {a // a ∈ s}, a.1.neg * b.neg := by
            simp [tensor_def]
    _ = ⨆ a ∈ s, a.neg * b.neg := by
            exact (iSup_subtype'' s (fun a => a.neg * b.neg))

/-- Tensor distributes over suprema from the right. -/
theorem tensor_sSup_right (a : BinaryEvidence) (s : Set BinaryEvidence) :
    a * sSup s = ⨆ b ∈ s, (a * b) := by
  ext
  · -- pos coordinate
    show a.pos * (sSup s).pos = (⨆ b ∈ s, a * b).pos
    change a.pos * (evidenceSSup s).pos = _
    have h_rhs : (⨆ b ∈ s, a * b).pos = ⨆ b ∈ s, a.pos * b.pos := by
      simpa using (iSup_pos_mul_right (a:=a) (s:=s))
    rw [h_rhs]
    simp only [evidenceSSup, ENNReal.mul_sSup]
    -- rewrite the index set for the supremum
    simpa using (iSup_image_ennreal (s:=s) (f:=BinaryEvidence.pos) (g:=fun p => a.pos * p))
  · -- neg coordinate
    show a.neg * (sSup s).neg = (⨆ b ∈ s, a * b).neg
    change a.neg * (evidenceSSup s).neg = _
    have h_rhs : (⨆ b ∈ s, a * b).neg = ⨆ b ∈ s, a.neg * b.neg := by
      simpa using (iSup_neg_mul_right (a:=a) (s:=s))
    rw [h_rhs]
    simp only [evidenceSSup, ENNReal.mul_sSup]
    simpa using (iSup_image_ennreal (s:=s) (f:=BinaryEvidence.neg) (g:=fun p => a.neg * p))

/-- Tensor distributes over suprema from the left. -/
theorem tensor_sSup_left (s : Set BinaryEvidence) (b : BinaryEvidence) :
    sSup s * b = ⨆ a ∈ s, (a * b) := by
  ext
  · -- pos coordinate
    show (sSup s).pos * b.pos = (⨆ a ∈ s, a * b).pos
    change (evidenceSSup s).pos * b.pos = _
    have h_rhs : (⨆ a ∈ s, a * b).pos = ⨆ a ∈ s, a.pos * b.pos := by
      simpa using (iSup_pos_mul_left (s:=s) (b:=b))
    rw [h_rhs]
    simp only [evidenceSSup, ENNReal.sSup_mul]
    simpa using (iSup_image_ennreal (s:=s) (f:=BinaryEvidence.pos) (g:=fun p => p * b.pos))
  · -- neg coordinate
    show (sSup s).neg * b.neg = (⨆ a ∈ s, a * b).neg
    change (evidenceSSup s).neg * b.neg = _
    have h_rhs : (⨆ a ∈ s, a * b).neg = ⨆ a ∈ s, a.neg * b.neg := by
      simpa using (iSup_neg_mul_left (s:=s) (b:=b))
    rw [h_rhs]
    simp only [evidenceSSup, ENNReal.sSup_mul]
    simpa using (iSup_image_ennreal (s:=s) (f:=BinaryEvidence.neg) (g:=fun p => p * b.neg))

/-- BinaryEvidence is a quantale under tensor product -/
instance : IsQuantale BinaryEvidence where
  mul_sSup_distrib := tensor_sSup_right
  sSup_mul_distrib := tensor_sSup_left

/-- BinaryEvidence is a commutative quantale -/
instance : Mettapedia.Algebra.QuantaleWeakness.IsCommQuantale BinaryEvidence where

/-! ### View to SimpleTruthValue

BinaryEvidence now has FULL Frame structure (complete Heyting algebra)!
- CompleteLattice: ⊓, ⊔, ⨅, ⨆, ⊥, ⊤
- Heyting implication: ⇨ (residuation)
- Complement: ¬ (negation)

This is exactly what PLN's lambda theory fibration needs!

The calibrated mapping between evidence counts and (strength, confidence).
Uses a prior parameter κ > 0.
-/

variable (κ : ℝ≥0∞) -- Prior/context size parameter

/-- Convert evidence counts to strength: s = n⁺ / (n⁺ + n⁻)
    Returns 0 if total evidence is 0 (undefined case).

    Note: This is the "improper prior" case (α₀ = β₀ = 0).
    For context-aware strength, use `strengthWith`. -/
noncomputable def toStrength (e : BinaryEvidence) : ℝ≥0∞ :=
  if e.total = 0 then 0 else e.pos / e.total

/-! ### Context-Aware Strength (Modal BinaryEvidence Theory)

The strength formula depends on the interpretation context (prior parameters).
The improper prior (α₀ = β₀ = 0) gives the "self-contained" formula above.
-/

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- Context-aware strength computation.
    This is the full Bayesian posterior mean for a Beta(α₀, β₀) prior:
    strength = (α₀ + pos) / (α₀ + β₀ + pos + neg)

    When ctx is the improper prior (α₀ = β₀ = 0), this equals `toStrength`. -/
noncomputable def strengthWith (ctx : BinaryContext) (e : BinaryEvidence) : ℝ≥0∞ :=
  (ctx.α₀ + e.pos) / (ctx.α₀ + ctx.β₀ + e.pos + e.neg)

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- The improper prior gives the same result as `toStrength`.
    This is the backward-compatibility theorem. -/
theorem strengthWith_improper (e : BinaryEvidence) :
    strengthWith BinaryContext.improper e = toStrength e := by
  unfold strengthWith toStrength BinaryContext.improper total
  simp only [zero_add]
  split_ifs with h
  · -- e.pos + e.neg = 0 in ENNReal means e.pos = 0 and e.neg = 0
    simp only [add_eq_zero] at h
    simp only [h.1, ENNReal.zero_div]
  · rfl

-- Helper lemma: 0.5 + 0.5 = 1 in ℝ≥0∞
-- ENNReal numeric literals are coercions from NNReal
private lemma ennreal_half_add_half : (0.5 : ℝ≥0∞) + 0.5 = 1 := by
  have eq1 : (0.5 : ℝ≥0∞) + 0.5 = (↑(0.5 : ℝ≥0) : ℝ≥0∞) + ↑(0.5 : ℝ≥0) := rfl
  have eq2 : (↑(0.5 : ℝ≥0) : ℝ≥0∞) + ↑(0.5 : ℝ≥0) = ↑((0.5 : ℝ≥0) + (0.5 : ℝ≥0)) :=
    (ENNReal.coe_add _ _).symm
  have eq3 : ((0.5 : ℝ≥0) + (0.5 : ℝ≥0)) = (1 : ℝ≥0) := by
    ext; simp only [NNReal.coe_add, NNReal.coe_one]; norm_num
  calc (0.5 : ℝ≥0∞) + 0.5
      = ↑((0.5 : ℝ≥0) + 0.5) := by rw [eq1, eq2]
    _ = ↑(1 : ℝ≥0) := by rw [eq3]
    _ = 1 := rfl

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- With the Jeffreys prior (α₀ = β₀ = 0.5), the formula adds 0.5 to each count.
    This is a "minimax" prior that minimizes worst-case prediction error. -/
theorem strengthWith_jeffreys (e : BinaryEvidence) :
    strengthWith BinaryContext.jeffreys e =
    (0.5 + e.pos) / (1 + e.pos + e.neg) := by
  unfold strengthWith BinaryContext.jeffreys
  congr 1
  -- Goal: 0.5 + 0.5 + e.pos + e.neg = 1 + e.pos + e.neg
  calc (0.5 : ℝ≥0∞) + 0.5 + e.pos + e.neg
      = (0.5 + 0.5) + e.pos + e.neg := by ring
    _ = 1 + e.pos + e.neg := by rw [ennreal_half_add_half]

/-- Convert evidence counts to confidence: c = total / (total + κ)
    Higher total evidence → higher confidence (approaches 1 as evidence → ∞) -/
noncomputable def toConfidence (e : BinaryEvidence) : ℝ≥0∞ :=
  e.total / (e.total + κ)

/-- Convert evidence to SimpleTruthValue (as reals in [0,1]) -/
noncomputable def toSTV (e : BinaryEvidence) : ℝ × ℝ :=
  ((toStrength e).toReal, (toConfidence κ e).toReal)

/-- Convert SimpleTruthValue to evidence counts (inverse of toSTV)
    Given (s, c) and prior κ, recover (n⁺, n⁻):
    - total = κ * c / (1 - c)
    - n⁺ = s * total
    - n⁻ = (1 - s) * total
-/
noncomputable def ofSTV (s c : ℝ) (_hc : c < 1) : BinaryEvidence :=
  let total : ℝ≥0∞ := κ * ENNReal.ofReal c / ENNReal.ofReal (1 - c)
  ⟨ENNReal.ofReal s * total, ENNReal.ofReal (1 - s) * total⟩

/-! ### Weight-Primary Truth Value Bridge -/

open Mettapedia.PLN.TruthValues.PLNWeightTV

/-- Diagnostic: odds-style ratio `n⁺/n⁻` (extended to `⊤` when `n⁻ = 0`).

This is **not** the PLN "weight" used for confidence plumbing (`w2c/w2c`).
It is occasionally useful for intuition/debugging, but it should not be fed to
`PLNWeightTV.w2c`, since `w2c (n⁺/n⁻) = n⁺/(n⁺+n⁻)` would collapse confidence to strength. -/
noncomputable def toOdds (e : BinaryEvidence) : ℝ≥0∞ :=
  if e.neg = 0 then ⊤ else e.pos / e.neg

/-- Log-odds diagnostic view induced by `toOdds`. -/
noncomputable def toLogOdds (e : BinaryEvidence) : ℝ :=
  Real.log (toOdds e).toReal

/-- Support/truth odds `n⁺ / n⁻` on the strength/direction axis.

This is a naming alias for `toOdds`, kept distinct from confidence odds
`c / (1 - c)` on the evidence-weight/concentration axis. -/
noncomputable def truthOdds (e : BinaryEvidence) : ℝ≥0∞ :=
  toOdds e

/-- Log support/truth odds on the strength/direction axis. -/
noncomputable def truthLogOdds (e : BinaryEvidence) : ℝ :=
  toLogOdds e

/-- Nondegenerate case of `toOdds`: when `neg ≠ 0`, odds are `pos/neg`. -/
@[simp] lemma toOdds_eq_div (e : BinaryEvidence) (hneg : e.neg ≠ 0) :
    toOdds e = e.pos / e.neg := by
  simp [toOdds, hneg]

@[simp] theorem truthOdds_eq_toOdds (e : BinaryEvidence) :
    truthOdds e = toOdds e :=
  rfl

@[simp] theorem truthLogOdds_eq_toLogOdds (e : BinaryEvidence) :
    truthLogOdds e = toLogOdds e :=
  rfl

/-- Tensor multiplication is multiplicative in odds space. -/
theorem toOdds_tensor_mul (x y : BinaryEvidence)
    (hx : x.neg ≠ 0) (hy : y.neg ≠ 0) :
    toOdds (x * y) = toOdds x * toOdds y := by
  have hxy : x.neg * y.neg ≠ 0 := mul_ne_zero hx hy
  rw [toOdds_eq_div (e := x * y) (by simpa [BinaryEvidence.tensor_def] using hxy),
      toOdds_eq_div (e := x) hx, toOdds_eq_div (e := y) hy]
  simp [BinaryEvidence.tensor_def]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [← (ENNReal.mul_inv (Or.inl hx) (Or.inr hy)).symm]
  ring

/-- Tensor multiplication is multiplicative in support/truth-odds space. -/
theorem truthOdds_tensor_mul (x y : BinaryEvidence)
    (hx : x.neg ≠ 0) (hy : y.neg ≠ 0) :
    truthOdds (x * y) = truthOdds x * truthOdds y := by
  simpa [truthOdds] using toOdds_tensor_mul x y hx hy

/-- Tensor multiplication is additive in log-odds space (finite/nonzero regime). -/
theorem toLogOdds_tensor_add (x y : BinaryEvidence)
    (hx_neg : x.neg ≠ 0) (hy_neg : y.neg ≠ 0)
    (hx_odds0 : toOdds x ≠ 0) (hy_odds0 : toOdds y ≠ 0)
    (hx_oddsTop : toOdds x ≠ ⊤) (hy_oddsTop : toOdds y ≠ ⊤) :
    toLogOdds (x * y) = toLogOdds x + toLogOdds y := by
  have hmul : toOdds (x * y) = toOdds x * toOdds y :=
    toOdds_tensor_mul x y hx_neg hy_neg
  have hx_pos_real : 0 < (toOdds x).toReal := ENNReal.toReal_pos hx_odds0 hx_oddsTop
  have hy_pos_real : 0 < (toOdds y).toReal := ENNReal.toReal_pos hy_odds0 hy_oddsTop
  calc
    toLogOdds (x * y)
        = Real.log ((toOdds x * toOdds y).toReal) := by
            simp [toLogOdds, hmul]
    _ = Real.log ((toOdds x).toReal * (toOdds y).toReal) := by
          simp [ENNReal.toReal_mul]
    _ = Real.log (toOdds x).toReal + Real.log (toOdds y).toReal := by
          simpa using Real.log_mul (ne_of_gt hx_pos_real) (ne_of_gt hy_pos_real)
    _ = toLogOdds x + toLogOdds y := by
          simp [toLogOdds]

/-- Tensor multiplication is additive in log support/truth-odds space
(finite/nonzero regime). -/
theorem truthLogOdds_tensor_add (x y : BinaryEvidence)
    (hx_neg : x.neg ≠ 0) (hy_neg : y.neg ≠ 0)
    (hx_odds0 : truthOdds x ≠ 0) (hy_odds0 : truthOdds y ≠ 0)
    (hx_oddsTop : truthOdds x ≠ ⊤) (hy_oddsTop : truthOdds y ≠ ⊤) :
    truthLogOdds (x * y) = truthLogOdds x + truthLogOdds y := by
  simpa [truthOdds, truthLogOdds] using
    toLogOdds_tensor_add x y hx_neg hy_neg hx_odds0 hy_odds0 hx_oddsTop hy_oddsTop

/-- Regraduation by exponentiation in evidence space.

This is the canonical power operation used for informativeness weighting. -/
noncomputable def power (e : BinaryEvidence) (w : ℝ) : BinaryEvidence :=
  ⟨e.pos ^ w, e.neg ^ w⟩

@[simp] theorem power_pos (e : BinaryEvidence) (w : ℝ) :
    (power e w).pos = e.pos ^ w := rfl

@[simp] theorem power_neg (e : BinaryEvidence) (w : ℝ) :
    (power e w).neg = e.neg ^ w := rfl

/-- Odds under regraduation are exponentiated (finite nonnegative exponent regime). -/
theorem toOdds_power_rpow (e : BinaryEvidence) (w : ℝ)
    (hw : 0 ≤ w) (hneg : e.neg ≠ 0) :
    toOdds (power e w) = (toOdds e) ^ w := by
  have hpow_neg_ne_zero : e.neg ^ w ≠ 0 := by
    intro h0
    rcases (ENNReal.rpow_eq_zero_iff).1 h0 with h | h
    · exact hneg h.1
    · linarith [hw, h.2]
  rw [toOdds_eq_div (e := power e w) hpow_neg_ne_zero, toOdds_eq_div (e := e) hneg]
  simp [power, ENNReal.div_rpow_of_nonneg, hw]

/-- Log-odds under regraduation scale linearly with the exponent
in the finite nonnegative exponent regime. -/
theorem toLogOdds_power_mul (e : BinaryEvidence) (w : ℝ)
    (hw : 0 ≤ w)
    (hneg : e.neg ≠ 0)
    (hodds0 : toOdds e ≠ 0) (hoddsTop : toOdds e ≠ ⊤) :
    toLogOdds (power e w) = w * toLogOdds e := by
  have hpow : toOdds (power e w) = (toOdds e) ^ w :=
    toOdds_power_rpow e w hw hneg
  have hpos_real : 0 < (toOdds e).toReal := ENNReal.toReal_pos hodds0 hoddsTop
  calc
    toLogOdds (power e w)
        = Real.log (((toOdds e) ^ w).toReal) := by
            simp [toLogOdds, hpow]
    _ = Real.log (((toOdds e).toReal) ^ w) := by
          simp [ENNReal.toReal_rpow]
    _ = w * Real.log (toOdds e).toReal := by
          simpa using (Real.log_rpow hpos_real w)
    _ = w * toLogOdds e := by
          simp [toLogOdds]

/-- Regraduation composes multiplicatively in the exponent. -/
@[simp] theorem power_power (e : BinaryEvidence) (a b : ℝ) :
    power (power e a) b = power e (a * b) := by
  apply BinaryEvidence.ext'
  · simp [power, ENNReal.rpow_mul]
  · simp [power, ENNReal.rpow_mul]

/-- Inverse regraduation recovers the original evidence for nonzero exponent. -/
@[simp] theorem power_power_inv (e : BinaryEvidence) (w : ℝ) (hw : w ≠ 0) :
    power (power e w) w⁻¹ = e := by
  apply BinaryEvidence.ext'
  · simpa [power] using (ENNReal.rpow_rpow_inv hw e.pos)
  · simpa [power] using (ENNReal.rpow_rpow_inv hw e.neg)

/-- Regraduation and inverse-regraduation commute in the opposite order as well. -/
@[simp] theorem power_inv_power (e : BinaryEvidence) (w : ℝ) (hw : w ≠ 0) :
    power (power e w⁻¹) w = e := by
  apply BinaryEvidence.ext'
  · simpa [power] using (ENNReal.rpow_inv_rpow hw e.pos)
  · simpa [power] using (ENNReal.rpow_inv_rpow hw e.neg)

/-- Canary theorem: odds are unchanged by regrade-then-unregrade. -/
@[simp] theorem toOdds_power_power_inv (e : BinaryEvidence) (w : ℝ) (hw : w ≠ 0) :
    toOdds (power (power e w) w⁻¹) = toOdds e := by
  simp [power_power_inv (e := e) (w := w) hw]

/-- Canary theorem: log-odds are unchanged by regrade-then-unregrade. -/
@[simp] theorem toLogOdds_power_power_inv (e : BinaryEvidence) (w : ℝ) (hw : w ≠ 0) :
    toLogOdds (power (power e w) w⁻¹) = toLogOdds e := by
  simp [power_power_inv (e := e) (w := w) hw]

/-- BinaryEvidence weight corresponding to the standard confidence↔weight transform.

For a prior size `κ`, PLN confidence is:
`c = total / (total + κ)`.

Define the (dimensionless) weight:
`w = c/(1-c) = total/κ` (for `κ > 0`).

Then `w2c w = w/(w+1) = total/(total+κ) = c`.
-/
noncomputable def toWeight (κ : ℝ≥0∞) (e : BinaryEvidence) : ℝ≥0∞ :=
  e.total / κ

/-- toStrength is always ≤ 1 -/
lemma toStrength_le_one (e : BinaryEvidence) : toStrength e ≤ 1 := by
  unfold toStrength
  split_ifs
  · norm_num
  · -- pos / (pos + neg) ≤ 1 since pos ≤ pos + neg
    trans ((e.pos + e.neg) / (e.pos + e.neg))
    · apply ENNReal.div_le_div_right
      exact le_self_add
    · simp

/-- Convert evidence to weight-primary truth value.
This is the natural representation: strength from `toStrength`, and weight computed
so that `WTV.confidence` matches `toConfidence κ` (up to the `c2w` saturation at `c = 1`). -/
noncomputable def toWTV (κ : ℝ≥0∞) (e : BinaryEvidence) : WTV where
  strength := (toStrength e).toReal
  weight := c2w (toConfidence κ e).toReal
  strength_nonneg := by
    apply ENNReal.toReal_nonneg
  strength_le_one := by
    have h := toStrength_le_one e
    have : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    rw [this] at h
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h
  weight_nonneg := by
    by_cases hconf : (toConfidence κ e).toReal < 1
    · -- Main case: use the `c/(1-c)` branch.
      exact Mettapedia.PLN.TruthValues.PLNWeightTV.WTV.c2w_nonneg _ (by
        exact ENNReal.toReal_nonneg) hconf
    · -- Saturation branch (`c ≥ 1`) returns a positive constant.
      unfold c2w
      simp [hconf]

theorem toWTV_confidence_eq_toConfidence (κ : ℝ≥0∞) (e : BinaryEvidence)
    (hconf : (toConfidence κ e).toReal < 1) :
    (toWTV κ e).confidence = (toConfidence κ e).toReal := by
  -- Expand the definitions: confidence = w2c(weight) and weight = c2w(confidence).
  simp [toWTV, WTV.confidence, w2c, c2w, hconf]
  -- Goal is the standard identity: w2c(c2w(c)) = c for c < 1.
  have h1 : (1 - (toConfidence κ e).toReal) ≠ 0 := by linarith
  field_simp [h1]
  ring

/-! ### Key Lemmas for the View

These connect the algebraic operations on BinaryEvidence to the standard PLN formulas.
-/

/-- Parallel combination in STV view corresponds to weighted averaging.
    This is PLN's revision rule!

    Note: We require total ≠ ⊤ to ensure the division algebra works correctly in ENNReal.
-/
theorem toStrength_hplus (x y : BinaryEvidence)
    (hx : x.total ≠ 0) (hy : y.total ≠ 0) (hxy : (x + y).total ≠ 0)
    (hx_ne_top : x.total ≠ ⊤) (hy_ne_top : y.total ≠ ⊤) :
    toStrength (x + y) =
    (x.total / (x + y).total) * toStrength x + (y.total / (x + y).total) * toStrength y := by
  -- The algebra: (x.pos + y.pos) / total_xy =
  --   (x.total / total_xy) * (x.pos / x.total) + (y.total / total_xy) * (y.pos / y.total)
  unfold toStrength
  simp only [hx, hy, hxy, ↓reduceIte]
  simp only [hplus_def, total] at *
  -- Key lemma: (a/T) * (p/a) = p/T when a ≠ 0, a ≠ ⊤
  have key : ∀ (p a T : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → (a / T) * (p / a) = p / T := by
    intros p a T ha0 haT
    rw [mul_comm, ← mul_div_assoc, ENNReal.div_mul_cancel ha0 haT]
  have h1 : (x.pos + x.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (x.pos / (x.pos + x.neg)) =
            x.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key x.pos (x.pos + x.neg) _ hx hx_ne_top
  have h2 : (y.pos + y.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (y.pos / (y.pos + y.neg)) =
            y.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key y.pos (y.pos + y.neg) _ hy hy_ne_top
  rw [h1, h2, ← ENNReal.add_div]

/-- The tensor product strength is at least the product of strengths.
    This shows that sequential composition preserves more positive evidence than
    the naive product formula would suggest.

    Mathematically: (x⁺y⁺)/(x⁺y⁺ + x⁻y⁻) ≥ (x⁺/(x⁺+x⁻)) * (y⁺/(y⁺+y⁻))
-/
theorem toStrength_tensor_ge (x y : BinaryEvidence) :
    toStrength (x * y) ≥ toStrength x * toStrength y := by
  unfold toStrength total
  simp only [tensor_def]
  -- Goal: (if x.pos * y.pos + x.neg * y.neg = 0 then 0 else (x.pos * y.pos) / ...)
  --       ≥ (if x.pos + x.neg = 0 then 0 else ...) * (if y.pos + y.neg = 0 then 0 else ...)
  by_cases hx : x.pos + x.neg = 0
  · -- x.total = 0: RHS has factor 0
    simp only [hx, ↓reduceIte, zero_mul, zero_le]
  · by_cases hy : y.pos + y.neg = 0
    · -- y.total = 0: RHS has factor 0
      simp only [hy, ↓reduceIte, mul_zero, zero_le]
    · -- Both totals nonzero
      simp only [hx, hy, ↓reduceIte]
      by_cases hxy : x.pos * y.pos + x.neg * y.neg = 0
      · -- Tensor total = 0: means x.pos * y.pos = 0 AND x.neg * y.neg = 0
        simp only [hxy, ↓reduceIte]
        -- LHS = 0, need 0 ≥ RHS (actually need to show RHS = 0)
        -- From hxy: x.pos * y.pos = 0, so either x.pos = 0 or y.pos = 0
        have hpos : x.pos * y.pos = 0 := (add_eq_zero.mp hxy).1
        -- So x.pos = 0 or y.pos = 0
        simp only [mul_eq_zero] at hpos
        rcases hpos with hxp | hyp
        · -- x.pos = 0
          rw [hxp, zero_add, ENNReal.zero_div, zero_mul]
        · -- y.pos = 0: goal has x.pos / (x.pos + x.neg) * (0 / (0 + y.neg))
          rw [hyp, zero_add, ENNReal.zero_div, mul_zero]
      · -- Main case: all totals nonzero
        simp only [hxy, ↓reduceIte]
        -- Need: (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg) ≥
        --       (x.pos / (x.pos + x.neg)) * (y.pos / (y.pos + y.neg))
        -- First rewrite RHS using div_mul_div_comm to get same numerator
        -- For ENNReal, we prove this directly using div = mul_inv
        have h_rhs : x.pos / (x.pos + x.neg) * (y.pos / (y.pos + y.neg)) =
                     (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          -- ENNReal.mul_inv : (a ≠ 0 ∨ b ≠ ⊤) → (a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹
          -- a = x.pos + x.neg, b = y.pos + y.neg
          -- We have hx : a ≠ 0 and hy : b ≠ 0
          rw [← (ENNReal.mul_inv (Or.inl hx) (Or.inr hy)).symm]
          ring
        rw [h_rhs, ge_iff_le]
        -- Now need: (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) ≤
        --           (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg)
        apply ENNReal.div_le_div_left
        -- Need: x.pos * y.pos + x.neg * y.neg ≤ (x.pos + x.neg) * (y.pos + y.neg)
        calc x.pos * y.pos + x.neg * y.neg
            ≤ x.pos * y.pos + x.neg * y.neg + (x.pos * y.neg + x.neg * y.pos) := by
              apply le_add_of_nonneg_right
              exact zero_le
          _ = (x.pos + x.neg) * (y.pos + y.neg) := by ring

end BinaryEvidence

/-! ## Q-Weighted Relations

A knowledge base is a Q-weighted relation: for each pair (A, B) of propositions,
we have an evidence value representing "A implies B."
-/

/-- A Q-weighted relation over types α and β -/
structure QRel (α β : Type*) where
  w : α → β → BinaryEvidence

namespace QRel

variable {α β γ : Type*}

/-- Composition of Q-weighted relations for finite intermediate type
    (R ∘ S)(A, C) = ⨆_B R(A,B) ⊗ S(B,C)

    For finite β, we compute this as a supremum over enumerated elements.
-/
noncomputable def comp [Fintype β] (R : QRel α β) (S : QRel β γ) : QRel α γ where
  w a c :=
    -- Take coordinatewise max over all path products
    ⟨Finset.univ.sup (fun b => (R.w a b * S.w b c).pos),
     Finset.univ.sup (fun b => (R.w a b * S.w b c).neg)⟩

/-- Identity relation: full evidence on the diagonal -/
def id [DecidableEq α] : QRel α α where
  w a b := if a = b then BinaryEvidence.one else BinaryEvidence.zero

/-- Composition gives at least each individual path contribution.

    The PLN deduction formula computes the strength of A→C given A→B and B→C.
    In the Q-weighted relations view, this is just composition.

    The key insight: the "direct path" term `sAB * sBC` comes from the tensor product,
    while the "indirect path via ¬B" term comes from considering the complement.
-/
theorem comp_is_deduction [Fintype β] (R : QRel α β) (S : QRel β γ) (a : α) (c : γ) :
    -- The composition gives at least the direct path contribution
    ∀ b, R.w a b * S.w b c ≤ (comp R S).w a c := by
  intro b
  unfold comp
  simp only [BinaryEvidence.le_def, BinaryEvidence.tensor_def]
  constructor
  · -- pos component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).pos)
    exact Finset.mem_univ b
  · -- neg component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).neg)
    exact Finset.mem_univ b

end QRel

/-! ## Residuation: The Right Adjoint to Tensor

Following the OSLF (Operational Semantics in Logical Form) framework, the PLN deduction
formula decomposes into two parts:
1. **Direct path**: A → B → C via tensor composition (⊗)
2. **Indirect path**: A → ¬B → C via residuation (⇒)

The full formula is: P(C|A) = P(B|A)·P(C|B) + P(¬B|A)·P(C|¬B)

In quantale terms, residuation is the right adjoint to tensor:
  x ⊗ y ≤ z  iff  y ≤ x ⇒ z

For evidence counts, this corresponds to:
  (x.pos * y.pos, x.neg * y.neg) ≤ (z.pos, z.neg)
  iff y ≤ residuate x z

The key insight from OSLF/Native Type Theory is that types are pairs (U, X) where:
- X is a "sort" (the kind of evidence)
- U is a "filter" on X (a subset/predicate on evidence)

For PLN, this maps to:
- X = BinaryEvidence (the carrier type)
- U = a filter defined by strength/confidence constraints
-/

namespace BinaryEvidence

/-- Residuation for evidence: the right adjoint to tensor.

    In the quantale [0,1], residuation is: x ⇒ z = min(1, z/x) if x > 0, else 1
    For evidence counts, we compute the "maximal y such that x ⊗ y ≤ z".

    Note: This is a partial operation - only meaningful when x ≠ 0.
    When x.pos = 0 or x.neg = 0, we return ⊤ for that component.
-/
noncomputable def residuate (x z : BinaryEvidence) : BinaryEvidence :=
  ⟨if x.pos = 0 then ⊤ else z.pos / x.pos,
   if x.neg = 0 then ⊤ else z.neg / x.neg⟩

/-- Residuation is right adjoint to tensor: x ⊗ y ≤ z iff y ≤ x ⇒ z

    Note: We require z ≠ ⊤ (componentwise) for the equivalence to hold cleanly.
    In the ⊤ case, both sides are trivially true (everything ≤ ⊤).
-/
theorem residuate_adjoint (x y z : BinaryEvidence)
    (hx_pos : x.pos ≠ 0) (hx_neg : x.neg ≠ 0)
    (hz_pos : z.pos ≠ ⊤) (hz_neg : z.neg ≠ ⊤) :
    x * y ≤ z ↔ y ≤ residuate x z := by
  unfold residuate
  simp only [hx_pos, hx_neg, ↓reduceIte, le_def, tensor_def]
  constructor
  · -- Forward: x ⊗ y ≤ z implies y ≤ x ⇒ z
    intro ⟨h_pos, h_neg⟩
    constructor
    · -- y.pos ≤ z.pos / x.pos
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_pos) (Or.inr hz_pos)]
      rw [mul_comm]
      exact h_pos
    · -- y.neg ≤ z.neg / x.neg
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_neg) (Or.inr hz_neg)]
      rw [mul_comm]
      exact h_neg
  · -- Backward: y ≤ x ⇒ z implies x ⊗ y ≤ z
    intro ⟨h_pos, h_neg⟩
    constructor
    · -- x.pos * y.pos ≤ z.pos
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_pos) (Or.inr hz_pos), mul_comm] at h_pos
      exact h_pos
    · -- x.neg * y.neg ≤ z.neg
      rw [ENNReal.le_div_iff_mul_le (Or.inl hx_neg) (Or.inr hz_neg), mul_comm] at h_neg
      exact h_neg

/-! ### The Full Deduction Formula via Quantale Operations

The PLN deduction formula can be expressed in terms of evidence operations:

```
P(C|A) = P(B|A) · P(C|B) + (1 - P(B|A)) · P(C|¬B)
       = sAB · sBC + (1 - sAB) · (pC - pB·sBC)/(1 - pB)
```

In evidence terms:
- Direct path: tensor(E_AB, E_BC) contributes sAB · sBC
- Indirect path: residuate(E_B, E_C) gives evidence for C|¬B

The full formula requires:
1. Marginals P(A), P(B), P(C) as context
2. BinaryEvidence E_AB for A→B and E_BC for B→C
3. Computation of P(C|¬B) via the complement formula
-/

/-- Strength of the "indirect path" P(C|¬B) = (P(C) - P(B)·P(C|B)) / (1 - P(B))

    This is the complement term in the deduction formula.
    It represents the probability of C given that we went through ¬B.
-/
noncomputable def complementStrength (pB pC sBC : ℝ≥0∞) : ℝ≥0∞ :=
  if pB = 1 then 0  -- Degenerate case: no ¬B path
  else (pC - pB * sBC) / (1 - pB)

/-- The full deduction formula expressed in evidence terms.

    Given:
    - E_AB: BinaryEvidence for A → B (with strength sAB = toStrength E_AB)
    - E_BC: BinaryEvidence for B → C (with strength sBC = toStrength E_BC)
    - pB: Prior probability P(B)
    - pC: Prior probability P(C)

    Returns evidence for A → C combining direct and indirect paths.

    Note: This is a simplified version that computes the strength directly.
    A full formalization would also track confidence through the computation.
-/
noncomputable def deductionEvidence
    (E_AB E_BC : BinaryEvidence)
    (pB pC : ℝ≥0∞)
    (_hE_AB : E_AB.total ≠ 0) (_hE_BC : E_BC.total ≠ 0)
    (_hpB : pB ≠ 1) : BinaryEvidence :=
  let sAB := toStrength E_AB
  let sBC := toStrength E_BC
  let direct := sAB * sBC
  let indirect := (1 - sAB) * complementStrength pB pC sBC
  let total_strength := direct + indirect
  -- Create evidence with this strength and combined total evidence
  let total_ev := E_AB.total + E_BC.total
  ⟨total_strength * total_ev, (1 - total_strength) * total_ev⟩

/-! ### Connecting BinaryEvidence to the Real-Valued Deduction Formula

The key connection between BinaryEvidence and PLNDeduction.simpleDeductionStrengthFormula:
- BinaryEvidence operations work on (n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞
- The deduction formula works on strengths s ∈ ℝ (in [0,1])
- The toStrength map connects them: s = n⁺ / (n⁺ + n⁻)

The main insight is that the deduction formula:
  sAC = sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)

Can be decomposed into:
  sAC = [direct path contribution] + [indirect path contribution]

Where:
- Direct path: A → B → C via tensor (gives sAB * sBC term)
- Indirect path: A → ¬B → C via residuation (gives the (1-sAB) * P(C|¬B) term)
-/

/-- The direct path strength: sAB * sBC
    This is the first term in the deduction formula. -/
noncomputable def directPathStrength (sAB sBC : ℝ≥0∞) : ℝ≥0∞ := sAB * sBC

/-- The indirect path strength: (1 - sAB) * P(C|¬B)
    This is the second term in the deduction formula. -/
noncomputable def indirectPathStrength (sAB pB pC sBC : ℝ≥0∞) : ℝ≥0∞ :=
  (1 - sAB) * complementStrength pB pC sBC

/-- The full deduction strength from component strengths.
    sAC = sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)
-/
noncomputable def deductionStrength (sAB sBC pB pC : ℝ≥0∞) : ℝ≥0∞ :=
  directPathStrength sAB sBC + indirectPathStrength sAB pB pC sBC

/-- Helper: toStrength of a constructed evidence is just the strength.
    If we construct evidence with pos = s*t and neg = (1-s)*t where s ≤ 1,
    then toStrength returns s.
-/
theorem toStrength_of_scaled (s t : ℝ≥0∞) (hs : s ≤ 1) (ht0 : t ≠ 0) (htT : t ≠ ⊤) :
    toStrength ⟨s * t, (1 - s) * t⟩ = s := by
  unfold toStrength total
  simp only
  have h_sum : s * t + (1 - s) * t = t := by
    rw [← add_mul, add_tsub_cancel_of_le hs, one_mul]
  rw [h_sum, if_neg ht0]
  exact ENNReal.mul_div_cancel_right ht0 htT

/-- When converted to strengths, deductionEvidence produces the deduction formula.

    This is the key theorem connecting BinaryEvidence-based computation to the
    real-valued formula in PLNDeduction.simpleDeductionStrengthFormula.

    The strength of deductionEvidence E_AB E_BC is:
      toStrength (deductionEvidence E_AB E_BC pB pC)
      = toStrength E_AB * toStrength E_BC
        + (1 - toStrength E_AB) * complementStrength pB pC (toStrength E_BC)

    Note: We require the total_strength ≤ 1 condition for the ENNReal arithmetic
    to work correctly (otherwise `a + (1 - a)` might not equal 1).
-/
theorem deductionEvidence_strength
    (E_AB E_BC : BinaryEvidence)
    (pB pC : ℝ≥0∞)
    (hE_AB : E_AB.total ≠ 0) (hE_BC : E_BC.total ≠ 0)
    (hpB : pB ≠ 1)
    (h_total_ne_zero : (E_AB.total + E_BC.total) ≠ 0)
    (h_total_ne_top : (E_AB.total + E_BC.total) ≠ ⊤)
    (h_strength_le_1 : deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC ≤ 1) :
    toStrength (deductionEvidence E_AB E_BC pB pC hE_AB hE_BC hpB) =
    deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC := by
  -- The deductionEvidence constructs evidence with structure:
  --   pos = s * total_ev
  --   neg = (1 - s) * total_ev
  -- where s = deductionStrength and total_ev = E_AB.total + E_BC.total
  set s := deductionStrength (toStrength E_AB) (toStrength E_BC) pB pC with hs_def
  set t := E_AB.total + E_BC.total with ht_def
  -- Show that deductionEvidence produces ⟨s * t, (1 - s) * t⟩
  have h_ev_eq : deductionEvidence E_AB E_BC pB pC hE_AB hE_BC hpB = ⟨s * t, (1 - s) * t⟩ := rfl
  rw [h_ev_eq]
  exact toStrength_of_scaled s t h_strength_le_1 h_total_ne_zero h_total_ne_top

end BinaryEvidence

/-! ## Connection to OSLF Modal Types

The OSLF algorithm generates modal types from rewrite rules. For PLN:

- `◊B` (possibly B) corresponds to evidence that supports B
- `⧫A` (was-possibly A) corresponds to evidence that came from A
- `⟨E⟩B` (after evidence E, possibly B) is the rely-possibly modality

The deduction rule A → B → C can be typed as:
  Γ ⊢ E_AB : A ↠ B    Δ ⊢ E_BC : B ↠ C
  ─────────────────────────────────────────
  Γ, Δ ⊢ comp(E_AB, E_BC) : A ↠ C

Where `↠` is the evidence-weighted implication type.

The tensor product `E_AB ⊗ E_BC` gives the "direct path" evidence,
and residuation gives the "indirect path" contribution.

This categorical structure (NT(CCC) in OSLF terminology) provides:
1. A topos structure with complete Heyting algebra homs
2. Modal operators from the rewrite semantics
3. Spatial types from term constructors
4. Behavioral types from reduction rules

For PLN, the key insight is that truth values form an enriched category
over the unit interval quantale [0,1], and the deduction formula is
precisely the composition law in this enriched category.
-/

/-! ## Summary

We now have:

1. `BinaryEvidence` : A proper commutative monoid with tensor product
2. `BinaryEvidence.hplus` : Parallel aggregation for independent evidence
3. `toSTV` / `ofSTV` : Views to/from SimpleTruthValue
4. `QRel` : Q-weighted relations with composition
5. `BinaryEvidence.residuate` : Right adjoint to tensor (for ¬B path)
6. `BinaryEvidence.deductionEvidence` : Full deduction formula in evidence terms

The deduction formula emerges as:
- **Direct path**: tensor product E_AB ⊗ E_BC (proven lower bound via `toStrength_tensor_ge`)
- **Indirect path**: via `complementStrength` and `residuate`
- **Full formula**: `deductionEvidence` combines both paths

## Connection to OSLF/Native Type Theory

The OSLF framework (Meredith & Stay) shows that spatial-behavioral type systems
can be algorithmically generated from rewrite systems. For PLN:

1. **Native Type Theory**: Types are pairs (U, X) = (filter, sort)
   - For PLN: X = BinaryEvidence carrier, U = strength/confidence constraints

2. **Modal Types from Rewrites**: The deduction rule generates modal types
   - `⟨E_AB⟩⟨E_BC⟩C` = evidence that A leads to C via B

3. **Quantale Structure**: The unit interval [0,1] with multiplication
   forms a commutative quantale, and PLN is the enriched category over it

4. **Residuation**: The right adjoint to tensor gives the "¬B path" term
   - `x ⊗ y ≤ z ↔ y ≤ x ⇒ z` (proven in `residuate_adjoint`)

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter on truth-value formulas
- Meredith & Stay, "Operational Semantics in Logical Form" (OSLF)
- Williams & Stay, "Native Type Theory" - topos-theoretic foundations
- Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/

/-! ## Meta-BinaryEvidence: Learning Hyperparameters (AGI Layer)

For AGI applications, hyperparameters themselves need to be learned from prediction accuracy.
This requires evidence about evidence (meta-level).

The key insight: meta-evidence records how well our context (prior) predicted outcomes.
If predictions are systematically off, we adjust the prior.
-/

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- A single prediction record: context, evidence, predicted strength, actual outcome -/
structure PredictionRecord where
  /-- The context used for prediction -/
  ctx : BinaryContext
  /-- The evidence at prediction time -/
  evidence : BinaryEvidence
  /-- The predicted probability (strength with context) -/
  prediction : ℝ≥0∞
  /-- The actual outcome: true = positive, false = negative -/
  actual : Bool

instance : Inhabited PredictionRecord :=
  ⟨⟨default, default, 0, false⟩⟩

namespace PredictionRecord

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- Create a prediction record from context and evidence -/
noncomputable def make (ctx : BinaryContext) (e : BinaryEvidence) (actual : Bool) : PredictionRecord :=
  ⟨ctx, e, BinaryEvidence.strengthWith ctx e, actual⟩

/-- The prediction error: |prediction - actual| where actual ∈ {0, 1} -/
noncomputable def error (r : PredictionRecord) : ℝ≥0∞ :=
  if r.actual then 1 - r.prediction else r.prediction

/-- Squared error for Brier score -/
noncomputable def squaredError (r : PredictionRecord) : ℝ≥0∞ :=
  (error r) * (error r)

end PredictionRecord

/-- Meta-evidence: a list of prediction records for learning priors -/
structure BinaryMetaEvidence where
  /-- List of prediction records -/
  records : List PredictionRecord

instance : Inhabited BinaryMetaEvidence := ⟨⟨[]⟩⟩

namespace BinaryMetaEvidence

/-- Empty meta-evidence -/
def empty : BinaryMetaEvidence := ⟨[]⟩

/-- Add a prediction record -/
def add (m : BinaryMetaEvidence) (r : PredictionRecord) : BinaryMetaEvidence :=
  ⟨r :: m.records⟩

/-- Combine two meta-evidence collections (metaHplus) -/
def hplus (m₁ m₂ : BinaryMetaEvidence) : BinaryMetaEvidence :=
  ⟨m₁.records ++ m₂.records⟩

/-- Number of prediction records -/
def count (m : BinaryMetaEvidence) : ℕ := m.records.length

/-- Sum of errors across all predictions -/
noncomputable def totalError (m : BinaryMetaEvidence) : ℝ≥0∞ :=
  m.records.foldl (fun acc r => acc + r.error) 0

/-- Mean error (average prediction error) -/
noncomputable def meanError (m : BinaryMetaEvidence) : ℝ≥0∞ :=
  if m.count = 0 then 0 else m.totalError / m.count

/-- Count of true positives (predicted high, was true) -/
noncomputable def truePositives (m : BinaryMetaEvidence) (threshold : ℝ≥0∞ := 0.5) : ℕ :=
  m.records.countP (fun r => r.prediction > threshold && r.actual)

/-- Count of false positives (predicted high, was false) -/
noncomputable def falsePositives (m : BinaryMetaEvidence) (threshold : ℝ≥0∞ := 0.5) : ℕ :=
  m.records.countP (fun r => r.prediction > threshold && !r.actual)

/-- Count of true negatives (predicted low, was false) -/
noncomputable def trueNegatives (m : BinaryMetaEvidence) (threshold : ℝ≥0∞ := 0.5) : ℕ :=
  m.records.countP (fun r => r.prediction ≤ threshold && !r.actual)

/-- Count of false negatives (predicted low, was true) -/
noncomputable def falseNegatives (m : BinaryMetaEvidence) (threshold : ℝ≥0∞ := 0.5) : ℕ :=
  m.records.countP (fun r => r.prediction ≤ threshold && r.actual)

end BinaryMetaEvidence

/-! ### Context Update Rule

The update rule adjusts α₀ and β₀ based on prediction accuracy.
A simple approach: if predictions are too high on average, increase β₀ (more prior mass toward 0).
If too low, increase α₀ (more prior mass toward 1).

More sophisticated approaches (empirical Bayes, moment matching) are possible.
-/

open Mettapedia.PLN.Evidence.EvidenceClass in
/-- Simple context update: adjust priors based on mean error direction.
    If predictions are systematically high (false positives), increase β₀.
    If predictions are systematically low (false negatives), increase α₀.

    Learning rate η controls how fast we update (default: 0.1).
-/
noncomputable def updateBinaryContext
    (ctx : BinaryContext) (metaEv : BinaryMetaEvidence) (η : ℝ≥0∞ := 0.1) : BinaryContext :=
  if metaEv.count = 0 then ctx else
  -- Count false positives and false negatives to determine direction
  let fp := metaEv.falsePositives
  let fn := metaEv.falseNegatives
  -- If more false positives, predictions are too high → increase β₀
  -- If more false negatives, predictions are too low → increase α₀
  if fp > fn then
    ⟨ctx.α₀, ctx.β₀ + η * (fp - fn)⟩
  else if fn > fp then
    ⟨ctx.α₀ + η * (fn - fp), ctx.β₀⟩
  else
    ctx

/-- BinaryContext is MetaLearnable from BinaryMetaEvidence -/
noncomputable instance :
    Mettapedia.PLN.Evidence.EvidenceClass.MetaLearnable
      Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext
      BinaryMetaEvidence where
  updateContext := fun ctx metaEv => updateBinaryContext ctx metaEv
  metaHplus := BinaryMetaEvidence.hplus

/-! ### Meta-BinaryEvidence Properties -/

/-- hplus is associative for meta-evidence -/
theorem metaHplus_assoc (m₁ m₂ m₃ : BinaryMetaEvidence) :
    BinaryMetaEvidence.hplus (BinaryMetaEvidence.hplus m₁ m₂) m₃ =
    BinaryMetaEvidence.hplus m₁ (BinaryMetaEvidence.hplus m₂ m₃) := by
  unfold BinaryMetaEvidence.hplus
  simp only [List.append_assoc]

/-- Empty is the identity for hplus -/
theorem metaHplus_empty_left (m : BinaryMetaEvidence) :
    BinaryMetaEvidence.hplus BinaryMetaEvidence.empty m = m := by
  unfold BinaryMetaEvidence.hplus BinaryMetaEvidence.empty
  simp only [List.nil_append]

theorem metaHplus_empty_right (m : BinaryMetaEvidence) :
    BinaryMetaEvidence.hplus m BinaryMetaEvidence.empty = m := by
  unfold BinaryMetaEvidence.hplus BinaryMetaEvidence.empty
  simp only [List.append_nil]

/-- Count is additive under hplus -/
theorem count_hplus (m₁ m₂ : BinaryMetaEvidence) :
    (BinaryMetaEvidence.hplus m₁ m₂).count = m₁.count + m₂.count := by
  unfold BinaryMetaEvidence.hplus BinaryMetaEvidence.count
  simp only [List.length_append]

/-- Helper: foldl with addition can shift the base -/
private theorem foldl_add_shift {α : Type*} [AddCommMonoid α] (f : PredictionRecord → α)
    (b : α) (l : List PredictionRecord) :
    List.foldl (fun acc r => acc + f r) b l = b + List.foldl (fun acc r => acc + f r) 0 l := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (b + f x), ih (f x)]
    rw [add_assoc]

/-- Total error is additive under hplus (semantically commutative) -/
theorem totalError_hplus (m₁ m₂ : BinaryMetaEvidence) :
    (BinaryMetaEvidence.hplus m₁ m₂).totalError = m₁.totalError + m₂.totalError := by
  unfold BinaryMetaEvidence.hplus BinaryMetaEvidence.totalError
  simp only [List.foldl_append]
  exact foldl_add_shift PredictionRecord.error _ _

/-! ## Additional BinaryEvidence Quantale Theory

These results provide structural interpretations of BinaryEvidence beyond the core
quantale instance: duality, transitivity, and Beta/weakness views.
-/

namespace BinaryEvidence

/-! ## The H × H^op Perspective -/

/-- The "opposite" evidence: swap positive and negative. -/
def swap (e : BinaryEvidence) : BinaryEvidence := ⟨e.neg, e.pos⟩

theorem swap_swap (e : BinaryEvidence) : swap (swap e) = e := rfl

theorem swap_tensor (e₁ e₂ : BinaryEvidence) :
    swap (e₁ * e₂) = swap e₁ * swap e₂ := by
  unfold swap
  simp only [BinaryEvidence.tensor_def]

/-- Swapping preserves the lattice order (since both components swap). -/
theorem swap_le_swap (e₁ e₂ : BinaryEvidence) :
    swap e₁ ≤ swap e₂ ↔ e₁.neg ≤ e₂.neg ∧ e₁.pos ≤ e₂.pos := by
  unfold swap
  simp only [BinaryEvidence.le_def]

/-! ## Quantale Transitivity = PLN Deduction -/

theorem evidence_tensor_transitivity (eAB eBC : BinaryEvidence) :
    eAB * eBC ≤ ⨆ (_ : Unit), eAB * eBC := by
  exact le_iSup (fun _ => eAB * eBC) ()

/-! ## Connection to Heyting Structure -/

noncomputable example : Order.Frame BinaryEvidence := inferInstance

/-- Strength as a point estimate (collapsing BinaryEvidence to 1D). -/
noncomputable def strengthAsPoint (e : BinaryEvidence) : ℝ :=
  (BinaryEvidence.toStrength e).toReal

/-- Confidence-as-width (heuristic, from the Beta view). -/
noncomputable def confidenceAsWidth (κ : ℝ≥0∞) (e : BinaryEvidence) : ℝ :=
  (BinaryEvidence.toConfidence κ e).toReal

/-- Confidence increases with total evidence (finite totals). -/
theorem confidence_monotone_in_total (κ : ℝ≥0∞) (e e' : BinaryEvidence)
    (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤) (hy_top : e'.total ≠ ⊤)
    (he' : e.total ≤ e'.total) :
    BinaryEvidence.toConfidence κ e ≤ BinaryEvidence.toConfidence κ e' := by
  unfold BinaryEvidence.toConfidence
  set x := e.total with hx_def
  set y := e'.total with hy_def
  have hx_top : x ≠ ⊤ := ne_top_of_le_ne_top hy_top he'
  have hxk_pos : x + κ ≠ 0 := by
    intro h; simp only [add_eq_zero] at h; exact hκ_pos h.2
  have hyk_pos : y + κ ≠ 0 := by
    intro h; simp only [add_eq_zero] at h; exact hκ_pos h.2
  have hxk_top : x + κ ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hx_top, hκ_top⟩
  have hyk_top' : y + κ ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hy_top, hκ_top⟩
  have key : x * (y + κ) ≤ y * (x + κ) := by
    calc x * (y + κ) = x * y + x * κ := by ring
      _ ≤ x * y + y * κ := by
            have hmul : x * κ ≤ y * κ := by
              have h' : κ * x ≤ κ * y := mul_le_mul_right he' κ
              simpa [mul_comm] using h'
            have hmul2 : x * κ + x * y ≤ y * κ + x * y :=
              add_le_add_left hmul (x * y)
            simpa [add_comm, add_left_comm, add_assoc] using hmul2
      _ = y * x + y * κ := by ring
      _ = y * (x + κ) := by ring
  calc x / (x + κ)
      = x * (y + κ) / ((x + κ) * (y + κ)) := by
          rw [ENNReal.mul_div_mul_right _ _ hyk_pos hyk_top']
    _ ≤ y * (x + κ) / ((x + κ) * (y + κ)) := ENNReal.div_le_div_right key _
    _ = y / (y + κ) := by
          rw [mul_comm (x + κ) (y + κ)]
          rw [ENNReal.mul_div_mul_right _ _ hxk_pos hxk_top]

/-! ## Connection to Beta Distribution -/

theorem hplus_is_beta_update (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg := by
  simp only [BinaryEvidence.hplus_def, and_self]

theorem tensor_is_confidence_compounding (e₁ e₂ : BinaryEvidence) :
    (e₁ * e₂).pos = e₁.pos * e₂.pos ∧
    (e₁ * e₂).neg = e₁.neg * e₂.neg := by
  simp only [BinaryEvidence.tensor_def, and_self]

/-! ## Weakness Measure on BinaryEvidence -/

def EvidenceWeight (U : Type*) [Fintype U] := U → BinaryEvidence

noncomputable def evidenceWeakness {U : Type*} [Fintype U]
    (μ : EvidenceWeight U) (H : Finset (U × U)) : BinaryEvidence :=
  sSup { μ p.1 * μ p.2 | p ∈ H }

theorem evidenceWeakness_mono {U : Type*} [Fintype U]
    (μ : EvidenceWeight U) (H₁ H₂ : Finset (U × U)) (h : H₁ ⊆ H₂) :
    evidenceWeakness μ H₁ ≤ evidenceWeakness μ H₂ := by
  unfold evidenceWeakness
  apply sSup_le_sSup
  intro e he
  obtain ⟨p, hp, rfl⟩ := he
  exact ⟨p, h hp, rfl⟩

end BinaryEvidence

end Mettapedia.PLN.Evidence.EvidenceQuantale
