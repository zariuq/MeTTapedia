import Mettapedia.Logic.IntensionalInheritance
import Mettapedia.Logic.ConceptOntology.Formation
import Mettapedia.Logic.PLNWeightTV

/-!
# Extensional/Intensional Inheritance Divergence and Pure Intensional Strength

This module makes two facts first-class on the *pre-closure* dual-concept surface,
where extensional and intensional inheritance are genuinely independent. (On the
closed/FCA surface the Galois closure forces the intent to be a function of the
extent, so the two coincide and the phenomenon is invisible; the divergence must be
stated on `DualConcept` / `Interpretation`, not on closed concepts.)

## (1) Qualitative divergence
* `extensional_not_intensional_of_extent_eq_of_not_intent_subset`: the abstract
  content — any two coextensive concepts with non-nested intents inherit each other
  extensionally but not intensionally, hence not fully.
* `heartConcept_kidneyConcept_diverges_of_coextensive`: the named instance under the
  hypothesis `hasHeart = hasKidney` (every hearted creature is kidneyed and
  conversely); `heartConcept_kidneyConcept_diverges` is the single-predicate kernel.
* `coextensive_iff_mutual_extensionalInherits`: mutual extensional inheritance is
  exactly coextension, so extensional inheritance cannot see intensional content.
* `inherits_of_extensionalInherits_of_isClosed`: the matching *collapse* on closed
  concepts — there, extensional inheritance does force full inheritance.

## (2) Pure intensional graded strength
* `pureIntensionalStrength`: the fraction of a superconcept's attributes that the
  subconcept also has. This is the genuine intensional dual of extensional
  inheritance probability; it is NOT the extensional proxy `finiteInheritanceStrength`.
* `pureIntensionalStrength_eq_one_iff`: it saturates at `1` exactly at intensional
  inheritance.
* `coextInterp_strength_diverges`: on a coextensive-but-distinct-intent pair the
  extensional and pure-intensional strengths give opposite verdicts.

## (3) The full inheritance truth value, credal interval, inference, and formation
* `fullInheritanceStrength` (`min` of the extensional and intensional strengths) with
  `fullInheritanceStrength_eq_one_iff`: saturates at full `Inherits`.
* `inheritanceTV` : the PLN `⟨strength, confidence⟩` truth value; the confidence is
  strictly below `1` for finite evidence (`inheritanceTV_confidence_lt_one`).
* `lowerInheritanceStrength` / `upperInheritanceStrength` / `inheritanceCredalWidth`
  over a gate family, with `inheritanceCredalWidth_eq_zero_iff` separating the precise
  (settled) case from the imprecise frontier.
* `fullInheritanceStrength_deduction`: the certain (strength-1) deduction rule.
* `formConjointConcept`: concept formation as a first-class act, warranted exactly at
  the divergence frontier (`formConjointConcept_intent_strict_of_diverges`).
-/

namespace Mettapedia.Logic.ExtensionalIntensionalDivergence

open Mettapedia.Logic.AbstractInheritance
open Mettapedia.Logic.IntensionalInheritance (heartConcept kidneyConcept unaryAttributeConcept)

universe u v w

/-! ## (1) Qualitative divergence on the pre-closure surface -/

section Qualitative
variable {Obj : Type u} {Attr : Type v}

/-- Mutual extensional inheritance is exactly coextension: extensional inheritance
is blind to intensional content. -/
theorem coextensive_iff_mutual_extensionalInherits (A B : DualConcept Obj Attr) :
    A.extent = B.extent ↔
      (DualConcept.ExtensionalInherits A B ∧ DualConcept.ExtensionalInherits B A) := by
  constructor
  · intro h; exact ⟨h.subset, h.symm.subset⟩
  · rintro ⟨h1, h2⟩; exact Set.Subset.antisymm h1 h2

/-- Full inheritance is the stronger relation: it always implies extensional
inheritance. -/
theorem extensionalInherits_of_inherits {A B : DualConcept Obj Attr}
    (h : DualConcept.Inherits A B) : DualConcept.ExtensionalInherits A B := h.1

/-- Abstract divergence: any two coextensive concepts whose intents are not nested
inherit each other extensionally but not intensionally — so extensional inheritance
never determines intensional inheritance. This is the general content of which
heart/kidney is the canonical instance. -/
theorem extensional_not_intensional_of_extent_eq_of_not_intent_subset
    {A B : DualConcept Obj Attr}
    (hext : A.extent = B.extent) (hint : ¬ B.intent ⊆ A.intent) :
    DualConcept.ExtensionalInherits A B
      ∧ DualConcept.ExtensionalInherits B A
      ∧ ¬ DualConcept.IntensionalInherits A B
      ∧ ¬ DualConcept.Inherits A B :=
  ⟨hext.subset, hext.symm.subset, hint, fun h => hint h.2⟩

end Qualitative

/-- The heart/kidney divergence (single-predicate kernel): the heart and kidney
concepts over the same predicate inherit each other extensionally but not
intensionally — extensional inheritance does not determine intensional inheritance. -/
theorem heartConcept_kidneyConcept_diverges {α : Type u} (p : α → Prop) :
    DualConcept.ExtensionalInherits (heartConcept p) (kidneyConcept p)
      ∧ DualConcept.ExtensionalInherits (kidneyConcept p) (heartConcept p)
      ∧ ¬ DualConcept.IntensionalInherits (heartConcept p) (kidneyConcept p)
      ∧ ¬ DualConcept.Inherits (heartConcept p) (kidneyConcept p) := by
  refine ⟨fun _ ha => ha, fun _ ha => ha, ?_, ?_⟩
  · intro h
    have hmem : ("kidney" : String) ∈ (heartConcept p).intent := h rfl
    simp only [heartConcept, unaryAttributeConcept, Set.mem_setOf_eq] at hmem
    exact absurd hmem (by decide)
  · intro h
    have hmem : ("kidney" : String) ∈ (heartConcept p).intent := h.2 rfl
    simp only [heartConcept, unaryAttributeConcept, Set.mem_setOf_eq] at hmem
    exact absurd hmem (by decide)

/-- The heart/kidney divergence under the equality hypothesis `hasHeart = hasKidney`
(two genuinely distinct predicates that happen to be coextensive): the concepts
inherit each other extensionally but not intensionally. -/
theorem heartConcept_kidneyConcept_diverges_of_coextensive {α : Type u}
    (hasHeart hasKidney : α → Prop) (h : hasHeart = hasKidney) :
    DualConcept.ExtensionalInherits (heartConcept hasHeart) (kidneyConcept hasKidney)
      ∧ DualConcept.ExtensionalInherits (kidneyConcept hasKidney) (heartConcept hasHeart)
      ∧ ¬ DualConcept.IntensionalInherits (heartConcept hasHeart) (kidneyConcept hasKidney)
      ∧ ¬ DualConcept.Inherits (heartConcept hasHeart) (kidneyConcept hasKidney) := by
  subst h
  exact heartConcept_kidneyConcept_diverges hasHeart

/-- Existence form: there are coextensive concepts that do not inherit each other —
extensional equality does not entail full inheritance. -/
theorem exists_coextensive_not_inherits :
    ∃ (Obj Attr : Type) (A B : DualConcept Obj Attr),
      A.extent = B.extent ∧ ¬ DualConcept.Inherits A B :=
  ⟨Unit, String, heartConcept (fun _ => True), kidneyConcept (fun _ => True), rfl,
    (heartConcept_kidneyConcept_diverges (fun _ : Unit => True)).2.2.2⟩

/-! ## Collapse on the closed/FCA surface (the negative contrast) -/

section Collapse
variable {Obj : Type u} {Attr : Type v}

/-- On closed concepts the divergence is impossible: extensional inheritance forces
full inheritance, because the Galois closure makes the intent a function of the
extent. This is the contrast that shows the divergence is genuinely a pre-closure
phenomenon. -/
theorem inherits_of_extensionalInherits_of_isClosed {r : Obj → Attr → Prop}
    {A B : DualConcept Obj Attr}
    (hA : DualConcept.IsClosed r A) (hB : DualConcept.IsClosed r B)
    (h : DualConcept.ExtensionalInherits A B) : DualConcept.Inherits A B := by
  have hle : DualConcept.toConcept A hA ≤ DualConcept.toConcept B hB :=
    _root_.Concept.extent_subset_extent_iff.mp h
  exact (DualConcept.toConcept_inherits_iff A B hA hB).mp hle

end Collapse

/-! ## (2) Pure intensional graded strength -/

section PureIntensional
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Attr]

/-- Pure intensional inheritance strength: the fraction of the superconcept's
attributes that the subconcept also possesses. This is the genuine intensional dual
of extensional inheritance probability — it reads the *intent* overlap, not the
extent overlap — and is deliberately a new notion, not the extensional proxy
`finiteInheritanceStrength`. -/
noncomputable def pureIntensionalStrength
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  if (I.meaning super).intent.ncard = 0 then 0
  else (((I.meaning sub).intent ∩ (I.meaning super).intent).ncard : ℝ)
        / ((I.meaning super).intent.ncard : ℝ)

/-- The pure intensional strength saturates at `1` exactly at intensional
inheritance: it is a faithful graded version of `IntensionalInherits`. -/
theorem pureIntensionalStrength_eq_one_iff
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (hsuper : (I.meaning super).intent.ncard ≠ 0) :
    pureIntensionalStrength I sub super = 1 ↔ I.IntensionalInherits sub super := by
  show pureIntensionalStrength I sub super = 1 ↔
      (I.meaning super).intent ⊆ (I.meaning sub).intent
  have hWfin : ((I.meaning super).intent).Finite := Set.toFinite _
  have hsub : (I.meaning sub).intent ∩ (I.meaning super).intent ⊆ (I.meaning super).intent :=
    Set.inter_subset_right
  unfold pureIntensionalStrength
  rw [if_neg hsuper,
      div_eq_iff (by exact_mod_cast hsuper : ((I.meaning super).intent.ncard : ℝ) ≠ 0),
      one_mul, Nat.cast_inj]
  constructor
  · intro h
    have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq h.symm) hWfin
    exact Set.inter_eq_right.mp heq
  · intro h
    rw [Set.inter_eq_right.mpr h]

end PureIntensional

/-! ### Generic `ncard`-ratio helpers (shared by both strengths) -/

section NcardRatio
variable {γ : Type*} [Finite γ]

private theorem ncardRatio_eq_one_iff {A B : Set γ} (hB : B.ncard ≠ 0) :
    ((A ∩ B).ncard : ℝ) / (B.ncard : ℝ) = 1 ↔ B ⊆ A := by
  have hBfin : B.Finite := Set.toFinite B
  rw [div_eq_iff (by exact_mod_cast hB), one_mul, Nat.cast_inj]
  constructor
  · intro h
    exact Set.inter_eq_right.mp
      (Set.eq_of_subset_of_ncard_le Set.inter_subset_right (le_of_eq h.symm) hBfin)
  · intro h
    rw [Set.inter_eq_right.mpr h]

private theorem ncardRatio_le_one (A B : Set γ) :
    ((A ∩ B).ncard : ℝ) / (B.ncard : ℝ) ≤ 1 := by
  rcases eq_or_ne B.ncard 0 with hB | hB
  · rw [hB]; simp
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hB)]
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite B)

end NcardRatio

/-! ### Bound for the pure intensional strength -/

section PureIntensionalBound
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Attr]

theorem pureIntensionalStrength_le_one
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    pureIntensionalStrength I sub super ≤ 1 := by
  unfold pureIntensionalStrength
  rcases eq_or_ne ((I.meaning super).intent.ncard) 0 with h | h
  · rw [if_pos h]; exact zero_le_one
  · rw [if_neg h]; exact ncardRatio_le_one _ _

omit [Fintype Attr] in
theorem pureIntensionalStrength_nonneg
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ pureIntensionalStrength I sub super := by
  unfold pureIntensionalStrength
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end PureIntensionalBound

/-! ### Pure extensional graded strength (the symmetric dual) -/

section PureExtensional
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

/-- Pure extensional inheritance strength: the fraction of the subconcept's
instances that lie in the superconcept. This is the `Set.ncard`-based extensional
companion of `pureIntensionalStrength`; it measures the same extensional overlap as
the Chapter-12 `finiteExtensionalProb`, in the symmetric representation. -/
noncomputable def pureExtensionalStrength
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  if (I.meaning sub).extent.ncard = 0 then 0
  else (((I.meaning super).extent ∩ (I.meaning sub).extent).ncard : ℝ)
        / ((I.meaning sub).extent.ncard : ℝ)

theorem pureExtensionalStrength_eq_one_iff
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (hsub : (I.meaning sub).extent.ncard ≠ 0) :
    pureExtensionalStrength I sub super = 1 ↔ I.ExtensionalInherits sub super := by
  show pureExtensionalStrength I sub super = 1 ↔
      (I.meaning sub).extent ⊆ (I.meaning super).extent
  unfold pureExtensionalStrength
  rw [if_neg hsub]
  exact ncardRatio_eq_one_iff hsub

theorem pureExtensionalStrength_le_one
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    pureExtensionalStrength I sub super ≤ 1 := by
  unfold pureExtensionalStrength
  rcases eq_or_ne ((I.meaning sub).extent.ncard) 0 with h | h
  · rw [if_pos h]; exact zero_le_one
  · rw [if_neg h]; exact ncardRatio_le_one _ _

omit [Fintype Obj] in
theorem pureExtensionalStrength_nonneg
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ pureExtensionalStrength I sub super := by
  unfold pureExtensionalStrength
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end PureExtensional

/-! ### Full inheritance strength: the combined ext+int truth value -/

section FullStrength
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj] [Fintype Attr]

private theorem min_eq_one_iff_of_le_one {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) :
    min a b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    exact ⟨le_antisymm ha (h ▸ min_le_left a b), le_antisymm hb (h ▸ min_le_right a b)⟩
  · rintro ⟨rfl, rfl⟩; exact min_self 1

/-- The full inheritance strength is the weakest-link (min) combination of the
extensional and pure-intensional strengths. It is a genuine graded version of full
`Inherits`: it reads both the extent overlap and the intent overlap, so it sees the
extensional/intensional divergence the extensional proxy alone cannot. -/
noncomputable def fullInheritanceStrength
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  min (pureExtensionalStrength I sub super) (pureIntensionalStrength I sub super)

omit [Fintype Obj] [Fintype Attr] in
theorem fullInheritanceStrength_nonneg
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ fullInheritanceStrength I sub super :=
  le_min (pureExtensionalStrength_nonneg I sub super)
    (pureIntensionalStrength_nonneg I sub super)

omit [Fintype Attr] in
theorem fullInheritanceStrength_le_one
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    fullInheritanceStrength I sub super ≤ 1 :=
  (min_le_left _ _).trans (pureExtensionalStrength_le_one I sub super)

/-- The full inheritance strength saturates at `1` exactly at full `Inherits`: it is
a faithful graded refinement of the qualitative full inheritance relation. -/
theorem fullInheritanceStrength_eq_one_iff
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (hsubE : (I.meaning sub).extent.ncard ≠ 0)
    (hsuperI : (I.meaning super).intent.ncard ≠ 0) :
    fullInheritanceStrength I sub super = 1 ↔ I.Inherits sub super := by
  unfold fullInheritanceStrength
  rw [min_eq_one_iff_of_le_one (pureExtensionalStrength_le_one I sub super)
        (pureIntensionalStrength_le_one I sub super),
      pureExtensionalStrength_eq_one_iff I sub super hsubE,
      pureIntensionalStrength_eq_one_iff I sub super hsuperI]
  exact (Interpretation.inherits_iff I sub super).symm

end FullStrength

/-! ## (I2) The inheritance truth value: ⟨strength, confidence⟩ -/

section TruthValue
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLNWeightTV
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

private theorem w2c_lt_one {x : ℝ} (hx : 0 ≤ x) : w2c x < 1 := by
  unfold w2c
  rw [div_lt_one (by linarith)]
  linarith

private theorem w2c_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) : w2c x = 0 ↔ x = 0 := by
  unfold w2c
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · linarith
  · intro h; exact Or.inl h

private theorem w2c_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : w2c x ≤ w2c y := by
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have hy1 : (0:ℝ) < y + 1 := by linarith
  have h1 : (x + 1) ≠ 0 := ne_of_gt hx1
  have h2 : (y + 1) ≠ 0 := ne_of_gt hy1
  have key : w2c y - w2c x = (y - x) / ((y + 1) * (x + 1)) := by
    unfold w2c; field_simp; ring
  have hnn : 0 ≤ w2c y - w2c x := by
    rw [key]; apply div_nonneg (by linarith); positivity
  linarith

/-- The evidence weight behind an inheritance judgment: the weakest of the
extensional and intensional evidence amounts (instances of the subconcept, attributes
of the superconcept). -/
noncomputable def inheritanceWeight
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  min ((I.meaning sub).extent.ncard : ℝ) ((I.meaning super).intent.ncard : ℝ)

omit [Fintype Obj] in
theorem inheritanceWeight_nonneg
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ inheritanceWeight I sub super :=
  le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weight-primary inheritance truth value (strength + evidence weight). -/
noncomputable def inheritanceWTV
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : WTV where
  strength := fullInheritanceStrength I sub super
  weight := inheritanceWeight I sub super
  strength_nonneg := fullInheritanceStrength_nonneg I sub super
  strength_le_one := fullInheritanceStrength_le_one I sub super
  weight_nonneg := inheritanceWeight_nonneg I sub super

/-- The inheritance truth value as a PLN simple truth value `⟨strength, confidence⟩`:
the strength is the combined ext+int strength, and the confidence `w/(w+1)` is read
from the evidence weight. -/
noncomputable def inheritanceTV
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) : STV :=
  (inheritanceWTV I sub super).toCTV

/-- The truth value's strength saturates at `1` exactly at full `Inherits`. -/
theorem inheritanceTV_strength_eq_one_iff [Fintype Attr]
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (hsubE : (I.meaning sub).extent.ncard ≠ 0)
    (hsuperI : (I.meaning super).intent.ncard ≠ 0) :
    (inheritanceTV I sub super).strength = 1 ↔ I.Inherits sub super := by
  show fullInheritanceStrength I sub super = 1 ↔ I.Inherits sub super
  exact fullInheritanceStrength_eq_one_iff I sub super hsubE hsuperI

/-- Finite evidence never yields certainty: the confidence is strictly below `1`. -/
theorem inheritanceTV_confidence_lt_one
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    (inheritanceTV I sub super).confidence < 1 := by
  show w2c (inheritanceWeight I sub super) < 1
  exact w2c_lt_one (inheritanceWeight_nonneg I sub super)

/-- Zero confidence exactly when there is no evidence (empty subconcept extent or
empty superconcept intent). -/
theorem inheritanceTV_confidence_eq_zero_iff
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    (inheritanceTV I sub super).confidence = 0 ↔ inheritanceWeight I sub super = 0 := by
  show w2c (inheritanceWeight I sub super) = 0 ↔ inheritanceWeight I sub super = 0
  exact w2c_eq_zero_iff (inheritanceWeight_nonneg I sub super)

/-- Confidence is monotone in the evidence weight: more evidence never lowers
confidence. -/
theorem inheritanceTV_confidence_mono
    (I J : Interpretation Carrier Obj Attr) (sub super sub' super' : Carrier)
    (h : inheritanceWeight I sub super ≤ inheritanceWeight J sub' super') :
    (inheritanceTV I sub super).confidence ≤ (inheritanceTV J sub' super').confidence := by
  show w2c (inheritanceWeight I sub super) ≤ w2c (inheritanceWeight J sub' super')
  exact w2c_mono (inheritanceWeight_nonneg I sub super) h

end TruthValue

/-! ## (I3) Credal inheritance: lower/upper strength over a gate family -/

section Credal
variable {Gate : Type*} [Fintype Gate] [Nonempty Gate]
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}

/-- The lower inheritance strength over a family of admissible interpretations
(gates): the infimum of the full strength across all gates — "robustly inherited". -/
noncomputable def lowerInheritanceStrength
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun g => fullInheritanceStrength (J g) sub super)

/-- The upper inheritance strength: the supremum across all gates —
"permissively inherited". -/
noncomputable def upperInheritanceStrength
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun g => fullInheritanceStrength (J g) sub super)

/-- The credal width: the imprecision of the inheritance judgment across the gate
family. Zero exactly when every gate agrees. -/
noncomputable def inheritanceCredalWidth
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) : ℝ :=
  upperInheritanceStrength J sub super - lowerInheritanceStrength J sub super

theorem lowerInheritanceStrength_le_gate
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) (g : Gate) :
    lowerInheritanceStrength J sub super ≤ fullInheritanceStrength (J g) sub super :=
  Finset.inf'_le _ (Finset.mem_univ g)

theorem gate_le_upperInheritanceStrength
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) (g : Gate) :
    fullInheritanceStrength (J g) sub super ≤ upperInheritanceStrength J sub super :=
  Finset.le_sup' (fun g => fullInheritanceStrength (J g) sub super) (Finset.mem_univ g)

theorem lowerInheritanceStrength_le_upper
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    lowerInheritanceStrength J sub super ≤ upperInheritanceStrength J sub super := by
  obtain ⟨g⟩ := (inferInstance : Nonempty Gate)
  exact (lowerInheritanceStrength_le_gate J sub super g).trans
    (gate_le_upperInheritanceStrength J sub super g)

theorem inheritanceCredalWidth_nonneg
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ inheritanceCredalWidth J sub super :=
  sub_nonneg.mpr (lowerInheritanceStrength_le_upper J sub super)

theorem lowerInheritanceStrength_nonneg
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    0 ≤ lowerInheritanceStrength J sub super := by
  apply Finset.le_inf'
  intro g _
  exact fullInheritanceStrength_nonneg (J g) sub super

theorem upperInheritanceStrength_le_one [Fintype Obj]
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    upperInheritanceStrength J sub super ≤ 1 := by
  apply Finset.sup'_le
  intro g _
  exact fullInheritanceStrength_le_one (J g) sub super

/-- The credal judgment is *precise* (width zero) exactly when every gate assigns the
same full strength. This separates settled inheritance from the imprecise frontier. -/
theorem inheritanceCredalWidth_eq_zero_iff
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    inheritanceCredalWidth J sub super = 0 ↔
      ∀ g h : Gate, fullInheritanceStrength (J g) sub super
        = fullInheritanceStrength (J h) sub super := by
  unfold inheritanceCredalWidth
  rw [sub_eq_zero]
  constructor
  · intro hEq g h
    refine le_antisymm ?_ ?_
    · exact (gate_le_upperInheritanceStrength J sub super g).trans
        (hEq ▸ lowerInheritanceStrength_le_gate J sub super h)
    · exact (gate_le_upperInheritanceStrength J sub super h).trans
        (hEq ▸ lowerInheritanceStrength_le_gate J sub super g)
  · intro hconst
    refine le_antisymm ?_ (lowerInheritanceStrength_le_upper J sub super)
    apply Finset.sup'_le
    intro g _
    apply Finset.le_inf'
    intro h _
    exact (hconst g h).le

end Credal

/-! ## (I5) Concept-level deduction (the certain inference rule) -/

section Inference
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj] [Fintype Attr]

/-- Deduction (transitivity) for full inheritance strength: chaining two saturated
inheritances `a → b` and `b → c` yields a saturated `a → c`. This is the certain
(strength-1) PLN deduction rule at the concept level; the graded/uncertain deduction
formula lives in the Bayesian-network bridge. -/
theorem fullInheritanceStrength_deduction
    (I : Interpretation Carrier Obj Attr) (a b c : Carrier)
    (haE : (I.meaning a).extent.ncard ≠ 0)
    (hbE : (I.meaning b).extent.ncard ≠ 0)
    (hbI : (I.meaning b).intent.ncard ≠ 0)
    (hcI : (I.meaning c).intent.ncard ≠ 0)
    (hab : fullInheritanceStrength I a b = 1)
    (hbc : fullInheritanceStrength I b c = 1) :
    fullInheritanceStrength I a c = 1 := by
  have iab := (fullInheritanceStrength_eq_one_iff I a b haE hbI).mp hab
  have ibc := (fullInheritanceStrength_eq_one_iff I b c hbE hcI).mp hbc
  exact (fullInheritanceStrength_eq_one_iff I a c haE hcI).mpr (I.inherits_trans iab ibc)

end Inference

/-! ## (I6) Concept formation as a first-class act -/

section Formation
variable {Obj : Type u} {Attr : Type v}

/-- Forming the conjoint concept of two concepts: the most specific concept that
inherits from both — its extent is their common instances, its intent the union of
their attributes (the meet in the concept lattice). This is a first-class concept
formation operation. -/
def formConjointConcept (A B : DualConcept Obj Attr) : DualConcept Obj Attr :=
  DualConcept.inter A B

theorem formConjointConcept_inherits_left (A B : DualConcept Obj Attr) :
    DualConcept.Inherits (formConjointConcept A B) A :=
  DualConcept.inter_inherits_left A B

theorem formConjointConcept_inherits_right (A B : DualConcept Obj Attr) :
    DualConcept.Inherits (formConjointConcept A B) B :=
  DualConcept.inter_inherits_right A B

/-- On coextensive inputs the formed concept preserves the extent: forming the
conjoint concept of two descriptions of the same things keeps those things. -/
theorem formConjointConcept_extent_of_coextensive (A B : DualConcept Obj Attr)
    (h : A.extent = B.extent) : (formConjointConcept A B).extent = A.extent := by
  show A.extent ∩ B.extent = A.extent
  rw [h, Set.inter_self]

/-- The warrant: forming the conjoint concept yields a genuinely NEW concept —
strictly more specific intensionally than its first input — exactly at the divergence
frontier (when the second input's intent is not already nested in the first).
Formation does real work precisely where extensional and intensional inheritance can
diverge. -/
theorem formConjointConcept_intent_strict_of_diverges (A B : DualConcept Obj Attr)
    (hAB : ¬ B.intent ⊆ A.intent) :
    A.intent ⊂ (formConjointConcept A B).intent := by
  show A.intent ⊂ A.intent ∪ B.intent
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_union_left, ?_⟩
  intro hEq
  apply hAB
  rw [hEq]
  exact Set.subset_union_right

/-- Universal property: the formed concept is *canonical* — any concept that inherits
from both inputs inherits from their conjoint concept. Formation produces exactly the
common specialization, nothing more, nothing less (the meet's universal property). -/
theorem formConjointConcept_universal {A B C : DualConcept Obj Attr}
    (hCA : DualConcept.Inherits C A) (hCB : DualConcept.Inherits C B) :
    DualConcept.Inherits C (formConjointConcept A B) :=
  DualConcept.inherits_inter_of_inherits hCA hCB

/-- Formation is symmetric: the conjoint concept does not depend on input order. -/
theorem formConjointConcept_comm (A B : DualConcept Obj Attr) :
    formConjointConcept A B = formConjointConcept B A := by
  unfold formConjointConcept DualConcept.inter
  rw [Set.inter_comm, Set.union_comm]

end Formation

/-! ## (I6-strong) Closed formation on the formed-concept carrier -/

section FormedClosureBridge

open Mettapedia.Logic.ConceptOntology

variable {Obj : Type u} {Attr : Type v} {Q : Type w}
variable [Fintype Obj] [Fintype Attr] [Preorder Q]

/-- The closed conjoint formation on the exact formed-concept carrier: take the FCA
meet of the two closed inputs, then forget back to a `DualConcept` together with its
closure witness. This is the honest closure-side construction corresponding to the
raw pre-closure `formConjointConcept`. -/
noncomputable def formedMeet
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) : FormedConcept G M :=
  ⟨DualConcept.ofConcept
      (DualConcept.toConcept A.1 (formedConcept_isClosed G M A) ⊓
       DualConcept.toConcept B.1 (formedConcept_isClosed G M B)),
    by
      rw [mem_finiteConceptFamily_iff]
      exact DualConcept.isClosed_ofConcept _⟩

/-- The closed conjoint construction preserves the exact FCA meet extent. -/
@[simp] theorem formedMeet_extent
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    (formedMeet G M A B).1.extent = A.1.extent ∩ B.1.extent := by
  rw [formedMeet]
  simp [DualConcept.ofConcept, DualConcept.toConcept, _root_.Concept.extent_inf]

/-- The intent of the closed conjoint construction is exactly the FCA closure of the
conjoined extent: everything scrutable from the common instances. -/
@[simp] theorem formedMeet_intent_eq_closure
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    (formedMeet G M A B).1.intent =
      _root_.upperPolar (crispRelation G M) (A.1.extent ∩ B.1.extent) := by
  rw [formedMeet]
  simp [DualConcept.ofConcept, DualConcept.toConcept, _root_.Concept.intent_inf]

/-- The raw posit and the closed construction agree extensionally: both are about
exactly the common instances. -/
theorem formConjointConcept_extent_eq_formedMeet
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    (formConjointConcept A.1 B.1).extent = (formedMeet G M A B).1.extent := by
  simp [formConjointConcept, DualConcept.inter, formedMeet_extent]

/-- The closed conjoint construction inherits from the raw posit: it carries every
explicitly posited attribute, and possibly more via closure. -/
theorem formedMeet_inherits_formConjointConcept
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    DualConcept.Inherits (formedMeet G M A B).1 (formConjointConcept A.1 B.1) := by
  constructor
  · intro x hx
    simpa [formConjointConcept, DualConcept.inter, formedMeet_extent] using hx
  · intro a ha
    rw [formedMeet_intent_eq_closure G M A B]
    rcases ha with ha | ha
    · rw [← (formedConcept_isClosed G M A).1] at ha
      exact (_root_.upperPolar_anti (r := crispRelation G M) Set.inter_subset_left) ha
    · rw [← (formedConcept_isClosed G M B).1] at ha
      exact (_root_.upperPolar_anti (r := crispRelation G M) Set.inter_subset_right) ha

/-- The raw posit is already closed exactly when its intent already matches the FCA
closure of its common extent, i.e. when no closure-added intent remains. -/
theorem formConjointConcept_isClosed_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    DualConcept.IsClosed (crispRelation G M) (formConjointConcept A.1 B.1) ↔
      A.1.intent ∪ B.1.intent =
        _root_.upperPolar (crispRelation G M) (A.1.extent ∩ B.1.extent) := by
  constructor
  · intro h
    exact h.1.symm
  · intro h
    let F := formedMeet G M A B
    have hFclosed : DualConcept.IsClosed (crispRelation G M) F.1 :=
      formedConcept_isClosed G M F
    have hIntentEq : (formConjointConcept A.1 B.1).intent = F.1.intent := by
      calc
        (formConjointConcept A.1 B.1).intent = A.1.intent ∪ B.1.intent := rfl
        _ = _root_.upperPolar (crispRelation G M) (A.1.extent ∩ B.1.extent) := h
        _ = F.1.intent := (formedMeet_intent_eq_closure G M A B).symm
    constructor
    · simpa [formConjointConcept, DualConcept.inter] using h.symm
    · calc
        _root_.lowerPolar (crispRelation G M) (formConjointConcept A.1 B.1).intent
            = _root_.lowerPolar (crispRelation G M) F.1.intent := by
                rw [hIntentEq]
        _ = F.1.extent := hFclosed.2
        _ = (formConjointConcept A.1 B.1).extent := by
              rw [← formConjointConcept_extent_eq_formedMeet G M A B]

/-- The closure-added intent beyond the raw posit: attributes scrutable from the
common extent but not explicit in the conjunction itself. -/
def scrutabilityGap
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) : Set Attr :=
  (formedMeet G M A B).1.intent \ (formConjointConcept A.1 B.1).intent

/-- The scrutability gap vanishes exactly when the raw posit is already closed. -/
theorem scrutabilityGap_eq_empty_iff
    (G : EvidenceGate Q) (M : Obj → Attr → Q)
    (A B : FormedConcept G M) :
    scrutabilityGap G M A B = ∅ ↔
      DualConcept.IsClosed (crispRelation G M) (formConjointConcept A.1 B.1) := by
  rw [formConjointConcept_isClosed_iff G M A B]
  unfold scrutabilityGap
  constructor
  · intro hGap
    apply Set.Subset.antisymm
    · intro a ha
      rcases ha with ha | ha
      · exact
          (formedMeet_inherits_formConjointConcept G M A B).2 (Or.inl ha)
      · exact
          (formedMeet_inherits_formConjointConcept G M A B).2 (Or.inr ha)
    · intro a ha
      by_contra hnot
      have hmem :
          a ∈ (formedMeet G M A B).1.intent \ (formConjointConcept A.1 B.1).intent :=
        ⟨by
            rw [formedMeet_intent_eq_closure G M A B]
            exact ha,
          hnot⟩
      have : a ∈ (∅ : Set Attr) := by
        rw [← hGap]
        exact hmem
      exact this.elim
  · intro hEq
    ext a
    constructor
    · intro ha
      have hclosure :
          a ∈ _root_.upperPolar (crispRelation G M) (A.1.extent ∩ B.1.extent) := by
        simpa [formedMeet_intent_eq_closure G M A B] using ha.1
      have hunion : a ∈ A.1.intent ∪ B.1.intent := by
        rw [hEq]
        exact hclosure
      have hraw : a ∈ (formConjointConcept A.1 B.1).intent := by
        simpa [formConjointConcept, DualConcept.inter] using hunion
      exact False.elim (ha.2 hraw)
    · intro ha
      exact False.elim ha

end FormedClosureBridge

/-! ### Numeric divergence: extensional and pure-intensional strength disagree -/

section Example

/-- A two-attribute interpretation whose two concepts share their extent (everything)
but have disjoint intents. -/
def coextInterp : Interpretation Bool Unit Bool where
  meaning b := { extent := Set.univ, intent := {b} }

/-- On the coextensive pair the concepts inherit each other extensionally, yet the
pure intensional strength is not `1`: the extensional and intensional strengths give
opposite verdicts on the very same pair. -/
theorem coextInterp_strength_diverges :
    coextInterp.ExtensionalInherits true false
      ∧ coextInterp.ExtensionalInherits false true
      ∧ pureIntensionalStrength coextInterp true false ≠ 1 := by
  refine ⟨fun _ ha => ha, fun _ ha => ha, ?_⟩
  rw [Ne, pureIntensionalStrength_eq_one_iff coextInterp true false
        (by simp [coextInterp])]
  intro h
  have hmem : (false : Bool) ∈ ({true} : Set Bool) := h (Set.mem_singleton_iff.mpr rfl)
  rw [Set.mem_singleton_iff] at hmem
  exact absurd hmem (by decide)

/-- The full inheritance strength reflects the divergence: on the coextensive pair it
is not `1`, because the intensional half fails even though the extensional half
saturates. This is the synthesis — the combined truth value sees what the extensional
proxy alone cannot. -/
theorem coextInterp_fullStrength_ne_one :
    fullInheritanceStrength coextInterp true false ≠ 1 := by
  have hE : (coextInterp.meaning true).extent.ncard ≠ 0 := by
    show (Set.univ : Set Unit).ncard ≠ 0
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_unit]
    decide
  have hI : (coextInterp.meaning false).intent.ncard ≠ 0 := by simp [coextInterp]
  rw [Ne, fullInheritanceStrength_eq_one_iff coextInterp true false hE hI]
  intro h
  have hmem : (false : Bool) ∈ ({true} : Set Bool) := h.2 (Set.mem_singleton_iff.mpr rfl)
  rw [Set.mem_singleton_iff] at hmem
  exact absurd hmem (by decide)

end Example

end Mettapedia.Logic.ExtensionalIntensionalDivergence
