import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.SetNotation
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.FreeProbability.NoncrossingPartitions

/-!
# Quantale Semantics for Hypercube Vertices

This module provides small, concrete “value spaces” (quantales in the broad sense used by
`Mettapedia.Algebra.QuantaleWeakness`) and explicit morphisms between them.

The main purpose is to support the Hypercube story that:

* classical / deterministic / quantum vertices can all be assigned a quantale-like value space;
* Goertzel-style weakness `weakness` is functorial along suitable morphisms.

In particular, we give a **noncommutative** quantale model for the `quantum` vertex and a
`QuantaleHom` into the Boolean quantale, then demonstrate the `map_weakness` transport lemma.
-/

namespace Mettapedia.ProbabilityTheory.Hypercube

namespace QuantaleSemantics

open Classical
open Set
open scoped ENNReal
open scoped Pointwise

-- We use the pointwise monoid structure on `Set α` from Mathlib (scoped `Pointwise`).
-- For the Boolean-quantale presentation, we equip `Unit` with the trivial commutative monoid.
section

local instance : CommMonoid Unit where
  one := ()
  mul _ _ := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  mul_comm _ _ := rfl

/-- A convenient Lean carrier for the Boolean quantale `{0,1}`: subsets of a singleton type. -/
abbrev BoolQuantale : Type :=
  Set Unit

/-- Membership in a pointwise product of subsets of `Unit`. -/
lemma unit_mem_mul_iff (S T : Set Unit) :
    (():Unit) ∈ S * T ↔ (():Unit) ∈ S ∧ (():Unit) ∈ T := by
  constructor
  · rintro ⟨x, hxS, y, hyT, _hxy⟩
    cases x
    cases y
    exact ⟨by simpa using hxS, by simpa using hyT⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(), hx, (), hy, rfl⟩

/-- A convenient Lean carrier for a **noncommutative** quantale: “languages” over two symbols. -/
abbrev LanguageQuantale (α : Type) : Type :=
  Set (FreeMonoid α)

/-- The noncommutative “quantum” vertex uses the language quantale on two symbols. -/
abbrev QuantumQuantale : Type :=
  LanguageQuantale Bool

/-- The `QuantaleType.free` semantics: languages over “noncrossing partition symbols”. -/
abbrev FreeQuantale : Type :=
  LanguageQuantale (Σ n : ℕ, Mettapedia.ProbabilityTheory.FreeProbability.NC n)

/-- The `QuantaleType.boolean` semantics: languages over positive block-sizes (interval partitions). -/
abbrev BooleanIndepQuantale : Type :=
  LanguageQuantale ℕ+

/-- The `QuantaleType.monotone` semantics: languages over ordered blocks (each block is a list of sizes). -/
abbrev MonotoneIndepQuantale : Type :=
  LanguageQuantale (List ℕ+)

/-! ## Commutative and interval value scales -/

/-- A convenient Lean carrier for the commutative `[0,1]`-like scale:
we use `ℝ≥0∞` (extended non-negative reals) since it is a complete lattice and a commutative monoid.

This is “probability-like” rather than literally `[0,1]`; the order/quantale structure is what
matters for the generic weakness story. -/
abbrev CommQuantale : Type :=
  ℝ≥0∞

/-- A convenient Lean carrier for an “interval” scale: a pair of commutative values.

This is the simplest Lean-realization of the “`[0,1]² interval`” story in `Hypercube/Basic.lean`. -/
abbrev IntervalQuantale : Type :=
  CommQuantale × CommQuantale

/-! ## Canonical morphisms to the Boolean quantale -/

/-- Collapse a commutative scale to the Boolean quantale by remembering only whether it is `0`. -/
noncomputable def commToBoolVal (x : CommQuantale) : BoolQuantale :=
  if x = 0 then ∅ else {()}

lemma mem_commToBoolVal (x : CommQuantale) :
    (():Unit) ∈ commToBoolVal x ↔ x ≠ 0 := by
  classical
  by_cases hx : x = 0 <;> simp [commToBoolVal, hx]

lemma commToBoolVal_map_mul (x y : CommQuantale) :
    commToBoolVal (x * y) = commToBoolVal x * commToBoolVal y := by
  classical
  ext u
  cases u
  simp [mem_commToBoolVal, unit_mem_mul_iff, mul_eq_zero]

lemma commToBoolVal_map_sSup (S : Set CommQuantale) :
    commToBoolVal (sSup S) = sSup (commToBoolVal '' S) := by
  classical
  ext u
  cases u
  constructor
  · intro hSup
    have hSup0 : sSup S ≠ 0 := (mem_commToBoolVal (x := sSup S)).1 hSup
    -- Extract a witness `a ∈ S` with `a ≠ 0`.
    have hExists : ∃ a ∈ S, a ≠ 0 := by
      by_contra hne
      have hAll0 : ∀ a ∈ S, a = 0 := by
        intro a haS
        have : ¬ a ≠ 0 := by
          intro ha0
          exact hne ⟨a, haS, ha0⟩
        exact not_ne_iff.mp this
      have : sSup S = 0 := (sSup_eq_bot).2 (by
        intro a haS
        -- `a = 0` means `a = ⊥` for this lattice.
        simp [hAll0 a haS])
      exact hSup0 this
    -- Show membership in the union-form of `sSup` for `Set Unit`.
    rcases hExists with ⟨a, haS, ha0⟩
    -- `sSup` for `Set` is `sUnion`.
    change (():Unit) ∈ sUnion (commToBoolVal '' S)
    refine Set.mem_sUnion.2 ?_
    refine ⟨commToBoolVal a, ?_, ?_⟩
    · exact ⟨a, haS, rfl⟩
    · exact (mem_commToBoolVal (x := a)).2 ha0
  · intro hSup
    -- Unpack membership in the union-form of `sSup` for `Set Unit`.
    have hSup' :
        ∃ T : Set Unit, T ∈ commToBoolVal '' S ∧ (():Unit) ∈ T := by
      simpa [Set.sSup_eq_sUnion, Set.mem_sUnion] using hSup
    rcases hSup' with ⟨T, hT, hmemT⟩
    rcases hT with ⟨a, haS, rfl⟩
    have ha0 : a ≠ 0 := (mem_commToBoolVal (x := a)).1 hmemT
    -- If `sSup S = 0`, then all elements of `S` are `0`, contradicting `ha0`.
    have hSup0 : sSup S ≠ 0 := by
      intro hSup0
      have hAll0 : ∀ b ∈ S, b = 0 := (sSup_eq_bot).1 (by simp [hSup0])
      exact ha0 (hAll0 a haS)
    exact (mem_commToBoolVal (x := sSup S)).2 hSup0

/-- A commutative-quantale morphism into the Boolean quantale. -/
noncomputable def commToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom CommQuantale BoolQuantale where
  toFun := commToBoolVal
  map_sSup' := commToBoolVal_map_sSup
  map_mul' _ _ := commToBoolVal_map_mul _ _

/-- Convenience: weakness transport along `commToBool`. -/
theorem commToBool_map_weakness
    {U : Type*} [Fintype U]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U CommQuantale)
    (H : Finset (U × U)) :
    commToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) commToBool wf) H := by
  simpa using
    (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.map_weakness
      (f := commToBool) (wf := wf) (H := H))

/-! ## Interval projections (used to connect interval vertices to point vertices) -/

lemma intervalUpper_map_mul (x y : IntervalQuantale) : (x * y).2 = x.2 * y.2 := rfl

lemma intervalUpper_map_sSup (S : Set IntervalQuantale) : (sSup S).2 = sSup (Prod.snd '' S) := by
  simpa using (Prod.snd_sSup (s := S))

/-- Project an interval value to its “upper” component. -/
noncomputable def intervalUpperToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom IntervalQuantale CommQuantale where
  toFun := Prod.snd
  map_sSup' := intervalUpper_map_sSup
  map_mul' _ _ := rfl

/-- A canonical interval-to-Boolean morphism (via the upper projection). -/
noncomputable def intervalToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom IntervalQuantale BoolQuantale where
  toFun := fun x => commToBoolVal x.2
  map_sSup' S := by
    -- `snd` commutes with `sSup`, and `commToBoolVal` commutes with `sSup`.
    have hsnd : (sSup S).2 = sSup (Prod.snd '' S) := intervalUpper_map_sSup (S := S)
    calc
      commToBoolVal (sSup S).2 = commToBoolVal (sSup (Prod.snd '' S)) := by simp [hsnd]
      _ = sSup (commToBoolVal '' (Prod.snd '' S)) := commToBoolVal_map_sSup (S := (Prod.snd '' S))
      _ = sSup ((fun x : IntervalQuantale => commToBoolVal x.2) '' S) := by
        simp [Set.image_image]
  map_mul' x y := by
    -- Only the upper coordinate matters.
    simpa [intervalUpper_map_mul] using commToBoolVal_map_mul x.2 y.2

/-- Convenience: weakness transport along `intervalToBool`. -/
theorem intervalToBool_map_weakness
    {U : Type*} [Fintype U]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U IntervalQuantale)
    (H : Finset (U × U)) :
    intervalToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) intervalToBool wf) H := by
  simpa using
    (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.map_weakness
      (f := intervalToBool) (wf := wf) (H := H))

/-! ## Boolean → commutative collapse

To connect the “Boolean quantale” semantics with the classical commutative `[0,1]`-like scale, we
provide the canonical embedding `{0,1} ↪ ℝ≥0∞` as a `QuantaleHom`.
-/

/-- Map the Boolean quantale `{0,1}` (as `Set Unit`) into `ℝ≥0∞` by `∅ ↦ 0`, `{()} ↦ 1`. -/
noncomputable def boolToCommVal (S : BoolQuantale) : CommQuantale :=
  if (():Unit) ∈ S then 1 else 0

lemma boolToCommVal_map_mul (S T : BoolQuantale) :
    boolToCommVal (S * T) = boolToCommVal S * boolToCommVal T := by
  classical
  by_cases hS : (():Unit) ∈ S <;> by_cases hT : (():Unit) ∈ T <;>
    simp [boolToCommVal, hS, hT, unit_mem_mul_iff]

lemma boolToCommVal_map_sSup (S : Set BoolQuantale) :
    boolToCommVal (sSup S) = sSup (boolToCommVal '' S) := by
  classical
  have hmem : (():Unit) ∈ sSup S ↔ ∃ A, A ∈ S ∧ (():Unit) ∈ A := by
    simp [Set.sSup_eq_sUnion, Set.mem_sUnion]
  by_cases h : ∃ A, A ∈ S ∧ (():Unit) ∈ A
  · have lhs : boolToCommVal (sSup S) = 1 := by simp [boolToCommVal, h]
    have hOneMem : (1 : CommQuantale) ∈ boolToCommVal '' S := by
      rcases h with ⟨A, hAS, hA⟩
      refine ⟨A, hAS, ?_⟩
      simp [boolToCommVal, hA]
    have hge : (1 : CommQuantale) ≤ sSup (boolToCommVal '' S) :=
      le_sSup hOneMem
    have hle : sSup (boolToCommVal '' S) ≤ (1 : CommQuantale) := by
      refine sSup_le ?_
      rintro x ⟨A, hAS, rfl⟩
      by_cases hA : (():Unit) ∈ A <;> simp [boolToCommVal, hA]
    have rhs : sSup (boolToCommVal '' S) = 1 := le_antisymm hle hge
    simpa [lhs, rhs]
  · have lhs : boolToCommVal (sSup S) = 0 := by simp [boolToCommVal, h]
    have hAll0 : ∀ x ∈ boolToCommVal '' S, x ≤ (0 : CommQuantale) := by
      rintro x ⟨A, hAS, rfl⟩
      have hA : (():Unit) ∉ A := by
        intro hA
        exact h ⟨A, hAS, hA⟩
      simp [boolToCommVal, hA]
    have rhs : sSup (boolToCommVal '' S) = 0 := by
      apply le_antisymm
      · exact sSup_le (hAll0)
      · exact bot_le
    simpa [lhs, rhs]

/-- Canonical `QuantaleHom` embedding the Boolean quantale into the commutative scale. -/
noncomputable def boolToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom BoolQuantale CommQuantale where
  toFun := boolToCommVal
  map_sSup' := boolToCommVal_map_sSup
  map_mul' := boolToCommVal_map_mul

/-- Convenience: weakness transport along `boolToComm`. -/
theorem boolToComm_map_weakness
    {U : Type*} [Fintype U]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BoolQuantale)
    (H : Finset (U × U)) :
    boolToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) boolToComm wf) H := by
  simpa using
    (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.map_weakness
      (f := boolToComm) (wf := wf) (H := H))

/-! ## Language quantales → Boolean (generic) -/

noncomputable def containsEmptyWord {α : Type} (L : LanguageQuantale α) : BoolQuantale :=
  if (1 : FreeMonoid α) ∈ L then {()} else ∅

lemma mem_containsEmptyWord {α : Type} (L : LanguageQuantale α) :
    (():Unit) ∈ containsEmptyWord L ↔ (1 : FreeMonoid α) ∈ L := by
  classical
  by_cases h : (1 : FreeMonoid α) ∈ L <;> simp [containsEmptyWord, h]

lemma one_mem_mul_iff {α : Type} (L M : LanguageQuantale α) :
    (1 : FreeMonoid α) ∈ L * M ↔ (1 : FreeMonoid α) ∈ L ∧ (1 : FreeMonoid α) ∈ M := by
  constructor
  · rintro ⟨x, hxL, y, hyM, hxy⟩
    have hlist : FreeMonoid.toList x ++ FreeMonoid.toList y = [] := by
      have : FreeMonoid.toList (x * y) = FreeMonoid.toList (1 : FreeMonoid α) := by
        -- `simp` is enough; `simpa` triggers the linter.
        simp [hxy] at *
      simpa [FreeMonoid.toList_mul, FreeMonoid.toList_one] using this
    have hx_nil : FreeMonoid.toList x = [] := (List.append_eq_nil_iff.mp hlist).1
    have hy_nil : FreeMonoid.toList y = [] := (List.append_eq_nil_iff.mp hlist).2
    have hx1 : x = (1 : FreeMonoid α) :=
      FreeMonoid.toList.injective (by simpa [FreeMonoid.toList_one] using hx_nil)
    have hy1 : y = (1 : FreeMonoid α) :=
      FreeMonoid.toList.injective (by simpa [FreeMonoid.toList_one] using hy_nil)
    constructor
    · simpa [hx1] using hxL
    · simpa [hy1] using hyM
  · rintro ⟨hx, hy⟩
    refine ⟨1, hx, 1, hy, by simp⟩

lemma containsEmptyWord_map_mul {α : Type} (L M : LanguageQuantale α) :
    containsEmptyWord (L * M) = containsEmptyWord L * containsEmptyWord M := by
  ext u
  cases u
  simp [mem_containsEmptyWord, one_mem_mul_iff, unit_mem_mul_iff]

lemma containsEmptyWord_map_sSup {α : Type} (S : Set (LanguageQuantale α)) :
    containsEmptyWord (sSup S) = sSup (containsEmptyWord '' S) := by
  ext u
  cases u
  simp [mem_containsEmptyWord, Set.sSup_eq_sUnion, Set.mem_sUnion]

/-- A canonical morphism from a language quantale to the Boolean quantale:
detect whether a language contains the empty word. -/
noncomputable def languageToBool {α : Type} :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (LanguageQuantale α) BoolQuantale where
  toFun := containsEmptyWord
  map_sSup' := containsEmptyWord_map_sSup
  map_mul' _ _ := containsEmptyWord_map_mul _ _

/-- Convenience: weakness transport along `languageToBool`. -/
theorem languageToBool_map_weakness {α : Type}
    {U : Type*} [Fintype U]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U (LanguageQuantale α))
    (H : Finset (U × U)) :
    languageToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) languageToBool wf) H := by
  simpa using
    (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.map_weakness
      (f := languageToBool) (wf := wf) (H := H))

/-! ## Language quantales → commutative scale

For each “independence quantale” (free/boolean/monotone), we provide a canonical morphism into the
commutative scale by composing `languageToBool` with `boolToComm`.
-/

noncomputable def languageToComm {α : Type} :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (LanguageQuantale α) CommQuantale :=
  Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.comp boolToComm (languageToBool (α := α))

theorem languageToComm_map_weakness {α : Type}
    {U : Type*} [Fintype U]
    (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U (LanguageQuantale α))
    (H : Finset (U × U)) :
    languageToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) languageToComm wf) H := by
  simpa using
    (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.map_weakness
      (f := languageToComm) (wf := wf) (H := H))

/-! ## Named specializations (to match `QuantaleType` in `Hypercube/Basic.lean`) -/

noncomputable abbrev quantumToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom QuantumQuantale BoolQuantale :=
  languageToBool (α := Bool)

noncomputable abbrev freeToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom FreeQuantale BoolQuantale :=
  languageToBool (α := (Σ n : ℕ, Mettapedia.ProbabilityTheory.FreeProbability.NC n))

noncomputable abbrev booleanIndepToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom BooleanIndepQuantale BoolQuantale :=
  languageToBool (α := ℕ+)

noncomputable abbrev monotoneIndepToBool :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom MonotoneIndepQuantale BoolQuantale :=
  languageToBool (α := List ℕ+)

noncomputable abbrev quantumToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom QuantumQuantale CommQuantale :=
  languageToComm (α := Bool)

noncomputable abbrev freeToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom FreeQuantale CommQuantale :=
  languageToComm (α := (Σ n : ℕ, Mettapedia.ProbabilityTheory.FreeProbability.NC n))

noncomputable abbrev booleanIndepToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom BooleanIndepQuantale CommQuantale :=
  languageToComm (α := ℕ+)

noncomputable abbrev monotoneIndepToComm :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom MonotoneIndepQuantale CommQuantale :=
  languageToComm (α := List ℕ+)

theorem quantumToBool_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U QuantumQuantale)
      (H : Finset (U × U)),
      quantumToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) quantumToBool wf) H :=
  fun wf H => by
    simpa [quantumToBool] using (languageToBool_map_weakness (α := Bool) (wf := wf) (H := H))

theorem freeToBool_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U FreeQuantale)
      (H : Finset (U × U)),
      freeToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) freeToBool wf) H :=
  fun wf H => by
    simpa [freeToBool] using
      (languageToBool_map_weakness
        (α := (Σ n : ℕ, Mettapedia.ProbabilityTheory.FreeProbability.NC n)) (wf := wf) (H := H))

theorem booleanIndepToBool_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BooleanIndepQuantale)
      (H : Finset (U × U)),
      booleanIndepToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) booleanIndepToBool wf) H :=
  fun wf H => by
    simpa [booleanIndepToBool] using
      (languageToBool_map_weakness (α := ℕ+) (wf := wf) (H := H))

theorem monotoneIndepToBool_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U MonotoneIndepQuantale)
      (H : Finset (U × U)),
      monotoneIndepToBool (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) monotoneIndepToBool wf) H :=
  fun wf H => by
    simpa [monotoneIndepToBool] using
      (languageToBool_map_weakness (α := List ℕ+) (wf := wf) (H := H))

theorem quantumToComm_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U QuantumQuantale)
      (H : Finset (U × U)),
      quantumToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) quantumToComm wf) H :=
  fun wf H => by
    simpa [quantumToComm] using (languageToComm_map_weakness (α := Bool) (wf := wf) (H := H))

theorem freeToComm_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U FreeQuantale)
      (H : Finset (U × U)),
      freeToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) freeToComm wf) H :=
  fun wf H => by
    simpa [freeToComm] using
      (languageToComm_map_weakness
        (α := (Σ n : ℕ, Mettapedia.ProbabilityTheory.FreeProbability.NC n)) (wf := wf) (H := H))

theorem booleanIndepToComm_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U BooleanIndepQuantale)
      (H : Finset (U × U)),
      booleanIndepToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) booleanIndepToComm wf) H :=
  fun wf H => by
    simpa [booleanIndepToComm] using
      (languageToComm_map_weakness (α := ℕ+) (wf := wf) (H := H))

theorem monotoneIndepToComm_map_weakness :
    ∀ {U : Type*} [Fintype U]
      (wf : Mettapedia.Algebra.QuantaleWeakness.WeightFunction U MonotoneIndepQuantale)
      (H : Finset (U × U)),
      monotoneIndepToComm (Mettapedia.Algebra.QuantaleWeakness.weakness wf H) =
        Mettapedia.Algebra.QuantaleWeakness.weakness
          (Mettapedia.Algebra.QuantaleWeakness.WeightFunction.map (U := U) monotoneIndepToComm wf) H :=
  fun wf H => by
    simpa [monotoneIndepToComm] using
      (languageToComm_map_weakness (α := List ℕ+) (wf := wf) (H := H))

/-! ## A small “semantics picker” for `QuantaleType`

Downstream hypercube modules sometimes want to talk about “the value quantale of a vertex” without
case-splitting manually.  This bundle provides:

* a carrier type `Q` with the structure needed for `weakness` (`Monoid` + `CompleteLattice`), and
* canonical structure-preserving maps into the Boolean and commutative scales.
-/

structure QuantaleTypeSemantics where
  Q : Type
  instMonoid : Monoid Q
  instCompleteLattice : CompleteLattice Q

attribute [instance] QuantaleTypeSemantics.instMonoid QuantaleTypeSemantics.instCompleteLattice

noncomputable def semanticsOfQuantaleType : QuantaleType → QuantaleTypeSemantics
  | .commutative => ⟨CommQuantale, by infer_instance, by infer_instance⟩
  | .interval => ⟨IntervalQuantale, by infer_instance, by infer_instance⟩
  | .noncommutative => ⟨QuantumQuantale, by infer_instance, by infer_instance⟩
  | .free => ⟨FreeQuantale, by infer_instance, by infer_instance⟩
  | .boolean => ⟨BooleanIndepQuantale, by infer_instance, by infer_instance⟩
  | .monotone => ⟨MonotoneIndepQuantale, by infer_instance, by infer_instance⟩
  | .booleanAlgebra => ⟨BoolQuantale, by infer_instance, by infer_instance⟩

noncomputable def toBoolOfQuantaleType :
    (t : QuantaleType) →
      Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (semanticsOfQuantaleType t).Q BoolQuantale
  | .commutative => by simpa [semanticsOfQuantaleType] using! commToBool
  | .interval => by simpa [semanticsOfQuantaleType] using! intervalToBool
  | .noncommutative => by simpa [semanticsOfQuantaleType] using! quantumToBool
  | .free => by simpa [semanticsOfQuantaleType] using! freeToBool
  | .boolean => by simpa [semanticsOfQuantaleType] using! booleanIndepToBool
  | .monotone => by simpa [semanticsOfQuantaleType] using! monotoneIndepToBool
  | .booleanAlgebra => by
      simpa [semanticsOfQuantaleType] using!
        (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.id (Q := BoolQuantale))

noncomputable def toCommOfQuantaleType :
    (t : QuantaleType) →
      Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (semanticsOfQuantaleType t).Q CommQuantale
  | .commutative => by
      simpa [semanticsOfQuantaleType] using!
        (Mettapedia.Algebra.QuantaleWeakness.QuantaleHom.id (Q := CommQuantale))
  | .interval => by simpa [semanticsOfQuantaleType] using! intervalUpperToComm
  | .noncommutative => by simpa [semanticsOfQuantaleType] using! quantumToComm
  | .free => by simpa [semanticsOfQuantaleType] using! freeToComm
  | .boolean => by simpa [semanticsOfQuantaleType] using! booleanIndepToComm
  | .monotone => by simpa [semanticsOfQuantaleType] using! monotoneIndepToComm
  | .booleanAlgebra => by simpa [semanticsOfQuantaleType] using! boolToComm

noncomputable def semanticsOfVertex (v : ProbabilityVertex) : QuantaleTypeSemantics :=
  semanticsOfQuantaleType (quantaleTypeOf v)

noncomputable def toBoolOfVertex (v : ProbabilityVertex) :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (semanticsOfVertex v).Q BoolQuantale :=
  toBoolOfQuantaleType (quantaleTypeOf v)

noncomputable def toCommOfVertex (v : ProbabilityVertex) :
    Mettapedia.Algebra.QuantaleWeakness.QuantaleHom (semanticsOfVertex v).Q CommQuantale :=
  toCommOfQuantaleType (quantaleTypeOf v)

end

end QuantaleSemantics

end Mettapedia.ProbabilityTheory.Hypercube
