import Mettapedia.GSLT.GraphTheory.Basic
import Mettapedia.GSLT.GraphTheory.FiniteSupportProjections

/-!
# Partial pairs and disjoint-union coding

Bucciarelli–Salibra §2.3 Definition 3 uses an injective partial coding map.
Section 3 Definition 5 combines factor coding only on same-component supports
and outputs. This file constructs that partial pair, not its completion or a
total weak-product graph model.
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-- Injectivity of a partial coding map concerns defined outputs only. -/
structure PartialCodingFunction (web : Web) where
  code : web.FiniteSubsets × web.carrier → Option web.carrier
  injective : ∀ {first second output},
    code first = some output → code second = some output → first = second

/-- An infinite web carrying a partial injective finite-input coding map. -/
structure PartialPair where
  web : Web
  coding : PartialCodingFunction web

namespace PartialPair

abbrev Carrier (pair : PartialPair) := pair.web.carrier

def domain (pair : PartialPair) : Set (pair.web.FiniteSubsets × pair.Carrier) :=
  {input | ∃ output, pair.coding.code input = some output}

def Total (pair : PartialPair) : Prop := ∀ input, input ∈ pair.domain

def Proper (pair : PartialPair) : Prop := ¬pair.Total

theorem projectLeft_eq_toLeft {α β : Type*} [DecidableEq α]
    (support : Finset (α ⊕ β)) : projectLeft support = support.toLeft := by
  ext output
  simp only [projectLeft, Finset.mem_filterMap, Finset.mem_toLeft]
  constructor
  · rintro ⟨input, hInput, hOutput⟩
    cases input with
    | inl value =>
        simp only [Option.some.injEq] at hOutput
        subst value
        exact hInput
    | inr value => cases hOutput
  · intro h
    exact ⟨.inl output, h, rfl⟩

theorem projectRight_eq_toRight {α β : Type*} [DecidableEq β]
    (support : Finset (α ⊕ β)) : projectRight support = support.toRight := by
  ext output
  simp only [projectRight, Finset.mem_filterMap, Finset.mem_toRight]
  constructor
  · rintro ⟨input, hInput, hOutput⟩
    cases input with
    | inl value => cases hOutput
    | inr value =>
        simp only [Option.some.injEq] at hOutput
        subst value
        exact hInput
  · intro h
    exact ⟨.inr output, h, rfl⟩

/-- The source partial map is undefined unless the entire support has the
same component as the output. It never silently projects away a component. -/
def disjointUnionCode (D₁ D₂ : GraphModel) :
    Finset (D₁.Carrier ⊕ D₂.Carrier) × (D₁.Carrier ⊕ D₂.Carrier) →
      Option (D₁.Carrier ⊕ D₂.Carrier)
  | (support, .inl output) =>
      if support = (projectLeft support).map Function.Embedding.inl then
        some (.inl (D₁.coding.code (projectLeft support, output))) else none
  | (support, .inr output) =>
      if support = (projectRight support).map Function.Embedding.inr then
        some (.inr (D₂.coding.code (projectRight support, output))) else none

theorem disjointUnionCode_inl_some_iff (D₁ D₂ : GraphModel)
    (support : Finset (D₁.Carrier ⊕ D₂.Carrier)) (output : D₁.Carrier)
    (token : D₁.Carrier ⊕ D₂.Carrier) :
    disjointUnionCode D₁ D₂ (support, .inl output) = some token ↔
      support = (projectLeft support).map Function.Embedding.inl ∧
        Sum.inl (D₁.coding.code (projectLeft support, output)) = token := by
  simp only [disjointUnionCode]
  by_cases h : support = (projectLeft support).map Function.Embedding.inl
  · rw [if_pos h]
    exact ⟨fun hCode => ⟨h, Option.some.inj hCode⟩,
      fun hCode => congrArg some hCode.2⟩
  · rw [if_neg h]
    constructor
    · intro hCode; cases hCode
    · intro hCode; exact (h hCode.1).elim

theorem disjointUnionCode_inr_some_iff (D₁ D₂ : GraphModel)
    (support : Finset (D₁.Carrier ⊕ D₂.Carrier)) (output : D₂.Carrier)
    (token : D₁.Carrier ⊕ D₂.Carrier) :
    disjointUnionCode D₁ D₂ (support, .inr output) = some token ↔
      support = (projectRight support).map Function.Embedding.inr ∧
        Sum.inr (D₂.coding.code (projectRight support, output)) = token := by
  simp only [disjointUnionCode]
  by_cases h : support = (projectRight support).map Function.Embedding.inr
  · rw [if_pos h]
    exact ⟨fun hCode => ⟨h, Option.some.inj hCode⟩,
      fun hCode => congrArg some hCode.2⟩
  · rw [if_neg h]
    constructor
    · intro hCode; cases hCode
    · intro hCode; exact (h hCode.1).elim

/-- The source domain guard restores genuine injectivity of defined outputs. -/
theorem disjointUnionCode_injective (D₁ D₂ : GraphModel)
    {first second : Finset (D₁.Carrier ⊕ D₂.Carrier) × (D₁.Carrier ⊕ D₂.Carrier)}
    {token : D₁.Carrier ⊕ D₂.Carrier}
    (hFirst : disjointUnionCode D₁ D₂ first = some token)
    (hSecond : disjointUnionCode D₁ D₂ second = some token) : first = second := by
  rcases first with ⟨a₁, output₁⟩
  rcases second with ⟨a₂, output₂⟩
  cases output₁ with
  | inl x₁ =>
      obtain ⟨hPure₁, hCode₁⟩ := (disjointUnionCode_inl_some_iff D₁ D₂ a₁ x₁ token).mp hFirst
      cases output₂ with
      | inl x₂ =>
          obtain ⟨hPure₂, hCode₂⟩ := (disjointUnionCode_inl_some_iff D₁ D₂ a₂ x₂ token).mp hSecond
          have hInputs := D₁.coding.injective (Sum.inl.inj (hCode₁.trans hCode₂.symm))
          obtain ⟨hSupport, hOutput⟩ := Prod.ext_iff.mp hInputs
          apply Prod.ext
          · exact hPure₁.trans ((congrArg (Finset.map Function.Embedding.inl) hSupport).trans hPure₂.symm)
          · exact congrArg Sum.inl hOutput
      | inr y₂ =>
          obtain ⟨_, hCode₂⟩ := (disjointUnionCode_inr_some_iff D₁ D₂ a₂ y₂ token).mp hSecond
          have h := hCode₁.trans hCode₂.symm
          cases h
  | inr y₁ =>
      obtain ⟨hPure₁, hCode₁⟩ := (disjointUnionCode_inr_some_iff D₁ D₂ a₁ y₁ token).mp hFirst
      cases output₂ with
      | inl x₂ =>
          obtain ⟨_, hCode₂⟩ := (disjointUnionCode_inl_some_iff D₁ D₂ a₂ x₂ token).mp hSecond
          have h := hCode₁.trans hCode₂.symm
          cases h
      | inr y₂ =>
          obtain ⟨hPure₂, hCode₂⟩ := (disjointUnionCode_inr_some_iff D₁ D₂ a₂ y₂ token).mp hSecond
          have hInputs := D₂.coding.injective (Sum.inr.inj (hCode₁.trans hCode₂.symm))
          obtain ⟨hSupport, hOutput⟩ := Prod.ext_iff.mp hInputs
          apply Prod.ext
          · exact hPure₁.trans ((congrArg (Finset.map Function.Embedding.inr) hSupport).trans hPure₂.symm)
          · exact congrArg Sum.inr hOutput

/-- Definition 5's proper partial pair. Definition 6 still requires its actual
canonical completion before this can yield a weak-product graph model. -/
def disjointUnion (D₁ D₂ : GraphModel) : PartialPair where
  web := {
    carrier := D₁.Carrier ⊕ D₂.Carrier
    decEq := inferInstance
    infinite := Sum.infinite_of_left
  }
  coding := {
    code := disjointUnionCode D₁ D₂
    injective := disjointUnionCode_injective D₁ D₂
  }

theorem disjointUnionCode_left (D₁ D₂ : GraphModel)
    (support : Finset D₁.Carrier) (output : D₁.Carrier) :
    disjointUnionCode D₁ D₂ (support.map Function.Embedding.inl, .inl output) =
      some (.inl (D₁.coding.code (support, output))) := by
  simp only [disjointUnionCode, projectLeft_eq_toLeft]
  have h : (support.map (Function.Embedding.inl : D₁.Carrier ↪ D₁.Carrier ⊕ D₂.Carrier)).toLeft = support := by
    rw [← Finset.disjSum_empty, Finset.toLeft_disjSum]
  simp only [h, ↓reduceIte]

theorem disjointUnionCode_right (D₁ D₂ : GraphModel)
    (support : Finset D₂.Carrier) (output : D₂.Carrier) :
    disjointUnionCode D₁ D₂ (support.map Function.Embedding.inr, .inr output) =
      some (.inr (D₂.coding.code (support, output))) := by
  simp only [disjointUnionCode, projectRight_eq_toRight]
  have h : (support.map (Function.Embedding.inr : D₂.Carrier ↪ D₁.Carrier ⊕ D₂.Carrier)).toRight = support := by
    rw [← Finset.empty_disjSum, Finset.toRight_disjSum]
  simp only [h, ↓reduceIte]

/-- Opposite-component support must be undefined, rather than erased. -/
theorem disjointUnionCode_inl_none_of_inr_mem (D₁ D₂ : GraphModel)
    (support : Finset (D₁.Carrier ⊕ D₂.Carrier)) (output : D₁.Carrier)
    (other : D₂.Carrier) (hOther : Sum.inr other ∈ support) :
    disjointUnionCode D₁ D₂ (support, .inl output) = none := by
  have hNotPure : support ≠ (projectLeft support).map Function.Embedding.inl := by
    intro hTwoSort
    have hMember : Sum.inr other ∈ (projectLeft support).map Function.Embedding.inl :=
      hTwoSort ▸ hOther
    obtain ⟨value, _, hValue⟩ := Finset.mem_map.mp hMember
    cases hValue
  simp only [disjointUnionCode, if_neg hNotPure]

theorem disjointUnionCode_inr_none_of_inl_mem (D₁ D₂ : GraphModel)
    (support : Finset (D₁.Carrier ⊕ D₂.Carrier)) (output : D₂.Carrier)
    (other : D₁.Carrier) (hOther : Sum.inl other ∈ support) :
    disjointUnionCode D₁ D₂ (support, .inr output) = none := by
  have hNotPure : support ≠ (projectRight support).map Function.Embedding.inr := by
    intro hTwoSort
    have hMember : Sum.inl other ∈ (projectRight support).map Function.Embedding.inr :=
      hTwoSort ▸ hOther
    obtain ⟨value, _, hValue⟩ := Finset.mem_map.mp hMember
    cases hValue
  simp only [disjointUnionCode, if_neg hNotPure]

/-- A missing mixed-component code proves the source union is genuinely
proper. Its completion cannot be replaced by a cast to a total pair. -/
theorem disjointUnion_proper (D₁ D₂ : GraphModel) (left : D₁.Carrier) (right : D₂.Carrier) :
    (disjointUnion D₁ D₂).Proper := by
  intro total
  change ∀ input, ∃ output, disjointUnionCode D₁ D₂ input = some output at total
  obtain ⟨output, hOutput⟩ := total ({Sum.inr right}, .inl left)
  have hMissing := disjointUnionCode_inl_none_of_inr_mem D₁ D₂ {Sum.inr right} left right
    (Finset.mem_singleton_self (Sum.inr right))
  have h := hMissing.symm.trans hOutput
  cases h

end PartialPair
end Mettapedia.GSLT.GraphTheory
