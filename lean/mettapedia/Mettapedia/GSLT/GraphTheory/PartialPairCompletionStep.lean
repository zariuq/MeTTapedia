import Mettapedia.GSLT.GraphTheory.PartialPair

/-!
# One canonical-completion successor

Bucciarelli–Salibra §2.3 Definition 4 adjoins one distinct token for each
undefined old finite-input/output pair. Sum tags keep these tokens disjoint
from the old web. This file constructs one successor partial pair: inputs
involving its new tokens remain undefined. It does not construct the limit
graph model or establish weak-product theory properties.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStep

open Mettapedia.GSLT.Core

abbrev Missing (pair : PartialPair) :=
  {input : pair.web.FiniteSubsets × pair.Carrier // pair.coding.code input = none}

abbrev Carrier (pair : PartialPair) := pair.Carrier ⊕ Missing pair

instance (pair : PartialPair) : DecidableEq (Missing pair) :=
  inferInstanceAs (DecidableEq
    {input : Finset pair.Carrier × pair.Carrier // pair.coding.code input = none})

/-- Complete precisely the old pairs, retaining their whole finite support. -/
def oldCode (pair : PartialPair) (input : pair.web.FiniteSubsets × pair.Carrier) :
    Carrier pair :=
  match h : pair.coding.code input with
  | some token => .inl token
  | none => .inr ⟨input, h⟩

theorem oldCode_of_defined (pair : PartialPair)
    (input : pair.web.FiniteSubsets × pair.Carrier) (token : pair.Carrier)
    (h : pair.coding.code input = some token) : oldCode pair input = .inl token := by
  unfold oldCode
  split <;> simp_all

theorem oldCode_of_missing (pair : PartialPair)
    (input : pair.web.FiniteSubsets × pair.Carrier)
    (h : pair.coding.code input = none) : oldCode pair input = .inr ⟨input, h⟩ := by
  unfold oldCode
  split <;> simp_all

theorem oldCode_injective (pair : PartialPair) : Function.Injective (oldCode pair) := by
  intro first second h
  cases hFirst : pair.coding.code first with
  | none =>
      rw [oldCode_of_missing pair first hFirst] at h
      cases hSecond : pair.coding.code second with
      | none =>
          rw [oldCode_of_missing pair second hSecond] at h
          exact congrArg Subtype.val (Sum.inr.inj h)
      | some token =>
          rw [oldCode_of_defined pair second token hSecond] at h
          cases h
  | some token =>
      rw [oldCode_of_defined pair first token hFirst] at h
      cases hSecond : pair.coding.code second with
      | none =>
          rw [oldCode_of_missing pair second hSecond] at h
          cases h
      | some other =>
          rw [oldCode_of_defined pair second other hSecond] at h
          have hTokens := Sum.inl.inj h
          subst other
          exact pair.coding.injective hFirst hSecond

/-- Only inputs entirely in the old web are filled in at this successor. -/
def code (pair : PartialPair) :
    Finset (Carrier pair) × Carrier pair → Option (Carrier pair)
  | (support, .inl output) =>
      if support = support.toLeft.map Function.Embedding.inl then
        some (oldCode pair (support.toLeft, output)) else none
  | (_, .inr _) => none

theorem code_inl_some_iff (pair : PartialPair) (support : Finset (Carrier pair))
    (output : pair.Carrier) (token : Carrier pair) :
    code pair (support, .inl output) = some token ↔
      support = support.toLeft.map Function.Embedding.inl ∧
        oldCode pair (support.toLeft, output) = token := by
  simp only [code]
  by_cases h : support = support.toLeft.map Function.Embedding.inl
  · rw [if_pos h]
    exact ⟨fun hCode => ⟨h, Option.some.inj hCode⟩,
      fun hCode => congrArg some hCode.2⟩
  · rw [if_neg h]
    constructor
    · intro hCode; cases hCode
    · intro hCode; exact (h hCode.1).elim

theorem code_inr (pair : PartialPair) (support : Finset (Carrier pair))
    (output : Missing pair) : code pair (support, .inr output) = none := rfl

theorem code_injective (pair : PartialPair)
    {first second : Finset (Carrier pair) × Carrier pair} {token : Carrier pair}
    (hFirst : code pair first = some token) (hSecond : code pair second = some token) :
    first = second := by
  rcases first with ⟨support₁, output₁⟩
  rcases second with ⟨support₂, output₂⟩
  cases output₁ with
  | inr missing => cases hFirst
  | inl output₁ =>
      obtain ⟨hPure₁, hCode₁⟩ := (code_inl_some_iff pair support₁ output₁ token).mp hFirst
      cases output₂ with
      | inr missing => cases hSecond
      | inl output₂ =>
          obtain ⟨hPure₂, hCode₂⟩ := (code_inl_some_iff pair support₂ output₂ token).mp hSecond
          have hInputs := oldCode_injective pair (hCode₁.trans hCode₂.symm)
          obtain ⟨hSupport, hOutput⟩ := Prod.ext_iff.mp hInputs
          apply Prod.ext
          · exact hPure₁.trans
              ((congrArg (Finset.map Function.Embedding.inl) hSupport).trans hPure₂.symm)
          · exact congrArg Sum.inl hOutput

/-- The actual enlarged web and partial injective coding at one stage. -/
def successor (pair : PartialPair) : PartialPair where
  web := {
    carrier := Carrier pair
    decEq := inferInstance
    infinite := Sum.infinite_of_left
  }
  coding := {
    code := code pair
    injective := code_injective pair
  }

theorem code_old (pair : PartialPair) (support : Finset pair.Carrier)
    (output : pair.Carrier) :
    code pair (support.map Function.Embedding.inl, .inl output) =
      some (oldCode pair (support, output)) := by
  simp only [code]
  have h : (support.map (Function.Embedding.inl : pair.Carrier ↪ Carrier pair)).toLeft =
      support := by
    rw [← Finset.disjSum_empty, Finset.toLeft_disjSum]
  simp only [h, ↓reduceIte]

/-- Existing defined codes are preserved under the old-web embedding. -/
theorem code_preserves_defined (pair : PartialPair) (support : Finset pair.Carrier)
    (output token : pair.Carrier) (h : pair.coding.code (support, output) = some token) :
    code pair (support.map Function.Embedding.inl, .inl output) = some (.inl token) := by
  rw [code_old, oldCode_of_defined pair _ token h]

/-- Each formerly undefined full old pair gets its own fresh token. -/
theorem code_fills_missing (pair : PartialPair) (support : Finset pair.Carrier)
    (output : pair.Carrier) (h : pair.coding.code (support, output) = none) :
    code pair (support.map Function.Embedding.inl, .inl output) =
      some (.inr ⟨(support, output), h⟩) := by
  rw [code_old, oldCode_of_missing pair _ h]

theorem code_none_of_fresh_mem (pair : PartialPair) (support : Finset (Carrier pair))
    (output : pair.Carrier) (fresh : Missing pair) (hFresh : Sum.inr fresh ∈ support) :
    code pair (support, .inl output) = none := by
  have hNotPure : support ≠ support.toLeft.map Function.Embedding.inl := by
    intro hTwoSort
    have hMember : Sum.inr fresh ∈ support.toLeft.map Function.Embedding.inl :=
      hTwoSort ▸ hFresh
    obtain ⟨value, _, hValue⟩ := Finset.mem_map.mp hMember
    cases hValue
  simp only [code, if_neg hNotPure]

/-- Definedness at this step is exactly membership in the embedded old inputs. -/
theorem domain_iff (pair : PartialPair) (input : (successor pair).web.FiniteSubsets ×
    (successor pair).Carrier) :
    input ∈ (successor pair).domain ↔
      ∃ (support : Finset pair.Carrier) (output : pair.Carrier),
        input = (support.map Function.Embedding.inl, Sum.inl output) := by
  rcases input with ⟨support, output⟩
  cases output with
  | inl output =>
      constructor
      · rintro ⟨token, hToken⟩
        obtain ⟨hTwoSort, _⟩ := (code_inl_some_iff pair support output token).mp hToken
        exact ⟨support.toLeft, output, congrArg (fun s => (s, Sum.inl output)) hTwoSort⟩
      · rintro ⟨oldSupport, oldOutput, hInput⟩
        rw [hInput]
        exact ⟨oldCode pair (oldSupport, oldOutput), code_old pair oldSupport oldOutput⟩
  | inr output =>
      constructor
      · rintro ⟨token, hToken⟩
        change none = some token at hToken
        cases hToken
      · rintro ⟨_, _, hInput⟩
        have h := congrArg Prod.snd hInput
        cases h

/-- A fresh output witnesses why one successor is not yet the total completion. -/
theorem successor_proper_of_missing (pair : PartialPair) (missing : Missing pair) :
    (successor pair).Proper := by
  intro total
  obtain ⟨token, hToken⟩ := total ((∅ : Finset (Carrier pair)), Sum.inr missing)
  change none = some token at hToken
  cases hToken

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStep
