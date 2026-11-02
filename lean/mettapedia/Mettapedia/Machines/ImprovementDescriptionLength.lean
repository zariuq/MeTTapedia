import Mettapedia.Machines.ImprovementInformation
import Mettapedia.InformationTheory.RelationStoreKolmogorov
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity
import Mettapedia.Computability.KolmogorovComplexity.NaturalWordEncoding

/-!
# Conditional descriptions of improvement results

The finite information classes from `ImprovementInformation` are encoded as
actual binary words. For every fixed auxiliary context, fewer than `2^L` of
these classes have plain conditional complexity below `L`. In particular some
class requires at least `floor(log₂(c+2))` bits. This applies to the existing
partial-recursive universal conditional interpreter, not a hypothetical oracle.

The context can contain the candidate, decoder, shared store, or other metadata.
Information placed there is not destroyed: conditioning on the whole output
makes its residual description constant-sized. No computable minimizer, prefix
complexity identity, or runtime complexity claim is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.DescriptionLength

open KolmogorovComplexity Mettapedia.InformationTheory.RelationStoreFloors
open scoped Classical

def codeWord {candidate : Nat} (code : Fin (candidate + 2)) : BinString :=
  NaturalWordEncoding.decode code.val

def readCode (candidate : Nat) (word : BinString) : Option (Fin (candidate + 2)) :=
  if bound : NaturalWordEncoding.encode word < candidate + 2 then
    some ⟨NaturalWordEncoding.encode word, bound⟩ else none

theorem readCode_word {candidate : Nat} (code : Fin (candidate + 2)) :
    readCode candidate (codeWord code) = some code := by
  simp [readCode, codeWord, NaturalWordEncoding.encode_decode, code.isLt]

theorem short_program_describes (U : ConditionalAlgorithm) (context : BinString)
    {candidate L : Nat} (code : Fin (candidate + 2))
    (reachable : ∃ p, codeWord code ∈ U p context)
    (short : plainConditionalComplexity U (codeWord code) context < L) :
    DescribedBelow (throughAlgorithm (fun p => U p context) (readCode candidate)) L code := by
  obtain ⟨p, hp, length⟩ := exists_program_of_plainConditionalComplexity U context (codeWord code) reachable
  exact ⟨p, (throughAlgorithm_of_mem hp).trans (readCode_word code), length ▸ short⟩

theorem few_short_results (U : ConditionalAlgorithm) (context : BinString) (candidate L : Nat)
    (reachable : ∀ code : Fin (candidate + 2), ∃ p, codeWord code ∈ U p context) :
    (Finset.univ.filter fun code : Fin (candidate + 2) =>
      plainConditionalComplexity U (codeWord code) context < L).card < 2 ^ L := by
  have included : (Finset.univ.filter fun code : Fin (candidate + 2) =>
      plainConditionalComplexity U (codeWord code) context < L) ⊆
      Finset.univ.filter (DescribedBelow (throughAlgorithm (fun p => U p context) (readCode candidate)) L) := by
    intro code member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      short_program_describes U context code (reachable code) (Finset.mem_filter.mp member).2⟩
  refine (Finset.card_le_card included).trans_lt ?_
  simpa using card_describedBelow_lt
    (throughAlgorithm (fun p => U p context) (readCode candidate)) (σ := Bool) (by simp) Finset.univ L

theorem some_result_needs_bits (U : ConditionalAlgorithm) (context : BinString) (candidate L : Nat)
    (reachable : ∀ code : Fin (candidate + 2), ∃ p, codeWord code ∈ U p context)
    (enough : 2 ^ L ≤ candidate + 2) :
    ∃ code : Fin (candidate + 2), L ≤ plainConditionalComplexity U (codeWord code) context := by
  have strict := (few_short_results U context candidate L reachable).trans_le enough
  by_contra h
  push Not at h
  have allShort : (Finset.univ.filter fun code : Fin (candidate + 2) =>
      plainConditionalComplexity U (codeWord code) context < L) = Finset.univ := by
    ext code
    simp [h code]
  rw [allShort] at strict
  simp at strict

/-- The fixed context may contain `candidate`; it is common to every compared
result. It cannot contain a different answer for each result in this theorem. -/
theorem universal_result_floor (context : BinString) (candidate : Nat) :
    ∃ code : Fin (candidate + 2), Nat.log 2 (candidate + 2) ≤
      canonicalPlainConditionalComplexity (codeWord code) context := by
  apply some_result_needs_bits universalConditionalAlgorithm context candidate
  · intro code
    exact canonicalPlainConditional_hasProgram context (codeWord code)
  · exact Nat.pow_log_le_self 2 (by omega)

/-- Moving the output into shared context removes its residual description,
not the memory required to retain that context. -/
theorem output_in_context_constant_cost (U : ConditionalAlgorithm) (universal : IsUniversalConditional U) :
    ∃ overhead : Nat, ∀ context : BinString,
      plainConditionalComplexity U context context ≤ overhead := by
  let copyContext : ConditionalAlgorithm := fun _ context => Part.some context
  have computableCopy : Partrec₂ copyContext := Computable.snd.partrec.to₂
  obtain ⟨compilerPrefix, compiled⟩ := universal copyContext computableCopy
  refine ⟨compilerPrefix.length, ?_⟩
  intro context
  have hp : context ∈ U compilerPrefix context := by
    simpa using compiled [] context context (by simp [copyContext])
  exact plainConditionalComplexity_le_of_program U context context compilerPrefix hp

end Mettapedia.Machines.KeyedImprovement.DescriptionLength
