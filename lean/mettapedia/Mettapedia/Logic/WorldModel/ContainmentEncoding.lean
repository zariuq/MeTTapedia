import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# Complexity-indexed containment payloads

An interpreter program witnessing a conditional complexity such as
`K(generator | feature, K(feature))` expects both the feature and its exact
complexity as auxiliary input.  A residual that transports only the witness
program and the original parameter therefore omits data required by that
interface.

This file gives the representation-level repair.  The corrected residual
contains three fields:

1. the binary representation of the complexity index;
2. the conditional reconstruction program;
3. the original residual parameter.

Nested `e2pair` encodings make the first two boundaries self-delimiting while
leaving the final residual untouched.  The positive theorem proves an exact
round trip.  The negative theorem proves that the corresponding two-field
encoding cannot be injective as an encoding of triples, because it erases the
complexity index.

This is the coding layer of a repaired algorithmic-containment construction.
It does not by itself assert the conditional chain rule, a complexity bound,
or family-level feature implication.
-/

namespace Mettapedia.Logic.WorldModel.ContainmentEncoding

open KolmogorovComplexity

/-- Encode an exact complexity index, a reconstruction program, and the
original residual. -/
def indexedResidual
    (complexityIndex : Nat) (reconstructionProgram residual : BinString) : BinString :=
  e2triple (binaryBits complexityIndex) reconstructionProgram residual

/-- Decode the three fields of `indexedResidual`. -/
def decodeIndexedResidual
    (input : BinString) : Option (Nat × BinString × BinString) :=
  match e2decodeTriple input with
  | none => none
  | some (complexityBits, reconstructionProgram, residual) =>
      some (ofBinaryBits complexityBits, reconstructionProgram, residual)

theorem decodeIndexedResidual_indexedResidual
    (complexityIndex : Nat) (reconstructionProgram residual : BinString) :
    decodeIndexedResidual
        (indexedResidual complexityIndex reconstructionProgram residual) =
      some (complexityIndex, reconstructionProgram, residual) := by
  simp [decodeIndexedResidual, indexedResidual, e2decodeTriple_e2triple,
    ofBinaryBits_binaryBits]

theorem indexedResidual_injective :
    Function.Injective (fun fields : Nat × BinString × BinString =>
      indexedResidual fields.1 fields.2.1 fields.2.2) := by
  intro left right h
  have hdecode := congrArg decodeIndexedResidual h
  simpa only [decodeIndexedResidual_indexedResidual, Option.some.injEq] using hdecode

theorem indexedResidual_length
    (complexityIndex : Nat) (reconstructionProgram residual : BinString) :
    (indexedResidual complexityIndex reconstructionProgram residual).length =
      (e2pair (binaryBits complexityIndex) reconstructionProgram).length +
        2 *
          (binaryBits
            (e2pair (binaryBits complexityIndex) reconstructionProgram).length).length +
        1 + residual.length := by
  exact e2triple_length (binaryBits complexityIndex) reconstructionProgram residual

theorem indexedResidual_length_le_log
    (complexityIndex : Nat) (reconstructionProgram residual : BinString) :
    (indexedResidual complexityIndex reconstructionProgram residual).length ≤
      (e2pair (binaryBits complexityIndex) reconstructionProgram).length +
        2 * Nat.log 2
          ((e2pair (binaryBits complexityIndex) reconstructionProgram).length + 1) +
        3 + residual.length := by
  exact e2triple_length_le_log
    (binaryBits complexityIndex) reconstructionProgram residual

/-- The uncorrected payload carries only the reconstruction program and the
residual, omitting the complexity index. -/
def unindexedResidual (reconstructionProgram residual : BinString) : BinString :=
  e2pair reconstructionProgram residual

/-- Omitting the complexity index is genuine information loss: two different
indices always produce the same unindexed payload when the remaining fields
are fixed. -/
theorem unindexedResidual_not_injective :
    ¬ Function.Injective (fun fields : Nat × BinString × BinString =>
      unindexedResidual fields.2.1 fields.2.2) := by
  intro injective
  let reconstructionProgram : BinString := []
  let residual : BinString := []
  have equalInputs :
      (0, reconstructionProgram, residual) =
        (1, reconstructionProgram, residual) := by
    apply injective
    rfl
  have impossible := congrArg Prod.fst equalInputs
  simp at impossible

#print axioms decodeIndexedResidual_indexedResidual
#print axioms indexedResidual_injective
#print axioms indexedResidual_length_le_log
#print axioms unindexedResidual_not_injective

end Mettapedia.Logic.WorldModel.ContainmentEncoding
