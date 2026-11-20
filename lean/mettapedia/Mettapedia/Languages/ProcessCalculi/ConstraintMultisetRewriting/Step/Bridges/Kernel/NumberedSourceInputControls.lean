import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceInput
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceSyntaxControls
import Mathlib.Tactic.IntervalCases

/-!
# Numbered envelopes through the actual truth-body prefix

The independently captured prefix feeds both the envelope and syntax
decoders. Their actual intermediate rows agree, so the numbered record,
decoded source node and admitted definition are joined. Auxiliary controls
retain duplicate bodies with distinct IDs and reject resetting chunk IDs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceInputControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation NumberedSourceSyntax NumberedSourceInput

theorem types_available : (numberedRows? 0 NumberedSourceSyntaxControls.rawTypes.toList).isSome = true := by decide +kernel
theorem terms_available : (numberedRows? 0 NumberedSourceSyntaxControls.rawTerms.toList).isSome = true := by decide +kernel

def typeBodies : List Json := (numberedRows? 0 NumberedSourceSyntaxControls.rawTypes.toList).get types_available
def termBodies : List Json := (numberedRows? 0 NumberedSourceSyntaxControls.rawTerms.toList).get terms_available

theorem types_numbered : NumberedAt 0 NumberedSourceSyntaxControls.rawTypes.toList typeBodies :=
  (numberedRows_eq_some_iff _ _ _).mp (Option.some_get types_available).symm

theorem terms_numbered : NumberedAt 0 NumberedSourceSyntaxControls.rawTerms.toList termBodies :=
  (numberedRows_eq_some_iff _ _ _).mp (Option.some_get terms_available).symm

theorem type_rows_eq : NumberedSourceSyntaxControls.typeRows = fun index => typeBodies[index]? := by
  funext index
  by_cases within : index < 4
  · interval_cases index <;> rfl
  · have missingRaw : NumberedSourceSyntaxControls.rawTypes[index]? = none := Array.getElem?_eq_none (by simpa [NumberedSourceSyntaxControls.rawTypes] using Nat.le_of_not_gt within)
    have length : typeBodies.length = 4 := by decide +kernel
    have missingBody : typeBodies[index]? = none := List.getElem?_eq_none (by omega)
    simp [NumberedSourceSyntaxControls.typeRows, missingRaw, missingBody]

theorem term_rows_eq : NumberedSourceSyntaxControls.termRows = fun index => termBodies[index]? := by
  funext index
  by_cases within : index < 5
  · interval_cases index <;> rfl
  · have missingRaw : NumberedSourceSyntaxControls.rawTerms[index]? = none := Array.getElem?_eq_none (by simpa [NumberedSourceSyntaxControls.rawTerms] using Nat.le_of_not_gt within)
    have length : termBodies.length = 5 := by decide +kernel
    have missingBody : termBodies[index]? = none := List.getElem?_eq_none (by omega)
    simp [NumberedSourceSyntaxControls.termRows, missingRaw, missingBody]

theorem cache_correct_for_bodies :
    TermCacheCorrect NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows (fun index => termBodies[index]?) NumberedSourceSyntaxControls.termCache := by
  have correct := NumberedSourceSyntaxControls.term_cache_correct
  rw [term_rows_eq] at correct
  exact correct

theorem raw_truth_readback :
    ∃ original body, NumberedSourceSyntaxControls.rawTerms.toList[4]? = some original ∧ identifier? original = some 4 ∧
      ExportCodec.at? original 1 = some body ∧ termBodies[4]? = some body ∧
      TermAt NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows (fun index => termBodies[index]?) 4 NumberedSourceSyntaxControls.decodedTruth ∧
      NumberedSourceSyntaxControls.decodedTruth = StandardTheoryInterpretation.Source.truthBody ∧
      admitConstantInTheory SourceProfile.primitiveContext
        (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (.global "T") NumberedSourceSyntaxControls.decodedTruth =
          some StandardTheoryInterpretation.Source.truthResult := by
  have found : NumberedSourceSyntaxControls.termCache 4 = some NumberedSourceSyntaxControls.decodedTruth := (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm
  obtain ⟨original,body,atRow,header,payload,bodyAt,node⟩ :=
    certified_term_readback NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows NumberedSourceSyntaxControls.rawTerms.toList termBodies terms_numbered
      NumberedSourceSyntaxControls.termCache cache_correct_for_bodies 4 NumberedSourceSyntaxControls.decodedTruth found
  exact ⟨original,body,atRow,header,payload,bodyAt,node,NumberedSourceSyntaxControls.decodedTruth_eq,NumberedSourceSyntaxControls.truth_constant_admitted⟩

theorem any_licensed_truth_read_agrees (other : Nat → Option SourceTerm)
    (correct : TermCacheCorrect NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows (fun index => termBodies[index]?) other)
    (term : SourceTerm) (found : other 4 = some term) : term = StandardTheoryInterpretation.Source.truthBody := by
  have same := term_caches_agree NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows (fun index => termBodies[index]?)
    other NumberedSourceSyntaxControls.termCache correct cache_correct_for_bodies 4 term NumberedSourceSyntaxControls.decodedTruth found
    (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm
  exact same.trans NumberedSourceSyntaxControls.decodedTruth_eq

theorem actual_type_chunks_compose :
    numberedRows? 0 (NumberedSourceSyntaxControls.rawTypes.toList.take 2 ++ NumberedSourceSyntaxControls.rawTypes.toList.drop 2) =
      some (typeBodies.take 2 ++ typeBodies.drop 2) := by
  apply numberedRows_append_checked
  · rfl
  · rfl

theorem reset_second_chunk_refused :
    numberedRows? 0 (NumberedSourceSyntaxControls.rawTypes.toList.drop 2) = none := rfl

def repeatedBodies : List Json :=
  [.arr #[.num 0,.str "same"],.arr #[.num 1,.str "same"]]

theorem repeated_bodies_retained : numberedRows? 0 repeatedBodies = some [.str "same",.str "same"] := rfl

theorem repeated_bodies_keep_both_origins :
    NumberedAt 0 repeatedBodies [.str "same",.str "same"] ∧ repeatedBodies.length = 2 :=
  ⟨(numberedRows_eq_some_iff _ _ _).mp repeated_bodies_retained,rfl⟩

theorem repeated_identifier_refused :
    numberedRows? 0 [.arr #[.num 0,.str "same"],.arr #[.num 0,.str "same"]] = none := rfl

/-- The retained source reader observes positions zero and one, allowing metadata. -/
theorem trailing_metadata_allowed :
    numberedRow? 0 (.arr #[.num 0,.str "body",.str "metadata"]) = some (.str "body") := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceInputControls
