import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceSyntax
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation

/-!
# Independent numbered JSON prefix and annotation/refusal controls

Literal numbered type and term rows feed the actual decoders and earn their
cache licences from empty. The resulting term is compared with the established
truth definition and consumed by constant admission. Syntax decoding alone
does not certify operator arity, constant annotation instances or term typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntaxControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation NumberedSourceSyntax

def symbols : ExportCodec.Symbols :=
  ⟨[("bool",TypeOp.bool),("fun",TypeOp.function)],[("=",Const.equality)]⟩

/-- Independent literal input records, including their actual numbered IDs. -/
def rawTypes : Array Json := #[
  .arr #[.num 0,.arr #[.str "op",.str "bool",.arr #[]]],
  .arr #[.num 1,.arr #[.str "op",.str "fun",.arr #[.num 0,.num 0]]],
  .arr #[.num 2,.arr #[.str "op",.str "fun",.arr #[.num 1,.num 0]]],
  .arr #[.num 3,.arr #[.str "op",.str "fun",.arr #[.num 1,.num 2]]]]

def rawTerms : Array Json := #[
  .arr #[.num 0,.arr #[.str "var",.str "p",.num 0]],
  .arr #[.num 1,.arr #[.str "abs",.num 0,.num 0]],
  .arr #[.num 2,.arr #[.str "const",.str "=",.num 3]],
  .arr #[.num 3,.arr #[.str "app",.num 2,.num 1]],
  .arr #[.num 4,.arr #[.str "app",.num 3,.num 1]]]

def numberedBody? (index : Nat) (record : Json) : Option Json := do
  match ← ExportCodec.array? record with
  | [number,body] => if (← ExportCodec.natural? number) = index then some body else none
  | _ => none

def typeRows (index : Nat) : Option Json := (rawTypes[index]?).bind (numberedBody? index)
def termRows (index : Nat) : Option Json := (rawTerms[index]?).bind (numberedBody? index)

theorem types_available : (types? symbols typeRows (fun _ => none) [0,1,2,3]).isSome = true := by decide +kernel

def typeCache : Nat → Option Ty := (types? symbols typeRows (fun _ => none) [0,1,2,3]).get types_available

theorem type_cache_decoded : types? symbols typeRows (fun _ => none) [0,1,2,3] = some typeCache :=
  (Option.some_get types_available).symm

theorem type_cache_correct : TypeCacheCorrect symbols typeRows typeCache :=
  types_sound symbols typeRows [0,1,2,3] (fun _ => none) typeCache
    (by intro index type impossible; cases impossible) type_cache_decoded

theorem terms_available : (terms? symbols termRows typeCache (fun _ => none) [0,1,2,3,4]).isSome = true := by decide +kernel

def termCache : Nat → Option SourceTerm :=
  (terms? symbols termRows typeCache (fun _ => none) [0,1,2,3,4]).get terms_available

theorem term_cache_decoded : terms? symbols termRows typeCache (fun _ => none) [0,1,2,3,4] = some termCache :=
  (Option.some_get terms_available).symm

theorem term_cache_correct : TermCacheCorrect symbols typeRows termRows termCache :=
  terms_sound symbols typeRows termRows typeCache type_cache_correct [0,1,2,3,4]
    (fun _ => none) termCache (by intro index term impossible; cases impossible) term_cache_decoded

theorem term_four_available : (termCache 4).isSome = true := by decide +kernel

def decodedTruth : SourceTerm := (termCache 4).get term_four_available

theorem decodedTruth_at : TermAt symbols typeRows termRows 4 decodedTruth :=
  term_cache_correct 4 decodedTruth (Option.some_get term_four_available).symm

/-- Decoder output is validated against the independently established body. -/
theorem decodedTruth_eq : decodedTruth = StandardTheoryInterpretation.Source.truthBody := by
  unfold StandardTheoryInterpretation.Source.truthBody
  rfl

theorem truth_source_checked :
    (checkSource SourceProfile.primitiveContext.signature
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) decodedTruth).isSome = true := by decide +kernel

theorem truth_constant_admitted :
    admitConstantInTheory SourceProfile.primitiveContext
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature) (.global "T") decodedTruth =
      some StandardTheoryInterpretation.Source.truthResult := by
  rw [decodedTruth_eq]
  exact StandardTheoryInterpretation.Source.truthAdmitted

theorem wrong_number_refused :
    numberedBody? 0 (.arr #[.num 1,.arr #[.str "var",.str "p",.num 0]]) = none := rfl

theorem type_bad_record_arity : typeRow? (.arr #[.str "op",.str "bool"]) = none := rfl
theorem type_bad_tag : typeRow? (.arr #[.str "arrow",.str "bool",.arr #[]]) = none := rfl
theorem term_bad_record_arity : termRow? (.arr #[.str "var",.str "p"]) = none := rfl
theorem term_bad_tag : termRow? (.arr #[.str "apply",.num 0,.num 0]) = none := rfl

theorem type_self_reference_refused :
    typeStep? symbols typeCache 1 (.arr #[.str "op",.str "fun",.arr #[.num 1,.num 0]]) = none := rfl
theorem type_forward_reference_refused :
    typeStep? symbols typeCache 1 (.arr #[.str "op",.str "fun",.arr #[.num 2,.num 0]]) = none := rfl
theorem missing_type_cache_refused :
    typeStep? symbols (fun _ => none) 1 (.arr #[.str "op",.str "fun",.arr #[.num 0,.num 0]]) = none := rfl
theorem missing_operator_refused :
    typeStep? symbols typeCache 4 (.arr #[.str "op",.str "missing",.arr #[]]) = none := rfl

theorem term_self_reference_refused :
    termStep? symbols typeCache termCache 3 (.arr #[.str "app",.num 3,.num 1]) = none := rfl
theorem term_forward_reference_refused :
    termStep? symbols typeCache termCache 3 (.arr #[.str "app",.num 4,.num 1]) = none := rfl
theorem missing_term_cache_refused :
    termStep? symbols typeCache (fun _ => none) 3 (.arr #[.str "app",.num 2,.num 1]) = none := rfl
theorem missing_annotation_cache_refused :
    termStep? symbols (fun _ => none) termCache 0 (.arr #[.str "var",.str "p",.num 0]) = none := rfl
theorem missing_constant_refused :
    termStep? symbols typeCache termCache 2 (.arr #[.str "const",.str "missing",.num 0]) = none := rfl
theorem nonvariable_binder_refused :
    termStep? symbols typeCache termCache 5 (.arr #[.str "abs",.num 2,.num 0]) = none := rfl

/-- Operator annotation syntax and operator arity are distinct checks. -/
theorem malformed_operator_annotation_parses :
    typeStep? symbols typeCache 4 (.arr #[.str "op",.str "fun",.arr #[.num 0]]) =
      some (.op TypeOp.function [Ty.bool]) := rfl

theorem malformed_operator_annotation_unformed :
    typeFormedB SourceProfile.primitiveContext.signature (.op TypeOp.function [Ty.bool]) = false := by decide +kernel

/-- The decoder preserves the written annotation; the signature checker refuses it. -/
theorem equality_annotation_parses :
    termStep? symbols typeCache termCache 5 (.arr #[.str "const",.str "=",.num 0]) =
      some (.const Const.equality Ty.bool) := rfl

theorem equality_annotation_infers : (SourceTerm.const Const.equality Ty.bool).inferType = some Ty.bool := by
  simp only [SourceTerm.inferType]

theorem equality_annotation_signature_refused :
    (checkSource SourceProfile.primitiveContext.signature
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (.const Const.equality Ty.bool)).isNone = true := by decide +kernel

theorem illtyped_application_parses :
    termStep? symbols typeCache termCache 5 (.arr #[.str "app",.num 0,.num 0]) =
      some (.app (.var (.global "p") Ty.bool) (.var (.global "p") Ty.bool)) := rfl

theorem illtyped_application_refused :
    (SourceTerm.app (.var (.global "p") Ty.bool) (.var (.global "p") Ty.bool)).check.isNone = true := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntaxControls
