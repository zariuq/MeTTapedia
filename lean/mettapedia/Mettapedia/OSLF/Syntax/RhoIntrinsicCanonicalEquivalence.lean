import Mettapedia.OSLF.Syntax.RhoIntrinsicSortedCoverage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping

/-!
# Complete intrinsic rho quotient and canonical sorted patterns

The canonical carrier is specified independently by the authored sorting
judgment and normalization fixed-point property. Actual readback supplies its
inverse, without choosing quotient representatives. Both inverse laws are
earned from coverage and canonical equality reflection. Comparing canonical
patterns consequently gives a constructive decision of source class equality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def Sorted (context : Ctx sig) (sort : Srt) (pattern : Pattern) : Prop :=
  match sort with
  | .nm => NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern
  | .pr => ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern

theorem Sorted.hashSetFree {context : Ctx sig} {sort : Srt} {pattern : Pattern}
    (typed : Sorted context sort pattern) : HashSetFree pattern := by
  cases sort with
  | nm => exact PureBoundary.rhoNameWellSorted_hashSetFree typed
  | pr => exact PureBoundary.rhoProcWellSorted_hashSetFree typed

theorem Sorted.canonicalize {context : Ctx sig} {sort : Srt} {pattern : Pattern}
    (typed : Sorted context sort pattern) : Sorted context sort (canonicalize pattern) := by
  cases sort with
  | nm => exact CanonicalTyping.canonicalize_nameWellSorted _ typed
  | pr => exact CanonicalTyping.canonicalize_procWellSorted _ typed

theorem sorted_coverage {context : Ctx sig} {sort : Srt} {pattern : Pattern}
    (typed : Sorted context sort pattern) :
    ∃ term, read context sort pattern = some term ∧ StructuralCongruence (encodeTerm term) pattern := by
  cases sort with
  | nm => exact sorted_name_coverage typed
  | pr => exact sorted_process_coverage typed

def CanonicalPattern (context : Ctx sig) (sort : Srt) :=
  {pattern : Pattern // Sorted context sort pattern ∧ canonicalize pattern = pattern}

theorem encoded_class_sorted {context : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE context sort) : Sorted context sort (encodeEquationClass value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
    apply Sorted.canonicalize
    cases sort with
    | nm => exact encodedTerm_typed term
    | pr => exact encodedTerm_typed term

theorem encoded_class_canonical {context : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE context sort) :
    canonicalize (encodeEquationClass value) = encodeEquationClass value := by
  induction value using Quotient.inductionOn with
  | _ term => exact canonicalize_idempotent (encodeTerm term)

def encodeCanonical {context : Ctx sig} {sort : Srt} (value : TermQ rhoSourceE context sort) :
    CanonicalPattern context sort :=
  ⟨encodeEquationClass value, encoded_class_sorted value, encoded_class_canonical value⟩

theorem canonical_read_isSome {context : Ctx sig} {sort : Srt}
    (pattern : CanonicalPattern context sort) : (classRead context sort pattern.val).isSome := by
  obtain ⟨term, readout, _⟩ := sorted_coverage pattern.property.1
  simp only [classRead, readout, Option.map_some, Option.isSome_some]

def decodeCanonical {context : Ctx sig} {sort : Srt} (pattern : CanonicalPattern context sort) :
    TermQ rhoSourceE context sort :=
  (classRead context sort pattern.val).get (canonical_read_isSome pattern)

theorem read_encoded_equation_class {context : Ctx sig} {sort : Srt}
    (value : TermQ rhoSourceE context sort) :
    classRead context sort (encodeEquationClass value) = some value := by
  induction value using Quotient.inductionOn with
  | _ term => exact canonical_encoded_class term

theorem decode_encode {context : Ctx sig} {sort : Srt} (value : TermQ rhoSourceE context sort) :
    decodeCanonical (encodeCanonical value) = value :=
  Option.get_of_eq_some _ (read_encoded_equation_class value)

theorem encode_decode {context : Ctx sig} {sort : Srt}
    (pattern : CanonicalPattern context sort) : encodeCanonical (decodeCanonical pattern) = pattern := by
  obtain ⟨term, readout, congruent⟩ := sorted_coverage pattern.property.1
  have sameReadout : classRead context sort pattern.val = some (project term) := by
    simp only [classRead, readout, Option.map_some]
  have decoded : decodeCanonical pattern = project term := Option.get_of_eq_some _ sameReadout
  apply Subtype.ext
  change encodeEquationClass (decodeCanonical pattern) = pattern.val
  rw [decoded]
  change canonicalize (encodeTerm term) = pattern.val
  exact (canonicalize_eq_of_structuralCongruence congruent
    (encodedTerm_hashSetFree term) pattern.property.1.hashSetFree).trans pattern.property.2

def canonicalEquiv (context : Ctx sig) (sort : Srt) :
    TermQ rhoSourceE context sort ≃ CanonicalPattern context sort where
  toFun := encodeCanonical
  invFun := decodeCanonical
  left_inv := decode_encode
  right_inv := encode_decode

def equationClassDecision (context : Ctx sig) (sort : Srt) :
    DecidableEq (TermQ rhoSourceE context sort) := fun first second =>
  if same : encodeEquationClass first = encodeEquationClass second then
    isTrue (canonical_encoding_injective context sort same)
  else isFalse (fun equal => same (congrArg encodeEquationClass equal))

def equationClassTest {context : Ctx sig} {sort : Srt}
    (first second : TermQ rhoSourceE context sort) : Bool :=
  decide (encodeEquationClass first = encodeEquationClass second)

theorem equationClassTest_true_iff {context : Ctx sig} {sort : Srt}
    (first second : TermQ rhoSourceE context sort) :
    equationClassTest first second = true ↔ first = second := by
  simp only [equationClassTest, decide_eq_true_eq, canonical_encoding_equality_iff]

theorem equationClassTest_false_iff {context : Ctx sig} {sort : Srt}
    (first second : TermQ rhoSourceE context sort) :
    equationClassTest first second = false ↔ first ≠ second := by
  simp only [equationClassTest, decide_eq_false_iff_not, canonical_encoding_equality_iff]

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
