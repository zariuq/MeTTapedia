import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalEquivalence

/-!
# Quotation-safety readout and exact class admission

The intrinsic parser preserves the complete quotation-aware binder check at
every supplied depth. A source equation class has a quote-safe representative
exactly when its earned canonical encoding passes the authored binder check.
This is an equation-compatible admission criterion, rather than a test on an
arbitrarily selected surface spelling.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.DerivedPresentationSyntax MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

mutual
theorem sorted_name_safety : ∀ {context : Ctx sig} {pattern : Pattern},
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern →
    ∃ term, readName context pattern = some term ∧
      ∀ depth, intrinsicQuoteSafe depth term = binderSafeAt "NQuote" depth pattern
  | context, _, .bvar lookup => by
    obtain ⟨position, readout⟩ := variableAt_exists_of_labels context Srt.nm _ lookup
    refine ⟨.var position, ?_, ?_⟩
    · simp only [readName, readout, Option.map_some]
    · intro depth
      change decide ((varIdx position).val < depth) = decide (_ < depth)
      rw [variableAt_read_index readout]
  | _, _, .fvar lookup => by simp [FreeSortContext.empty] at lookup
  | context, _, .quote typed => by
    obtain ⟨process, readout, safety⟩ := sorted_process_safety typed
    refine ⟨quoteRaw process, ?_, ?_⟩
    · change (readProcess context _).map quoteRaw = some (quoteRaw process)
      rw [readout]
      rfl
    · intro depth
      change (intrinsicQuoteSafe 0 process && true) = binderSafeAt "NQuote" 0 _
      rw [Bool.and_true, safety 0]

theorem sorted_process_safety : ∀ {context : Ctx sig} {pattern : Pattern},
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern →
    ∃ term, readProcess context pattern = some term ∧
      ∀ depth, intrinsicQuoteSafe depth term = binderSafeAt "NQuote" depth pattern
  | context, _, .bvar lookup => by
    obtain ⟨position, readout⟩ := variableAt_exists_of_labels context Srt.pr _ lookup
    refine ⟨.var position, ?_, ?_⟩
    · simp only [readProcess, readout, Option.map_some]
    · intro depth
      change decide ((varIdx position).val < depth) = decide (_ < depth)
      rw [variableAt_read_index readout]
  | _, _, .fvar lookup => by simp [FreeSortContext.empty] at lookup
  | _, _, .unit => ⟨null, rfl, fun _ => rfl⟩
  | context, _, .drop typed => by
    obtain ⟨name, readout, safety⟩ := sorted_name_safety typed
    refine ⟨dropRaw name, ?_, ?_⟩
    · change (readName context _).map dropRaw = some (dropRaw name)
      rw [readout]
      rfl
    · intro depth
      change (intrinsicQuoteSafe depth name && true) = (binderSafeAt "NQuote" depth _ && true)
      rw [safety depth]
  | context, _, .output nameTyped payloadTyped => by
    obtain ⟨name, nameRead, nameSafety⟩ := sorted_name_safety nameTyped
    obtain ⟨payload, payloadRead, payloadSafety⟩ := sorted_process_safety payloadTyped
    refine ⟨outputRaw name payload, ?_, ?_⟩
    · change ((readName context _).bind fun channel =>
        (readProcess context _).map (outputRaw channel)) = some (outputRaw name payload)
      rw [nameRead, payloadRead]
      rfl
    · intro depth
      change (intrinsicQuoteSafe depth name && (intrinsicQuoteSafe depth payload && true)) =
        (binderSafeAt "NQuote" depth _ && (binderSafeAt "NQuote" depth _ && true))
      rw [nameSafety depth, payloadSafety depth]
  | context, _, .input nameTyped bodyTyped => by
    obtain ⟨name, nameRead, nameSafety⟩ := sorted_name_safety nameTyped
    obtain ⟨body, bodyRead, bodySafety⟩ :=
      sorted_process_safety (context := Srt.nm :: context) bodyTyped
    refine ⟨inputRaw name body, ?_, ?_⟩
    · change ((readName context _).bind fun channel =>
        (readProcess (Srt.nm :: context) _).map (inputRaw channel)) = some (inputRaw name body)
      rw [nameRead, bodyRead]
      rfl
    · intro depth
      change (intrinsicQuoteSafe depth name && (intrinsicQuoteSafe (depth + 1) body && true)) =
        (binderSafeAt "NQuote" depth _ && (binderSafeAt "NQuote" (depth + 1) _ && true))
      rw [nameSafety depth, bodySafety (depth + 1)]
  | _, _, .parallel typed => sorted_processes_safety typed

theorem sorted_processes_safety : ∀ {context : Ctx sig} {patterns : List Pattern},
    ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) patterns →
    ∃ term, readProcesses context patterns = some term ∧
      ∀ depth, intrinsicQuoteSafe depth term = binderSafeListAt "NQuote" depth patterns
  | _, _, .nil => ⟨null, rfl, fun _ => rfl⟩
  | context, _, .cons headTyped tailTyped => by
    obtain ⟨head, headRead, headSafety⟩ := sorted_process_safety headTyped
    obtain ⟨tail, tailRead, tailSafety⟩ := sorted_processes_safety tailTyped
    refine ⟨parallel head tail, ?_, ?_⟩
    · change ((readProcess context _).bind fun first =>
        (readProcesses context _).map (parallel first)) = some (parallel head tail)
      rw [headRead, tailRead]
      rfl
    · intro depth
      change (intrinsicQuoteSafe depth head && (intrinsicQuoteSafe depth tail && true)) =
        (binderSafeAt "NQuote" depth _ && binderSafeListAt "NQuote" depth _)
      rw [headSafety depth, tailSafety depth, Bool.and_true]
end

theorem sorted_safety {context : Ctx sig} {sort : Srt} {pattern : Pattern}
    (typed : Sorted context sort pattern) :
    ∃ term, read context sort pattern = some term ∧
      ∀ depth, intrinsicQuoteSafe depth term = binderSafeAt "NQuote" depth pattern := by
  cases sort with
  | nm => exact sorted_name_safety typed
  | pr => exact sorted_process_safety typed

theorem has_quote_safe_representative_iff {sort : Srt} (value : TermQ rhoSourceE [] sort) :
    HasQuoteSafeRepresentative value ↔ binderSafeAt "NQuote" 0 (encodeEquationClass value) = true := by
  constructor
  · rintro ⟨term, represented, safe⟩
    rw [← represented, encodeEquationClass_mk]
    apply CanonicalTyping.canonicalize_binderSafeAt
    rw [encodeTerm_quoteSafe]
    exact safe
  · intro safe
    obtain ⟨term, readout, safety⟩ := sorted_safety (encoded_class_sorted value)
    have termRead : classRead [] sort (encodeEquationClass value) = some (project term) := by
      simp only [classRead, readout, Option.map_some]
    have represented : project term = value :=
      Option.some.inj (termRead.symm.trans (read_encoded_equation_class value))
    exact ⟨term, represented, (safety 0).trans safe⟩

def quoteSafeClassTest {sort : Srt} (value : TermQ rhoSourceE [] sort) : Bool :=
  binderSafeAt "NQuote" 0 (encodeEquationClass value)

theorem quoteSafeClassTest_true_iff {sort : Srt} (value : TermQ rhoSourceE [] sort) :
    quoteSafeClassTest value = true ↔ HasQuoteSafeRepresentative value :=
  (has_quote_safe_representative_iff value).symm

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
