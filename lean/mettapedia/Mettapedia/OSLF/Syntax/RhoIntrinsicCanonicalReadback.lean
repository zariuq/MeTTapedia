import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackConstructors

/-!
# Canonical readback for the complete intrinsic rho carrier

The existing independently defined sorted-pattern judgments supply induction
on constructor arguments and input bodies. Canonicalization preserves their
intrinsic readback classes. Together with the whole encoding roundtrip, this
earns equality reflection of the canonical encoding on every source equation
class. The intrinsic carrier still differs from the separately sealed authored
carrier; this theorem introduces no quotation-scope restriction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

mutual
theorem name_canonical_readout {free : FreeSortContext} :
    ∀ {bound : List String} {pattern : Pattern},
      NameWellSorted rhoReflectivePresentation free bound pattern →
      ∀ context : Ctx sig,
        readNameClass context (canonicalize pattern) = readNameClass context pattern
  | _, _, .bvar _, _ => rfl
  | _, _, .fvar _, _ => rfl
  | _, _, .quote typed, context => by
    change readNameClass context (normalizeQuote (canonicalize _)) =
      readNameClass context (.apply "NQuote" [_])
    rw [readNameClass_normalizeQuote, readNameClass_quote,
      process_canonical_readout typed context]

theorem process_canonical_readout {free : FreeSortContext} :
    ∀ {bound : List String} {pattern : Pattern},
      ProcWellSorted rhoReflectivePresentation free bound pattern →
      ∀ context : Ctx sig,
        readProcessClass context (canonicalize pattern) = readProcessClass context pattern
  | _, _, .bvar _, _ => rfl
  | _, _, .fvar _, _ => rfl
  | _, _, .unit, _ => rfl
  | _, _, .drop typed, context => by
    change readProcessClass context (canonicalize (.apply "PDrop" [_])) =
      readProcessClass context (.apply "PDrop" [_])
    rw [canonicalize_apply_general "PDrop" [_] (by simp)]
    change readProcessClass context (.apply "PDrop" [canonicalize _]) =
      readProcessClass context (.apply "PDrop" [_])
    rw [readProcessClass_drop, readProcessClass_drop, name_canonical_readout typed context]
  | _, _, .output nameTyped payloadTyped, context => by
    change readProcessClass context (canonicalize (.apply "POutput" [_, _])) =
      readProcessClass context (.apply "POutput" [_, _])
    rw [canonicalize_apply_general "POutput" [_, _] (by simp)]
    change readProcessClass context (.apply "POutput" [canonicalize _, canonicalize _]) =
      readProcessClass context (.apply "POutput" [_, _])
    rw [readProcessClass_output, readProcessClass_output,
      name_canonical_readout nameTyped context, process_canonical_readout payloadTyped context]
  | _, _, .input nameTyped bodyTyped, context => by
    change readProcessClass context (canonicalize (.apply "PInput" [_, .lambda none _])) =
      readProcessClass context (.apply "PInput" [_, .lambda none _])
    rw [canonicalize_apply_general "PInput" [_, _] (by simp)]
    change readProcessClass context
        (.apply "PInput" [canonicalize _, .lambda none (canonicalize _)]) =
      readProcessClass context (.apply "PInput" [_, .lambda none _])
    rw [readProcessClass_input, readProcessClass_input, name_canonical_readout nameTyped context,
      process_canonical_readout bodyTyped (Srt.nm :: context)]
  | _, _, .parallel typed, context => by
    change readProcessClass context
        (collapseBag (normalizeBagElements (canonicalizeList _))) =
      readProcessesClass context _
    rw [readProcessClass_normalizedBag, processes_canonical_readout typed context]

theorem processes_canonical_readout {free : FreeSortContext} :
    ∀ {bound : List String} {patterns : List Pattern},
      ProcListWellSorted rhoReflectivePresentation free bound patterns →
      ∀ context : Ctx sig,
        readProcessesClass context (canonicalizeList patterns) = readProcessesClass context patterns
  | _, _, .nil, _ => rfl
  | _, _, .cons headTyped tailTyped, context => by
    change readProcessesClass context (canonicalize _ :: canonicalizeList _) =
      readProcessesClass context (_ :: _)
    rw [readProcessesClass_cons, readProcessesClass_cons,
      process_canonical_readout headTyped context, processes_canonical_readout tailTyped context]
end

def classRead (context : Ctx sig) (sort : Srt) (pattern : Pattern) :
    Option (TermQ rhoSourceE context sort) := (read context sort pattern).map project

theorem canonical_encoded_class {context : Ctx sig} {sort : Srt}
    (term : Term sig context sort) :
    classRead context sort (canonicalize (encodeTerm term)) = some (project term) := by
  obtain ⟨decoded, readout, sameClass⟩ := read_encoded_class term
  have original : classRead context sort (encodeTerm term) = some (project term) := by
    simp only [classRead, readout, Option.map_some, sameClass]
  cases sort with
  | nm =>
    change readNameClass context (canonicalize (encodeTerm term)) = some (project term)
    rw [name_canonical_readout (encodedTerm_typed term) context]
    exact original
  | pr =>
    change readProcessClass context (canonicalize (encodeTerm term)) = some (project term)
    rw [process_canonical_readout (encodedTerm_typed term) context]
    exact original

theorem canonical_encoding_injective (context : Ctx sig) (sort : Srt) :
    Function.Injective (encodeEquationClass (Γ := context) (s := sort)) := by
  intro first second
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      intro equal
      change canonicalize (encodeTerm first) = canonicalize (encodeTerm second) at equal
      have sameReadout := congrArg (classRead context sort) equal
      rw [canonical_encoded_class, canonical_encoded_class] at sameReadout
      exact Option.some.inj sameReadout

theorem canonical_encoding_equality_iff {context : Ctx sig} {sort : Srt}
    (first second : TermQ rhoSourceE context sort) :
    encodeEquationClass first = encodeEquationClass second ↔ first = second :=
  ⟨fun equal => canonical_encoding_injective context sort equal, congrArg encodeEquationClass⟩

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
