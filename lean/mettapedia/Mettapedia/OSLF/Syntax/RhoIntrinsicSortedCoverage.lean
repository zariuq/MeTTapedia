import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Coverage of independently authored sorted rho patterns

Every sorted pattern with the intrinsic context labels and no free pattern
variables has an actual intrinsic readback. Encoding that independently read
term is structurally congruent to the supplied pattern. Parallel collections
are covered at every length; input bodies retain their name binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

theorem variableAt_exists_of_labels : ∀ (context : Ctx sig) (sort : Srt) (index : Nat),
    (contextLabels context)[index]? = some (sortLabel sort) →
    ∃ position, variableAt context sort index = some position
  | [], _, _, lookup => by simp [contextLabels] at lookup
  | head :: tail, sort, 0, lookup => by
    have same : head = sort := by
      cases head <;> cases sort <;> simp_all [contextLabels, sortLabel]
    subst head
    exact ⟨Var.zero, by simp [variableAt]⟩
  | head :: tail, sort, index + 1, lookup => by
    have nextLookup : (contextLabels tail)[index]? = some (sortLabel sort) := lookup
    obtain ⟨position, readout⟩ := variableAt_exists_of_labels tail sort index nextLookup
    exact ⟨position.succ, by simp [variableAt, readout]⟩

theorem variableAt_read_index : ∀ {context : Ctx sig} {sort : Srt} {index : Nat}
    {position : Var context sort},
    variableAt context sort index = some position → (varIdx position).val = index
  | [], _, _, position, _ => nomatch position
  | head :: tail, sort, 0, position, readout => by
    simp only [variableAt] at readout
    split at readout
    · next same =>
      subst head
      have samePosition : position = Var.zero := (Option.some.inj readout).symm
      subst position
      rfl
    · cases readout
  | _ :: tail, sort, index + 1, position, readout => by
    simp only [variableAt, Option.map_eq_some_iff] at readout
    obtain ⟨previous, previousRead, rfl⟩ := readout
    simp only [varIdx, Fin.val_succ, variableAt_read_index previousRead]

mutual
theorem sorted_name_coverage : ∀ {context : Ctx sig} {pattern : Pattern},
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern →
    ∃ term, readName context pattern = some term ∧ StructuralCongruence (encodeTerm term) pattern
  | context, _, .bvar lookup => by
    obtain ⟨position, readout⟩ := variableAt_exists_of_labels context Srt.nm _ lookup
    refine ⟨.var position, ?_, ?_⟩
    · simp only [readName, readout, Option.map_some]
    · change StructuralCongruence (.bvar (varIdx position).val) (.bvar _)
      rw [variableAt_read_index readout]
      exact .refl _
  | _, _, .fvar lookup => by simp [FreeSortContext.empty] at lookup
  | context, _, .quote typed => by
    obtain ⟨process, readout, congruent⟩ := sorted_process_coverage typed
    refine ⟨quoteRaw process, ?_, ?_⟩
    · change (readProcess context _).map quoteRaw = some (quoteRaw process)
      rw [readout]
      rfl
    · exact applyCongruence_of_forall₂ "NQuote" (.cons congruent .nil)

theorem sorted_process_coverage : ∀ {context : Ctx sig} {pattern : Pattern},
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) pattern →
    ∃ term, readProcess context pattern = some term ∧ StructuralCongruence (encodeTerm term) pattern
  | context, _, .bvar lookup => by
    obtain ⟨position, readout⟩ := variableAt_exists_of_labels context Srt.pr _ lookup
    refine ⟨.var position, ?_, ?_⟩
    · simp only [readProcess, readout, Option.map_some]
    · change StructuralCongruence (.bvar (varIdx position).val) (.bvar _)
      rw [variableAt_read_index readout]
      exact .refl _
  | _, _, .fvar lookup => by simp [FreeSortContext.empty] at lookup
  | _, _, .unit => ⟨null, rfl, .refl _⟩
  | context, _, .drop typed => by
    obtain ⟨name, readout, congruent⟩ := sorted_name_coverage typed
    refine ⟨dropRaw name, ?_, ?_⟩
    · change (readName context _).map dropRaw = some (dropRaw name)
      rw [readout]
      rfl
    · exact applyCongruence_of_forall₂ "PDrop" (.cons congruent .nil)
  | context, _, .output nameTyped payloadTyped => by
    obtain ⟨name, nameRead, nameCongruence⟩ := sorted_name_coverage nameTyped
    obtain ⟨payload, payloadRead, payloadCongruence⟩ := sorted_process_coverage payloadTyped
    refine ⟨outputRaw name payload, ?_, ?_⟩
    · change ((readName context _).bind fun channel =>
        (readProcess context _).map (outputRaw channel)) = some (outputRaw name payload)
      rw [nameRead, payloadRead]
      rfl
    · exact applyCongruence_of_forall₂ "POutput"
        (.cons nameCongruence (.cons payloadCongruence .nil))
  | context, _, .input nameTyped bodyTyped => by
    obtain ⟨name, nameRead, nameCongruence⟩ := sorted_name_coverage nameTyped
    obtain ⟨body, bodyRead, bodyCongruence⟩ :=
      sorted_process_coverage (context := Srt.nm :: context) bodyTyped
    refine ⟨inputRaw name body, ?_, ?_⟩
    · change ((readName context _).bind fun channel =>
        (readProcess (Srt.nm :: context) _).map (inputRaw channel)) = some (inputRaw name body)
      rw [nameRead, bodyRead]
      rfl
    · exact applyCongruence_of_forall₂ "PInput"
        (.cons nameCongruence (.cons (.lambda_cong none _ _ bodyCongruence) .nil))
  | _, _, .parallel typed => sorted_processes_coverage typed

theorem sorted_processes_coverage : ∀ {context : Ctx sig} {patterns : List Pattern},
    ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels context) patterns →
    ∃ term, readProcesses context patterns = some term ∧
      StructuralCongruence (encodeTerm term) (.collection .hashBag patterns none)
  | _, _, .nil => ⟨null, rfl, .symm _ _ .par_empty⟩
  | context, _, .cons headTyped tailTyped => by
    obtain ⟨head, headRead, headCongruence⟩ := sorted_process_coverage headTyped
    obtain ⟨tail, tailRead, tailCongruence⟩ := sorted_processes_coverage tailTyped
    refine ⟨parallel head tail, ?_, ?_⟩
    · change ((readProcess context _).bind fun first =>
        (readProcesses context _).map (parallel first)) = some (parallel head tail)
      rw [headRead, tailRead]
      rfl
    · exact .trans _ _ _
        (collectionCongruence_of_forall₂ .hashBag none
          (.cons headCongruence (.cons tailCongruence .nil)))
        (.par_flatten [_] _)
end

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
