import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-!
# Semantic substitution outside the local binder scope

Substitution for a binder beyond a term's quote-aware scope cannot replace a
name or activate a drop. It performs only the semantic normalization already
specified by COMM. The statement applies to the declaration-derived rho
grammar and arbitrary free-name contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSubstitutionInert

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-- An out-of-scope substitution records that no name was replaced. -/
theorem nameMark_above_scope
    {free : FreeSortContext} {bound : List String}
    {name replacement : Pattern} {depth index : Nat}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (safe : binderSafeAt "NQuote" depth name = true)
    (above : depth ≤ index) :
    semanticSubstNameMark index replacement name =
      (semanticNormalizeName name, false) := by
  have normalizedSafe :=
    (semanticNormalizeName_preserves bound typed depth safe).2
  unfold semanticSubstNameMark
  generalize normalizedEq : semanticNormalizeName name = normalized at normalizedSafe ⊢
  cases normalized <;> try rfl
  rename_i localIndex
  have within : localIndex < depth := by
    simpa [binderSafeAt] using normalizedSafe
  have different : localIndex ≠ index := by omega
  simp [different]

/-- Name substitution beyond the scope only normalizes the name. -/
theorem name_above_scope
    {free : FreeSortContext} {bound : List String}
    {name replacement : Pattern} {depth index : Nat}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (safe : binderSafeAt "NQuote" depth name = true)
    (above : depth ≤ index) :
    semanticSubstName index replacement name = semanticNormalizeName name := by
  unfold semanticSubstName
  rw [nameMark_above_scope typed safe above]

mutual
  /-- A process with no access to the substituted binder cannot activate a
  drop or change a channel; only semantic normalization remains. -/
  theorem proc_above_scope
      {free : FreeSortContext} {bound : List String}
      {process replacement : Pattern} {depth index : Nat}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      (safe : binderSafeAt "NQuote" depth process = true)
      (above : depth ≤ index) :
      semanticSubstProc index replacement process = semanticNormalizeProc process := by
    cases typed with
    | bvar lookup =>
        rename_i localIndex
        have within : localIndex < depth := by simpa [binderSafeAt] using safe
        have different : localIndex ≠ index := by omega
        simp [semanticSubstProc, semanticNormalizeProc, different]
    | fvar lookup => rfl
    | unit => rfl
    | drop nameTyped =>
        rename_i name
        have nameSafe : binderSafeAt "NQuote" depth name = true := by
          simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using safe
        change semanticSubstProc index replacement (.apply "PDrop" [name]) = _
        rw [semanticSubstProc.eq_4,
          nameMark_above_scope nameTyped nameSafe above]
        simp only [rhoReflectivePresentation, semanticNormalizeProc.eq_5]
        split <;> simp_all
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have components : binderSafeAt "NQuote" depth channel = true ∧
            binderSafeAt "NQuote" depth payload = true := by
          simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using safe
        change semanticSubstProc index replacement (.apply "POutput" [channel, payload]) = _
        rw [semanticSubstProc.eq_5,
          name_above_scope channelTyped components.1 above,
          proc_above_scope payloadTyped components.2 above]
        rfl
    | input channelTyped bodyTyped =>
        rename_i channel body
        have components : binderSafeAt "NQuote" depth channel = true ∧
            binderSafeAt "NQuote" (depth + 1) body = true := by
          simpa [binderSafeAt, binderSafeListAt, rhoReflectivePresentation] using safe
        change semanticSubstProc index replacement
          (.apply "PInput" [channel, .lambda none body]) = _
        rw [semanticSubstProc.eq_6,
          name_above_scope channelTyped components.1 above,
          proc_above_scope bodyTyped components.2 (Nat.add_le_add_right above 1)]
        rfl
    | parallel processesTyped =>
        rename_i processes
        have processesSafe : binderSafeListAt "NQuote" depth processes = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        change semanticSubstProc index replacement (.collection .hashBag processes none) = _
        rw [semanticSubstProc.eq_10,
          list_above_scope processesTyped processesSafe above]
        rfl

  /-- List form of out-of-scope substitution. -/
  theorem list_above_scope
      {free : FreeSortContext} {bound : List String}
      {processes : List Pattern} {replacement : Pattern} {depth index : Nat}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      (safe : binderSafeListAt "NQuote" depth processes = true)
      (above : depth ≤ index) :
      semanticSubstProcList index replacement processes =
        semanticNormalizeProcList processes := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
        rename_i process processes
        have components : binderSafeAt "NQuote" depth process = true ∧
            binderSafeListAt "NQuote" depth processes = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        simp only [semanticSubstProcList, semanticNormalizeProcList]
        rw [proc_above_scope processTyped components.1 above,
          list_above_scope processesTyped components.2 above]
end

/-- Closed, normalized names are inert under every surrounding COMM. -/
theorem closed_name_inert
    {free : FreeSortContext} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free [] name)
    (safe : binderSafeAt "NQuote" 0 name = true)
    (normalized : semanticNormalizeName name = name)
    (index : Nat) (replacement : Pattern) :
    semanticSubstName index replacement name = name := by
  rw [name_above_scope typed safe (Nat.zero_le index), normalized]

/-- A normalized handler with one request binder is unaffected by substitution
for any outer code binder. -/
theorem one_binder_inert
    {free : FreeSortContext} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free ["Name"] process)
    (safe : binderSafeAt "NQuote" 1 process = true)
    (normalized : semanticNormalizeProc process = process)
    {index : Nat} (above : 1 ≤ index) (replacement : Pattern) :
    semanticSubstProc index replacement process = process := by
  rw [proc_above_scope typed safe above, normalized]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSubstitutionInert
