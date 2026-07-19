import Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution

/-!
# Scope and sort preservation for semantic COMM substitution

The operational rho substitution deliberately treats quotation as opaque and
normalizes quote/drop names.  These theorems connect that implementation to
the declaration-derived rho sorts and the quote-aware scope checker.  They
state preservation on genuine closed rho terms, excluding dangling raw de
Bruijn indices rather than weakening the calculus to accommodate them.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

private theorem drop_wellSorted_inv
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound
      (.apply "PDrop" [name])) :
    NameWellSorted rhoReflectivePresentation free bound name := by
  generalize patternEq : (.apply "PDrop" [name] : Pattern) = process at typed
  cases typed <;> simp [rhoReflectivePresentation] at patternEq
  rename_i nameTyped
  simpa [patternEq] using nameTyped

/-! ## Semantic normalization -/

mutual
  /-- Semantic name normalization preserves both the derived name sort and
  quote-aware scope safety. -/
  theorem semanticNormalizeName_preserves
      {free : FreeSortContext} (bound : List String) {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name)
      (depth : Nat)
      (safe : binderSafeAt "NQuote" depth name = true) :
      NameWellSorted rhoReflectivePresentation free bound
          (semanticNormalizeName name) ∧
        binderSafeAt "NQuote" depth (semanticNormalizeName name) = true := by
    cases typed with
    | bvar lookup =>
        exact ⟨by simpa [semanticNormalizeName] using
            (NameWellSorted.bvar lookup),
          by simpa [semanticNormalizeName] using safe⟩
    | fvar lookup =>
        exact ⟨by simpa [semanticNormalizeName] using
            (NameWellSorted.fvar lookup),
          by simpa [semanticNormalizeName] using safe⟩
    | quote processTyped =>
        rename_i process
        change
          NameWellSorted rhoReflectivePresentation free bound
              (semanticNormalizeName (.apply "NQuote" [process])) ∧
            binderSafeAt "NQuote" depth
              (semanticNormalizeName (.apply "NQuote" [process])) = true
        have processSafe : binderSafeAt "NQuote" 0 process = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        by_cases dropShape : ∃ innerName, process = .apply "PDrop" [innerName]
        · obtain ⟨innerName, rfl⟩ := dropShape
          have innerTyped := drop_wellSorted_inv processTyped
          have innerSafe : binderSafeAt "NQuote" 0 innerName = true := by
            simpa [binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation] using processSafe
          have normalized :=
            semanticNormalizeName_preserves bound innerTyped 0 innerSafe
          exact ⟨by simpa [semanticNormalizeName] using normalized.1,
            by
              simpa [semanticNormalizeName] using
                (binderSafeAt_mono "NQuote" normalized.2
                  (Nat.zero_le depth))⟩
        · have notDrop :
              ∀ innerName, process = .apply "PDrop" [innerName] → False := by
            intro innerName equality
            exact dropShape ⟨innerName, equality⟩
          have normalized :=
            semanticNormalizeProc_preserves bound processTyped 0 processSafe
          rw [semanticNormalizeName.eq_4 process notDrop]
          exact ⟨NameWellSorted.quote normalized.1,
            by simpa [binderSafeAt] using normalized.2⟩

  /-- Process form of semantic-normalization preservation. -/
  theorem semanticNormalizeProc_preserves
      {free : FreeSortContext} (bound : List String) {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      (depth : Nat)
      (safe : binderSafeAt "NQuote" depth process = true) :
      ProcWellSorted rhoReflectivePresentation free bound
          (semanticNormalizeProc process) ∧
        binderSafeAt "NQuote" depth (semanticNormalizeProc process) = true := by
    cases typed with
    | bvar lookup =>
        exact ⟨by simpa [semanticNormalizeProc] using
            (ProcWellSorted.bvar lookup),
          by simpa [semanticNormalizeProc] using safe⟩
    | fvar lookup =>
        exact ⟨by simpa [semanticNormalizeProc] using
            (ProcWellSorted.fvar lookup),
          by simpa [semanticNormalizeProc] using safe⟩
    | unit =>
        exact ⟨by simpa [semanticNormalizeProc] using
            (ProcWellSorted.unit :
              ProcWellSorted rhoReflectivePresentation free bound
                (.apply rhoReflectivePresentation.parallelUnitConstructor [])),
          by simpa [semanticNormalizeProc] using safe⟩
    | drop nameTyped =>
        rename_i name
        have nameSafe : binderSafeAt "NQuote" depth name = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation] using safe
        have normalized :=
          semanticNormalizeName_preserves bound nameTyped depth nameSafe
        exact ⟨by
            simpa [semanticNormalizeProc, rhoReflectivePresentation] using
              (ProcWellSorted.drop normalized.1),
          by
            simpa [semanticNormalizeProc, binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation] using normalized.2⟩
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have componentsSafe :
            binderSafeAt "NQuote" depth channel = true ∧
              binderSafeAt "NQuote" depth payload = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation] using safe
        have channelNormalized :=
          semanticNormalizeName_preserves bound channelTyped depth componentsSafe.1
        have payloadNormalized :=
          semanticNormalizeProc_preserves bound payloadTyped depth componentsSafe.2
        exact ⟨by
            simpa [semanticNormalizeProc, rhoReflectivePresentation] using
              (ProcWellSorted.output channelNormalized.1 payloadNormalized.1),
          by
            simpa [semanticNormalizeProc, binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation] using
              And.intro channelNormalized.2 payloadNormalized.2⟩
    | input channelTyped bodyTyped =>
        rename_i channel body
        have componentsSafe :
            binderSafeAt "NQuote" depth channel = true ∧
              binderSafeAt "NQuote" (depth + 1) body = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation] using safe
        have channelNormalized :=
          semanticNormalizeName_preserves bound channelTyped depth componentsSafe.1
        have bodyNormalized :=
          semanticNormalizeProc_preserves
            (rhoReflectivePresentation.nameSort :: bound) bodyTyped
            (depth + 1) componentsSafe.2
        exact ⟨by
            simpa [semanticNormalizeProc, rhoReflectivePresentation] using
              (ProcWellSorted.input channelNormalized.1 bodyNormalized.1),
          by
            simpa [semanticNormalizeProc, binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation] using
              And.intro channelNormalized.2 bodyNormalized.2⟩
    | parallel processesTyped =>
        rename_i processes
        have processesSafe :
            binderSafeListAt "NQuote" depth processes = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        have normalized :=
          semanticNormalizeProcList_preserves bound processesTyped depth processesSafe
        exact ⟨by
            simpa [semanticNormalizeProc, rhoReflectivePresentation] using
              (ProcWellSorted.parallel normalized.1),
          by
            simpa [semanticNormalizeProc, binderSafeAt,
              rhoReflectivePresentation] using normalized.2⟩

  /-- List form of semantic-normalization preservation. -/
  theorem semanticNormalizeProcList_preserves
      {free : FreeSortContext} (bound : List String) {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      (depth : Nat)
      (safe : binderSafeListAt "NQuote" depth processes = true) :
      ProcListWellSorted rhoReflectivePresentation free bound
          (semanticNormalizeProcList processes) ∧
        binderSafeListAt "NQuote" depth
          (semanticNormalizeProcList processes) = true := by
    cases typed with
    | nil =>
        exact ⟨ProcListWellSorted.nil,
          by simp [semanticNormalizeProcList, binderSafeListAt]⟩
    | cons processTyped processesTyped =>
        rename_i process processes
        have componentsSafe :
            binderSafeAt "NQuote" depth process = true ∧
              binderSafeListAt "NQuote" depth processes = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        have processNormalized :=
          semanticNormalizeProc_preserves bound processTyped depth componentsSafe.1
        have processesNormalized :=
          semanticNormalizeProcList_preserves bound processesTyped depth componentsSafe.2
        exact ⟨by
            simpa [semanticNormalizeProcList] using
              (ProcListWellSorted.cons processNormalized.1 processesNormalized.1),
          by
            simpa [semanticNormalizeProcList, binderSafeListAt,
              Bool.and_eq_true] using
              And.intro processNormalized.2 processesNormalized.2⟩
end

/-! ## Removing one closed communication binder -/

/-- Substituting a closed name for the outermost communication binder
preserves the declaration-derived name sort and quote-aware scope.  The
`index` parameter counts local input binders between the current position and
the communication binder. -/
theorem semanticSubstName_preserves
    {free : FreeSortContext} {index : Nat} {name replacement : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free
      (List.replicate (index + 1) rhoReflectivePresentation.nameSort) name)
    (safe : binderSafeAt "NQuote" (index + 1) name = true)
    (replacementTyped :
      NameWellSorted rhoReflectivePresentation free [] replacement)
    (replacementSafe : binderSafeAt "NQuote" 0 replacement = true) :
    NameWellSorted rhoReflectivePresentation free
        (List.replicate index rhoReflectivePresentation.nameSort)
        (semanticSubstName index replacement name) ∧
      binderSafeAt "NQuote" index
        (semanticSubstName index replacement name) = true := by
  have normalization := semanticNormalizeName_preserves
    (List.replicate (index + 1) rhoReflectivePresentation.nameSort)
    typed (index + 1) safe
  have normalizedTyped := normalization.1
  have normalizedSafe := normalization.2
  unfold semanticSubstName semanticSubstNameMark
  generalize normalizedEq : semanticNormalizeName name = normalizedName at normalizedTyped normalizedSafe ⊢
  cases normalizedTyped with
  | bvar lookup =>
      rename_i boundIndex
      have within : boundIndex < index + 1 := by
        simpa [binderSafeAt] using normalizedSafe
      by_cases hit : boundIndex = index
      · subst boundIndex
        exact ⟨by
            simpa using replacementTyped.weakenBoundRight
              (List.replicate index rhoReflectivePresentation.nameSort),
          by
            simpa using binderSafeAt_mono "NQuote" replacementSafe
              (Nat.zero_le index)⟩
      · have below : boundIndex < index := by omega
        simp only [beq_iff_eq, hit, ↓reduceIte]
        exact ⟨by
            apply NameWellSorted.bvar
            simp [below],
          by simp [binderSafeAt, below]⟩
  | fvar lookup =>
      exact ⟨by simpa using (NameWellSorted.fvar lookup),
        by simp [binderSafeAt]⟩
  | quote processTyped =>
      rename_i process
      have processSafe : binderSafeAt "NQuote" 0 process = true := by
        simpa [binderSafeAt, rhoReflectivePresentation] using normalizedSafe
      have processClosed :
          ProcWellSorted rhoReflectivePresentation free [] process := by
        simpa using
          (procWellSorted_restrictToBinderPrefix
            (depth := 0)
            (tail := List.replicate (index + 1)
              rhoReflectivePresentation.nameSort)
            processTyped processSafe)
      exact ⟨by
          simpa [rhoReflectivePresentation] using
            (NameWellSorted.quote
              (processClosed.weakenBoundRight
                (List.replicate index rhoReflectivePresentation.nameSort))),
        by simpa [binderSafeAt, rhoReflectivePresentation] using processSafe⟩

mutual
  /-- Process substitution removes one communication-name binder while
  preserving the process sort and quote-aware scope. -/
  theorem semanticSubstProc_preserves
      {free : FreeSortContext} {index : Nat}
      {process replacement : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free
        (List.replicate (index + 1) rhoReflectivePresentation.nameSort)
        process)
      (safe : binderSafeAt "NQuote" (index + 1) process = true)
      (replacementTyped :
        NameWellSorted rhoReflectivePresentation free [] replacement)
      (replacementSafe : binderSafeAt "NQuote" 0 replacement = true) :
      ProcWellSorted rhoReflectivePresentation free
          (List.replicate index rhoReflectivePresentation.nameSort)
          (semanticSubstProc index replacement process) ∧
        binderSafeAt "NQuote" index
          (semanticSubstProc index replacement process) = true := by
    cases typed with
    | bvar lookup =>
        rename_i boundIndex
        have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
        have nameLookup :
            (List.replicate (index + 1)
              rhoReflectivePresentation.nameSort)[boundIndex]? =
                some rhoReflectivePresentation.nameSort := by
          apply List.getElem?_eq_some_iff.mpr
          exact ⟨inBounds, by simp⟩
        rw [nameLookup] at lookup
        simp [rhoReflectivePresentation] at lookup
    | fvar lookup =>
        exact ⟨by simpa [semanticSubstProc] using
            (ProcWellSorted.fvar lookup),
          by simp [semanticSubstProc, binderSafeAt]⟩
    | unit =>
        refine ⟨by simpa [semanticSubstProc] using
            (ProcWellSorted.unit :
              ProcWellSorted rhoReflectivePresentation free
                (List.replicate index rhoReflectivePresentation.nameSort)
                (.apply rhoReflectivePresentation.parallelUnitConstructor [])), ?_⟩
        change binderSafeListAt "NQuote" index [] = true
        rfl
    | drop nameTyped =>
        rename_i name
        have nameSafe : binderSafeAt "NQuote" (index + 1) name = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation] using safe
        have substituted := semanticSubstName_preserves
          nameTyped nameSafe replacementTyped replacementSafe
        generalize markedEq :
          semanticSubstNameMark index replacement name = marked
        obtain ⟨substitutedName, matched⟩ := marked
        have substitutedTyped :
            NameWellSorted rhoReflectivePresentation free
              (List.replicate index rhoReflectivePresentation.nameSort)
              substitutedName := by
          simpa [semanticSubstName, markedEq] using substituted.1
        have substitutedSafe :
            binderSafeAt "NQuote" index substitutedName = true := by
          simpa [semanticSubstName, markedEq] using substituted.2
        cases substitutedTyped with
        | bvar substitutedLookup =>
            rename_i substitutedIndex
            have substitutedBound : substitutedIndex < index := by
              simpa [binderSafeAt] using substitutedSafe
            cases matched <;>
              exact ⟨by
                  simpa [semanticSubstProc, markedEq,
                    rhoReflectivePresentation] using
                    (ProcWellSorted.drop
                      (NameWellSorted.bvar substitutedLookup)),
                by
                  simp [semanticSubstProc, markedEq, binderSafeAt,
                    binderSafeListAt, rhoReflectivePresentation,
                    substitutedBound]⟩
        | fvar substitutedLookup =>
            cases matched <;>
              exact ⟨by
                  simpa [semanticSubstProc, markedEq,
                    rhoReflectivePresentation] using
                    (ProcWellSorted.drop
                      (NameWellSorted.fvar substitutedLookup)),
                by
                  simp [semanticSubstProc, markedEq, binderSafeAt,
                    binderSafeListAt, rhoReflectivePresentation]⟩
        | quote quotedTyped =>
            rename_i quotedProcess
            have quotedSafe :
                binderSafeAt "NQuote" 0 quotedProcess = true := by
              simpa [binderSafeAt, rhoReflectivePresentation] using
                substitutedSafe
            cases matched with
            | false =>
                exact ⟨by
                    simpa [semanticSubstProc, markedEq,
                      rhoReflectivePresentation] using
                      (ProcWellSorted.drop
                        (NameWellSorted.quote quotedTyped)),
                  by
                    simpa [semanticSubstProc, markedEq, binderSafeAt,
                      binderSafeListAt, rhoReflectivePresentation] using
                      substitutedSafe⟩
            | true =>
                exact ⟨by
                    simpa [semanticSubstProc, markedEq,
                      rhoReflectivePresentation] using quotedTyped,
                  by
                    simpa [semanticSubstProc, markedEq,
                      rhoReflectivePresentation] using
                      (binderSafeAt_mono "NQuote" quotedSafe
                        (Nat.zero_le index))⟩
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) channel = true ∧
              binderSafeAt "NQuote" (index + 1) payload = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation] using safe
        have channelSubstituted := semanticSubstName_preserves
          channelTyped componentsSafe.1 replacementTyped replacementSafe
        have payloadSubstituted := semanticSubstProc_preserves
          payloadTyped componentsSafe.2 replacementTyped replacementSafe
        exact ⟨by
            simpa [semanticSubstProc, rhoReflectivePresentation] using
              (ProcWellSorted.output channelSubstituted.1
                payloadSubstituted.1),
          by
            simpa [semanticSubstProc, binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation] using
              And.intro channelSubstituted.2 payloadSubstituted.2⟩
    | input channelTyped bodyTyped =>
        rename_i channel body
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) channel = true ∧
              binderSafeAt "NQuote" (index + 2) body = true := by
          simpa [binderSafeAt, binderSafeListAt,
            rhoReflectivePresentation, Nat.add_assoc] using safe
        have bodyTyped' :
            ProcWellSorted rhoReflectivePresentation free
              (List.replicate (index + 2)
                rhoReflectivePresentation.nameSort) body := by
          simpa [List.replicate_succ, Nat.add_assoc] using bodyTyped
        have channelSubstituted := semanticSubstName_preserves
          channelTyped componentsSafe.1 replacementTyped replacementSafe
        have bodySubstituted := semanticSubstProc_preserves
          bodyTyped' componentsSafe.2 replacementTyped replacementSafe
        exact ⟨by
            simpa [semanticSubstProc, List.replicate_succ,
              rhoReflectivePresentation] using
              (ProcWellSorted.input channelSubstituted.1 bodySubstituted.1),
          by
            simpa [semanticSubstProc, binderSafeAt, binderSafeListAt,
              rhoReflectivePresentation, Nat.add_assoc] using
              And.intro channelSubstituted.2 bodySubstituted.2⟩
    | parallel processesTyped =>
        rename_i processes
        have processesSafe :
            binderSafeListAt "NQuote" (index + 1) processes = true := by
          simpa [binderSafeAt, rhoReflectivePresentation] using safe
        have processesSubstituted := semanticSubstProcList_preserves
          processesTyped processesSafe replacementTyped replacementSafe
        exact ⟨by
            simpa [semanticSubstProc, rhoReflectivePresentation] using
              (ProcWellSorted.parallel processesSubstituted.1),
          by
            simpa [semanticSubstProc, binderSafeAt,
              rhoReflectivePresentation] using processesSubstituted.2⟩

  /-- List form of one-binder semantic substitution. -/
  theorem semanticSubstProcList_preserves
      {free : FreeSortContext} {index : Nat}
      {processes : List Pattern} {replacement : Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free
        (List.replicate (index + 1) rhoReflectivePresentation.nameSort)
        processes)
      (safe : binderSafeListAt "NQuote" (index + 1) processes = true)
      (replacementTyped :
        NameWellSorted rhoReflectivePresentation free [] replacement)
      (replacementSafe : binderSafeAt "NQuote" 0 replacement = true) :
      ProcListWellSorted rhoReflectivePresentation free
          (List.replicate index rhoReflectivePresentation.nameSort)
          (semanticSubstProcList index replacement processes) ∧
        binderSafeListAt "NQuote" index
          (semanticSubstProcList index replacement processes) = true := by
    cases typed with
    | nil =>
        exact ⟨ProcListWellSorted.nil,
          by simp [semanticSubstProcList, binderSafeListAt]⟩
    | cons processTyped processesTyped =>
        rename_i process processes
        have componentsSafe :
            binderSafeAt "NQuote" (index + 1) process = true ∧
              binderSafeListAt "NQuote" (index + 1) processes = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        have processSubstituted := semanticSubstProc_preserves
          processTyped componentsSafe.1 replacementTyped replacementSafe
        have processesSubstituted := semanticSubstProcList_preserves
          processesTyped componentsSafe.2 replacementTyped replacementSafe
        exact ⟨by
            simpa [semanticSubstProcList] using
              (ProcListWellSorted.cons processSubstituted.1
                processesSubstituted.1),
          by
            simpa [semanticSubstProcList, binderSafeListAt,
              Bool.and_eq_true] using
              And.intro processSubstituted.2 processesSubstituted.2⟩
end

/-- The paper COMM contractum of a closed, scope-safe body and payload is
again a closed, scope-safe process. -/
theorem semanticCommSubst_preserves
    {free : FreeSortContext} {body payload : Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      [rhoReflectivePresentation.nameSort] body)
    (bodySafe : binderSafeAt "NQuote" 1 body = true)
    (payloadTyped :
      ProcWellSorted rhoReflectivePresentation free [] payload)
    (payloadSafe : binderSafeAt "NQuote" 0 payload = true) :
    ProcWellSorted rhoReflectivePresentation free []
        (semanticCommSubst body payload) ∧
      binderSafeAt "NQuote" 0 (semanticCommSubst body payload) = true := by
  have payloadNormalized :=
    semanticNormalizeProc_preserves [] payloadTyped 0 payloadSafe
  let replacement : Pattern :=
    .apply "NQuote" [semanticNormalizeProc payload]
  have replacementTyped :
      NameWellSorted rhoReflectivePresentation free [] replacement := by
    exact NameWellSorted.quote payloadNormalized.1
  have replacementSafe : binderSafeAt "NQuote" 0 replacement = true := by
    simpa [replacement, binderSafeAt] using payloadNormalized.2
  have bodyTyped' :
      ProcWellSorted rhoReflectivePresentation free
        (List.replicate (0 + 1) rhoReflectivePresentation.nameSort) body := by
    simpa using bodyTyped
  have preserved := semanticSubstProc_preserves
    bodyTyped' bodySafe replacementTyped replacementSafe
  simpa [semanticCommSubst, replacement] using preserved

/-! ## Positive and negative controls -/

/-- Positive: the canonical bound drop and nil payload meet the exact COMM
preservation hypotheses. -/
theorem boundDrop_nil_semanticCommSubst_closed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
        (semanticCommSubst (.apply "PDrop" [.bvar 0])
          (.apply "PZero" [])) ∧
      binderSafeAt "NQuote" 0
        (semanticCommSubst (.apply "PDrop" [.bvar 0])
          (.apply "PZero" [])) = true := by
  apply semanticCommSubst_preserves
  · exact .drop (.bvar (by decide))
  · decide +kernel
  · exact .unit
  · decide +kernel

/-- Negative: an input-bound variable beneath quotation is rejected before
COMM, because quotation seals its body from the surrounding binder. -/
theorem quotedBoundDrop_not_binderSafe :
    binderSafeAt "NQuote" 1
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution
