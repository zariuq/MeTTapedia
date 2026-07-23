import Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-!
# Canonicalization preserves rho sorts

The rho canonicalizer is compiled from the authored reflective presentation.
This file proves that it maps presentation-derived names to names and
presentation-derived processes to processes.  The parallel case is the only
substantial one: flattening, unit removal, sorting, and wrapper collapse all
preserve the process-list judgment.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-! ## Listwise closure lemmas -/

/-- The derived list judgment is equivalent to pointwise membership in the
derived process judgment. -/
theorem procListWellSorted_iff_forall_mem
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern} :
    ProcListWellSorted presentation free bound processes ↔
      ∀ process ∈ processes, ProcWellSorted presentation free bound process := by
  constructor
  · intro typed process membership
    induction processes generalizing process with
    | nil => simp at membership
    | cons head processes inductionHypothesis =>
        cases typed
        rename_i headTyped tailTyped
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · exact headTyped
        · exact inductionHypothesis tailTyped process membership
  · intro pointwise
    induction processes with
    | nil => exact .nil
    | cons process processes inductionHypothesis =>
        exact .cons (pointwise process (by simp))
          (inductionHypothesis fun member membership =>
            pointwise member (by simp [membership]))

/-- Splicing a well-sorted parallel component yields a well-sorted list. -/
theorem bagSplice_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process)
    (parallelCollection : presentation.parallelCollection = .hashBag) :
    ProcListWellSorted presentation free bound (bagSplice process) := by
  cases typed with
  | bvar lookup =>
      exact .cons (.bvar lookup) .nil
  | fvar lookup =>
      exact .cons (.fvar lookup) .nil
  | unit =>
      exact .cons .unit .nil
  | drop nameTyped =>
      exact .cons (.drop nameTyped) .nil
  | output channelTyped payloadTyped =>
      exact .cons (.output channelTyped payloadTyped) .nil
  | input channelTyped bodyTyped =>
      exact .cons (.input channelTyped bodyTyped) .nil
  | parallel processesTyped =>
      simpa [bagSplice, parallelCollection] using processesTyped

/-- Flattening well-sorted parallel components preserves list sorting. -/
theorem flatMap_bagSplice_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes)
    (parallelCollection : presentation.parallelCollection = .hashBag) :
    ProcListWellSorted presentation free bound
      (processes.flatMap bagSplice) := by
  rw [procListWellSorted_iff_forall_mem] at typed ⊢
  intro process membership
  rw [List.mem_flatMap] at membership
  obtain ⟨source, sourceMember, processMember⟩ := membership
  have sourceTyped := typed source sourceMember
  exact (procListWellSorted_iff_forall_mem.mp
    (bagSplice_procListWellSorted sourceTyped parallelCollection))
      process processMember

/-- Filtering a well-sorted process list preserves its judgment. -/
theorem filter_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern} (keep : Pattern → Bool)
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcListWellSorted presentation free bound (processes.filter keep) := by
  rw [procListWellSorted_iff_forall_mem] at typed ⊢
  intro process membership
  exact typed process (List.mem_of_mem_filter membership)

/-- Sorting a well-sorted process list by the canonical structural order
preserves its judgment. -/
theorem sortPatterns_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcListWellSorted presentation free bound (sortPatterns processes) := by
  rw [procListWellSorted_iff_forall_mem] at typed ⊢
  intro process membership
  exact typed process (sortPatterns_mem_iff.mp membership)

/-- Parallel normalization preserves the derived process-list judgment. -/
theorem normalizeBagElements_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes)
    (parallelCollection : presentation.parallelCollection = .hashBag) :
    ProcListWellSorted presentation free bound
      (normalizeBagElements processes) := by
  apply sortPatterns_procListWellSorted
  apply filter_procListWellSorted
  exact flatMap_bagSplice_procListWellSorted typed parallelCollection

/-- Removing the representation-only empty/singleton parallel wrapper
preserves process sorting. -/
theorem collapseBag_procWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes)
    (parallelCollection : presentation.parallelCollection = .hashBag)
    (parallelUnitConstructor : presentation.parallelUnitConstructor = "PZero") :
    ProcWellSorted presentation free bound (collapseBag processes) := by
  cases processes with
  | nil =>
      simpa [collapseBag, parallelUnitConstructor] using
        (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor []))
  | cons process processes =>
      cases processes with
      | nil =>
          exact (procListWellSorted_iff_forall_mem.mp typed) process (by simp)
      | cons second remainder =>
          simpa [collapseBag, parallelCollection] using
            (ProcWellSorted.parallel typed)

/-! ## Quote-aware scope closure lemmas -/

/-- Splicing a scope-safe parallel component preserves list safety. -/
theorem bagSplice_binderSafeListAt
    {quoteConstructor : String} {depth : Nat} {process : Pattern}
    (safe : binderSafeAt quoteConstructor depth process = true) :
    binderSafeListAt quoteConstructor depth (bagSplice process) = true := by
  cases process <;>
    simp_all [bagSplice, binderSafeAt, binderSafeListAt]
  next collectionType elements rest =>
    cases collectionType <;> cases rest <;>
      simp_all [binderSafeAt, binderSafeListAt]

/-- Flattening scope-safe parallel components preserves list safety. -/
theorem flatMap_bagSplice_binderSafeListAt
    {quoteConstructor : String} {depth : Nat} {processes : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth processes = true) :
    binderSafeListAt quoteConstructor depth
      (processes.flatMap bagSplice) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro process membership
  rw [List.mem_flatMap] at membership
  obtain ⟨source, sourceMember, processMember⟩ := membership
  exact (binderSafeListAt_eq_true_iff _ _ _).mp
    (bagSplice_binderSafeListAt (safe source sourceMember)) process processMember

/-- Filtering a scope-safe list preserves scope safety. -/
theorem filter_binderSafeListAt
    {quoteConstructor : String} {depth : Nat} {processes : List Pattern}
    (keep : Pattern → Bool)
    (safe : binderSafeListAt quoteConstructor depth processes = true) :
    binderSafeListAt quoteConstructor depth (processes.filter keep) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro process membership
  exact safe process (List.mem_of_mem_filter membership)

/-- Sorting a scope-safe list by the canonical structural order preserves
scope safety. -/
theorem sortPatterns_binderSafeListAt
    {quoteConstructor : String} {depth : Nat} {processes : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth processes = true) :
    binderSafeListAt quoteConstructor depth (sortPatterns processes) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro process membership
  exact safe process (sortPatterns_mem_iff.mp membership)

/-- Parallel normalization preserves quote-aware scope safety. -/
theorem normalizeBagElements_binderSafeListAt
    {quoteConstructor : String} {depth : Nat} {processes : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth processes = true) :
    binderSafeListAt quoteConstructor depth
      (normalizeBagElements processes) = true := by
  apply sortPatterns_binderSafeListAt
  apply filter_binderSafeListAt
    (fun pattern => pattern ≠ .apply "PZero" [])
  exact flatMap_bagSplice_binderSafeListAt safe

/-- Removing the empty/singleton parallel wrapper preserves quote-aware scope
safety. -/
theorem collapseBag_binderSafeAt
    {quoteConstructor : String} {depth : Nat} {processes : List Pattern}
    (safe : binderSafeListAt quoteConstructor depth processes = true) :
    binderSafeAt quoteConstructor depth (collapseBag processes) = true := by
  cases processes with
  | nil => simp [collapseBag, binderSafeAt, binderSafeListAt]
  | cons process processes =>
      cases processes with
      | nil =>
          simpa [collapseBag, binderSafeListAt] using safe
      | cons second remainder =>
          simpa [collapseBag, binderSafeAt] using safe

/-- Quote/drop normalization preserves scope safety.  When cancellation
exposes a name checked at depth zero, monotonicity admits it at the surrounding
depth. -/
theorem normalizeQuote_binderSafeAt
    {depth : Nat} {process : Pattern}
    (safe : binderSafeAt "NQuote" 0 process = true) :
    binderSafeAt "NQuote" depth (normalizeQuote process) = true := by
  by_cases dropShape : ∃ name, process = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := dropShape
    have nameSafe : binderSafeAt "NQuote" 0 name = true := by
      simpa [binderSafeAt, binderSafeListAt] using safe
    simpa [normalizeQuote] using
      (binderSafeAt_mono "NQuote" nameSafe (Nat.zero_le depth))
  · have notDrop : ∀ name, process ≠ .apply "PDrop" [name] := by
      intro name equality
      exact dropShape ⟨name, equality⟩
    rw [normalizeQuote_eq_quote_of_not_drop notDrop]
    simpa [binderSafeAt] using safe

/-! ## Sort preservation of the canonicalizer -/

/-- Orienting quote/drop cancellation preserves the name sort. -/
theorem normalizeQuote_nameWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process)
    (quoteConstructor : presentation.quoteConstructor = "NQuote")
    (dropConstructor : presentation.dropConstructor = "PDrop") :
    NameWellSorted presentation free bound (normalizeQuote process) := by
  cases typed with
  | bvar lookup =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.bvar lookup))
  | fvar lookup =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.fvar lookup))
  | unit =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.unit :
          ProcWellSorted presentation free bound
            (.apply presentation.parallelUnitConstructor [])))
  | drop nameTyped =>
      simpa [normalizeQuote, quoteConstructor, dropConstructor] using nameTyped
  | output channelTyped payloadTyped =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.output channelTyped payloadTyped))
  | input channelTyped bodyTyped =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.input channelTyped bodyTyped))
  | parallel processesTyped =>
      simpa [normalizeQuote, quoteConstructor] using
        (NameWellSorted.quote (ProcWellSorted.parallel processesTyped))

mutual
  /-- Canonicalization maps a presentation-derived rho name to a name in the
same free and bound contexts. -/
  theorem canonicalize_nameWellSorted
      {free : FreeSortContext} (bound : List String) {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name) :
      NameWellSorted rhoReflectivePresentation free bound (canonicalize name) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped =>
        change NameWellSorted rhoReflectivePresentation free bound
          (normalizeQuote (canonicalize _))
        exact normalizeQuote_nameWellSorted
          (canonicalize_procWellSorted bound processTyped) rfl rfl

  /-- Canonicalization maps a presentation-derived rho process to a process in
the same free and bound contexts. -/
  theorem canonicalize_procWellSorted
      {free : FreeSortContext} (bound : List String) {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
      ProcWellSorted rhoReflectivePresentation free bound (canonicalize process) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | unit => exact .unit
    | drop nameTyped =>
        simpa [canonicalize, canonicalizeList, rhoReflectivePresentation] using
          (ProcWellSorted.drop (canonicalize_nameWellSorted bound nameTyped))
    | output channelTyped payloadTyped =>
        simpa [canonicalize, canonicalizeList, rhoReflectivePresentation] using
          (ProcWellSorted.output
            (canonicalize_nameWellSorted bound channelTyped)
            (canonicalize_procWellSorted bound payloadTyped))
    | input channelTyped bodyTyped =>
        simpa [canonicalize, canonicalizeList, rhoReflectivePresentation] using
          (ProcWellSorted.input
            (canonicalize_nameWellSorted bound channelTyped)
            (canonicalize_procWellSorted
              (rhoReflectivePresentation.nameSort :: bound) bodyTyped))
    | parallel processesTyped =>
        change ProcWellSorted rhoReflectivePresentation free bound
          (collapseBag
            (normalizeBagElements (canonicalizeList _)))
        apply collapseBag_procWellSorted
        apply normalizeBagElements_procListWellSorted
          (canonicalize_procListWellSorted bound processesTyped)
        rfl
        rfl
        rfl

  /-- Canonicalization maps a presentation-derived rho process list to a list
in the same free and bound contexts. -/
  theorem canonicalize_procListWellSorted
      {free : FreeSortContext} (bound : List String) {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
      ProcListWellSorted rhoReflectivePresentation free bound
        (canonicalizeList processes) := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        exact .cons (canonicalize_procWellSorted bound processTyped)
          (canonicalize_procListWellSorted bound processesTyped)
end

/-! ## Quote-aware scope preservation of the canonicalizer -/

/-- Canonicalization preserves quote-aware scope safety.  This statement is
representation-generic: it does not need a rho sorting derivation because the
canonicalizer traverses unknown constructors conservatively. -/
theorem canonicalize_binderSafeAt
    (pattern : Pattern) (depth : Nat)
    (safe : binderSafeAt "NQuote" depth pattern = true) :
    binderSafeAt "NQuote" depth (canonicalize pattern) = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simpa [canonicalize] using safe
  | hfvar name => simpa [canonicalize] using safe
  | happly constructor arguments inductionHypothesis =>
      cases arguments with
      | nil => simp [canonicalize, canonicalizeList, binderSafeAt, binderSafeListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = "NQuote"
              · subst constructor
                have argumentSafe : binderSafeAt "NQuote" 0 argument = true := by
                  simpa [binderSafeAt] using safe
                change binderSafeAt "NQuote" depth
                  (normalizeQuote (canonicalize argument)) = true
                exact normalizeQuote_binderSafeAt
                  (inductionHypothesis argument (by simp) 0 argumentSafe)
              · have argumentSafe :
                    binderSafeAt "NQuote" depth argument = true := by
                  simpa [binderSafeAt, binderSafeListAt, quoted] using safe
                simpa [canonicalize, canonicalizeList, binderSafeAt,
                  binderSafeListAt, quoted] using
                    (inductionHypothesis argument (by simp) depth argumentSafe)
          | cons second remainder =>
              have argumentsSafe :
                  binderSafeListAt "NQuote" depth
                    (argument :: second :: remainder) = true := by
                simpa [binderSafeAt] using safe
              have canonicalArgumentsSafe :
                  binderSafeListAt "NQuote" depth
                    (canonicalizeList (argument :: second :: remainder)) = true := by
                rw [binderSafeListAt_eq_true_iff] at argumentsSafe ⊢
                intro canonicalArgument canonicalMember
                rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
                obtain ⟨source, sourceMember, rfl⟩ := canonicalMember
                exact inductionHypothesis source sourceMember depth
                  (argumentsSafe source sourceMember)
              by_cases quoted : constructor = "NQuote"
              · subst constructor
                change binderSafeListAt "NQuote" depth
                  (canonicalize argument :: canonicalize second ::
                    canonicalizeList remainder) = true
                simpa [canonicalizeList] using canonicalArgumentsSafe
              · simp only [canonicalize]
                change binderSafeListAt "NQuote" depth
                  (canonicalize argument :: canonicalize second ::
                    canonicalizeList remainder) = true
                simpa [canonicalizeList] using canonicalArgumentsSafe
  | hlambda binderName body inductionHypothesis =>
      have bodySafe : binderSafeAt "NQuote" (depth + 1) body = true := by
        simpa [binderSafeAt] using safe
      simpa [canonicalize, binderSafeAt] using
        (inductionHypothesis (depth + 1) bodySafe)
  | hmultiLambda arity binderNames body inductionHypothesis =>
      have bodySafe : binderSafeAt "NQuote" (depth + arity) body = true := by
        simpa [binderSafeAt] using safe
      simpa [canonicalize, binderSafeAt] using
        (inductionHypothesis (depth + arity) bodySafe)
  | hsubst body replacement bodyInduction replacementInduction =>
      have componentsSafe :
          binderSafeAt "NQuote" (depth + 1) body = true ∧
            binderSafeAt "NQuote" depth replacement = true := by
        simpa [binderSafeAt, Bool.and_eq_true] using safe
      simpa [canonicalize, binderSafeAt, Bool.and_eq_true] using
        And.intro
          (bodyInduction (depth + 1) componentsSafe.1)
          (replacementInduction depth componentsSafe.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsSafe :
          binderSafeListAt "NQuote" depth elements = true := by
        simpa [binderSafeAt] using safe
      have canonicalElementsSafe :
          binderSafeListAt "NQuote" depth (canonicalizeList elements) = true := by
        rw [binderSafeListAt_eq_true_iff] at elementsSafe ⊢
        intro canonicalElement canonicalMember
        rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
        obtain ⟨source, sourceMember, rfl⟩ := canonicalMember
        exact inductionHypothesis source sourceMember depth
          (elementsSafe source sourceMember)
      cases collectionType with
      | vec => simpa [canonicalize, binderSafeAt] using canonicalElementsSafe
      | hashSet => simpa [canonicalize, binderSafeAt] using canonicalElementsSafe
      | hashBag =>
          cases rest with
          | none =>
              change binderSafeAt "NQuote" depth
                (collapseBag (normalizeBagElements (canonicalizeList elements))) = true
              exact collapseBag_binderSafeAt
                (normalizeBagElements_binderSafeListAt canonicalElementsSafe)
          | some restValue =>
              simpa [canonicalize, binderSafeAt] using canonicalElementsSafe

/-- List form of quote-aware scope preservation. -/
theorem canonicalizeList_binderSafeListAt
    (patterns : List Pattern) (depth : Nat)
    (safe : binderSafeListAt "NQuote" depth patterns = true) :
    binderSafeListAt "NQuote" depth (canonicalizeList patterns) = true := by
  rw [binderSafeListAt_eq_true_iff] at safe ⊢
  intro canonicalPattern canonicalMember
  rw [canonicalizeList_eq_map, List.mem_map] at canonicalMember
  obtain ⟨source, sourceMember, rfl⟩ := canonicalMember
  exact canonicalize_binderSafeAt source depth (safe source sourceMember)

/-! ## Positive and negative controls -/

/-- Positive: canonicalizing a parallel process with a removable unit still
produces a process. -/
theorem canonicalize_parallel_unit_procWellSorted (name : String) :
    let free : FreeSortContext := fun candidate =>
      if candidate = name then some rhoReflectivePresentation.nameSort else none
    ProcWellSorted rhoReflectivePresentation free []
      (canonicalize
        (.collection .hashBag
          [.apply "PZero" [],
           .apply "POutput" [.fvar name, .apply "PZero" []]] none)) := by
  dsimp
  apply canonicalize_procWellSorted []
  exact .parallel (.cons .unit (.cons (.output (.fvar (by simp)) .unit) .nil))

/-- Negative: canonicalization preserves sorting; it does not make a parallel
bag into a name. -/
theorem canonicalize_parallel_not_nameWellSorted :
    ¬NameWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (canonicalize (.collection .hashBag [.apply "PZero" []] none)) := by
  rw [show canonicalize (.collection .hashBag [.apply "PZero" []] none) =
      .apply "PZero" [] by
    simp [canonicalize, canonicalizeList, normalizeBagElements, bagSplice,
      collapseBag, sortPatterns]]
  intro typed
  generalize patternEq : (Pattern.apply "PZero" []) = pattern at typed
  cases typed <;> simp_all [rhoReflectivePresentation]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
