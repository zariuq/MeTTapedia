import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

theorem check_procListWellSorted_iff_forall_mem
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern} :
    ProcListWellSorted presentation free bound processes ↔
      ∀ process ∈ processes, ProcWellSorted presentation free bound process := by
  constructor
  · intro typed process membership
    induction processes generalizing process with
    | nil => simp at membership
    | cons head tail inductionHypothesis =>
        cases typed with
        | cons headTyped tailTyped =>
            rcases List.mem_cons.mp membership with rfl | membership
            · exact headTyped
            · exact inductionHypothesis tailTyped process membership
  · intro pointwise
    induction processes with
    | nil => exact .nil
    | cons process processes inductionHypothesis =>
        exact .cons (pointwise process (by simp))
          (inductionHypothesis fun member membership =>
            pointwise member (by simp [membership]))

theorem check_parallelSplice_procListWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process) :
    ProcListWellSorted presentation free bound
      (parallelSplice presentation.toReflectivePresentationDecl process) := by
  cases typed with
  | bvar lookup => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.bvar lookup)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | fvar lookup => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.fvar lookup)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | unit => simpa [parallelSplice] using
      (ProcListWellSorted.cons
        (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor []))
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | drop nameTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.drop nameTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | output channelTyped payloadTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons
        (ProcWellSorted.output channelTyped payloadTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | input channelTyped bodyTyped => simpa [parallelSplice] using
      (ProcListWellSorted.cons (ProcWellSorted.input channelTyped bodyTyped)
        (ProcListWellSorted.nil : ProcListWellSorted presentation free bound []))
  | parallel processesTyped => simpa [parallelSplice] using processesTyped

theorem check_normalizeParallelElementsBy_procListWellSorted
    {Key : Type} [LinearOrder Key]
    (key : Pattern → Key)
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcListWellSorted presentation free bound
      (normalizeParallelElementsBy key
        presentation.toReflectivePresentationDecl processes) := by
  rw [check_procListWellSorted_iff_forall_mem] at typed ⊢
  intro process membership
  have sourceMembership : process ∈
      ((processes.flatMap
        (parallelSplice presentation.toReflectivePresentationDecl)).filter
          fun pattern =>
            pattern ≠ .apply presentation.parallelUnitConstructor []) :=
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key _).mem_iff.mp
      membership
  have flatMembership := List.mem_of_mem_filter sourceMembership
  rw [List.mem_flatMap] at flatMembership
  obtain ⟨source, sourceMember, processMember⟩ := flatMembership
  exact (check_procListWellSorted_iff_forall_mem.mp
    (check_parallelSplice_procListWellSorted (typed source sourceMember)))
      process processMember

theorem check_collapseParallel_procWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes) :
    ProcWellSorted presentation free bound
      (collapseParallel presentation.toReflectivePresentationDecl processes) := by
  cases processes with
  | nil => exact .unit
  | cons process processes =>
      cases processes with
      | nil =>
          exact (check_procListWellSorted_iff_forall_mem.mp typed) process (by simp)
      | cons second remainder => exact .parallel typed

theorem check_finishQuote_nameWellSorted
    {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
    {bound : List String} {process : Pattern}
    (typed : ProcWellSorted presentation free bound process) :
    NameWellSorted presentation free bound
      (finishNormalizeReflectiveApply
        presentation.toReflectivePresentationDecl
        presentation.quoteConstructor [process]) := by
  cases typed with
  | bvar lookup => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote (ProcWellSorted.bvar lookup))
  | fvar lookup => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote (ProcWellSorted.fvar lookup))
  | unit => simpa [finishNormalizeReflectiveApply] using
      (NameWellSorted.quote
        (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor [])))
  | drop nameTyped => simpa [finishNormalizeReflectiveApply] using nameTyped
  | output channelTyped payloadTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.output channelTyped payloadTyped))
  | input channelTyped bodyTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.input channelTyped bodyTyped))
  | parallel processesTyped =>
      simpa [finishNormalizeReflectiveApply] using
        (NameWellSorted.quote (ProcWellSorted.parallel processesTyped))

mutual
  theorem check_canonicalizeByAt_nameWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {name : Pattern}
      (typed : NameWellSorted presentation free bound name) :
      NameWellSorted presentation free bound
        (canonicalizeByAt key presentation.toReflectivePresentationDecl
          availableDepth name) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped =>
        simp only [canonicalizeByAt, beq_self_eq_true, if_true,
          canonicalizeListByAt]
        exact check_finishQuote_nameWellSorted
          (check_canonicalizeByAt_procWellSorted key presentation quote_ne_drop
            0 processTyped)

  theorem check_canonicalizeByAt_procWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {process : Pattern}
      (typed : ProcWellSorted presentation free bound process) :
      ProcWellSorted presentation free bound
        (canonicalizeByAt key presentation.toReflectivePresentationDecl
          availableDepth process) := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | unit =>
        simp [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply]
        exact (ProcWellSorted.unit : ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor []))
    | drop nameTyped =>
        have drop_ne_quote : presentation.dropConstructor ≠
            presentation.quoteConstructor := Ne.symm quote_ne_drop
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, drop_ne_quote] using
          (ProcWellSorted.drop
            (check_canonicalizeByAt_nameWellSorted key presentation
              quote_ne_drop availableDepth nameTyped))
    | output channelTyped payloadTyped =>
        let childDepth :=
          if presentation.outputConstructor == presentation.quoteConstructor
          then 0 else availableDepth
        have channelNormalized := check_canonicalizeByAt_nameWellSorted key
          presentation quote_ne_drop childDepth channelTyped
        have payloadNormalized := check_canonicalizeByAt_procWellSorted key
          presentation quote_ne_drop childDepth payloadTyped
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, childDepth] using
          (ProcWellSorted.output channelNormalized payloadNormalized)
    | input channelTyped bodyTyped =>
        let childDepth :=
          if presentation.inputConstructor == presentation.quoteConstructor
          then 0 else availableDepth
        have channelNormalized := check_canonicalizeByAt_nameWellSorted key
          presentation quote_ne_drop childDepth channelTyped
        have bodyNormalized := check_canonicalizeByAt_procWellSorted key
          presentation quote_ne_drop (childDepth + 1) bodyTyped
        simpa [canonicalizeByAt, canonicalizeListByAt,
          finishNormalizeReflectiveApply, childDepth] using
          (ProcWellSorted.input channelNormalized bodyNormalized)
    | parallel processesTyped =>
        simp only [canonicalizeByAt, beq_self_eq_true, if_true]
        apply check_collapseParallel_procWellSorted
        apply check_normalizeParallelElementsBy_procListWellSorted
        exact check_canonicalizeListByAt_procListWellSorted key presentation
          quote_ne_drop availableDepth processesTyped

  theorem check_canonicalizeListByAt_procListWellSorted
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key)
      (presentation : ReflectiveProcessSignature)
      (quote_ne_drop : presentation.quoteConstructor ≠
        presentation.dropConstructor)
      {free : FreeSortContext} (availableDepth : Nat)
      {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted presentation free bound processes) :
      ProcListWellSorted presentation free bound
        (canonicalizeListByAt key presentation.toReflectivePresentationDecl
          availableDepth processes) := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        exact .cons
          (check_canonicalizeByAt_procWellSorted key presentation
            quote_ne_drop availableDepth processTyped)
          (check_canonicalizeListByAt_procListWellSorted key presentation
            quote_ne_drop availableDepth processesTyped)
end

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
