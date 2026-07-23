import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Scope-safe restriction of derived presentation terms

The shared `Pattern` representation admits arbitrary de Bruijn indices, while
`NameWellSorted` and `ProcWellSorted` assign sorts relative to an ambient
binder context.  A quote-aware scope witness identifies the prefix of that
context on which a term actually depends.  The theorems below remove the
unused suffix and retain exactly that binder prefix.

Quotation is the important case: its body is checked from depth zero, so the
body is reconstructed in the empty context and then weakened into the local
prefix.  No language-specific reduction rule participates.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

mutual
  /-- A quote-aware name depends only on the declared local binder prefix, not
  on the ambient suffix of its sorting context. -/
  theorem nameWellSorted_restrictToBinderPrefix
      {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
      {depth : Nat} {tail : List String} {name : Pattern}
      (typed : NameWellSorted presentation free
        (List.replicate depth presentation.nameSort ++ tail) name)
      (safe : binderSafeAt presentation.quoteConstructor depth name = true) :
      NameWellSorted presentation free
        (List.replicate depth presentation.nameSort) name := by
    cases typed with
    | bvar lookup =>
        rename_i index
        apply NameWellSorted.bvar
        have indexBound : index < depth := by
          simpa [binderSafeAt] using safe
        have inPrefix :
            index < (List.replicate depth presentation.nameSort).length := by
          simpa using indexBound
        rw [List.getElem?_append_left inPrefix] at lookup
        exact lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped =>
        rename_i process
        have processSafe :
            binderSafeAt presentation.quoteConstructor 0 process = true := by
          simpa [binderSafeAt] using safe
        have processClosed :
            ProcWellSorted presentation free [] process := by
          simpa using
            (procWellSorted_restrictToBinderPrefix
              (depth := 0)
              (tail := List.replicate depth presentation.nameSort ++ tail)
              processTyped processSafe)
        exact .quote (by
          simpa using processClosed.weakenBoundRight
            (List.replicate depth presentation.nameSort))

  /-- Process form of binder-prefix restriction. -/
  theorem procWellSorted_restrictToBinderPrefix
      {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
      {depth : Nat} {tail : List String} {process : Pattern}
      (typed : ProcWellSorted presentation free
        (List.replicate depth presentation.nameSort ++ tail) process)
      (safe : binderSafeAt presentation.quoteConstructor depth process = true) :
      ProcWellSorted presentation free
        (List.replicate depth presentation.nameSort) process := by
    cases typed with
    | bvar lookup =>
        rename_i index
        apply ProcWellSorted.bvar
        have indexBound : index < depth := by
          simpa [binderSafeAt] using safe
        have inPrefix :
            index < (List.replicate depth presentation.nameSort).length := by
          simpa using indexBound
        rw [List.getElem?_append_left inPrefix] at lookup
        exact lookup
    | fvar lookup => exact .fvar lookup
    | unit => exact .unit
    | drop nameTyped =>
        rename_i name
        have nameSafe :
            binderSafeAt presentation.quoteConstructor depth name = true := by
          by_cases sameConstructor :
              presentation.dropConstructor = presentation.quoteConstructor
          · have closedSafe :
                binderSafeAt presentation.quoteConstructor 0 name = true := by
              simpa [binderSafeAt, sameConstructor] using safe
            exact binderSafeAt_mono presentation.quoteConstructor closedSafe
              (Nat.zero_le depth)
          · simpa [binderSafeAt, binderSafeListAt, sameConstructor] using safe
        exact .drop (nameWellSorted_restrictToBinderPrefix nameTyped nameSafe)
    | output channelTyped payloadTyped =>
        rename_i channel payload
        have componentsSafe :
            binderSafeAt presentation.quoteConstructor depth channel = true ∧
              binderSafeAt presentation.quoteConstructor depth payload = true := by
          simpa [binderSafeAt, binderSafeListAt] using safe
        exact .output
          (nameWellSorted_restrictToBinderPrefix channelTyped componentsSafe.1)
          (procWellSorted_restrictToBinderPrefix payloadTyped componentsSafe.2)
    | input channelTyped bodyTyped =>
        rename_i channel body
        have componentsSafe :
            binderSafeAt presentation.quoteConstructor depth channel = true ∧
              binderSafeAt presentation.quoteConstructor (depth + 1) body = true := by
          simpa [binderSafeAt, binderSafeListAt] using safe
        have bodyTyped' :
            ProcWellSorted presentation free
              (List.replicate (depth + 1) presentation.nameSort ++ tail) body := by
          simpa [List.replicate_succ] using bodyTyped
        exact .input
          (nameWellSorted_restrictToBinderPrefix channelTyped componentsSafe.1)
          (by
            simpa [List.replicate_succ] using
              procWellSorted_restrictToBinderPrefix bodyTyped' componentsSafe.2)
    | parallel processesTyped =>
        rename_i processes
        have processesSafe :
            binderSafeListAt presentation.quoteConstructor depth processes = true := by
          simpa [binderSafeAt] using safe
        exact .parallel
          (procListWellSorted_restrictToBinderPrefix processesTyped processesSafe)

  /-- List form of binder-prefix restriction. -/
  theorem procListWellSorted_restrictToBinderPrefix
      {presentation : ReflectiveProcessSignature} {free : FreeSortContext}
      {depth : Nat} {tail : List String} {processes : List Pattern}
      (typed : ProcListWellSorted presentation free
        (List.replicate depth presentation.nameSort ++ tail) processes)
      (safe :
        binderSafeListAt presentation.quoteConstructor depth processes = true) :
      ProcListWellSorted presentation free
        (List.replicate depth presentation.nameSort) processes := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        rename_i process processes
        have componentsSafe :
            binderSafeAt presentation.quoteConstructor depth process = true ∧
              binderSafeListAt presentation.quoteConstructor depth processes = true := by
          simpa [binderSafeListAt, Bool.and_eq_true] using safe
        exact .cons
          (procWellSorted_restrictToBinderPrefix processTyped componentsSafe.1)
          (procListWellSorted_restrictToBinderPrefix processesTyped componentsSafe.2)
end

/-! ## Positive and negative controls -/

private def prefixPresentation : ReflectiveProcessSignature where
  name := "prefix-control"
  nameSort := "Name"
  processSort := "Proc"
  quoteConstructor := "Quote"
  dropConstructor := "Drop"
  outputConstructor := "Output"
  inputConstructor := "Input"
  parallelUnitConstructor := "Zero"
  parallelCollection := .hashBag
  quoteDropEquation := "QuoteDrop"

/-- Positive: a local input binder remains available after an unused ambient
suffix is removed. -/
theorem restrictToBinderPrefix_keeps_local_name :
    NameWellSorted prefixPresentation FreeSortContext.empty ["Name"] (.bvar 0) := by
  have typed :
      NameWellSorted prefixPresentation FreeSortContext.empty
        (["Name"] ++ ["Unused"]) (.bvar 0) := by
    apply NameWellSorted.bvar
    rfl
  exact nameWellSorted_restrictToBinderPrefix
    (presentation := prefixPresentation) (depth := 1) (tail := ["Unused"])
    typed (by decide)

/-- Negative control: the ambient suffix is not retained in the restricted
judgment. -/
theorem restrictToBinderPrefix_rejects_ambient_name :
    ¬NameWellSorted prefixPresentation FreeSortContext.empty ["Name"]
      (.bvar 1) := by
  intro typed
  cases typed
  rename_i lookup
  simp at lookup

end Mettapedia.OSLF.MeTTaIL.ScopedDerivedPresentationSyntax
