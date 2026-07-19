import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Syntax derived from a reflective presentation

A `ReflectivePresentationDecl` names the constructors and sorts of a
reflective process calculus inside its authored `LanguageDef`.  The judgments
below provide the corresponding induction principle on the shared `Pattern`
carrier.  They are indexed by the declaration data; they are not a second term
syntax and contain no hard-coded rho constructor names.
-/

namespace Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Sort assignment for free pattern variables. -/
abbrev FreeSortContext := String → Option String

/-- Empty free-variable sort assignment. -/
def FreeSortContext.empty : FreeSortContext := fun _ => none

mutual
  /-- Well-sorted names derived from a reflective presentation. -/
  inductive NameWellSorted
      (presentation : ReflectivePresentationDecl)
      (free : FreeSortContext) : List String → Pattern → Prop where
    | bvar {bound : List String} {index : Nat} :
        bound[index]? = some presentation.nameSort →
        NameWellSorted presentation free bound (.bvar index)
    | fvar {bound : List String} {name : String} :
        free name = some presentation.nameSort →
        NameWellSorted presentation free bound (.fvar name)
    | quote {bound : List String} {process : Pattern} :
        ProcWellSorted presentation free bound process →
        NameWellSorted presentation free bound
          (.apply presentation.quoteConstructor [process])

  /-- Well-sorted processes derived from a reflective presentation. -/
  inductive ProcWellSorted
      (presentation : ReflectivePresentationDecl)
      (free : FreeSortContext) : List String → Pattern → Prop where
    | bvar {bound : List String} {index : Nat} :
        bound[index]? = some presentation.processSort →
        ProcWellSorted presentation free bound (.bvar index)
    | fvar {bound : List String} {name : String} :
        free name = some presentation.processSort →
        ProcWellSorted presentation free bound (.fvar name)
    | unit {bound : List String} :
        ProcWellSorted presentation free bound
          (.apply presentation.parallelUnitConstructor [])
    | drop {bound : List String} {name : Pattern} :
        NameWellSorted presentation free bound name →
        ProcWellSorted presentation free bound
          (.apply presentation.dropConstructor [name])
    | output {bound : List String} {channel payload : Pattern} :
        NameWellSorted presentation free bound channel →
        ProcWellSorted presentation free bound payload →
        ProcWellSorted presentation free bound
          (.apply presentation.outputConstructor [channel, payload])
    | input {bound : List String} {channel body : Pattern} :
        NameWellSorted presentation free bound channel →
        ProcWellSorted presentation free (presentation.nameSort :: bound) body →
        ProcWellSorted presentation free bound
          (.apply presentation.inputConstructor [channel, .lambda none body])
    | parallel {bound : List String} {processes : List Pattern} :
        ProcListWellSorted presentation free bound processes →
        ProcWellSorted presentation free bound
          (.collection presentation.parallelCollection processes none)

  /-- List form used by the presentation's parallel collection. -/
  inductive ProcListWellSorted
      (presentation : ReflectivePresentationDecl)
      (free : FreeSortContext) : List String → List Pattern → Prop where
    | nil {bound : List String} : ProcListWellSorted presentation free bound []
    | cons {bound : List String} {process : Pattern} {processes : List Pattern} :
        ProcWellSorted presentation free bound process →
        ProcListWellSorted presentation free bound processes →
        ProcListWellSorted presentation free bound (process :: processes)
end

/-! ## Generic structural consequences -/

mutual
  /-- Extending the outer end of a de Bruijn sort context preserves every
  derived name judgment.  Existing indices retain their meanings because the
  new binders are appended outside them. -/
  theorem NameWellSorted.weakenBoundRight
      {presentation : ReflectivePresentationDecl} {free : FreeSortContext}
      {bound : List String} {name : Pattern}
      (typed : NameWellSorted presentation free bound name)
      (extension : List String) :
      NameWellSorted presentation free (bound ++ extension) name := by
    cases typed with
    | bvar lookup =>
        apply NameWellSorted.bvar
        have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
        rw [List.getElem?_append_left inBounds]
        exact lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped => exact .quote (processTyped.weakenBoundRight extension)

  /-- Process form of outer-context weakening. -/
  theorem ProcWellSorted.weakenBoundRight
      {presentation : ReflectivePresentationDecl} {free : FreeSortContext}
      {bound : List String} {process : Pattern}
      (typed : ProcWellSorted presentation free bound process)
      (extension : List String) :
      ProcWellSorted presentation free (bound ++ extension) process := by
    cases typed with
    | bvar lookup =>
        apply ProcWellSorted.bvar
        have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
        rw [List.getElem?_append_left inBounds]
        exact lookup
    | fvar lookup => exact .fvar lookup
    | unit => exact .unit
    | drop nameTyped => exact .drop (nameTyped.weakenBoundRight extension)
    | output channelTyped payloadTyped =>
        exact .output (channelTyped.weakenBoundRight extension)
          (payloadTyped.weakenBoundRight extension)
    | input channelTyped bodyTyped =>
        exact .input (channelTyped.weakenBoundRight extension) (by
          simpa [List.cons_append] using bodyTyped.weakenBoundRight extension)
    | parallel processesTyped =>
        exact .parallel (processesTyped.weakenBoundRight extension)

  /-- List form of outer-context weakening. -/
  theorem ProcListWellSorted.weakenBoundRight
      {presentation : ReflectivePresentationDecl} {free : FreeSortContext}
      {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted presentation free bound processes)
      (extension : List String) :
      ProcListWellSorted presentation free (bound ++ extension) processes := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        exact .cons (processTyped.weakenBoundRight extension)
          (processesTyped.weakenBoundRight extension)
end

/-! ## List elimination utilities -/

/-- Every selected component of a well-sorted process list is well-sorted. -/
theorem ProcListWellSorted.getElem
    {presentation : ReflectivePresentationDecl} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes)
    (index : Nat) (indexBound : index < processes.length) :
    ProcWellSorted presentation free bound processes[index] := by
  induction processes generalizing index with
  | nil => simp at indexBound
  | cons process processes inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
      cases index with
      | zero => simpa using headTyped
      | succ index =>
          exact inductionHypothesis tailTyped index (by simpa using indexBound)

/-- Removing a component preserves well-sortedness of the remaining process
list. -/
theorem ProcListWellSorted.eraseIdx
    {presentation : ReflectivePresentationDecl} {free : FreeSortContext}
    {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted presentation free bound processes)
    (index : Nat) :
    ProcListWellSorted presentation free bound (processes.eraseIdx index) := by
  induction processes generalizing index with
  | nil => exact .nil
  | cons process processes inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
      cases index with
      | zero => exact tailTyped
      | succ index => exact .cons headTyped (inductionHypothesis tailTyped index)

/-! ## Presentation-parametric examples -/

section Examples

variable (presentation : ReflectivePresentationDecl)

/-- Positive: the presentation's unit is a process without any context. -/
example : ProcWellSorted presentation FreeSortContext.empty []
    (.apply presentation.parallelUnitConstructor []) :=
  .unit

/-- Positive: quoting the unit yields a name. -/
example : NameWellSorted presentation FreeSortContext.empty []
    (.apply presentation.quoteConstructor
      [.apply presentation.parallelUnitConstructor []]) :=
  .quote .unit

/-- Negative: a top-level bound variable is rejected in an empty context. -/
theorem bvar_zero_not_name_wellSorted_empty :
    ¬ NameWellSorted presentation FreeSortContext.empty [] (.bvar 0) := by
  intro typed
  cases typed with
  | bvar lookup => simp at lookup

end Examples

end Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
