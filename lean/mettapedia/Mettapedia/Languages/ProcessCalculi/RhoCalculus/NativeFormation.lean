import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

/-!
# Executable formation and alpha admission for the authored rho syntax

The source judgments are the existing reflective-presentation Proc/Name/List
judgments. Formation does not follow from validity of a raw structural proof.
Quotation-scope admission is a separate, explicitly selected boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeFormation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

abbrev Proc (free : FreeSortContext) (bound : List String) (p : Pattern) :=
  ProcWellSorted rhoReflectivePresentation free bound p
abbrev Name (free : FreeSortContext) (bound : List String) (p : Pattern) :=
  NameWellSorted rhoReflectivePresentation free bound p
abbrev Processes (free : FreeSortContext) (bound : List String) (ps : List Pattern) :=
  ProcListWellSorted rhoReflectivePresentation free bound ps

mutual
  def checkName (free : FreeSortContext) (bound : List String) : Pattern → Bool
    | .bvar index => bound[index]? == some "Name"
    | .fvar name => free name == some "Name"
    | .apply "NQuote" [process] => checkProc free bound process
    | _ => false

  def checkProc (free : FreeSortContext) (bound : List String) : Pattern → Bool
    | .bvar index => bound[index]? == some "Proc"
    | .fvar name => free name == some "Proc"
    | .apply "PZero" [] => true
    | .apply "PDrop" [name] => checkName free bound name
    | .apply "POutput" [channel, payload] =>
        checkName free bound channel && checkProc free bound payload
    | .apply "PInput" [channel, .lambda none body] =>
        checkName free bound channel && checkProc free ("Name" :: bound) body
    | .collection .hashBag processes none => checkProcesses free bound processes
    | _ => false

  def checkProcesses (free : FreeSortContext) (bound : List String) : List Pattern → Bool
    | [] => true
    | p :: ps => checkProc free bound p && checkProcesses free bound ps
end

mutual
  theorem checkName_sound (free : FreeSortContext) (bound : List String)
      (p : Pattern) (accepted : checkName free bound p = true) : Name free bound p := by
    unfold checkName at accepted
    split at accepted
    · exact .bvar (by simpa only [beq_iff_eq, rhoReflectivePresentation] using accepted)
    · exact .fvar (by simpa only [beq_iff_eq, rhoReflectivePresentation] using accepted)
    · exact .quote (checkProc_sound free bound _ accepted)
    · contradiction

  theorem checkProc_sound (free : FreeSortContext) (bound : List String)
      (p : Pattern) (accepted : checkProc free bound p = true) : Proc free bound p := by
    unfold checkProc at accepted
    split at accepted
    · exact .bvar (by simpa only [beq_iff_eq, rhoReflectivePresentation] using accepted)
    · exact .fvar (by simpa only [beq_iff_eq, rhoReflectivePresentation] using accepted)
    · exact .unit
    · exact .drop (checkName_sound free bound _ accepted)
    · simp only [Bool.and_eq_true] at accepted
      obtain ⟨channel, payload⟩ := accepted
      exact .output (checkName_sound free bound _ channel) (checkProc_sound free bound _ payload)
    · simp only [Bool.and_eq_true] at accepted
      obtain ⟨channel, body⟩ := accepted
      exact .input (checkName_sound free bound _ channel) (checkProc_sound free ("Name" :: bound) _ body)
    · exact .parallel (checkProcesses_sound free bound _ accepted)
    · contradiction

  theorem checkProcesses_sound (free : FreeSortContext) (bound : List String)
      (ps : List Pattern) (accepted : checkProcesses free bound ps = true) :
      Processes free bound ps := by
    cases ps with
    | nil => exact .nil
    | cons p ps =>
        change (checkProc free bound p && checkProcesses free bound ps) = true at accepted
        simp only [Bool.and_eq_true] at accepted
        obtain ⟨head, tail⟩ := accepted
        exact .cons (checkProc_sound free bound p head) (checkProcesses_sound free bound ps tail)
end

mutual
  theorem checkName_complete {free : FreeSortContext} {bound : List String}
      {p : Pattern} (typed : NameWellSorted rhoReflectivePresentation free bound p) : checkName free bound p = true := by
    cases typed with
    | bvar lookup => simpa [checkName, rhoReflectivePresentation] using lookup
    | fvar lookup => simpa [checkName, rhoReflectivePresentation] using lookup
    | quote typed => exact checkProc_complete typed

  theorem checkProc_complete {free : FreeSortContext} {bound : List String}
      {p : Pattern} (typed : ProcWellSorted rhoReflectivePresentation free bound p) : checkProc free bound p = true := by
    cases typed with
    | bvar lookup => simpa [checkProc, rhoReflectivePresentation] using lookup
    | fvar lookup => simpa [checkProc, rhoReflectivePresentation] using lookup
    | unit => rfl
    | drop typed => exact checkName_complete typed
    | output channel payload =>
        simpa only [checkProc, rhoReflectivePresentation, Bool.and_eq_true] using
          And.intro (checkName_complete channel) (checkProc_complete payload)
    | input channel body =>
        simpa only [checkProc, rhoReflectivePresentation, Bool.and_eq_true] using
          And.intro (checkName_complete channel) (checkProc_complete body)
    | parallel typed => exact checkProcesses_complete typed

  theorem checkProcesses_complete {free : FreeSortContext} {bound : List String}
      {ps : List Pattern} (typed : ProcListWellSorted rhoReflectivePresentation free bound ps) : checkProcesses free bound ps = true := by
    cases typed with
    | nil => rfl
    | cons head tail =>
        simpa only [checkProcesses, Bool.and_eq_true] using
          And.intro (checkProc_complete head) (checkProcesses_complete tail)
end

theorem checkProc_exact (free : FreeSortContext) (bound : List String) (p : Pattern) :
    checkProc free bound p = true ↔ Proc free bound p :=
  ⟨checkProc_sound free bound p, checkProc_complete⟩

theorem checkName_exact (free : FreeSortContext) (bound : List String) (p : Pattern) :
    checkName free bound p = true ↔ Name free bound p :=
  ⟨checkName_sound free bound p, checkName_complete⟩

mutual
  theorem name_canonical {free : FreeSortContext} {bound : List String} {p : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound p) :
      p.hasCanonicalBinderMetadata = true := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | quote typed =>
        simpa only [rhoReflectivePresentation, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Bool.and_true] using proc_canonical typed

  theorem proc_canonical {free : FreeSortContext} {bound : List String} {p : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound p) :
      p.hasCanonicalBinderMetadata = true := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | unit => rfl
    | drop typed =>
        simpa only [rhoReflectivePresentation, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Bool.and_true] using name_canonical typed
    | output channel payload =>
        simpa only [rhoReflectivePresentation, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Bool.and_true, Bool.and_eq_true] using
          And.intro (name_canonical channel) (proc_canonical payload)
    | input channel body =>
        simpa only [rhoReflectivePresentation, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Option.isNone, Bool.true_and,
          Bool.and_true, Bool.and_eq_true] using
          And.intro (name_canonical channel) (proc_canonical body)
    | parallel typed => exact processes_canonical typed

  theorem processes_canonical {free : FreeSortContext} {bound : List String} {ps : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound ps) :
      Pattern.hasCanonicalBinderMetadataList ps = true := by
    cases typed with
    | nil => rfl
    | cons head tail =>
        simpa only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] using
          And.intro (proc_canonical head) (processes_canonical tail)
end

/-- The quotation boundary is checked explicitly rather than inferred from
ordinary de Bruijn sorting. -/
def checkAdmittedProc (free : FreeSortContext) (bound : List String) (p : Pattern) : Bool :=
  checkProc free bound p && binderSafeAt "NQuote" bound.length p

def checkAdmittedName (free : FreeSortContext) (bound : List String) (p : Pattern) : Bool :=
  checkName free bound p && binderSafeAt "NQuote" bound.length p

theorem checkAdmittedProc_exact (free : FreeSortContext) (bound : List String) (p : Pattern) :
    checkAdmittedProc free bound p = true ↔
      Proc free bound p ∧ binderSafeAt "NQuote" bound.length p = true := by
  simp only [checkAdmittedProc, Bool.and_eq_true, checkProc_exact]

theorem checkAdmittedName_exact (free : FreeSortContext) (bound : List String) (p : Pattern) :
    checkAdmittedName free bound p = true ↔
      Name free bound p ∧ binderSafeAt "NQuote" bound.length p = true := by
  simp only [checkAdmittedName, Bool.and_eq_true, checkName_exact]

/-- Raw source display names are compared through the existing metadata
erasure. This does not add raw-alpha equations to StructuralCongruence. -/
def checkAlpha (first second : Pattern) : Bool :=
  first.eraseBinderMetadata == second.eraseBinderMetadata

theorem checkAlpha_exact (first second : Pattern) :
    checkAlpha first second = true ↔ AlphaEquiv first second := by
  simp only [checkAlpha, beq_iff_eq, AlphaEquiv, Pattern.AlphaEquiv]

theorem checkAlpha_structural {first second : Pattern}
    (accepted : checkAlpha first second = true) :
    StructuralCongruence first.eraseBinderMetadata second.eraseBinderMetadata :=
  StructuralCongruence.alpha _ _ ((checkAlpha_exact first second).mp accepted)

/-- On the actual source carrier the alpha check is literal equality;
the metadata-erasure observer is only needed for source display syntax. -/
theorem checkAlpha_proc_iff_eq {free : FreeSortContext} {bound : List String}
    {first second : Pattern} (firstTyped : Proc free bound first)
    (secondTyped : Proc free bound second) :
    checkAlpha first second = true ↔ first = second :=
  (checkAlpha_exact first second).trans
    (Pattern.alphaEquiv_iff_eq_of_canonical (proc_canonical firstTyped) (proc_canonical secondTyped))

namespace Controls

private def zero : Pattern := .apply "PZero" []
private def channel : Pattern := .apply "NQuote" [zero]
private def boundDrop : Pattern := .apply "PDrop" [.bvar 0]
private def input : Pattern := .apply "PInput" [channel, .lambda none boundDrop]
private def crossesQuote : Pattern := .apply "PInput"
  [channel, .lambda none (.apply "POutput" [.apply "NQuote" [boundDrop], zero])]

example : Proc FreeSortContext.empty [] input :=
  (checkProc_exact _ _ _).mp (by decide)
example : Name FreeSortContext.empty [] channel :=
  (checkName_exact _ _ _).mp (by decide)
example : ¬Proc FreeSortContext.empty [] channel := by
  intro typed
  have accepted := checkProc_complete typed
  contradiction
example : Proc FreeSortContext.empty [] crossesQuote :=
  (checkProc_exact _ _ _).mp (by decide)
example : checkAdmittedProc FreeSortContext.empty [] crossesQuote = false := by decide
example : checkAdmittedProc FreeSortContext.empty ["Name"] boundDrop = true := by decide
example : checkAdmittedProc FreeSortContext.empty ["Proc"] boundDrop = false := by decide
example : checkProc FreeSortContext.empty [] (.collection .hashSet [zero] none) = false := by decide
example : checkProc FreeSortContext.empty [] (.apply "unknown" []) = false := by decide
example : checkProc FreeSortContext.empty [] (.apply "PInput" [channel, .lambda (some "x") boundDrop]) = false := by decide
example : checkAlpha (.lambda (some "x") (.bvar 0)) (.lambda (some "y") (.bvar 0)) = true := by
  apply (checkAlpha_exact _ _).mpr
  simp only [AlphaEquiv, Pattern.AlphaEquiv, Pattern.eraseBinderMetadata]
example : checkAlpha (.lambda none (.bvar 0)) (.lambda none (.bvar 1)) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have same := (checkAlpha_exact _ _).mp accepted
  simp only [AlphaEquiv, Pattern.AlphaEquiv, Pattern.eraseBinderMetadata] at same
  cases same

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeFormation
