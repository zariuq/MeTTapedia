import Mettapedia.OSLF.Syntax.RhoWholeNameAdmission
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Rho whole-name admission after structural canonicalization

Parallel-unit and quote/drop equations can expose a whole bound name from a
surface spelling such as `@(*x | 0)`. The pure rho canonicalizer selects an
equivalent representative before scope admission and translation. Literal
quoted code whose normal form is not a whole name remains sealed.

These results concern mathematical canonical representatives. They do not
change the executable surface parser or assert that every raw source step
has already been transported to its canonical representative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Scope admission on the computed representative of the rho equations. -/
def canonicalWholeNameSafeAt (depth : Nat) (pattern : Pattern) : Bool :=
  wholeNameSafeAt depth (Canonical.canonicalize pattern)

/-- Closed admission after pure rho canonicalization. -/
def canonicalWholeNameSafe (pattern : Pattern) : Bool :=
  canonicalWholeNameSafeAt 0 pattern

/-- On well-sorted pure rho processes, admission depends on the structural
congruence class rather than the spelling chosen for a representative. -/
theorem canonicalWholeNameSafe_congr {free : FreeSortContext}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free [] source)
    (targetTyped : ProcWellSorted rhoReflectivePresentation free [] target)
    (equivalent : StructuralCongruence source target) :
    canonicalWholeNameSafe source = canonicalWholeNameSafe target := by
  have same := Canonical.canonicalize_eq_of_structuralCongruence equivalent
    (PureBoundary.rhoProcWellSorted_hashSetFree sourceTyped)
    (PureBoundary.rhoProcWellSorted_hashSetFree targetTyped)
  simp only [canonicalWholeNameSafe, canonicalWholeNameSafeAt, same]

/-- A canonically admitted source has a translation of its representative.
The original spelling and representative are structurally congruent. -/
theorem canonical_source_coverage {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    StructuralCongruence source (Canonical.canonicalize source) ∧
      ∃ t, tProc (Env.empty []) (Canonical.canonicalize source) = some t := by
  constructor
  · exact Canonical.canonicalize_sound source
  · exact closed_admitted_translates_wholeNameSafe hfree
      (CanonicalTyping.canonicalize_procWellSorted [] typed) safe

private theorem canonicalize_structural_unit_bound_name :
    Canonical.canonicalize (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]) =
        .bvar 0 := by
  simp [Canonical.canonicalize, Canonical.canonicalizeList,
    Canonical.normalizeQuote, Canonical.normalizeBagElements,
    Canonical.bagSplice, Canonical.sortPatterns, Canonical.collapseBag]

/-- The structural parallel unit exposes the same bound name as `@*x`.
This is a positive control for the mathematical admission criterion. -/
theorem structural_unit_bound_name_canonical_control :
    let wrapped : Pattern := .apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none]
    canonicalWholeNameSafeAt 1 wrapped = true ∧
    tName (Env.empty []).up (Canonical.canonicalize wrapped) =
      some (quoT (.var .zero)) ∧
    StructuralCongruence wrapped (Canonical.canonicalize wrapped) := by
  dsimp [canonicalWholeNameSafeAt]
  have hsc := Canonical.canonicalize_sound
    (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PZero" []] none])
  rw [canonicalize_structural_unit_bound_name] at hsc
  rw [canonicalize_structural_unit_bound_name]
  exact ⟨by decide, rfl, hsc⟩

/-- Canonicalization does not turn an unrelated quoted output that mentions
the outer bound variable into a whole name. It remains outside the seal. -/
theorem literal_output_quote_canonical_control :
    canonicalWholeNameSafeAt 1
      (.apply "NQuote" [.apply "POutput"
        [.bvar 0, .apply "PZero" []]]) = false := by
  decide

/-- Raw authored strict-core steps remain paper steps when both endpoints
are moved to structural canonical representatives. This does not assert
that the exact canonical spelling is itself an authored executor step. -/
theorem raw_strict_step_canonical_paper {free : FreeSortContext}
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (step : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      source target) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (Canonical.canonicalize source) (Canonical.canonicalize target)) := by
  obtain ⟨paper⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoStep_sound
      typed step
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
    (StructuralCongruence.symm _ _ (Canonical.canonicalize_sound source))
    paper (Canonical.canonicalize_sound target)⟩

/-- A step on the admitted canonical representative enters the proved
strict-core simulation. Transporting arbitrary raw steps to this
representative is a separate operational theorem. -/
theorem canonical_representative_strict_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true)
    (step : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      (Canonical.canonicalize source) target) :
    ∃ s t, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps strictRules s t := by
  exact wholeNameSafe_strict_simulation hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe step

/-- The same representative-level comparison holds in the profile whose
additional Drop rule is explicitly declared. -/
theorem canonical_representative_book_simulation {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop
      (Canonical.canonicalize source) target) :
    ∃ s t, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      tProc (Env.empty []) target = some t ∧ Steps bookRules s t := by
  exact wholeNameSafe_book_simulation hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe step

/-- A strict-core step in the target is reflected by a source step after
structural rearrangement of the admitted canonical representative. -/
theorem canonical_representative_strict_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps strictRules s u →
        ∃ source' target',
          StructuralCongruence (Canonical.canonicalize source) source' ∧
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
            source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  exact wholeNameSafe_strict_reflection hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe

/-- The separately declared Drop profile has the same representative-level
reflection property. -/
theorem canonical_representative_book_reflection {free : FreeSortContext}
    (hfree : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (safe : canonicalWholeNameSafe source = true) :
    ∃ s, tProc (Env.empty []) (Canonical.canonicalize source) = some s ∧
      ∀ {u : Term sig [] Srt.pr}, Steps bookRules s u →
        ∃ source' target',
          StructuralCongruence (Canonical.canonicalize source) source' ∧
          RhoCombinedInterpretedStep.RhoStepWithDrop source' target' ∧
          ∃ t, tProc (Env.empty []) target' = some t ∧ cls t = cls u := by
  exact wholeNameSafe_book_reflection hfree
    (CanonicalTyping.canonicalize_procWellSorted [] typed) safe

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
