import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
import Mettapedia.GSLT.Dynamics.ProtocolModuloEquations
import Mettapedia.GSLT.Core.StructuralIsomorphism

/-!
# The authored rho semantics over a supplied free-name context

The same declaration-derived sorted carrier supports closed terms and terms
with declared free names. Canonical equations and actual authored contextual
firings generate its modulo-equations GSLT through the shared occurrence
construction. The empty-free instance has exactly the existing closed rho
carrier, equations and endpoint steps. Reserved implementation names therefore
need no extra rho constructor, rewrite rule, or unsorted semantic universe.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-- Formation in the process fibre is the independently derived rho
sorting and quotation-scope judgment at the supplied free names. -/
theorem process_iff (free : FreeSortContext) (pattern : Pattern) :
    RhoTermWellSorted free rhoProc pattern ↔
      ProcWellSorted rhoReflectivePresentation free [] pattern ∧
        binderSafeAt "NQuote" 0 pattern = true := by
  constructor
  · rintro ⟨process | name, safe⟩
    · exact ⟨process.2, safe⟩
    · exact False.elim (rhoProc_ne_rhoName name.1)
  · rintro ⟨typed, safe⟩
    exact ⟨.inl ⟨rfl, typed⟩, safe⟩

theorem name_iff (free : FreeSortContext) (pattern : Pattern) :
    RhoTermWellSorted free rhoName pattern ↔
      NameWellSorted rhoReflectivePresentation free [] pattern ∧
        binderSafeAt "NQuote" 0 pattern = true := by
  constructor
  · rintro ⟨process | name, safe⟩
    · exact False.elim (rhoName_ne_rhoProc process.1)
    · exact ⟨name.2, safe⟩
  · rintro ⟨typed, safe⟩
    exact ⟨.inr ⟨rfl, typed⟩, safe⟩

abbrev Process (free : FreeSortContext) := RhoTerm free rhoProc

def termCanonicalize {free : FreeSortContext} {sort : LangSort rhoCalc}
    (term : RhoTerm free sort) : RhoTerm free sort := by
  refine ⟨canonicalize term.1, ?_⟩
  rcases term.2 with ⟨sorted, safe⟩
  rcases sorted with ⟨rfl, typed⟩ | ⟨rfl, typed⟩
  · exact ⟨.inl ⟨rfl, canonicalize_procWellSorted [] typed⟩,
      canonicalize_binderSafeAt term.1 0 safe⟩
  · exact ⟨.inr ⟨rfl, canonicalize_nameWellSorted [] typed⟩,
      canonicalize_binderSafeAt term.1 0 safe⟩

/-- Actual authored firings produce another inhabitant of the same fibre. -/
def stepTarget {free : FreeSortContext} (source : Process free) {target : Pattern}
    (step : RhoStep source.1 target) : Process free :=
  ⟨target, (process_iff free target).mpr (rhoStep_preserves_closed
    ((process_iff free source.1).mp source.2).1
    ((process_iff free source.1).mp source.2).2 step)⟩

/-- This is the same rewrite system compiled from the one authored rho rule set. -/
def rewriteSystem (free : FreeSortContext) : RewriteSystem where
  Sorts := LangSort rhoCalc
  procSort := rhoProc
  Term := RhoTerm free
  Reduces source target := RhoStep source.1 target.1

@[simp] theorem closed_rewriteSystem :
    rewriteSystem FreeSortContext.empty = rhoRewriteSystem := rfl

def equations (free : FreeSortContext) : Setoid (Process free) where
  r first second := canonicalize first.1 = canonicalize second.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem equations_iff_structuralCongruence {free : FreeSortContext}
    (first second : Process free) :
    (equations free).r first second ↔ StructuralCongruence first.1 second.1 := by
  exact (structuralCongruence_iff_canonicalize_eq
    (rhoProcWellSorted_hashSetFree ((process_iff free first.1).mp first.2).1)
    (rhoProcWellSorted_hashSetFree ((process_iff free second.1).mp second.2).1)).symm

/-- A real primitive firing carries its actual finite contextual depth. -/
structure RawReceipt {free : FreeSortContext} (source target : Process free) where
  depth : Nat
  firing : RhoStepAt depth source.1 target.1

theorem RawReceipt.step {free : FreeSortContext} {source target : Process free}
    (receipt : RawReceipt source target) : RhoStep source.1 target.1 :=
  ⟨receipt.depth, receipt.firing⟩

/-- Canonical equation saturation of the actual authored rho firings. -/
def theory (free : FreeSortContext) : GSLT :=
  Mettapedia.GSLT.Dynamics.ProtocolModuloEquations.saturatedSystem
    (equations free) RawReceipt

/-- The generated endpoint relation retains both supplied representatives,
with exactly one actual authored firing between their equation classes. -/
theorem step_iff {free : FreeSortContext} {source target : Process free} :
    (theory free).Step source target ↔
      ∃ redex contractum : Process free,
        (equations free).r source redex ∧ RhoStep redex.1 contractum.1 ∧
          (equations free).r contractum target := by
  constructor
  · rintro ⟨occurrence⟩
    exact ⟨occurrence.redex, occurrence.contractum, occurrence.sourceEquation,
      occurrence.receipt.step, occurrence.targetEquation⟩
  · rintro ⟨redex, contractum, before, ⟨depth, firing⟩, after⟩
    exact ⟨⟨redex, contractum, before, ⟨depth, firing⟩, after⟩⟩

/-- Every actual raw firing enters the parameterized generated semantics. -/
theorem of_step {free : FreeSortContext} {source target : Process free}
    (step : RhoStep source.1 target.1) : (theory free).Step source target :=
  step_iff.mpr ⟨source, target, rfl, step, rfl⟩

/-- The existing closed semantic theory is the empty-free specialization,
including its actual equation-saturated endpoint relation. -/
theorem closed_step_iff {source target : Process FreeSortContext.empty} :
    (theory FreeSortContext.empty).Step source target ↔
      rhoLanguageDefGSLT.Step source target := by
  exact step_iff

/-- The comparison transports equations and actual steps in both directions. -/
def closedComparison : GSLT.StructuralIsomorphism
    (theory FreeSortContext.empty) rhoLanguageDefGSLT where
  termEquiv := Equiv.refl _
  equiv_iff := fun _ _ => Iff.rfl
  step_iff := fun _ _ => closed_step_iff.symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem
