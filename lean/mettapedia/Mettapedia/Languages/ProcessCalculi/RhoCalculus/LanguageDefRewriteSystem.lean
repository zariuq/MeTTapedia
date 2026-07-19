import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# The closed rho rewrite system derived from `rhoCalc`

The executable MeTTaIL carrier is intentionally a shared raw `Pattern` AST.
The semantic input to OSLF is narrower: terms are closed and indexed by one of
the sorts authored by `rhoCalc`.  This module packages that derived carrier in
the existing `RewriteSystem` structure.  Its process reduction is the least
relation compiled from the authored `Comm` and `ParCong` rules.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- A raw pattern inhabits a closed rho sort exactly when the
declaration-derived typing judgment assigns it that sort and its de Bruijn
indices respect quotation boundaries. -/
def RhoClosedTermWellSorted (sort : LangSort rhoCalc) (pattern : Pattern) : Prop :=
  ((sort = rhoProc ∧
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] pattern) ∨
    (sort = rhoName ∧
      NameWellSorted rhoReflectivePresentation FreeSortContext.empty [] pattern)) ∧
    binderSafeAt "NQuote" 0 pattern = true

/-- Closed terms at an authored rho sort.  The syntax and both distinguished
sorts come from `rhoCalc`; this is a derived semantic carrier, not a second AST. -/
abbrev RhoClosedTerm (sort : LangSort rhoCalc) :=
  { pattern : Pattern // RhoClosedTermWellSorted sort pattern }

/-- The two authored rho sorts are distinct. -/
theorem rhoProc_ne_rhoName : rhoProc ≠ rhoName := by
  decide

theorem rhoName_ne_rhoProc : rhoName ≠ rhoProc :=
  Ne.symm rhoProc_ne_rhoName

/-- The process fiber is exactly the declaration-derived closed process
judgment. -/
theorem rhoClosedTermWellSorted_process_iff (pattern : Pattern) :
    RhoClosedTermWellSorted rhoProc pattern ↔
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] pattern ∧
        binderSafeAt "NQuote" 0 pattern = true := by
  constructor
  · intro typed
    rcases typed with ⟨sorted, safe⟩
    rcases sorted with ⟨_, processTyped⟩ | ⟨sortEquality, _⟩
    · exact ⟨processTyped, safe⟩
    · exact False.elim (rhoProc_ne_rhoName sortEquality)
  · rintro ⟨processTyped, safe⟩
    exact ⟨Or.inl ⟨rfl, processTyped⟩, safe⟩

/-- The name fiber is exactly the declaration-derived closed name judgment. -/
theorem rhoClosedTermWellSorted_name_iff (pattern : Pattern) :
    RhoClosedTermWellSorted rhoName pattern ↔
      NameWellSorted rhoReflectivePresentation FreeSortContext.empty [] pattern ∧
        binderSafeAt "NQuote" 0 pattern = true := by
  constructor
  · intro typed
    rcases typed with ⟨sorted, safe⟩
    rcases sorted with ⟨sortEquality, _⟩ | ⟨_, nameTyped⟩
    · exact False.elim (rhoName_ne_rhoProc sortEquality)
    · exact ⟨nameTyped, safe⟩
  · rintro ⟨nameTyped, safe⟩
    exact ⟨Or.inr ⟨rfl, nameTyped⟩, safe⟩

namespace RhoClosedTerm

/-- Forget the sorting witness and recover the shared executable pattern. -/
def toPattern {sort : LangSort rhoCalc} (term : RhoClosedTerm sort) : Pattern :=
  term.1

/-- Canonicalization remains within every authored rho sort. -/
def canonicalize {sort : LangSort rhoCalc}
    (term : RhoClosedTerm sort) : RhoClosedTerm sort := by
  refine ⟨Canonical.canonicalize term.1, ?_⟩
  rcases term.2 with ⟨sorted, safe⟩
  rcases sorted with ⟨rfl, processTyped⟩ | ⟨rfl, nameTyped⟩
  · exact ⟨Or.inl ⟨rfl, canonicalize_procWellSorted [] processTyped⟩,
      canonicalize_binderSafeAt term.1 0 safe⟩
  · exact ⟨Or.inr ⟨rfl, canonicalize_nameWellSorted [] nameTyped⟩,
      canonicalize_binderSafeAt term.1 0 safe⟩

@[simp]
theorem canonicalize_toPattern {sort : LangSort rhoCalc}
    (term : RhoClosedTerm sort) :
    term.canonicalize.toPattern = Canonical.canonicalize term.toPattern :=
  rfl

/-- Every raw target reached from a closed process carries a derived closed
process witness.  This discharges the scope and sorting side condition at the
rewrite-system boundary instead of assuming it at each consumer. -/
def stepTarget (source : RhoClosedTerm rhoProc) {target : Pattern}
    (step : RhoStep source.1 target) : RhoClosedTerm rhoProc := by
  refine ⟨target, (rhoClosedTermWellSorted_process_iff target).mpr ?_⟩
  have sourceClosed := (rhoClosedTermWellSorted_process_iff source.1).mp source.2
  exact rhoStep_preserves_closed sourceClosed.1 sourceClosed.2 step

@[simp]
theorem stepTarget_toPattern (source : RhoClosedTerm rhoProc)
    {target : Pattern} (step : RhoStep source.1 target) :
    (source.stepTarget step).toPattern = target :=
  rfl

end RhoClosedTerm

/-- The OSLF input mechanically derived from the strict rho `LanguageDef`:

- sorts are exactly `rhoCalc.types`;
- terms are closed values accepted by the reflective presentation;
- process reduction is the least finite contextual relation generated by the
  authored `Comm` and `ParCong` rules.
-/
def rhoRewriteSystem : RewriteSystem where
  Sorts := LangSort rhoCalc
  procSort := rhoProc
  Term := RhoClosedTerm
  Reduces source target := RhoStep source.1 target.1

/-- Reduction in the derived rewrite system is definitionally the contextual
relation compiled from `rhoCalc`. -/
theorem rhoRewriteSystem_reduces_iff
    (source target : RhoClosedTerm rhoProc) :
    rhoRewriteSystem.Reduces source target ↔ RhoStep source.1 target.1 :=
  Iff.rfl

/-- Every derived closed rewrite is sound for the established
`COMM`/`PAR`/`EQUIV` relation on raw patterns. -/
theorem rhoRewriteSystem_reduces_sound
    {source target : RhoClosedTerm rhoProc}
    (step : rhoRewriteSystem.Reduces source target) :
    Nonempty (Reduces source.1 target.1) := by
  apply rhoStep_sound
  · exact ((rhoClosedTermWellSorted_process_iff source.1).mp source.2).1
  · exact step

/-! ## Positive and negative controls -/

/-- The closed nil process inhabits the process fiber. -/
def closedNil : RhoClosedTerm rhoProc :=
  ⟨.apply "PZero" [],
    (rhoClosedTermWellSorted_process_iff _).mpr ⟨.unit, by decide⟩⟩

/-- Quoting the closed nil process inhabits the name fiber. -/
def closedNilName : RhoClosedTerm rhoName :=
  ⟨.apply "NQuote" [.apply "PZero" []],
    (rhoClosedTermWellSorted_name_iff _).mpr ⟨.quote .unit, by decide⟩⟩

/-- A closed communication source. -/
def closedCommSource : RhoClosedTerm rhoProc :=
  ⟨.collection .hashBag
      [.apply "PInput"
        [closedNilName.1, .lambda none (.apply "PZero" [])],
       .apply "POutput" [closedNilName.1, .apply "PZero" []]] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel
          (.cons (.input (.quote .unit) .unit)
            (.cons (.output (.quote .unit) .unit) .nil)),
        by decide⟩⟩

/-- The corresponding closed COMM contractum. -/
def closedCommTarget : RhoClosedTerm rhoProc :=
  ⟨.collection .hashBag [.apply "PZero" []] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons .unit .nil), by decide⟩⟩

/-- Positive: the authored COMM rule reduces the closed synchronization
source to its closed contractum. -/
theorem closedCommSource_reduces_closedCommTarget :
    rhoRewriteSystem.Reduces closedCommSource closedCommTarget := by
  have step := RhoStep.comm
    (free := FreeSortContext.empty) (bound := [])
    closedNilName.1 (.apply "PZero" []) (.apply "PZero" []) [] .unit .unit
  change RhoStep closedCommSource.1 closedCommTarget.1
  simpa [closedCommSource, closedCommTarget, closedNilName,
    semanticCommSubst, semanticSubstProc, semanticNormalizeName,
    semanticNormalizeProc, semanticNormalizeProcList] using step

/-- A free drop of a closed quotation is a valid closed process, but remains
inert because pure rho authors no executable Drop rule. -/
def closedFreeDrop : RhoClosedTerm rhoProc :=
  ⟨freeDrop,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.drop (.quote .unit), by decide⟩⟩

/-- Negative: the closed free-drop process has no derived outgoing step. -/
theorem closedFreeDrop_irreducible (target : RhoClosedTerm rhoProc) :
    ¬ rhoRewriteSystem.Reduces closedFreeDrop target := by
  exact no_freeDrop_step target.1

/-- Negative: finite-set syntax cannot inhabit the closed pure-rho process
fiber. -/
theorem finiteSet_not_closedProcess :
    ¬RhoClosedTermWellSorted rhoProc
      (.collection .hashSet [.apply "PZero" []] none) := by
  intro typed
  have processTyped := ((rhoClosedTermWellSorted_process_iff _).mp typed).1
  have pure := rhoProcWellSorted_hashSetFree processTyped
  simp [HashSetFree] at pure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
