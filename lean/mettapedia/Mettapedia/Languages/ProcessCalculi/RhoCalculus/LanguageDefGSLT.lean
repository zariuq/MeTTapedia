import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# The rho GSLT derived from `rhoCalc`

The authored rho `LanguageDef` supplies the grammar and primitive contextual
rules.  `LanguageDefRewriteSystem` derives its closed, sort-indexed term
carrier and process rewrite system.  This module adds the equational quotient
required by a graph-structured lambda theory:

- process equations are equality of the proved canonical representatives;
- rewriting starts from that canonical representative and uses only the
  rules derived from `rhoCalc`;
- targets are taken modulo the same process equations.

The unrestricted raw-pattern `StructuralCongruence` remains useful as a
representation-level soundness target, but it is not used as the semantic
setoid because it does not preserve the authored rho sorts.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- The closed process fiber derived from the process sort authored by
`rhoCalc`. -/
abbrev RhoProcess := RhoClosedTerm rhoProc

/-- Sort-respecting rho process equations, computed by the canonical section.

Both arguments already inhabit the closed process fiber, so parallel laws can
never be transported into a name position merely because both constructs use
the shared raw `Pattern` representation. -/
def rhoProcessEquations : Setoid RhoProcess where
  r left right :=
    Canonical.canonicalize left.1 = Canonical.canonicalize right.1
  iseqv :=
    { refl := fun _ => rfl
      symm := fun equality => equality.symm
      trans := fun first second => first.trans second }

@[simp]
theorem rhoProcessEquations_iff (left right : RhoProcess) :
    rhoProcessEquations.r left right ↔
      Canonical.canonicalize left.1 = Canonical.canonicalize right.1 :=
  Iff.rfl

/-- Equivalent closed processes compute to the same canonical term, including
its declaration-derived sorting witness. -/
theorem canonicalize_eq_of_rhoProcessEquations
    {left right : RhoProcess}
    (equivalent : rhoProcessEquations.r left right) :
    left.canonicalize = right.canonicalize := by
  apply Subtype.ext
  exact equivalent

/-- On the derived closed process carrier, canonical equality and the
established pure structural equations coincide exactly.  The typing witnesses
are essential: unrestricted raw structural congruence is not sort preserving. -/
theorem rhoProcessEquations_iff_structuralCongruence
    (left right : RhoProcess) :
    rhoProcessEquations.r left right ↔
      StructuralCongruence left.1 right.1 := by
  have leftTyped := ((rhoClosedTermWellSorted_process_iff left.1).mp left.2).1
  have rightTyped := ((rhoClosedTermWellSorted_process_iff right.1).mp right.2).1
  have leftPure := PureBoundary.rhoProcWellSorted_hashSetFree leftTyped
  have rightPure := PureBoundary.rhoProcWellSorted_hashSetFree rightTyped
  exact (structuralCongruence_iff_canonicalize_eq leftPure rightPure).symm

/-- Compute one representative for every closed-process equation class. -/
def rhoProcessRepresentative : Quotient rhoProcessEquations → RhoProcess :=
  Quotient.lift RhoClosedTerm.canonicalize
    (fun _ _ equivalent => canonicalize_eq_of_rhoProcessEquations equivalent)

/-- The computed representative remains in its original equation class. -/
theorem rhoProcessRepresentative_spec
    (equivalenceClass : Quotient rhoProcessEquations) :
    Quotient.mk rhoProcessEquations
        (rhoProcessRepresentative equivalenceClass) = equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro process
  apply Quotient.sound
  change Canonical.canonicalize (Canonical.canonicalize process.1) =
    Canonical.canonicalize process.1
  exact Canonical.canonicalize_idempotent process.1

@[simp]
theorem rhoProcessRepresentative_mk (process : RhoProcess) :
    rhoProcessRepresentative (Quotient.mk rhoProcessEquations process) =
      process.canonicalize :=
  rfl

/-- One rho process rewrite modulo the authored equations.

The middle edge is a step of the `rhoCalc`-derived rewrite system.  The two
outer witnesses are the standard source and target transports through the
equational quotient. -/
def rhoProcessRewrites (source target : RhoProcess) : Prop :=
  ∃ redex contractum : RhoProcess,
    rhoProcessEquations.r source redex ∧
    rhoRewriteSystem.Reduces redex contractum ∧
    rhoProcessEquations.r contractum target

/-- Process rewriting is invariant under changing the source presentation. -/
theorem rhoProcessRewrites_resp_left :
    ∀ {source source' target : RhoProcess},
      rhoProcessEquations.r source source' →
      rhoProcessRewrites source target →
      ∃ target', rhoProcessRewrites source' target' ∧
        rhoProcessEquations.r target target' := by
  intro source source' target sourceEquivalent
  rintro ⟨redex, contractum, redexEquivalent, baseStep, targetEquivalent⟩
  exact ⟨target,
    ⟨redex, contractum, sourceEquivalent.symm.trans redexEquivalent,
      baseStep, targetEquivalent⟩,
    rfl⟩

/-- Process rewriting is invariant under changing the target presentation. -/
theorem rhoProcessRewrites_resp_right :
    ∀ {source target target' : RhoProcess},
      rhoProcessRewrites source target →
      rhoProcessEquations.r target target' →
      rhoProcessRewrites source target' := by
  intro source target target'
  rintro ⟨redex, contractum, redexEquivalent, baseStep, targetEquivalent⟩ equivalent
  exact ⟨redex, contractum, redexEquivalent, baseStep,
    targetEquivalent.trans equivalent⟩

/-- The graph-structured lambda theory obtained from the one authored rho
language definition. -/
def rhoLanguageDefGSLT : GSLT where
  Term := RhoProcess
  equations := rhoProcessEquations
  rewrites := rhoProcessRewrites
  rewrites_resp_left := rhoProcessRewrites_resp_left
  rewrites_resp_right := rhoProcessRewrites_resp_right

/-- Every authored base step embeds into the equation-saturated rho GSLT. -/
theorem rhoRewriteSystem_reduces_to_gsltStep
    {source target : RhoProcess}
    (step : rhoRewriteSystem.Reduces source target) :
    rhoLanguageDefGSLT.Step source target :=
  ⟨source, target, rfl, step, rfl⟩

/-- Canonical process equations are sound for the established raw structural
congruence.  This is a forgetful soundness map, not the semantic definition of
the sorted equations. -/
theorem rhoProcessEquations_sound
    {left right : RhoProcess}
    (equivalent : rhoProcessEquations.r left right) :
    StructuralCongruence left.1 right.1 :=
  structuralCongruence_of_canonicalize_eq equivalent

/-- Every step of the derived rho GSLT forgets to an established
`COMM`/`PAR`/`EQUIV` reduction on raw patterns. -/
theorem rhoProcessRewrites_sound
    {source target : RhoProcess}
    (step : rhoProcessRewrites source target) :
    Nonempty (Reduces source.1 target.1) := by
  obtain ⟨redex, contractum, redexEquivalent, baseStep,
    targetEquivalent⟩ := step
  obtain ⟨baseStep⟩ := rhoRewriteSystem_reduces_sound baseStep
  exact ⟨Reduces.equiv
    (rhoProcessEquations_sound redexEquivalent)
    baseStep
    (rhoProcessEquations_sound targetEquivalent)⟩

theorem rhoLanguageDefGSLT_step_sound
    {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    Nonempty (Reduces source.1 target.1) :=
  rhoProcessRewrites_sound step

/-! ## Positive and negative controls -/

/-- Positive equation control: a singleton parallel presentation and its sole
component denote the same closed process. -/
theorem closedParallelSingleton_equivalent_nil :
    rhoProcessEquations.r closedCommTarget closedNil := by
  simpa [rhoProcessEquations, closedCommTarget, closedNil] using
    (Canonical.canonicalize_parallel_singleton (.apply "PZero" []))

/-- Negative equation control: executable free Drop is not smuggled into the
equational theory. -/
theorem closedFreeDrop_not_equivalent_nil :
    ¬rhoProcessEquations.r closedFreeDrop closedNil := by
  exact Canonical.canonicalize_free_drop_not_process

/-- Positive: the closed COMM example is a step of the derived GSLT. -/
theorem closedCommSource_step :
    rhoLanguageDefGSLT.Step closedCommSource closedCommTarget := by
  exact rhoRewriteSystem_reduces_to_gsltStep
    closedCommSource_reduces_closedCommTarget

/-- Every raw `COMM`/`PAR`/`EQUIV` source contains an input/output action.
This small invariant is useful for semantic negative controls, because it is
preserved by the representation-level structural equations. -/
theorem ioCount_pos_of_reduces
    {source target : Pattern} (step : Reduces source target) :
    0 < ioCount source := by
  induction step with
  | comm =>
      simp [ioCount]
  | @equiv source redex target contractum sourceEquivalent _ _ inductionHypothesis =>
      have countEquality := ioCount_SC sourceEquivalent
      omega
  | par _ inductionHypothesis =>
      simp [ioCount] at inductionHypothesis ⊢
      omega
  | par_any _ inductionHypothesis =>
      simp [ioCount, List.map_append, List.sum_append] at inductionHypothesis ⊢
      omega

/-- Negative: a closed free Drop remains inert even after passing through the
canonical equation section. -/
theorem closedFreeDrop_irreducible_in_gslt (target : RhoProcess) :
    ¬rhoLanguageDefGSLT.Step closedFreeDrop target := by
  intro step
  obtain ⟨rawStep⟩ := rhoLanguageDefGSLT_step_sound step
  have positive := ioCount_pos_of_reduces rawStep
  simp [closedFreeDrop, DerivedContextualStep.freeDrop, ioCount] at positive

/-- Negative: quotation is a name constructor, so a quoted redex cannot be
misclassified as a process on which the GSLT may step. -/
theorem quotedComm_not_process :
    ¬RhoClosedTermWellSorted rhoProc commUnderQuote := by
  intro typed
  have processTyped := ((rhoClosedTermWellSorted_process_iff _).mp typed).1
  generalize patternEq : commUnderQuote = pattern at processTyped
  cases processTyped <;>
    simp_all [commUnderQuote, rhoReflectivePresentation]

/-- Negative: finite-set contexts are not terms of the pure process fiber. -/
theorem finiteSet_context_not_process :
    ¬RhoClosedTermWellSorted rhoProc commUnderSet := by
  intro typed
  have processTyped := ((rhoClosedTermWellSorted_process_iff _).mp typed).1
  have pure := PureBoundary.rhoProcWellSorted_hashSetFree processTyped
  simp [commUnderSet, HashSetFree] at pure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
