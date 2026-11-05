import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Interoperability
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReduction

/-!
# MeTTa-Calculus Paper Map

Theorem-level index mapping the equations and rules in:

- `hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

to concrete Lean theorem names in this repository.

The reduction canaries below concern the corrected step `Corrected.cstep`:
COMM opens both inputs apart, unifies their patterns by the principal,
idempotent unifier and applies the dot once; REFL is recursive. The canary's
reduct is `@0 | a`; the naive reading's capturing reduct `@0 | @0` is the
subject of the separating theorems in `Corrected.Controls`. The shared-fragment
bridges retain their stated source restrictions.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-! ## Structural equivalence equations (`equiv`) -/

/-- Paper equation: `P | 0 ≡ P` (left form). -/
theorem paper_equiv_par_nil_left (p : Proc) :
    pPar [pZero, p] ≈ₘ p := nil_left p

/-- Paper equation: `P | 0 ≡ P` (right form). -/
theorem paper_equiv_par_nil_right (p : Proc) :
    pPar [p, pZero] ≈ₘ p := nil_right p

/-- Paper equation: `P | Q ≡ Q | P`. -/
theorem paper_equiv_par_comm (p q : Proc) :
    pPar [p, q] ≈ₘ pPar [q, p] := comm p q

/-- Paper equation: associativity of parallel composition. -/
theorem paper_equiv_par_assoc (p q r : Proc) :
    pPar [pPar [p, q], r] ≈ₘ pPar [p, pPar [q, r]] := assoc p q r

/-! ## Reduction rules (`COMM`, `REFL`) -/

/-- The canary's `COMM` reduct `@0 | a`: the second input's free `a` stays free. -/
def demoCommReduct : Proc := par (nQuote pZero) (.fvar "a")

/-- The listener `REFL` emits for the canary. -/
def demoReflectReduct : Proc := pFor (tProc demoCommReduct) demoChan pZero

/-- Paper `COMM` canary (positive): a concrete symmetric rendezvous step. -/
theorem paper_comm_positive :
    Corrected.cstep demoCommSource = [demoCommReduct] := by
  decide +kernel

/-- Paper `COMM` canary (negative): mismatched terms block rendezvous. -/
theorem paper_comm_negative :
    Corrected.cstep demoBlocked = [] := by
  decide +kernel

/-- Paper `REFL` canary (positive): reflection emits the future state. -/
theorem paper_refl_positive :
    Corrected.cstep demoReflectSource = [demoReflectReduct] := by
  decide +kernel

/-- Paper `REFL` canary (negative): no future step means no reflection output. -/
theorem paper_refl_negative :
    Corrected.cstep (pReflect demoChan demoBlocked) = [] := by
  decide +kernel

/-- Paper `COMM` is a step of the relational rules: the corrected reduct is
related to the canary under the variable convention. -/
theorem paper_comm_relational :
    Corrected.Step Corrected.conventional demoCommSource demoCommReduct :=
  Corrected.cstep_sound (by decide +kernel) (by rw [paper_comm_positive]; exact List.mem_singleton_self _)

/-! ## The corrected `COMM` and its metatheory -/

/-- Soundness: every reduct of the corrected step of a calculus process is a
step of the relational rules under the variable convention. -/
theorem paper_comm_sound {p q : Proc} (inCalc : Corrected.calcTerm p = true)
    (reduct : q ∈ Corrected.cstep p) : Corrected.Step Corrected.conventional p q :=
  Corrected.cstep_sound inCalc reduct

/-- Completeness up to alpha on the closing fragment. -/
theorem paper_comm_complete {p q : Proc} (step : Corrected.Step Corrected.closing p q) :
    ∃ q' ∈ Corrected.cstep p, Corrected.AlphaEq q' q :=
  Corrected.cstep_complete step

/-- Alpha-invariance: alpha-equivalent processes have the same reducts. -/
theorem paper_comm_alpha_invariant {p p' : Proc} (alpha : Corrected.AlphaEq p p') :
    Corrected.cstep p = Corrected.cstep p' :=
  Corrected.cstep_alpha_invariant alpha

/-- The unifier `COMM` uses is principal. -/
theorem paper_comm_unifier_principal {t u : Term} {bs : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
    (found : Corrected.unify t u = some bs) : Corrected.Principal t u bs :=
  Corrected.unify_principal found

/-! ## Shared-fragment bridge theorems -/

/-- Shared fragment map:
successful MeTTa→ρ translation yields a canonical open-map path-bisim witness
at the translated image. -/
theorem paper_shared_to_rho_openmap_self {p : Proc} {rp : Proc}
    (htr : toRhoSharedProc? p = some rp) :
    Mettapedia.CategoryTheory.GeneralizedOpenMaps.PathBisim RhoSharedOpenInst rp rp :=
  shared_translation_pathBisim_self htr

/-- Shared-core forward simulation map (step level). -/
theorem paper_shared_to_rho_forward_simulation_step
    {p q : Proc} {rp : Proc}
    (htr : toRhoSharedProc? p = some rp)
    (hstep : SharedCoreReduces p q) :
    ∃ rq : Proc,
      toRhoSharedProc? q = some rq ∧
      RhoSharedCoreReduces rp rq ∧
      RhoSharedCoreReducesFrom p rp rq :=
  sharedCore_step_forward_restricted htr hstep

/-- Shared-core backward simulation map (step level, source-anchored). -/
theorem paper_shared_to_rho_backward_simulation_step
    {p : Proc} {rp rq : Proc}
    (hρ : RhoSharedCoreReducesFrom p rp rq) :
    ∃ q : Proc, SharedCoreReduces p q ∧ toRhoSharedProc? q = some rq :=
  sharedCore_step_backward_restricted hρ

/-- Shared-core backward inversion map (step level, intrinsic rho-side relation). -/
theorem paper_shared_to_rho_backward_inversion_step
    {rp rq : Proc}
    (hρ : RhoSharedCoreReduces rp rq) :
    ∃ p q : Proc,
      toRhoSharedProc? p = some rp ∧
      SharedCoreReduces p q ∧
      toRhoSharedProc? q = some rq :=
  rhoSharedCore_step_inversion hρ

/-- Shared-core bisimulation map (step level, forward + backward). -/
theorem paper_shared_to_rho_step_bisimulation
    {p : Proc} {rp : Proc}
    (htr : toRhoSharedProc? p = some rp) :
    (∀ q : Proc, SharedCoreReduces p q →
      ∃ rq : Proc,
        toRhoSharedProc? q = some rq ∧
        RhoSharedCoreReduces rp rq ∧
        RhoSharedCoreReducesFrom p rp rq) ∧
    (∀ rq : Proc, RhoSharedCoreReducesFrom p rp rq →
      ∃ q : Proc, SharedCoreReduces p q ∧ toRhoSharedProc? q = some rq) :=
  sharedCore_step_bisimulation htr

/-- Shared-core forward simulation map (star level). -/
theorem paper_shared_to_rho_forward_simulation_stepStar
    {p q : Proc} {rp : Proc}
    (htr : toRhoSharedProc? p = some rp)
    (hsteps : SharedCoreReducesStar p q) :
    ∃ rq : Proc,
      toRhoSharedProc? q = some rq ∧
      RhoSharedCoreReducesStar rp rq ∧
      RhoSharedCoreReducesStarFrom p rp rq :=
  sharedCore_stepStar_forward_restricted htr hsteps

/-- Shared-core backward simulation map (star level, source-anchored). -/
theorem paper_shared_to_rho_backward_simulation_stepStar
    {p : Proc} {rp rq : Proc}
    (hρ : RhoSharedCoreReducesStarFrom p rp rq) :
    ∃ q : Proc, SharedCoreReducesStar p q ∧ toRhoSharedProc? q = some rq :=
  sharedCore_stepStar_backward_restricted hρ

/-- Shared-core backward inversion map (star level, intrinsic rho-side relation). -/
theorem paper_shared_to_rho_backward_inversion_stepStar
    {rp rq : Proc}
    (hρ : RhoSharedCoreReducesStar rp rq) :
    ∃ p q : Proc,
      toRhoSharedProc? p = some rp ∧
      SharedCoreReducesStar p q ∧
      toRhoSharedProc? q = some rq :=
  rhoSharedCore_stepStar_inversion hρ

/-- Shared-core bisimulation map (star level, forward + backward). -/
theorem paper_shared_to_rho_stepStar_bisimulation
    {p : Proc} {rp : Proc}
    (htr : toRhoSharedProc? p = some rp) :
    (∀ q : Proc, SharedCoreReducesStar p q →
      ∃ rq : Proc,
        toRhoSharedProc? q = some rq ∧
        RhoSharedCoreReducesStar rp rq ∧
        RhoSharedCoreReducesStarFrom p rp rq) ∧
    (∀ rq : Proc, RhoSharedCoreReducesStarFrom p rp rq →
      ∃ q : Proc, SharedCoreReducesStar p q ∧ toRhoSharedProc? q = some rq) :=
  sharedCore_stepStar_bisimulation htr

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
