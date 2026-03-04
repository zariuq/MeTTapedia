import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Interoperability

/-!
# MeTTa-Calculus Paper Clause Map

Theorem-level index mapping clauses in:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

to concrete Lean theorem names in this repository.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-! ## Structural equivalence clauses (`equiv`) -/

/-- Paper clause: `P | 0 ≡ P` (left form). -/
theorem paper_equiv_par_nil_left (p : Proc) :
    pPar [pZero, p] ≈ₘ p := nil_left p

/-- Paper clause: `P | 0 ≡ P` (right form). -/
theorem paper_equiv_par_nil_right (p : Proc) :
    pPar [p, pZero] ≈ₘ p := nil_right p

/-- Paper clause: `P | Q ≡ Q | P`. -/
theorem paper_equiv_par_comm (p q : Proc) :
    pPar [p, q] ≈ₘ pPar [q, p] := comm p q

/-- Paper clause: associativity of parallel composition. -/
theorem paper_equiv_par_assoc (p q r : Proc) :
    pPar [pPar [p, q], r] ≈ₘ pPar [p, pPar [q, r]] := assoc p q r

/-! ## Reduction clauses (`COMM`, `REFL`) -/

/-- Paper `COMM` canary (positive): a concrete symmetric rendezvous step. -/
theorem paper_comm_positive :
    demoCommTarget ∈ step demoCommSource := by
  simpa using (show demoCommTarget ∈ step demoCommSource from by native_decide)

/-- Paper `COMM` canary (negative): mismatched terms block rendezvous. -/
theorem paper_comm_negative :
    step demoBlocked = [] := by
  simpa using (show step demoBlocked = [] from by native_decide)

/-- Paper `REFL` canary (positive): one-step reflection emits future state. -/
theorem paper_refl_positive :
    demoReflectTarget ∈ step demoReflectSource := by
  simpa using (show demoReflectTarget ∈ step demoReflectSource from by native_decide)

/-- Paper `REFL` canary (negative): no future step means no reflection output. -/
theorem paper_refl_negative :
    step (pReflect demoChan demoBlocked) = [] := by
  simpa using (show step (pReflect demoChan demoBlocked) = [] from by native_decide)

/-! ## Shared-fragment bridge clauses -/

/-- Shared fragment clause map:
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
