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

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
