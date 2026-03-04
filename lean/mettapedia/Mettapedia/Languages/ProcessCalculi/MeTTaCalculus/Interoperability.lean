import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction
import Mettapedia.CategoryTheory.GeneralizedOpenMaps
import Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-!
# MeTTa-Calculus ↔ ρ/Open-Map Interoperability (Shared Fragment)

This file provides a minimal formal bridge from the shared quote/drop/parallel
fragment of MeTTa-calculus into the existing ρ-calculus/open-map stack.

## Source attribution

Bridge motivation comes from:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

where quote/drop and parallel bag structure align with ρ-style syntax.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.CategoryTheory.GeneralizedOpenMaps

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-! ## Shared-fragment translation to ρ syntax -/

mutual
/-- Translate shared-fragment MeTTa process into ρ process syntax.

Supported constructors:
- `MZero`
- `MDrop(MQuote p)` via recursive name translation
- bag parallel composition
-/
def toRhoSharedProc? : Proc → Option Pattern
  | .apply "MZero" [] => some (.apply "PZero" [])
  | .apply "MDrop" [n] => do
      let rn ← toRhoSharedName? n
      pure (.apply "PDrop" [rn])
  | .collection .hashBag elems none => do
      let elems' ← elems.mapM toRhoSharedProc?
      pure (.collection .hashBag elems' none)
  | _ => none

/-- Translate shared-fragment MeTTa names into ρ names (`MQuote`). -/
def toRhoSharedName? : Name → Option Pattern
  | .apply "MQuote" [p] => do
      let rp ← toRhoSharedProc? p
      pure (.apply "NQuote" [rp])
  | _ => none
end

def InSharedFragment (p : Proc) : Prop := (toRhoSharedProc? p).isSome

example : toRhoSharedProc? pZero = some (.apply "PZero" []) := by
  native_decide

example : toRhoSharedName? (nQuote pZero) = some (.apply "NQuote" [.apply "PZero" []]) := by
  native_decide

example : toRhoSharedProc? (pReflect demoChan demoCommSource) = none := by
  native_decide

/-! ## Open-map kit over ρ reductions -/

/-- Open-map kit reusing the existing ρ reduction/closure layer. -/
def RhoSharedOpenInst : BisimulationKit Pattern Unit where
  step := fun p q =>
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces p q)
  stepStar := fun p q =>
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar p q)
  step_sub_star := by
    intro p q hpq
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReducesStar.single
      (Classical.choice hpq)⟩
  observable := fun _ _ => True

private def eqPathWitness (K : BisimulationKit Pattern Unit) : PathWitness K where
  rel := Eq
  symm := by
    intro p q h
    exact h.symm
  lift := by
    intro p q hpq p' hstep
    subst hpq
    exact ⟨p', K.step_sub_star hstep, rfl⟩
  obs := by
    intro p q hpq _ ho
    simpa [hpq] using ho

theorem rho_pathBisim_refl (p : Pattern) :
    PathBisim RhoSharedOpenInst p p :=
  ⟨eqPathWitness RhoSharedOpenInst, rfl⟩

/-- Shared-fragment interoperability theorem:
any successfully translated shared-fragment process has a canonical
ρ/open-map path-bisim witness at its image. -/
theorem shared_translation_pathBisim_self {p : Proc} {rp : Pattern}
    (_htr : toRhoSharedProc? p = some rp) :
    PathBisim RhoSharedOpenInst rp rp := by
  exact rho_pathBisim_refl rp

/-- Span-style corollary using the generalized-open-map `(E,S)` witness form. -/
theorem shared_translation_esBisim_self {p : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp) :
    ESBisimilar RhoSharedOpenInst rp rp := by
  exact (pathBisim_iff_esBisimilar RhoSharedOpenInst rp rp).mp
    (shared_translation_pathBisim_self htr)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
