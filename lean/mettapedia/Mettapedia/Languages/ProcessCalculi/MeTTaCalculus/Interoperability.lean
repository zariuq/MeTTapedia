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

/-! ## Shared-core simulation layer -/

/-- Shared-core MeTTa one-step relation used for interoperability:
quote/drop plus binary bag congruence lifting. -/
inductive SharedCoreReduces : Proc → Proc → Prop where
  | drop (p : Proc) :
      SharedCoreReduces (pDrop (nQuote p)) p
  | par_left {p p' q : Proc} :
      SharedCoreReduces p p' →
      SharedCoreReduces (pPar [p, q]) (pPar [p', q])
  | par_right {p q q' : Proc} :
      SharedCoreReduces q q' →
      SharedCoreReduces (pPar [p, q]) (pPar [p, q'])

abbrev SharedCoreReducesStar := ProcessCalculi.RTClosureProp SharedCoreReduces

/-- ρ-side restricted shared-core one-step relation:
exact image of translated shared-core MeTTa one-steps. -/
def RhoSharedCoreReduces (rp rq : Pattern) : Prop :=
  ∃ p q : Proc,
    toRhoSharedProc? p = some rp ∧
    SharedCoreReduces p q ∧
    toRhoSharedProc? q = some rq

/-- Source-anchored variant of `RhoSharedCoreReduces` for simulation statements. -/
def RhoSharedCoreReducesFrom (p : Proc) (rp rq : Pattern) : Prop :=
  toRhoSharedProc? p = some rp ∧
  ∃ q : Proc, SharedCoreReduces p q ∧ toRhoSharedProc? q = some rq

/-- ρ-side restricted shared-core star relation:
exact image of translated shared-core MeTTa star reductions. -/
def RhoSharedCoreReducesStar (rp rq : Pattern) : Prop :=
  ∃ p q : Proc,
    toRhoSharedProc? p = some rp ∧
    SharedCoreReducesStar p q ∧
    toRhoSharedProc? q = some rq

/-- Source-anchored variant of `RhoSharedCoreReducesStar`. -/
def RhoSharedCoreReducesStarFrom (p : Proc) (rp rq : Pattern) : Prop :=
  toRhoSharedProc? p = some rp ∧
  ∃ q : Proc, SharedCoreReducesStar p q ∧ toRhoSharedProc? q = some rq

/-- Intrinsic inversion for the rho-side restricted shared-core one-step relation:
unpacks a translated MeTTa shared-core witness pair, without fixing any source process. -/
theorem rhoSharedCore_step_inversion
    {rp rq : Pattern}
    (hρ : RhoSharedCoreReduces rp rq) :
    ∃ p q : Proc,
      toRhoSharedProc? p = some rp ∧
      SharedCoreReduces p q ∧
      toRhoSharedProc? q = some rq := by
  exact hρ

/-- Intrinsic inversion for the rho-side restricted shared-core star relation:
unpacks a translated MeTTa shared-core star witness pair, without fixing any source process. -/
theorem rhoSharedCore_stepStar_inversion
    {rp rq : Pattern}
    (hρ : RhoSharedCoreReducesStar rp rq) :
    ∃ p q : Proc,
      toRhoSharedProc? p = some rp ∧
      SharedCoreReducesStar p q ∧
      toRhoSharedProc? q = some rq := by
  exact hρ

/-- If a shared-core step starts from a translatable source, its target is
also translatable. -/
private theorem sharedCore_target_translatable
    {p q : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp)
    (hstep : SharedCoreReduces p q) :
    ∃ rq : Pattern, toRhoSharedProc? q = some rq := by
  induction hstep generalizing rp with
  | drop p =>
      cases hp : toRhoSharedProc? p with
      | none =>
          simp [pDrop, nQuote, toRhoSharedProc?, toRhoSharedName?, hp] at htr
      | some rp0 =>
          exact ⟨rp0, by simp⟩
  | @par_left p p' q hpp' ih =>
      cases hp : toRhoSharedProc? p with
      | none =>
          simp [pPar, toRhoSharedProc?, hp] at htr
      | some rpl =>
          cases hq : toRhoSharedProc? q with
          | none =>
              simp [pPar, toRhoSharedProc?, hp, hq] at htr
          | some rpr =>
              obtain ⟨rpl', hp'⟩ := ih hp
              refine ⟨.collection .hashBag [rpl', rpr] none, ?_⟩
              simp [pPar, toRhoSharedProc?, hp', hq]
  | @par_right p q q' hqq' ih =>
      cases hp : toRhoSharedProc? p with
      | none =>
          simp [pPar, toRhoSharedProc?, hp] at htr
      | some rpl =>
          cases hq : toRhoSharedProc? q with
          | none =>
              simp [pPar, toRhoSharedProc?, hp, hq] at htr
          | some rpr =>
              obtain ⟨rpr', hq'⟩ := ih hq
              refine ⟨.collection .hashBag [rpl, rpr'] none, ?_⟩
              simp [pPar, toRhoSharedProc?, hp, hq']

/-- Forward simulation (one-step), shared-core restricted. -/
theorem sharedCore_step_forward_restricted
    {p q : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp)
    (hstep : SharedCoreReduces p q) :
    ∃ rq : Pattern,
      toRhoSharedProc? q = some rq ∧
      RhoSharedCoreReduces rp rq ∧
      RhoSharedCoreReducesFrom p rp rq := by
  rcases sharedCore_target_translatable htr hstep with ⟨rq, hq⟩
  exact ⟨rq, hq, ⟨p, q, htr, hstep, hq⟩, ⟨htr, q, hstep, hq⟩⟩

/-- Backward simulation (one-step), shared-core restricted and source-anchored. -/
theorem sharedCore_step_backward_restricted
    {p : Proc} {rp rq : Pattern}
    (hρ : RhoSharedCoreReducesFrom p rp rq) :
    ∃ q : Proc, SharedCoreReduces p q ∧ toRhoSharedProc? q = some rq := by
  rcases hρ with ⟨_, q, hstep, hq⟩
  exact ⟨q, hstep, hq⟩

/-- Combined one-step shared-core bisimulation correspondence
(forward + backward), source-anchored at `p`. -/
theorem sharedCore_step_bisimulation
    {p : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp) :
    (∀ q : Proc, SharedCoreReduces p q →
      ∃ rq : Pattern,
        toRhoSharedProc? q = some rq ∧
        RhoSharedCoreReduces rp rq ∧
        RhoSharedCoreReducesFrom p rp rq) ∧
    (∀ rq : Pattern, RhoSharedCoreReducesFrom p rp rq →
      ∃ q : Proc, SharedCoreReduces p q ∧ toRhoSharedProc? q = some rq) := by
  constructor
  · intro q hq
    exact sharedCore_step_forward_restricted htr hq
  · intro rq hρ
    exact sharedCore_step_backward_restricted hρ

/-- Forward simulation (star), shared-core restricted. -/
theorem sharedCore_stepStar_forward_restricted
    {p q : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp)
    (hsteps : SharedCoreReducesStar p q) :
    ∃ rq : Pattern,
      toRhoSharedProc? q = some rq ∧
      RhoSharedCoreReducesStar rp rq ∧
      RhoSharedCoreReducesStarFrom p rp rq := by
  induction hsteps generalizing rp with
  | refl p =>
      exact ⟨rp, htr, ⟨p, p, htr, ProcessCalculi.RTClosureProp.refl p, htr⟩,
        ⟨htr, p, ProcessCalculi.RTClosureProp.refl p, htr⟩⟩
  | @step p m q hpm hmq ih =>
      rcases sharedCore_step_forward_restricted (p := p) (q := m) (rp := rp) htr hpm with
        ⟨rm, htm, _, _⟩
      rcases ih htm with ⟨rq, htq, _, _⟩
      refine ⟨rq, htq, ?_, ?_⟩
      · exact ⟨p, q, htr, ProcessCalculi.RTClosureProp.step hpm hmq, htq⟩
      · exact ⟨htr, q, ProcessCalculi.RTClosureProp.step hpm hmq, htq⟩

/-- Backward simulation (star), shared-core restricted and source-anchored. -/
theorem sharedCore_stepStar_backward_restricted
    {p : Proc} {rp rq : Pattern}
    (hρ : RhoSharedCoreReducesStarFrom p rp rq) :
    ∃ q : Proc, SharedCoreReducesStar p q ∧ toRhoSharedProc? q = some rq := by
  rcases hρ with ⟨_, q, hsteps, hq⟩
  exact ⟨q, hsteps, hq⟩

/-- Combined star-level shared-core bisimulation correspondence
(forward + backward), source-anchored at `p`. -/
theorem sharedCore_stepStar_bisimulation
    {p : Proc} {rp : Pattern}
    (htr : toRhoSharedProc? p = some rp) :
    (∀ q : Proc, SharedCoreReducesStar p q →
      ∃ rq : Pattern,
        toRhoSharedProc? q = some rq ∧
        RhoSharedCoreReducesStar rp rq ∧
        RhoSharedCoreReducesStarFrom p rp rq) ∧
    (∀ rq : Pattern, RhoSharedCoreReducesStarFrom p rp rq →
      ∃ q : Proc, SharedCoreReducesStar p q ∧ toRhoSharedProc? q = some rq) := by
  constructor
  · intro q hq
    exact sharedCore_stepStar_forward_restricted htr hq
  · intro rq hρ
    exact sharedCore_stepStar_backward_restricted hρ

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
