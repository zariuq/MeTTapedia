import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Strict
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Criteria

/-!
# The gap between the uniform criterion and Gorla's compositionality, narrowed

The strict separation (`strict_separation_solvable`) is under the uniform criterion: homomorphism of
parallel composition (Gorla's Definition 5.2) and success sensitiveness (his Property 5), with
composition of systems restricted to solvable joint knowledge. Gorla's Property 1 alone lets a
translation coordinate the two parts through a context `C|(□1; □2)`.

**What this module adds.** In his treatment of known separations (§5.1, before Theorem 5.1) Gorla
assumes that the context of parallel composition is `(νñ)(□1 | □2 | R)`: both holes at top level,
beside a coordinating process. The reflective calculus has no restriction, so such a context is
`□1 | (□2 | R)` (`coordinated R`). In the faithful calculus every such context keeps the reachable
success of its first hole (`keepsFirst_coordinated`, from persistence), so the separation holds for
every compositional translation whose parallel context is coordinated, whatever `R`
(`no_coordinatedTranslation`): from the step with restricted composition
(`step_not_into_rho_coordinated`), from the step with the none-guarded program of
`NullsOnTheStep.ParallelClosed`, and from the step with its positive program, whose tell is on an
unknown the neighbour's knowledge shares (a composition that shares unknowns, unlike the tensor).

**What stays open.** A compositional translation may put a hole under a prefix, and then the argument
fails: in the faithful calculus, the context that guards its first hole behind an input on a channel
nobody outputs on does not keep the success of `@0!(0)` (`guarded_context_fails`). Gorla's
Proposition 5.6 shows that in a valid encoding (all five properties) whose target equivalence is
reduction sensitive, both holes of the parallel context are at top level; that proposition, for this
source and this target, is the missing step from this module to his full criteria. It is not proved
here, and the separation is not claimed for contexts with guarded holes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus CompositionalTranslation KeepsFirst no_compositionalTranslation)
open ByInstantiation (G)

universe u

/-- **A coordinated parallel context**: both holes at top level, beside a fixed process `R`. -/
def coordinated (R : RhoProcess) (first second : RhoProcess) : RhoProcess := par first (par second R)

/-- **Every coordinated context keeps the reachable success of its first hole.** -/
theorem keepsFirst_coordinated (ω : G [] .nm) (R : RhoProcess) :
    KeepsFirst (rhoParallel ω) (coordinated R) :=
  fun _ second succeeds => (rhoParallel_persistent ω).succeeds_par (par second R) succeeds

/-- **No compositional translation with a coordinated parallel context** goes from a switchable
calculus into the faithful reflective calculus. -/
theorem no_coordinatedTranslation {L : ParallelCalculus.{u}} (switchable : L.Switchable)
    (ω : G [] .nm) (R : RhoProcess) (τ : CompositionalTranslation L (rhoParallel ω))
    (shape : τ.context = coordinated R) : False :=
  no_compositionalTranslation switchable (rhoParallel_persistent ω).respects τ
    (by rw [shape]; exact keepsFirst_coordinated ω R)

/-- **From the step, with composition restricted to solvable joint knowledge**: no translation of the
step into the faithful reflective calculus is compositional with a coordinated parallel context (on
composable pairs) and success sensitive. -/
theorem step_not_into_rho_coordinated (ω : G [] .nm) (R : RhoProcess)
    (τ : CompositionalTranslation (stepParallelSolvable ω) (rhoParallel ω))
    (shape : τ.context = coordinated R) : False :=
  no_coordinatedTranslation (solvable_switchable ω) ω R τ shape

/-- **From the step with the none-guarded program.** -/
theorem none_not_into_rho_coordinated (ω : G [] .nm) (R : RhoProcess)
    (τ : CompositionalTranslation NullsOnTheStep.ParallelClosed.source (rhoParallel ω))
    (shape : τ.context = coordinated R) : False :=
  no_coordinatedTranslation NullsOnTheStep.ParallelClosed.source_switchable ω R τ shape

/-- **From the step with the positive program** (a tell on a shared unknown). -/
theorem positiveTell_not_into_rho_coordinated (ω : G [] .nm) (R : RhoProcess)
    (τ : CompositionalTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource (rhoParallel ω))
    (shape : τ.context = coordinated R) : False :=
  no_coordinatedTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource_switchable ω R τ shape

/-! ## A context with a guarded hole does not keep success, in the faithful calculus -/

section Guarded

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize IsCanonical IsCanonicalList)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (rhoLanguageDefGSLT)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (input output)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls (channel zero payload)
open ByInstantiation (read)

/-- The process `T` guarded by an input on `@(@0!(0))`, a channel on which nothing outputs. -/
def guard (T : RhoProcess) : RhoProcess :=
  ⟨input Source.otherChannel T.1, (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote (.output (.quote .unit (by decide)) .unit) (by decide))
      (((rhoClosedTermWellSorted_process_iff _).mp T.2).1.weakenBoundRight _),
     by
      have sealed := ((rhoClosedTermWellSorted_process_iff _).mp T.2).2
      simp [input, Source.otherChannel, payload, output, channel, zero, binderSafeAt, binderSafeListAt,
        binderSafeAt_mono "NQuote" sealed (Nat.zero_le 1)]⟩⟩

/-- **A parallel context with its first hole guarded.** -/
def guardedContext (first second : RhoProcess) : RhoProcess := par (guard first) second

theorem guarded_payload_prime : IsPrime (input Source.otherChannel payload) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.input (.quote (.output (.quote .unit (by decide)) .unit) (by decide)) (.output (.quote .unit (by decide)) .unit), rfl⟩, ?_, ?_, ?_⟩
  · simp [input, Source.otherChannel, payload, output, channel, zero, IsCanonical, IsCanonicalList]
  · simp [input]
  · intro elements
    simp [input]

/-- The guarded output `@(@0!(0))(y).@0!(0)` beside `0` has one prime, the input. -/
theorem guarded_inventory :
    (fromProcess (guardedContext outputNil nil)).1 = {input Source.otherChannel payload} := by
  rw [guardedContext, fromProcess_par, fromProcess_primes, fromProcess_primes]
  change ReflectiveCalculus.primes (input Source.otherChannel payload) +
    ReflectiveCalculus.primes (.apply "PZero" []) = _
  rw [ReflectiveCalculus.primes_of_isPrime guarded_payload_prime,
    show ReflectiveCalculus.primes (.apply "PZero" []) = 0 from ReflectiveCalculus.primes_zero, add_zero]

/-- **In the faithful calculus, a context with a guarded hole does not keep the success of its
first hole**: `@0!(0)` shows its barb on `@0`, and guarded by an input on a channel nobody outputs on,
beside `0`, it never does. -/
theorem guarded_context_fails : ¬ KeepsFirst (rhoParallel ByInstantiation.nameZero) guardedContext := by
  intro keeps
  obtain ⟨P, run, payload', member⟩ := keeps outputNil nil ⟨outputNil, .refl, outputNil_barb⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨Q, step, _⟩
  · change _ ∈ (fromProcess (guardedContext outputNil nil)).1 at member
    rw [guarded_inventory, Multiset.mem_singleton] at member
    simp [input, output] at member
  · obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
    have inside : output rule.outputChannel rule.payload ∈ (CanonicalBag.append rule.redex residue).1 := by
      rw [CanonicalBag.append_inventory]
      exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))
    rw [← source, guarded_inventory, Multiset.mem_singleton] at inside
    simp [input, output] at inside

end Guarded

#print axioms guarded_context_fails
#print axioms keepsFirst_coordinated
#print axioms no_coordinatedTranslation
#print axioms step_not_into_rho_coordinated
#print axioms none_not_into_rho_coordinated
#print axioms positiveTell_not_into_rho_coordinated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
