import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.LanguageDef.ProofGSLTCyclic
import Mettapedia.GSLT.LanguageDef.ProofGSLTConversionTier

/-!
# The compiled obstructions, as instances of one criterion

Several independent results in this development say that some quantity
cannot be computed from some projection.  Each was proved separately, on its
own fixture, with its own argument.  This module exhibits them as instances
of the single criterion in `Core.NonFactorization`: a non-trivial fibre.

Doing so is not bookkeeping.  Two things fall out that were not available
while the results stood apart.

First, **generalization for free**.  The proof-irrelevance obstruction was
proved for derivation size.  Read through the criterion, the operative fact
is that the shadow is a proposition, hence a subsingleton — so *every*
invariant that separates two derivations fails to factor, simultaneously and
for the same reason.  `no_separating_invariant_survives_truncation` states
that, and the original cost result becomes one line.

Second, **both signs in one vocabulary**.  Acceptance genuinely does factor,
through the rule table alone.  Stating that as fibre-constancy over the same
definitions makes "what a projection loses" and "what it keeps" comparable
claims rather than differently-shaped ones.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.NonFactorizationInstances

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.GSLT.Core.NonFactorization

universe uV

/-! ## Proof irrelevance

The shadow is `Nonempty (Derivation …)`, a proposition.  Propositions
separate nothing, so the criterion applies to every separating invariant at
once. -/

/-- **The general form of the proof-relevance obstruction.**  Truncating a
derivation to the proposition that some derivation exists loses *every*
quantity that distinguishes two derivations of the same judgment — not one
quantity at a time, and not as a matter of proof difficulty.

Cost, provenance, which route was taken, whether two translations agree: each
is an instance obtained by naming two derivations it separates. -/
theorem no_separating_invariant_survives_truncation
    {presentation : ValidatedPresentation} {goal : Pattern} {V : Sort uV}
    (invariant : Derivation presentation goal → V)
    {left right : Derivation presentation goal}
    (separates : invariant left ≠ invariant right) :
    ¬ Factors (Ambient.truncate (presentation := presentation) (goal := goal))
        invariant :=
  NonTrivialFiber.not_factors
    { left := left, right := right, sameShadow := rfl
      differentValue := separates }

/-- The size fibre: one judgment, two derivations, different sizes. -/
def sizeFiber :
    NonTrivialFiber
      (Ambient.truncate (presentation := Ambient.ambientValidated)
        (goal := Ambient.goalJ Ambient.target))
      Ambient.derivationSize where
  left := Ambient.shortProof
  right := Ambient.longProof
  sameShadow := rfl
  differentValue := by
    rw [Ambient.shortProof_size, Ambient.longProof_size]
    decide

/-- The original cost result, recovered from the criterion. -/
theorem cost_does_not_factor :
    ¬ Factors
        (Ambient.truncate (presentation := Ambient.ambientValidated)
          (goal := Ambient.goalJ Ambient.target))
        Ambient.derivationSize :=
  sizeFiber.not_factors

/-! ## The coinductive discharge licence

Here the shadow is the checker's verdict at a fixed goal and context.  The
trivial companion and the productive cycle are accepted alike, so the verdict
cannot carry the licence. -/

/-- The discharge fibre: two accepted pre-proofs of the same goal from the
same context, with opposite licences. -/
def dischargeFiber :
    NonTrivialFiber
      (fun proof =>
        checkOpenRaw Cyclic.cyclicValidated [Cyclic.holds Cyclic.nuFormula]
          (Cyclic.holds Cyclic.nuFormula) proof)
      Cyclic.dischargeLicensed where
  left := .premise 0
  right := Cyclic.nuCycle
  sameShadow := by
    rw [Cyclic.identity_open_proof_checks, Cyclic.nuCycle_checks]
  differentValue := by
    rw [Cyclic.identity_not_licensed, Cyclic.nuCycle_licensed]
    decide

/-- The discharge licence is not a function of acceptance. -/
theorem discharge_does_not_factor_through_verdict :
    ¬ Factors
        (fun proof =>
          checkOpenRaw Cyclic.cyclicValidated [Cyclic.holds Cyclic.nuFormula]
            (Cyclic.holds Cyclic.nuFormula) proof)
        Cyclic.dischargeLicensed :=
  dischargeFiber.not_factors

/-- **Coarsening.**  A verdict enriched with the goal and the context is no
better, because the enrichment is constant here.  This is the general reason
an obstruction at a fine projection survives every weakening of it. -/
theorem discharge_does_not_factor_through_enriched_verdict :
    ¬ Factors
        (fun proof =>
          (Cyclic.holds Cyclic.nuFormula, [Cyclic.holds Cyclic.nuFormula],
            checkOpenRaw Cyclic.cyclicValidated
              [Cyclic.holds Cyclic.nuFormula]
              (Cyclic.holds Cyclic.nuFormula) proof))
        Cyclic.dischargeLicensed :=
  (dischargeFiber.coarsen
    (coarsen := fun verdict =>
      (Cyclic.holds Cyclic.nuFormula, [Cyclic.holds Cyclic.nuFormula], verdict))
    (fun _ => rfl)).not_factors

/-! ## The positive side

Acceptance loses nothing, because the fibres of the rule-table projection are
trivial.  This is the same criterion with the opposite verdict, and stating
it here makes the two comparable. -/

/-- **Acceptance factors through the rule table.**  Two presentations with
the same rule lookup accept exactly the same proofs, so nothing else about a
presentation reaches the checker. -/
theorem acceptance_constantOnFibers :
    ConstantOnFibers (fun presentation : ValidatedPresentation =>
        presentation.1.lookupRule?)
      (fun presentation : ValidatedPresentation => checkRaw presentation) := by
  intro source target agree
  funext goal proof
  exact checkRaw_congr (fun id => congrFun agree id) goal proof

end Mettapedia.GSLT.LanguageDef.ProofGSLT.NonFactorizationInstances
