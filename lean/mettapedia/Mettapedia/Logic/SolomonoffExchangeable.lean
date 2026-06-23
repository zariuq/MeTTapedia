import Mettapedia.Logic.Exchangeability
import Mettapedia.Logic.DeFinetti
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.SolomonoffMeasure
import Mettapedia.Logic.SolomonoffPrior
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.MarkovDeFinettiMixtureRepresentation
import Mathlib.Data.List.OfFn

/-!
# Solomonoff Induction Restricted to Exchangeable and Markov Domains

This file formalizes the **predictor-level** collapse behind νPLN:
Solomonoff-style prediction restricted to a structured binary domain factors through
the corresponding sufficient statistic.

## The Key Insight

Solomonoff's universal prior M(x) assigns probability to all computable sequences.
When restricted to **exchangeable binary** sequences:

1. Exchangeability implies probabilities depend only on counts (combinatorics).
2. Therefore the Solomonoff-style predictor `μ(x++[b]) / μ(x)` depends only on `(n⁺, n⁻)`.
3. BinaryEvidence accumulation is just `hplus` on evidence counts.

When restricted to **Markov-exchangeable binary** sequences:

1. One-step probabilities depend only on the transition-count summary `(counts,last)`.
2. In the binary presentation this becomes `(ff,ft,tf,tt,lastBit)`.
3. The file packages both the general `Fin 2` and explicit `Bool` surfaces.

Note: The full measure-theoretic de Finetti representation theorem IS formalized in
`Mettapedia.Logic.DeFinetti` (with zero sorries), including the Hausdorff moment theorem.
This file focuses on the semimeasure-level predictor collapse, which is the direct
justification for PLN BinaryEvidence.

## Domain Characterization

**Theorem (predictor form)**: For the class of exchangeable binary environments, Solomonoff
prediction collapses from "arbitrary program mixture state" to just `(n⁺, n⁻)` (BinaryEvidence).

**Full de Finetti** (proven in `DeFinetti.lean`): Exchangeable ↔ Bernoulli mixture representation.
This gives the closed form of the predictor (Beta-Bernoulli conjugacy).

## References

- [LLM as Solomonoff Approximation](https://arxiv.org/abs/2505.15784) - domain restrictions
- [McCall 2004](https://onlinelibrary.wiley.com/doi/abs/10.1111/j.0026-1386.2004.00190.x) -
  Kolmogorov, Solomonoff, de Finetti connections
- [Diaconis & Freedman 1980](https://projecteuclid.org/journals/annals-of-probability/volume-8/issue-4/Finite-Exchangeable-Sequences/10.1214/aop/1176994663.full) - finite exchangeability

-/

namespace Mettapedia.Logic.SolomonoffExchangeable

open scoped ENNReal

open Mettapedia.Logic.SolomonoffPrior
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.EvidenceQuantale

/-! ## Exchangeable Programs -/

section ExchangeablePrograms

/-- A semimeasure on finite strings is *exchangeable* if permuting coordinates of any
    length-`n` Boolean vector does not change the weight assigned to that string. -/
def SemimeasureExchangeable (μ : BinString → ℝ) : Prop :=
  ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin n), ∀ xs : Fin n → Bool,
    μ (List.ofFn xs) = μ (List.ofFn (xs ∘ σ.symm))

/-! ### Basic Consequence: Dependence Only on Counts

The key structural consequence we use from exchangeability is count-invariance: two length-`n`
bitstrings with the same number of `true`s get the same weight.

This is the semimeasure analogue of `Exchangeability.exchangeable_same_counts_same_prob` and is the
exact statement needed for the "sufficient statistics = (n⁺, n⁻)" story at the Solomonoff level.
-/

theorem semimeasureExchangeable_same_counts {μ : BinString → ℝ} (hexch : SemimeasureExchangeable μ)
    {n : ℕ} (xs₁ xs₂ : Fin n → Bool) (hcount : countTrue xs₁ = countTrue xs₂) :
    μ (List.ofFn xs₁) = μ (List.ofFn xs₂) := by
  classical
  obtain ⟨σ, hσ⟩ := same_counts_exists_perm (n := n) xs₁ xs₂ hcount
  -- `hexch` gives invariance under permutation; choose the permutation witnessing `xs₂ = xs₁ ∘ σ`.
  have hperm := hexch n σ.symm xs₁
  -- `hperm : μ(ofFn xs₁) = μ(ofFn (xs₁ ∘ σ))`
  simpa [hσ] using hperm

/-- The cylinder semimeasure induced by a monotone machine and a finite program set
    is exchangeable. This is the semantic notion we need for "exchangeable programs". -/
def ProgramsExchangeable (U : MonotoneMachine) (programs : Finset BinString) : Prop :=
  SemimeasureExchangeable (fun x => U.cylinderMeasure programs x)

/- The class of programs that generate exchangeable binary sequences.

   In this file we avoid a per-program predicate because the current Solomonoff
   development treats exchangeability as a property of the *mixture semimeasure*
   over a program set.
-/
-- NOTE: for the current Solomonoff formalization, exchangeability is a property of the
-- *mixture semimeasure* over a program set, not of a single deterministic program.
-- We therefore work with `ProgramsExchangeable` instead of a per-program predicate.

/-! ### Markov de Finetti Bridge

The theorem below packages the class-restricted row-process consequences already
proved in the Markov de Finetti development at a surface that downstream
Solomonoff-style predictor results can call directly.
-/

section MarkovDeFinettiBridge

open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence

variable {k : ℕ}

/-- Under Markov exchangeability plus strong recurrence, one-step prediction
depends only on the transition-count summary of a nonempty history. -/
theorem markovExchangeable_strongRecurrence_predictor_eq_of_same_summary
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
    (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
    (hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
    (x : Fin k) :
    μ (xs ++ [x]) = μ (ys ++ [x]) := by
  exact
    mu_append_singleton_eq_of_same_summary_list
      (k := k) (μ := μ) (hμ := hμ) xs ys hlen hx hstart hsum x

/-- Under Markov exchangeability plus strong recurrence, the class-restricted
row law factors through the canonical directing row kernel on finite coordinate
projections. -/
theorem markovExchangeable_strongRecurrence_restrictClass_rowLaw_factorizes
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (C : Set (Fin k))
    (i : Fin k) (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (rowProcessLaw_restrictClass (k := k) C P i)
      =
    (rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  exact
    rowProcessLaw_restrictClass_factorizes_of_markovExchangeable_strongRecurrence
      (k := k) μ hμ P hExt hStrRec C i m sel hsel

/-- Under Markov exchangeability plus strong recurrence inside a class `C`, the
class-restricted row law for each `i ∈ C` factors through the canonical
directing row kernel on finite coordinate projections. -/
theorem markovExchangeable_strongRecurrenceInClass_restrictClass_rowLaw_factorizes
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : StrongRecurrenceInClass (k := k) C P)
    (i : Fin k) (hi : i ∈ C)
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (rowProcessLaw_restrictClass (k := k) C P i)
      =
    (rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  exact
    rowProcessLaw_restrictClass_factorizes_of_markovExchangeable_strongRecurrenceInClass
      (k := k) μ hμ P hExt C hStrRecC i hi m sel hsel

/-- Public bridge from Markov-exchangeable strong-recurrence data to two
class-restricted consequences used by downstream predictor arguments:

1. predictor equality depends only on the transition-count state;
2. the class-restricted row law factors through the canonical directing row
   kernel on all finite coordinate selections.

This theorem packages the new public `MixtureRepresentation` wrappers at the
same abstraction level as the predictor story, instead of leaving the rowwise
factorization only as internal bridge infrastructure. -/
theorem markovExchangeable_strongRecurrence_class_transition_structure
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (C : Set (Fin k)) :
    (∀ (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
      (x : Fin k),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (i : Fin k) (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
      Measure.map
          (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
          (rowProcessLaw_restrictClass (k := k) C P i)
        =
      (rowProcessLaw_restrictClass (k := k) C P i).bind
        (fun r =>
          Measure.pi
            (fun _ : Fin m =>
              (directingRowKernel (k := k) P i r : Measure (Fin k))))) := by
  refine ⟨?_, ?_⟩
  · intro xs ys hlen hx hstart hsum x
    exact
      markovExchangeable_strongRecurrence_predictor_eq_of_same_summary
        (k := k) (μ := μ) (hμ := hμ) xs ys hlen hx hstart hsum x
  · intro i m sel hsel
    exact
      markovExchangeable_strongRecurrence_restrictClass_rowLaw_factorizes
        (k := k) μ hμ P hExt hStrRec C i m sel hsel

/-- Class-recurrence analogue of
`markovExchangeable_strongRecurrence_class_transition_structure`.

The predictor-equality half still only uses Markov exchangeability. The
factorization half is available for each row index `i ∈ C`, which is the exact
scope supported by class recurrence. -/
theorem markovExchangeable_strongRecurrenceInClass_class_transition_structure
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (C : Set (Fin k))
    (hStrRecC : StrongRecurrenceInClass (k := k) C P) :
    (∀ (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
      (x : Fin k),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (i : Fin k), i ∈ C →
      ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map
            (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw_restrictClass (k := k) C P i)
          =
        (rowProcessLaw_restrictClass (k := k) C P i).bind
          (fun r =>
            Measure.pi
              (fun _ : Fin m =>
                (directingRowKernel (k := k) P i r : Measure (Fin k))))) := by
  refine ⟨?_, ?_⟩
  · intro xs ys hlen hx hstart hsum x
    exact
      markovExchangeable_strongRecurrence_predictor_eq_of_same_summary
        (k := k) (μ := μ) (hμ := hμ) xs ys hlen hx hstart hsum x
  · intro i hi m sel hsel
    exact
      markovExchangeable_strongRecurrenceInClass_restrictClass_rowLaw_factorizes
        (k := k) μ hμ P hExt C hStrRecC i hi m sel hsel

/-- The class-restricted public Markov de Finetti surface supplies exactly the
same downstream transition-structure package as the explicit theorem above,
but without requiring callers to thread the extension law and recurrence proof
manually. -/
theorem classRestrictedMarkovMixtureSurface_class_transition_structure
    (M : Mettapedia.Logic.ClassRestrictedMarkovMixtureSurface k C μ) :
    (∀ (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
      (x : Fin k),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (i : Fin k), i ∈ C →
      ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map
            (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw_restrictClass (k := k) C M.extensionLaw i)
          =
        (rowProcessLaw_restrictClass (k := k) C M.extensionLaw i).bind
          (fun r =>
            Measure.pi
              (fun _ : Fin m =>
                (directingRowKernel (k := k) M.extensionLaw i r : Measure (Fin k))))) := by
  exact Mettapedia.Logic.ClassRestrictedMarkovMixtureSurface.class_transition_structure M

end MarkovDeFinettiBridge

section MarkovBinaryBridge

open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-- Public downstream package for the binary Markov-domain conditions used by
the post-νPLN bridge. The law is Markov-exchangeable, lower semicomputable, and
paired with a Markov-Dirichlet reference family for the same binary alphabet. -/
structure MarkovBinaryPLNDomainConditions
    (μ : FiniteAlphabet.PrefixMeasure (Fin 2)) where
  markovExchangeable : MarkovExchangeablePrefixMeasure (k := 2) μ
  lowerSemicomputable :
    Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
      (α := Fin 2) μ
  prior : Fin 2 → Mettapedia.Logic.EvidenceDirichlet.DirichletParams 2

/-- The explicit binary `(ff,ft,tf,tt,lastBit)` summary agrees exactly with the
generic `Fin 2` transition-summary presentation. This is the equivalence handle
for moving between the abstract Markov domain theorem and the binary νPLN-facing
surface. -/
theorem markovExchangeable_binary_summary_presentations_agree
    (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) :
    binarySummary xs = binarySummary ys ↔
      TransCounts.summary (k := 2) (encodeBoolWord xs) =
        TransCounts.summary (k := 2) (encodeBoolWord ys) := by
  exact binarySummary_eq_iff_fin2Summary_eq xs ys

/-- Binary Markov-domain characterization in the generic `Fin 2` presentation:
the sufficient state is the transition-count matrix together with the current
state. -/
theorem markovExchangeable_binary_domain_characterization_fin2
    (μ : FiniteAlphabet.PrefixMeasure (Fin 2))
    (hμ : MarkovExchangeablePrefixMeasure (k := 2) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin 2) μ)
    (prior : Fin 2 → Mettapedia.Logic.EvidenceDirichlet.DirichletParams 2) :
    (∀ (xs ys : List (Fin 2)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys)
      (x : Fin 2),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (xs ys : List (Fin 2)) (_hx : 0 < xs.length)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys),
      ∃ state : TransCounts 2 × Fin 2,
        TransCounts.summary (k := 2) xs = some state ∧
        TransCounts.summary (k := 2) ys = some state ∧
        ∀ a : Fin 2,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior) (xs ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior) xs *
              ENNReal.ofReal (MarkovDirichlet.stepProb prior state.1 state.2 a) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior) (ys ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior) ys *
              ENNReal.ofReal (MarkovDirichlet.stepProb prior state.1 state.2 a)) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact markovExchangeable_domain_characterization_fin2 (μ := μ) hμ hμLSC prior

/-- The same binary Markov-domain characterization, but presented on `Bool`
histories using the explicit state `(ff,ft,tf,tt,lastBit)`. Together with
`markovExchangeable_binary_summary_presentations_agree`, this gives the νPLN-
facing binary surface without changing the underlying theorem. -/
theorem markovExchangeable_binary_domain_characterization_bool
    (μ : FiniteAlphabet.PrefixMeasure (Fin 2))
    (hμ : MarkovExchangeablePrefixMeasure (k := 2) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin 2) μ)
    (prior : Fin 2 → Mettapedia.Logic.EvidenceDirichlet.DirichletParams 2) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys)
      (x : Bool),
      μ (encodeBoolWord (xs ++ [x])) = μ (encodeBoolWord (ys ++ [x]))) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact markovExchangeable_domain_characterization_bool (μ := μ) hμ hμLSC prior

namespace MarkovBinaryPLNDomainConditions

variable {μ : FiniteAlphabet.PrefixMeasure (Fin 2)}

/-- Packaged binary Markov-domain theorem in the generic `Fin 2` presentation. -/
theorem domain_characterization_fin2
    (hdom : MarkovBinaryPLNDomainConditions μ) :
    (∀ (xs ys : List (Fin 2)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys)
      (x : Fin 2),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (xs ys : List (Fin 2)) (_hx : 0 < xs.length)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys),
      ∃ state : TransCounts 2 × Fin 2,
        TransCounts.summary (k := 2) xs = some state ∧
        TransCounts.summary (k := 2) ys = some state ∧
        ∀ a : Fin 2,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (xs ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) xs *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (ys ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) ys *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a)) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact
    markovExchangeable_binary_domain_characterization_fin2
      (μ := μ) hdom.markovExchangeable hdom.lowerSemicomputable hdom.prior

/-- Packaged binary Markov-domain theorem in the explicit `Bool` presentation. -/
theorem domain_characterization_bool
    (hdom : MarkovBinaryPLNDomainConditions μ) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys)
      (x : Bool),
      μ (encodeBoolWord (xs ++ [x])) = μ (encodeBoolWord (ys ++ [x]))) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact
    markovExchangeable_binary_domain_characterization_bool
      (μ := μ) hdom.markovExchangeable hdom.lowerSemicomputable hdom.prior

/-- Under the packaged binary Markov-domain conditions, one-step prediction for
the true environment depends only on the generic `Fin 2` summary state. -/
theorem predictor_eq_of_same_summary_fin2
    (hdom : MarkovBinaryPLNDomainConditions μ)
    (xs ys : List (Fin 2)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
    (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
    (hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys)
    (x : Fin 2) :
    μ (xs ++ [x]) = μ (ys ++ [x]) := by
  exact (hdom.domain_characterization_fin2).1 xs ys hlen hx hstart hsum x

/-- Under the packaged binary Markov-domain conditions, one-step prediction for
the true environment depends only on the explicit binary summary state. -/
theorem predictor_eq_of_same_summary_bool
    (hdom : MarkovBinaryPLNDomainConditions μ)
    (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hlen : xs.length = ys.length) (hx : 0 < xs.length)
    (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
    (hsum : binarySummary xs = binarySummary ys)
    (x : Bool) :
    μ (encodeBoolWord (xs ++ [x])) = μ (encodeBoolWord (ys ++ [x])) := by
  exact (hdom.domain_characterization_bool).1 xs ys hlen hx hstart hsum x

/-- Under the packaged binary Markov-domain conditions, the Markov-Dirichlet
reference predictor uses the same generic `Fin 2` state on equal-summary
histories. -/
theorem dirichlet_common_state_update_fin2
    (hdom : MarkovBinaryPLNDomainConditions μ)
    (xs ys : List (Fin 2)) (hx : 0 < xs.length)
    (hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys) :
    ∃ state : TransCounts 2 × Fin 2,
      TransCounts.summary (k := 2) xs = some state ∧
      TransCounts.summary (k := 2) ys = some state ∧
      ∀ a : Fin 2,
        (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (xs ++ [a]) =
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) xs *
            ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a) ∧
        (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (ys ++ [a]) =
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) ys *
            ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a) := by
  exact (hdom.domain_characterization_fin2).2.1 xs ys hx hsum

/-- Under the packaged binary Markov-domain conditions, the Markov-Dirichlet
reference predictor uses the same explicit binary state on equal-summary
histories. -/
theorem dirichlet_common_state_update_bool
    (hdom : MarkovBinaryPLNDomainConditions μ)
    (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (hx : 0 < xs.length)
    (hsum : binarySummary xs = binarySummary ys) :
    ∃ state : BinarySummaryState,
      binarySummary xs = some state ∧
      binarySummary ys = some state ∧
      ∀ a : Bool,
        (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
            (encodeBoolWord (xs ++ [a])) =
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord xs) *
            ENNReal.ofReal
              (MarkovDirichlet.stepProb hdom.prior
                (BinarySummaryState.toFin2State state).1
                (BinarySummaryState.toFin2State state).2
                (boolToFin2 a)) ∧
        (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
            (encodeBoolWord (ys ++ [a])) =
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord ys) *
            ENNReal.ofReal
              (MarkovDirichlet.stepProb hdom.prior
                (BinarySummaryState.toFin2State state).1
                (BinarySummaryState.toFin2State state).2
                (boolToFin2 a)) := by
  exact (hdom.domain_characterization_bool).2.1 xs ys hx hsum

/-- The Solomonoff finite-alphabet comparator still gives the standard
log-loss regret bound against any law satisfying the packaged binary Markov
domain conditions. -/
theorem solomonoff_regret_bound
    (hdom : MarkovBinaryPLNDomainConditions μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
        (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
          (α := Fin 2)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
          (α := Fin 2)) n ≤
          Real.log (1 / c.toReal) := by
  exact (hdom.domain_characterization_bool).2.2 n

end MarkovBinaryPLNDomainConditions

/-- Packaged binary post-Markov domain conditions together with the honest
class-restricted Markov de Finetti surface.

This extends the earlier binary domain package by adding exactly the extra
class-recurrence data that is currently proved at the public surface level. -/
structure MarkovBinaryPLNDomainConditionsInClass
    (C : Set (Fin 2))
    (μ : FiniteAlphabet.PrefixMeasure (Fin 2)) where
  surface : Mettapedia.Logic.ClassRestrictedMarkovMixtureSurface 2 C μ
  lowerSemicomputable :
    Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
      (α := Fin 2) μ
  prior : Fin 2 → Mettapedia.Logic.EvidenceDirichlet.DirichletParams 2

namespace MarkovBinaryPLNDomainConditionsInClass

variable {C : Set (Fin 2)} {μ : FiniteAlphabet.PrefixMeasure (Fin 2)}

/-- Forget the class-recurrence payload and recover the binary Markov-domain
conditions package used for predictor and regret consequences. -/
def toDomainConditions
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) :
    MarkovBinaryPLNDomainConditions μ :=
  ⟨hdom.surface.markovExchangeable, hdom.lowerSemicomputable, hdom.prior⟩

/-- The generic `Fin 2` binary domain theorem remains available under the
class-restricted package. -/
theorem domain_characterization_fin2
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) :
    (∀ (xs ys : List (Fin 2)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys)
      (x : Fin 2),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (xs ys : List (Fin 2)) (_hx : 0 < xs.length)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys),
      ∃ state : TransCounts 2 × Fin 2,
        TransCounts.summary (k := 2) xs = some state ∧
        TransCounts.summary (k := 2) ys = some state ∧
        ∀ a : Fin 2,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (xs ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) xs *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (ys ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) ys *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a)) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact hdom.toDomainConditions.domain_characterization_fin2

/-- The explicit `Bool` presentation of the binary domain theorem remains
available under the class-restricted package. -/
theorem domain_characterization_bool
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys)
      (x : Bool),
      μ (encodeBoolWord (xs ++ [x])) = μ (encodeBoolWord (ys ++ [x]))) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  exact hdom.toDomainConditions.domain_characterization_bool

/-- Class-restricted row-law factorization in the generic `Fin 2` row-index
presentation. -/
theorem restrictClass_rowLaw_factorizes_fin2
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ)
    (i : Fin 2) (hi : i ∈ C)
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin 2 => fun j : Fin m => r (sel j))
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
          (k := 2) C hdom.surface.extensionLaw i)
      =
    (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
      (k := 2) C hdom.surface.extensionLaw i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (Mettapedia.Logic.MarkovDeFinettiHard.directingRowKernel
              (k := 2) hdom.surface.extensionLaw i r :
              Measure (Fin 2)))) := by
  exact hdom.surface.restrictClass_rowLaw_factorizes i hi m sel hsel

/-- Class-restricted row-law factorization in the explicit binary `Bool`
presentation of the active row. -/
theorem restrictClass_rowLaw_factorizes_bool
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ)
    (b : Bool) (hb : boolToFin2 b ∈ C)
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin 2 => fun j : Fin m => r (sel j))
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
          (k := 2) C hdom.surface.extensionLaw (boolToFin2 b))
      =
    (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
      (k := 2) C hdom.surface.extensionLaw (boolToFin2 b)).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (Mettapedia.Logic.MarkovDeFinettiHard.directingRowKernel
              (k := 2) hdom.surface.extensionLaw (boolToFin2 b) r :
              Measure (Fin 2)))) := by
  exact hdom.restrictClass_rowLaw_factorizes_fin2 (boolToFin2 b) hb m sel hsel

/-- Standard Solomonoff regret bound under the packaged class-restricted binary
Markov conditions. -/
theorem solomonoff_regret_bound
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
        (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
          (α := Fin 2)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
          (α := Fin 2)) n ≤
          Real.log (1 / c.toReal) := by
  exact hdom.toDomainConditions.solomonoff_regret_bound n

/-- Binary class-recurrence transition structure in the generic `Fin 2`
presentation: summary-state predictor equality, shared Markov-Dirichlet update
state, Solomonoff regret bound, and class-restricted row-law factorization. -/
theorem class_transition_structure_fin2
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) :
    (∀ (xs ys : List (Fin 2)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys)
      (x : Fin 2),
      μ (xs ++ [x]) = μ (ys ++ [x])) ∧
    (∀ (xs ys : List (Fin 2)) (_hx : 0 < xs.length)
      (_hsum : TransCounts.summary (k := 2) xs = TransCounts.summary (k := 2) ys),
      ∃ state : TransCounts 2 × Fin 2,
        TransCounts.summary (k := 2) xs = some state ∧
        TransCounts.summary (k := 2) ys = some state ∧
        ∀ a : Fin 2,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (xs ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) xs *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) (ys ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior) ys *
              ENNReal.ofReal (MarkovDirichlet.stepProb hdom.prior state.1 state.2 a)) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) ∧
    (∀ (i : Fin 2), i ∈ C →
      ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map
            (fun r : ℕ → Fin 2 => fun j : Fin m => r (sel j))
            (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
              (k := 2) C hdom.surface.extensionLaw i)
          =
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
          (k := 2) C hdom.surface.extensionLaw i).bind
          (fun r =>
            Measure.pi
              (fun _ : Fin m =>
                (Mettapedia.Logic.MarkovDeFinettiHard.directingRowKernel
                  (k := 2) hdom.surface.extensionLaw i r :
                  Measure (Fin 2))))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (MarkovBinaryPLNDomainConditionsInClass.domain_characterization_fin2 hdom).1
  · exact (MarkovBinaryPLNDomainConditionsInClass.domain_characterization_fin2 hdom).2.1
  · intro n
    exact MarkovBinaryPLNDomainConditionsInClass.solomonoff_regret_bound hdom n
  · intro i hi m sel hsel
    exact
      MarkovBinaryPLNDomainConditionsInClass.restrictClass_rowLaw_factorizes_fin2
        hdom i hi m sel hsel

/-- Binary class-recurrence transition structure in the explicit `Bool`
presentation: summary-state predictor equality, shared Markov-Dirichlet update
state, Solomonoff regret bound, and class-restricted row-law factorization. -/
theorem class_transition_structure_bool
    (hdom : MarkovBinaryPLNDomainConditionsInClass C μ) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys)
      (x : Bool),
      μ (encodeBoolWord (xs ++ [x])) = μ (encodeBoolWord (ys ++ [x]))) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) hdom.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb hdom.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) μ c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) ∧
    (∀ (b : Bool), boolToFin2 b ∈ C →
      ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map
            (fun r : ℕ → Fin 2 => fun j : Fin m => r (sel j))
            (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
              (k := 2) C hdom.surface.extensionLaw (boolToFin2 b))
          =
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass
          (k := 2) C hdom.surface.extensionLaw (boolToFin2 b)).bind
          (fun r =>
            Measure.pi
              (fun _ : Fin m =>
                (Mettapedia.Logic.MarkovDeFinettiHard.directingRowKernel
                  (k := 2) hdom.surface.extensionLaw (boolToFin2 b) r :
                  Measure (Fin 2))))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (MarkovBinaryPLNDomainConditionsInClass.domain_characterization_bool hdom).1
  · exact (MarkovBinaryPLNDomainConditionsInClass.domain_characterization_bool hdom).2.1
  · intro n
    exact MarkovBinaryPLNDomainConditionsInClass.solomonoff_regret_bound hdom n
  · intro b hb m sel hsel
    exact
      MarkovBinaryPLNDomainConditionsInClass.restrictClass_rowLaw_factorizes_bool
        hdom b hb m sel hsel

end MarkovBinaryPLNDomainConditionsInClass

end MarkovBinaryBridge

end ExchangeablePrograms

/-! ## Solomonoff Restricted to Exchangeable Class -/

section RestrictedSolomonoff

/-- A *restricted* Solomonoff-style prior, implemented as the cylinder semimeasure of a
    monotone machine over a finite, prefix-free set of programs.

    Exchangeability is taken to be a property of this induced semimeasure. -/
structure RestrictedSolomonoffPrior where
  U : MonotoneMachine
  programs : Finset BinString
  hpf : PrefixFree (↑programs : Set BinString)
  hexch : ProgramsExchangeable U programs

namespace RestrictedSolomonoffPrior

/-- The induced semimeasure on finite strings (cylinder weights). -/
noncomputable def μ (M : RestrictedSolomonoffPrior) : BinString → ℝ :=
  fun x => M.U.cylinderMeasure M.programs x

/-- Concrete program-mass completeness criterion: selected programs saturate the
Kraft mass exactly (`= 1`). -/
def ProgramMassComplete (M : RestrictedSolomonoffPrior) : Prop :=
  kraftSum M.programs = 1

/-- Program-mass completeness implies normalized root mass for the induced
restricted Solomonoff semimeasure. -/
theorem mu_nil_eq_one_of_programMassComplete
    (M : RestrictedSolomonoffPrior) (hcomplete : ProgramMassComplete M) :
    M.μ [] = 1 := by
  classical
  unfold RestrictedSolomonoffPrior.μ MonotoneMachine.cylinderMeasure
  have hfilter : M.programs.filter (fun p => M.U.produces p []) = M.programs := by
    ext p
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    unfold MonotoneMachine.produces
    intro ⟨i, hi⟩
    simp at hi
  rw [hfilter]
  simpa [ProgramMassComplete, kraftSum] using hcomplete

theorem mu_same_counts (M : RestrictedSolomonoffPrior) {n : ℕ} (xs₁ xs₂ : Fin n → Bool)
    (hcount : countTrue xs₁ = countTrue xs₂) :
    M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) := by
  -- Unfold the induced semimeasure and apply the abstract exchangeability lemma.
  simpa [RestrictedSolomonoffPrior.μ, ProgramsExchangeable] using
    semimeasureExchangeable_same_counts (μ := fun x => M.U.cylinderMeasure M.programs x) M.hexch xs₁ xs₂ hcount

/-! ### Solomonoff-Style Prediction (Semimeasure Level)

The Solomonoff predictor uses the semimeasure ratio `μ(x++[b]) / μ(x)`. This is a *partial*
operation when `μ(x) = 0`, so we model it with `Option`.
-/

/-- Conditional prediction for the next bit under a (possibly defective) semimeasure.

Returns `none` when the conditioning event has weight `0`. -/
noncomputable def predictBit (M : RestrictedSolomonoffPrior) (x : BinString) (b : Bool) : Option ℝ :=
  if M.μ x = 0 then none else some (M.μ (x ++ [b]) / M.μ x)

private lemma countTrue_snoc {n : ℕ} (xs : Fin n → Bool) (b : Bool) :
    countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b) =
      countTrue xs + (if b then 1 else 0) := by
  classical
  -- Turn this into a finset-card computation on `Fin (n+1)` and split off the last coordinate.
  unfold countTrue
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i : Fin (n + 1) =>
      Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b i = true)
  let t : Finset (Fin (n + 1)) :=
    (Finset.univ.filter (fun i : Fin n => xs i = true)).map Fin.castSuccEmb
  have hs : s = (if b then insert (Fin.last n) t else t) := by
    ext j
    -- Membership in `s` is just the defining predicate.
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    cases b <;> cases j using Fin.lastCases <;> simp [t]
  have htcard : t.card = (Finset.univ.filter (fun i : Fin n => xs i = true)).card := by
    simp [t]
  cases b with
  | false =>
    -- `s = t` (no new `true` at the end).
    have hst : s = t := by simp [hs]
    change s.card =
      (Finset.univ.filter (fun i : Fin n => xs i = true)).card + (if (false = true) then 1 else 0)
    -- Reduce to `t.card = ...` using `hst`.
    rw [hst]
    simp [htcard]
  | true =>
    -- `s = insert (last n) t`, and `last n ∉ t`.
    have hst : s = insert (Fin.last n) t := by simp [hs]
    change s.card =
      (Finset.univ.filter (fun i : Fin n => xs i = true)).card + (if (true = true) then 1 else 0)
    have hnot : Fin.last n ∉ t := by
      intro hmem
      rcases Finset.mem_map.1 hmem with ⟨i, _hi, hi_last⟩
      have hi_last' := hi_last
      -- Convert `castSuccEmb` to `castSucc` without solving the contradiction automatically.
      -- After simplification this hypothesis becomes `False`, closing the goal.
      simp [Fin.castSuccEmb_apply] at hi_last'
    -- Card adds one for the new `true`.
    rw [hst]
    simp [Finset.card_insert_of_notMem hnot, htcard]

/-- The induced semimeasure depends only on counts (already proven), and therefore so does the
Solomonoff-style predictor `μ(x++[b]) / μ(x)` for any fixed `b`. -/
theorem predictBit_ofFn_same_counts (M : RestrictedSolomonoffPrior) {n : ℕ}
    (xs₁ xs₂ : Fin n → Bool) (hcount : countTrue xs₁ = countTrue xs₂) (b : Bool) :
    M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  classical
  -- First, the denominators agree by exchangeability.
  have hden :
      M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) :=
    M.mu_same_counts xs₁ xs₂ hcount
  by_cases hzero : M.μ (List.ofFn xs₁) = 0
  · -- Both sides are `none`.
    have hzero₂ : M.μ (List.ofFn xs₂) = 0 := by
      simp [hden] at hzero
      simpa using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero, hzero₂]
  · -- Denominators are nonzero, so we reduce to showing the numerators agree.
    have hcount' :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b) =
          countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b) := by
      simp [countTrue_snoc, hcount]
    have hnum :
        M.μ (List.ofFn xs₁ ++ [b]) = M.μ (List.ofFn xs₂ ++ [b]) := by
      -- Rewrite `List.ofFn xs ++ [b]` as `List.ofFn (Fin.snoc xs b)`.
      have hsnoc₁ :
          List.ofFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b) = List.ofFn xs₁ ++ [b] := by
        -- `ofFn_succ'` gives a `concat` form; `concat_eq_append` turns it into `++ [b]`.
        rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b)]
        simp [List.concat_eq_append]
      have hsnoc₂ :
          List.ofFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b) = List.ofFn xs₂ ++ [b] := by
        rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b)]
        simp [List.concat_eq_append]
      -- Apply count-invariance at length `n+1`.
      have h :=
        M.mu_same_counts (n := n + 1)
          (xs₁ := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₁ b)
          (xs₂ := Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs₂ b)
          hcount'
      -- Rewrite the `Fin.snoc`-generated lists into `List.ofFn xs ++ [b]` without triggering
      -- simp expansions of `List.ofFn`.
      rw [hsnoc₁, hsnoc₂] at h
      exact h
    -- Finish by unfolding `predictBit`.
    have hzero₂ : M.μ (List.ofFn xs₂) ≠ 0 := by
      simpa [hden] using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero₂, hnum, hden]

end RestrictedSolomonoffPrior

/-- **Practical νPLN Theorem**: For exchangeable Solomonoff priors, counts are sufficient.

    Probabilities depend only on (n⁺, n⁻), which follows directly from exchangeability
    via `mu_same_counts`. Note: the full de Finetti theorem IS formalized in
    `Mettapedia.Logic.DeFinetti` and gives the closed-form Beta-Bernoulli representation.

    **This justifies PLN BinaryEvidence = (n⁺, n⁻) for exchangeable binary domains.**
-/
theorem solomonoff_exchangeable_counts_sufficient (M : RestrictedSolomonoffPrior) :
    ∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      M.μ (List.ofFn xs₁) = M.μ (List.ofFn xs₂) :=
  fun _n xs₁ xs₂ h => M.mu_same_counts xs₁ xs₂ h

/-- **νPLN Core Theorem (Predictor Form)**:

For an exchangeable restricted Solomonoff prior, the Solomonoff-style predictor
`μ(x++[b]) / μ(x)` depends only on the count statistic `(n⁺, n⁻)` of the observed prefix.

This is the precise “domain restriction ⇒ state compression” statement:
exchangeability collapses the relevant state from “program mixture” to `ℕ × ℕ`. -/
theorem solomonoff_exchangeable_predictBit_same_counts (M : RestrictedSolomonoffPrior) :
    ∀ {n : ℕ} (xs₁ xs₂ : Fin n → Bool),
      countTrue xs₁ = countTrue xs₂ →
      ∀ b : Bool,
        M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  intro n xs₁ xs₂ hcount b
  exact Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior.predictBit_ofFn_same_counts
    (M := M) xs₁ xs₂ hcount b

/-! ### BinaryEvidence View: Count Update = `hplus`

The BinaryEvidence quantale uses `hplus` to aggregate independent observations:
adding one `true` increments `n⁺`; adding one `false` increments `n⁻`.
-/

/-- Convert natural count statistics to BinaryEvidence counts. -/
def evidenceOfCounts (n_pos n_neg : ℕ) : BinaryEvidence :=
  ⟨(n_pos : ℝ≥0∞), (n_neg : ℝ≥0∞)⟩

/-- BinaryEvidence contributed by a single observation bit. -/
def evidenceOfBit (b : Bool) : BinaryEvidence :=
  if b then ⟨1, 0⟩ else ⟨0, 1⟩

/-- BinaryEvidence corresponding to a length-`n` observation vector. -/
def evidenceOfFn {n : ℕ} (xs : Fin n → Bool) : BinaryEvidence :=
  evidenceOfCounts (countTrue xs) (countFalse xs)

/-- `evidenceOfFn xs` is equivalent to knowing only `countTrue xs` (since `countFalse` is determined
by `count_partition`). -/
theorem evidenceOfFn_eq_iff_countTrue_eq {n : ℕ} (xs₁ xs₂ : Fin n → Bool) :
    evidenceOfFn xs₁ = evidenceOfFn xs₂ ↔ countTrue xs₁ = countTrue xs₂ := by
  constructor
  · intro heq
    have hpos :
        ((countTrue xs₁ : ℕ) : ℝ≥0∞) = ((countTrue xs₂ : ℕ) : ℝ≥0∞) := by
      simpa [evidenceOfFn, evidenceOfCounts] using congrArg BinaryEvidence.pos heq
    exact Nat.cast_injective hpos
  · intro hcount
    have hfalse : countFalse xs₁ = countFalse xs₂ := by
      -- Use `countTrue + countFalse = n` on both sides.
      have hpart₁ := count_partition (n := n) xs₁
      have hpart₂ := count_partition (n := n) xs₂
      have hsum : countTrue xs₁ + countFalse xs₁ = countTrue xs₂ + countFalse xs₂ := by
        calc
          countTrue xs₁ + countFalse xs₁ = n := hpart₁
          _ = countTrue xs₂ + countFalse xs₂ := hpart₂.symm
      -- Cancel the `countTrue` terms using `hcount`.
      have hsum' : countTrue xs₁ + countFalse xs₁ = countTrue xs₁ + countFalse xs₂ := by
        simpa [hcount] using hsum
      exact Nat.add_left_cancel hsum'
    ext <;> simp [evidenceOfFn, evidenceOfCounts, hcount, hfalse]

/-- **νPLN core (BinaryEvidence form)**: For an exchangeable restricted Solomonoff prior, the
Solomonoff-style predictor depends only on the BinaryEvidence state `evidenceOfFn xs`.

This is the clean “state compression” statement: in the exchangeable-binary setting, the
predictor factors through the sufficient statistic `(n⁺, n⁻)`. -/
theorem solomonoff_exchangeable_predictBit_same_evidence (M : RestrictedSolomonoffPrior) :
    ∀ {n : ℕ} (xs₁ xs₂ : Fin n → Bool),
      evidenceOfFn xs₁ = evidenceOfFn xs₂ →
      ∀ b : Bool,
        M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  intro n xs₁ xs₂ heq b
  -- Extract equality of `countTrue` from the equality of BinaryEvidence states.
  have hpos :
      ((countTrue xs₁ : ℕ) : ℝ≥0∞) = ((countTrue xs₂ : ℕ) : ℝ≥0∞) := by
    simpa [evidenceOfFn, evidenceOfCounts] using congrArg BinaryEvidence.pos heq
  have hcount : countTrue xs₁ = countTrue xs₂ := by
    exact Nat.cast_injective hpos
  exact solomonoff_exchangeable_predictBit_same_counts (M := M) xs₁ xs₂ hcount b

/-- Bridge theorem from semimeasure-level exchangeability to measure-level
infinite exchangeability.

If a probability measure on infinite binary sequences has the same finite-prefix
laws as a `RestrictedSolomonoffPrior`, then the coordinate process is
`InfiniteExchangeable` under that measure. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    InfiniteExchangeable (fun i ω => ω i) μ := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμprob
  refine ⟨?_⟩
  intro n
  refine ⟨?_⟩
  intro σ vals
  have hvals :
      μ {ω | ∀ i : Fin n, ω i = vals i} =
        ENNReal.ofReal (M.μ (List.ofFn vals)) := hprefix n vals
  have hpermVals :
      μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} =
        ENNReal.ofReal (M.μ (List.ofFn (vals ∘ σ.symm))) := hprefix n (vals ∘ σ.symm)
  have hμ :
      M.μ (List.ofFn vals) = M.μ (List.ofFn (vals ∘ σ.symm)) := by
    simpa [RestrictedSolomonoffPrior.μ, ProgramsExchangeable] using M.hexch n σ vals
  have hreindex :
      μ {ω | ∀ i : Fin n, ω (σ i) = vals i} =
        μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} := by
    congr 1
    ext ω
    constructor <;> intro h i
    · simpa using h (σ.symm i)
    · simpa using h (σ i)
  calc
    μ {ω | ∀ i : Fin n, ω i = vals i}
        = ENNReal.ofReal (M.μ (List.ofFn vals)) := hvals
    _ = ENNReal.ofReal (M.μ (List.ofFn (vals ∘ σ.symm))) := by simp [hμ]
    _ = μ {ω | ∀ i : Fin n, ω i = vals (σ.symm i)} := by simpa using hpermVals.symm
    _ = μ {ω | ∀ i : Fin n, ω (σ i) = vals i} := hreindex.symm

/-- One-hop version of the Solomonoff→exchangeability bridge using the named
no-leakage cylinder-law condition from `SolomonoffMeasure`, so no external
`hprefix` argument is required. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ) :
    InfiniteExchangeable (fun i ω => ω i) μ := by
  refine restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
    (M := M) (μ := μ) (hμprob := hμprob) ?_
  exact Mettapedia.Logic.hprefix_of_noLeakageAtCylindersLaw
    (U := M.U) (programs := M.programs) (μ := μ) hNoLeak

/-- One-hop concrete criterion packaged without external witnesses:
if selected programs emit at every depth and root mass is normalized, then the
canonical machine-induced measure is probability and infinite-exchangeable. -/
theorem restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms
    (M : RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms M.U M.programs)
    (hroot : M.μ [] = 1) :
    ∃ μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString,
      ∃ hμprob : MeasureTheory.IsProbabilityMeasure μ,
        μ = Mettapedia.Logic.totalOutputProgramMeasure
          (U := M.U) (programs := M.programs) htot ∧
        @InfiniteExchangeable _ _ (fun i ω => ω i) μ hμprob := by
  let μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString :=
    Mettapedia.Logic.totalOutputProgramMeasure (U := M.U) (programs := M.programs) htot
  have hμprob : MeasureTheory.IsProbabilityMeasure μ := by
    simpa [μ, RestrictedSolomonoffPrior.μ] using
      (Mettapedia.Logic.isProbabilityMeasure_totalOutputProgramMeasure_of_root_one
        (U := M.U) (programs := M.programs) (htot := htot) hroot)
  letI : MeasureTheory.IsProbabilityMeasure μ := hμprob
  have hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ := by
    simpa [μ] using
      (Mettapedia.Logic.noLeakageAtCylindersLaw_totalOutputProgramMeasure
        (U := M.U) (programs := M.programs) htot)
  refine ⟨μ, hμprob, rfl, ?_⟩
  exact restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M := M) (μ := μ) (hμprob := hμprob) hNoLeak

/-- One-hop concrete criterion with no explicit `hroot` argument:
derive normalization from `ProgramMassComplete` and then apply the
total-output route. -/
theorem restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms_and_programMassComplete
    (M : RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms M.U M.programs)
    (hcomplete : RestrictedSolomonoffPrior.ProgramMassComplete M) :
    ∃ μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString,
      ∃ hμprob : MeasureTheory.IsProbabilityMeasure μ,
        μ = Mettapedia.Logic.totalOutputProgramMeasure
          (U := M.U) (programs := M.programs) htot ∧
        @InfiniteExchangeable _ _ (fun i ω => ω i) μ hμprob := by
  exact restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms
    (M := M) (htot := htot)
    (hroot := RestrictedSolomonoffPrior.mu_nil_eq_one_of_programMassComplete
      (M := M) hcomplete)

/-- Deprecated entrypoint: use
`restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw`
or the concrete
`restrictedSolomonoff_infiniteExchangeable_exists_of_totalOutputOnPrograms_and_programMassComplete`. -/
theorem restrictedSolomonoff_infiniteExchangeable_of_cylinderLaw
    (M : RestrictedSolomonoffPrior)
    (μ : MeasureTheory.Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    (hμprob : MeasureTheory.IsProbabilityMeasure μ)
    (hCylinder :
      ∀ x : BinString,
        μ (Mettapedia.Logic.SolomonoffPrior.InfBinString.Cylinder x) =
          ENNReal.ofReal (M.μ x)) :
    InfiniteExchangeable (fun i ω => ω i) μ :=
  restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
    (M := M) (μ := μ) (hμprob := hμprob) hCylinder

theorem evidenceOfFn_snoc {n : ℕ} (xs : Fin n → Bool) (b : Bool) :
    evidenceOfFn (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs b) =
      evidenceOfFn xs + evidenceOfBit b := by
  classical
  -- Unfold and compute the count updates.
  cases b with
  | false =>
    unfold evidenceOfFn evidenceOfCounts evidenceOfBit
    have htrue :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) = countTrue xs := by
      simpa using (RestrictedSolomonoffPrior.countTrue_snoc (xs := xs) (b := false))
    have hfalse :
        countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) = countFalse xs + 1 := by
      have hpart₁ := count_partition (n := n) xs
      have hpart₂ :=
        count_partition (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false)
      have hpart₂' :
          countTrue xs +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
            n + 1 := by
        simpa [htrue] using hpart₂
      have hpart₁' : countTrue xs + (countFalse xs + 1) = n + 1 := by
        omega
      have heq :
          countTrue xs +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
            countTrue xs + (countFalse xs + 1) := by
        calc
          countTrue xs +
                countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs false) =
              n + 1 := hpart₂'
          _ = countTrue xs + (countFalse xs + 1) := by
              simpa using hpart₁'.symm
      exact Nat.add_left_cancel heq
    ext <;> simp [BinaryEvidence.hplus_def, htrue, hfalse, Nat.cast_add]
  | true =>
    unfold evidenceOfFn evidenceOfCounts evidenceOfBit
    have htrue :
        countTrue (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) = countTrue xs + 1 := by
      simpa using (RestrictedSolomonoffPrior.countTrue_snoc (xs := xs) (b := true))
    have hfalse :
        countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) = countFalse xs := by
      have hpart₁ := count_partition (n := n) xs
      have hpart₂ :=
        count_partition (n := n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true)
      have hpart₂' : (countTrue xs + 1) +
            countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
          n + 1 := by
        simpa only [htrue, Nat.add_assoc] using hpart₂
      have hpart₁' : (countTrue xs + 1) + countFalse xs = n + 1 := by
        -- Add one to the count partition equation and reassociate to match the LHS of `hpart₂'`.
        have h1 : (countTrue xs + countFalse xs) + 1 = n + 1 :=
          congrArg (fun t => t + 1) hpart₁
        -- Reassociate and commute to put the `+ 1` next to `countTrue xs`.
        have h2 : countTrue xs + countFalse xs + 1 = n + 1 := by
          simpa only [Nat.add_assoc] using h1
        have h3 : countTrue xs + 1 + countFalse xs = n + 1 := by
          simpa only [Nat.add_right_comm] using h2
        simpa only [Nat.add_assoc] using h3
      have heq :
          (countTrue xs + 1) +
              countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
            (countTrue xs + 1) + countFalse xs := by
        calc
          (countTrue xs + 1) +
                countFalse (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) xs true) =
              n + 1 := hpart₂'
          _ = (countTrue xs + 1) + countFalse xs := by
              simpa using hpart₁'.symm
      exact Nat.add_left_cancel heq
    ext <;> simp [BinaryEvidence.hplus_def, htrue, hfalse, Nat.cast_add]

end RestrictedSolomonoff

/-! ## The Domain Characterization Theorem -/

section DomainCharacterization

/-- Positive domain criterion: inside the exchangeable restricted-Solomonoff
domain, the next-bit predictor depends only on the `BinaryEvidence` state. -/
theorem restrictedSolomonoff_domain_characterization_positive
    (M : RestrictedSolomonoffPrior) :
    ∀ {n : ℕ} (xs₁ xs₂ : Fin n → Bool),
      evidenceOfFn xs₁ = evidenceOfFn xs₂ →
      ∀ b : Bool,
        M.predictBit (List.ofFn xs₁) b = M.predictBit (List.ofFn xs₂) b := by
  intro n xs₁ xs₂ heq b
  exact solomonoff_exchangeable_predictBit_same_evidence (M := M) xs₁ xs₂ heq b

/-- Negative diagnostic: in the exchangeable restricted-Solomonoff domain,
predictor mismatch on equal `BinaryEvidence` states is impossible. -/
theorem restrictedSolomonoff_no_same_evidence_predictor_mismatch
    (M : RestrictedSolomonoffPrior) :
    ¬ ∃ (n : ℕ) (xs₁ xs₂ : Fin n → Bool) (b : Bool),
        evidenceOfFn xs₁ = evidenceOfFn xs₂ ∧
        M.predictBit (List.ofFn xs₁) b ≠ M.predictBit (List.ofFn xs₂) b := by
  intro h
  rcases h with ⟨n, xs₁, xs₂, b, heq, hne⟩
  exact hne
    (restrictedSolomonoff_domain_characterization_positive
      (M := M) xs₁ xs₂ heq b)

end DomainCharacterization

/-! ## Markov Witnesses for Restricted Solomonoff Priors -/

section MarkovDomainCharacterization

open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-- Honest witness that a restricted Solomonoff prior is being compared against
an actual binary Markov-exchangeable prefix law satisfying the packaged domain
conditions. This keeps the post-Markov bridge witness-based rather than
pretending every restricted Solomonoff prior is automatically Markov-exchangeable. -/
structure RestrictedSolomonoffMarkovWitness (M : RestrictedSolomonoffPrior) where
  law : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin 2)
  domain : MarkovBinaryPLNDomainConditions law
  prefix_agrees :
    ∀ xs : Mettapedia.Logic.SolomonoffPrior.BinString,
      law (encodeBoolWord xs) = ENNReal.ofReal (M.μ xs)

namespace RestrictedSolomonoffMarkovWitness

variable {M : RestrictedSolomonoffPrior}

/-- Transfer equality of the witnessed binary prefix law back to equality of the
restricted Solomonoff semimeasure on the corresponding Boolean prefixes. -/
theorem mu_eq_of_law_eq
    (W : RestrictedSolomonoffMarkovWitness M)
    {xs ys : Mettapedia.Logic.SolomonoffPrior.BinString}
    (h : W.law (encodeBoolWord xs) = W.law (encodeBoolWord ys)) :
    M.μ xs = M.μ ys := by
  have h' : ENNReal.ofReal (M.μ xs) = ENNReal.ofReal (M.μ ys) := by
    simpa [W.prefix_agrees xs, W.prefix_agrees ys] using h
  have hxnonneg : 0 ≤ M.μ xs := by
    simpa [RestrictedSolomonoffPrior.μ] using M.U.cylinderMeasure_nonneg M.programs xs
  have hynonneg : 0 ≤ M.μ ys := by
    simpa [RestrictedSolomonoffPrior.μ] using M.U.cylinderMeasure_nonneg M.programs ys
  have hreal := congrArg ENNReal.toReal h'
  simpa [ENNReal.toReal_ofReal hxnonneg, ENNReal.toReal_ofReal hynonneg] using hreal

/-- Equal binary summary states imply equal witnessed prefix-law mass on the
underlying prefixes, by summing the equal one-step extension masses over the
two possible next bits. -/
theorem law_eq_of_same_summary_bool
    (W : RestrictedSolomonoffMarkovWitness M)
    (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hlen : xs.length = ys.length) (hx : 0 < xs.length)
    (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
    (hsum : binarySummary xs = binarySummary ys) :
    W.law (encodeBoolWord xs) = W.law (encodeBoolWord ys) := by
  have hfalse :=
    W.domain.predictor_eq_of_same_summary_bool xs ys hlen hx hstart hsum false
  have htrue :=
    W.domain.predictor_eq_of_same_summary_bool xs ys hlen hx hstart hsum true
  have hsumx :
      W.law (encodeBoolWord (xs ++ [false])) + W.law (encodeBoolWord (xs ++ [true])) =
        W.law (encodeBoolWord xs) := by
    simpa [encodeBoolWord_append, boolToFin2, Fin.sum_univ_two]
      using W.law.additive' (encodeBoolWord xs)
  have hsumy :
      W.law (encodeBoolWord (ys ++ [false])) + W.law (encodeBoolWord (ys ++ [true])) =
        W.law (encodeBoolWord ys) := by
    simpa [encodeBoolWord_append, boolToFin2, Fin.sum_univ_two]
      using W.law.additive' (encodeBoolWord ys)
  calc
    W.law (encodeBoolWord xs)
        = W.law (encodeBoolWord (xs ++ [false])) + W.law (encodeBoolWord (xs ++ [true])) := by
            exact hsumx.symm
    _ = W.law (encodeBoolWord (ys ++ [false])) + W.law (encodeBoolWord (ys ++ [true])) := by
          rw [hfalse, htrue]
    _ = W.law (encodeBoolWord ys) := hsumy

end RestrictedSolomonoffMarkovWitness

/-- Positive domain criterion for the post-Markov binary Solomonoff story:
given an honest Markov witness, the restricted Solomonoff predictor depends
only on the explicit binary summary `(ff,ft,tf,tt,lastBit)`. -/
theorem restrictedSolomonoff_markov_domain_characterization_positive_bool
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    ∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys) (b : Bool),
      M.predictBit xs b = M.predictBit ys b := by
  intro xs ys hlen hx hstart hsum b
  have hnumLaw :=
    W.domain.predictor_eq_of_same_summary_bool xs ys hlen hx hstart hsum b
  have hnum :
      M.μ (xs ++ [b]) = M.μ (ys ++ [b]) :=
    RestrictedSolomonoffMarkovWitness.mu_eq_of_law_eq (W := W) hnumLaw
  have hdenLaw :=
    RestrictedSolomonoffMarkovWitness.law_eq_of_same_summary_bool
      (W := W) xs ys hlen hx hstart hsum
  have hden : M.μ xs = M.μ ys :=
    RestrictedSolomonoffMarkovWitness.mu_eq_of_law_eq (W := W) hdenLaw
  by_cases hzero : M.μ xs = 0
  · have hzero' : M.μ ys = 0 := by simpa [hden] using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero, hzero']
  · have hzero' : M.μ ys ≠ 0 := by simpa [hden] using hzero
    simp [RestrictedSolomonoffPrior.predictBit, hzero', hnum, hden]

/-- The same post-Markov binary Solomonoff theorem, but stated using the
generic `Fin 2` summary presentation on the encoded histories. -/
theorem restrictedSolomonoff_markov_domain_characterization_positive_fin2
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    ∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum :
        TransCounts.summary (k := 2) (encodeBoolWord xs) =
          TransCounts.summary (k := 2) (encodeBoolWord ys))
      (b : Bool),
      M.predictBit xs b = M.predictBit ys b := by
  intro xs ys hlen hx hstart hsum b
  refine restrictedSolomonoff_markov_domain_characterization_positive_bool
    (M := M) (W := W) xs ys hlen hx hstart ?_ b
  exact (markovExchangeable_binary_summary_presentations_agree xs ys).2 hsum

/-- Negative diagnostic: under an honest Markov witness, equal explicit binary
summary states cannot yield different restricted-Solomonoff next-bit
predictions. -/
theorem restrictedSolomonoff_markov_no_same_summary_predictor_mismatch_bool
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    ¬ ∃ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
        (hlen : xs.length = ys.length) (hx : 0 < xs.length)
        (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
        (b : Bool),
        binarySummary xs = binarySummary ys ∧
        M.predictBit xs b ≠ M.predictBit ys b := by
  intro h
  rcases h with ⟨xs, ys, hlen, hx, hstart, b, hsum, hneq⟩
  exact hneq
    (restrictedSolomonoff_markov_domain_characterization_positive_bool
      (M := M) (W := W) xs ys hlen hx hstart hsum b)

/-- Negative diagnostic in the generic `Fin 2` summary presentation. -/
theorem restrictedSolomonoff_markov_no_same_summary_predictor_mismatch_fin2
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    ¬ ∃ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
        (hlen : xs.length = ys.length) (hx : 0 < xs.length)
        (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
        (b : Bool),
        TransCounts.summary (k := 2) (encodeBoolWord xs) =
          TransCounts.summary (k := 2) (encodeBoolWord ys) ∧
        M.predictBit xs b ≠ M.predictBit ys b := by
  intro h
  rcases h with ⟨xs, ys, hlen, hx, hstart, b, hsum, hneq⟩
  exact hneq
    (restrictedSolomonoff_markov_domain_characterization_positive_fin2
      (M := M) (W := W) xs ys hlen hx hstart hsum b)

/-- Direct νPLN-facing Markov master chain in the explicit binary presentation:

1. the restricted Solomonoff predictor depends only on the binary Markov
   summary `(ff,ft,tf,tt,lastBit)`;
2. equal-summary histories share the same Markov-Dirichlet update state;
3. the witnessed law still satisfies the standard Solomonoff regret bound.

This is the honest post-Markov analogue of the exchangeable `νPLN` story:
the sufficient statistic is no longer plain counts, but the Markov state
`(transition counts, current bit)`. -/
theorem restrictedSolomonoff_markov_nupln_master_chain_bool
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys) (b : Bool),
      M.predictBit xs b = M.predictBit ys b) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb W.domain.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb W.domain.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) W.law c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy W.law
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
              (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact restrictedSolomonoff_markov_domain_characterization_positive_bool (M := M) (W := W)
  · intro xs ys hx hsum
    exact W.domain.dirichlet_common_state_update_bool xs ys hx hsum
  · intro n
    exact W.domain.solomonoff_regret_bound n

/-- The same direct Markov νPLN master chain, presented through the generic
`Fin 2` transition-summary state on the encoded histories. -/
theorem restrictedSolomonoff_markov_nupln_master_chain_fin2
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum :
        TransCounts.summary (k := 2) (encodeBoolWord xs) =
          TransCounts.summary (k := 2) (encodeBoolWord ys))
      (b : Bool),
      M.predictBit xs b = M.predictBit ys b) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum :
        TransCounts.summary (k := 2) (encodeBoolWord xs) =
          TransCounts.summary (k := 2) (encodeBoolWord ys)),
      ∃ state : TransCounts 2 × Fin 2,
        TransCounts.summary (k := 2) (encodeBoolWord xs) = some state ∧
        TransCounts.summary (k := 2) (encodeBoolWord ys) = some state ∧
        ∀ a : Fin 2,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord xs ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal (MarkovDirichlet.stepProb W.domain.prior state.1 state.2 a) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord ys ++ [a]) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal (MarkovDirichlet.stepProb W.domain.prior state.1 state.2 a)) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin 2)) W.law c ∧
          Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy W.law
            (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
              (α := Fin 2)) n ≤
            Real.log (1 / c.toReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact restrictedSolomonoff_markov_domain_characterization_positive_fin2 (M := M) (W := W)
  · intro xs ys hx hsum
    have hx' : 0 < (encodeBoolWord xs).length := by
      simpa using hx
    exact W.domain.dirichlet_common_state_update_fin2 (encodeBoolWord xs) (encodeBoolWord ys) hx' hsum
  · intro n
    exact W.domain.solomonoff_regret_bound n

/-- Short νPLN-style justification theorem for the honest Markov witness:
the restricted Solomonoff predictor and the canonical Markov-Dirichlet
reference family collapse to the same explicit binary summary state. -/
theorem restrictedSolomonoff_markov_nupln_justification_bool
    (M : RestrictedSolomonoffPrior)
    (W : RestrictedSolomonoffMarkovWitness M) :
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString)
      (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (_hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (_hsum : binarySummary xs = binarySummary ys) (b : Bool),
      M.predictBit xs b = M.predictBit ys b) ∧
    (∀ (xs ys : Mettapedia.Logic.SolomonoffPrior.BinString) (_hx : 0 < xs.length)
      (_hsum : binarySummary xs = binarySummary ys),
      ∃ state : BinarySummaryState,
        binarySummary xs = some state ∧
        binarySummary ys = some state ∧
        ∀ a : Bool,
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord (xs ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord xs) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb W.domain.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a)) ∧
          (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
              (encodeBoolWord (ys ++ [a])) =
            (MarkovDirichlet.markovDirichletPrefixMeasure (k := 2) (by decide) W.domain.prior)
                (encodeBoolWord ys) *
              ENNReal.ofReal
                (MarkovDirichlet.stepProb W.domain.prior
                  (BinarySummaryState.toFin2State state).1
                  (BinarySummaryState.toFin2State state).2
                  (boolToFin2 a))) := by
  exact (restrictedSolomonoff_markov_nupln_master_chain_bool (M := M) (W := W)).elim
    (fun hpred hrest => ⟨hpred, hrest.1⟩)

end MarkovDomainCharacterization

/-! ## The νPLN Story -/

section NuPLN

open MeasureTheory

/-- A restricted Solomonoff prior whose finite-prefix law is realized by a
probability law on infinite bitstrings satisfies the standard νPLN domain
conditions. -/
theorem restrictedSolomonoff_plnDomainConditions_of_prefixLaw
    (M : RestrictedSolomonoffPrior)
    (μ : Measure InfBinString)
    (hμprob : IsProbabilityMeasure μ)
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    Mettapedia.Logic.DeFinetti.PLNDomainConditions (fun i ω => ω i) μ := by
  simpa [Mettapedia.Logic.DeFinetti.PLNDomainConditions] using
    restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
      (M := M) μ hμprob hprefix

/-- νPLN master chain specialized to restricted Solomonoff priors whose
finite-prefix law is realized on infinite binary streams. -/
theorem restrictedSolomonoff_nupln_master_chain_of_prefixLaw
    (M : RestrictedSolomonoffPrior)
    (μ : Measure InfBinString)
    (hμprob : IsProbabilityMeasure μ)
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    ∃ (B : Mettapedia.Logic.DeFinetti.BernoulliMixture),
      Mettapedia.Logic.DeFinetti.Represents B (fun i (ω : InfBinString) => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        countTrue xs₁ = countTrue xs₂ → B.prob xs₁ = B.prob xs₂) ∧
      (∀ n_pos n_neg : ℕ,
        Mettapedia.Logic.Exchangeability.evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ,
        n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
        |Mettapedia.Logic.EvidenceCounts.plnStrength n_pos n_neg -
            Mettapedia.Logic.EvidenceCounts.uniformPosteriorMean n_pos n_neg| < ε) := by
  letI : IsProbabilityMeasure μ := hμprob
  have hX : ∀ i : ℕ, Measurable (fun ω : InfBinString => ω i) := by
    intro i
    exact measurable_pi_apply i
  exact
    Mettapedia.Logic.DeFinetti.nupln_master_chain
      (X := fun i (ω : InfBinString) => ω i)
      (μ := μ)
      hX
      (restrictedSolomonoff_plnDomainConditions_of_prefixLaw
        (M := M) μ hμprob hprefix)

/-- Short νPLN consequence specialized to restricted Solomonoff priors:
exchangeable prefix-law realizations admit a Bernoulli-mixture representation
with counts as sufficient statistics. -/
theorem restrictedSolomonoff_nupln_justification_of_prefixLaw
    (M : RestrictedSolomonoffPrior)
    (μ : Measure InfBinString)
    (hμprob : IsProbabilityMeasure μ)
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    ∃ (B : Mettapedia.Logic.DeFinetti.BernoulliMixture),
      Mettapedia.Logic.DeFinetti.Represents B (fun i (ω : InfBinString) => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        countTrue xs₁ = countTrue xs₂ → B.prob xs₁ = B.prob xs₂) := by
  letI : IsProbabilityMeasure μ := hμprob
  have hX : ∀ i : ℕ, Measurable (fun ω : InfBinString => ω i) := by
    intro i
    exact measurable_pi_apply i
  exact
    Mettapedia.Logic.DeFinetti.nupln_justification
      (X := fun i (ω : InfBinString) => ω i)
      (μ := μ)
      hX
      (restrictedSolomonoff_plnDomainConditions_of_prefixLaw
        (M := M) μ hμprob hprefix)

end NuPLN

/-! ## Computational Aspects -/

section Computational

/- TODO: computational statements (tractability, relation to LLM approximations).

   These should be written as prose, or as precise complexity statements once we have an
   explicit computational model for the restricted inference.
-/

end Computational

end Mettapedia.Logic.SolomonoffExchangeable
