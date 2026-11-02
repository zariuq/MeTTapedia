import Mettapedia.GSLT.Dynamics.WeightedInferenceHandlers
import Mettapedia.GSLT.Dynamics.ResumptionOperationTheory

/-!
# Finite inference expectations as weighted operations

This opt-in adapter consumes the independent inference theory. It constructs
an exhaustive weighted source for a handler's expectation and connects that
source to the existing finite operation theory. It does not identify one
sample with an exact posterior, or certify a native RNG or a textual parser.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.CertifiedInferenceOperations
open Finset Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.WeightedInference
open Mettapedia.GSLT.Dynamics
open WeightedInferenceHandlers WeightedBranchingResumption WeightedLinearInterpretation
open _root_.CategoryTheory Mettapedia.CategoryTheory.FiniteOperationTheory
open scoped Classical

variable {S : Type} [Fintype S] {target : S → ℝ} (h : Handler target)

abbrev State := Option (Fin (Fintype.card h.compile.Noise))

noncomputable def enumerate : Fin (Fintype.card h.compile.Noise) → h.compile.Noise :=
  (Fintype.equivFin h.compile.Noise).symm

noncomputable def expectationSource : Coalgebra (State h) S ℝ
  | none => .inr (List.ofFn fun i =>
      (some i, h.compile.law.1 (enumerate h i) * h.compile.weight (enumerate h i)))
  | some i => .inl (h.compile.output (enumerate h i))

/-- The source keeps each finite sampling occurrence, including zero weights. -/
theorem source_linear (f : S → ℝ) :
    evaluate (contributions (expectationSource h) 2 none) (Sum.elim f (fun _ => 0)) =
      ∑ s, target s * f s := by
  rw [contributions, expectationSource, evaluate_sequence, evaluate_ofFn]
  simp only [contributions, expectationSource, evaluate, one_mul, add_zero]
  change (∑ i, h.compile.law.1 (enumerate h i) * h.compile.weight (enumerate h i) *
    f (h.compile.output (enumerate h i))) = _
  have reindex := Fintype.sum_equiv (Fintype.equivFin h.compile.Noise).symm
    (fun i => h.compile.law.1 (enumerate h i) *
      (h.compile.weight (enumerate h i) * f (h.compile.output (enumerate h i))))
    (fun w => h.compile.law.1 w * (h.compile.weight w * f (h.compile.output w))) (fun _ => rfl)
  simp only [mul_assoc]
  rw [reindex]
  exact h.sound.integral f

abbrev Theory := ResumptionOperationTheory.FreeTheory (Operation (State h) ℝ) Response

def arity (n : Nat) : Theory h := n

/-- The same finite-arity operation theory used by native execution. Its
generic interface keeps this opt-in adapter independent of a native machine. -/
noncomputable def expectationOperation {n : Nat} (observe : S ⊕ State h → Fin n) :
    arity h n ⟶ arity h 1 :=
  ofTerms fun _ => ResumptionAlgebra.bind (cut (expectationSource h) 2 none)
    (fun leaf => ResumptionAlgebra.pure (observe leaf))

/-- The established operation handler executes this independently constructed
source; observation is downstream of the complete occurrence account. -/
theorem operation_correspondence {n : Nat} (observe : S ⊕ State h → Fin n) :
    (Mettapedia.CategoryTheory.FiniteOperationTheory.terms
      ((Mettapedia.GSLT.Dynamics.ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
        (expectationOperation h observe)) (0 : Fin 1)).run =
      (contributions (expectationSource h) 2 none).map (fun leaf => (observe leaf.1, leaf.2)) := by
  change WeightedResumption.interpret catalogue
    (ResumptionAlgebra.bind (cut (expectationSource h) 2 none)
      (fun leaf => ResumptionAlgebra.pure (observe leaf))) = _
  rw [WeightedResumption.interpret_map, interpret_cut]

/-- Budget zero retains the request as pending. -/
theorem pending_not_answer : contributions (expectationSource h) 0 none = [(Sum.inr none, 1)] := rfl

section FrozenProbes
variable {Θ Ω O Id : Type} [Fintype Ω] [Fintype O]

/-- The frozen request retains model, parameter, evidence, proposal and
purpose. Two equal present answers do not identify these dependencies. -/
structure Probe (Θ Ω O Id : Type) [Fintype Ω] [Fintype O] where
  request : Request Θ Ω O Id
  sampler : Handler request.target

/-- A checkpoint contains the full occurrence frontier, including unfinished
states and their accumulated coefficients. Its owner is the frozen probe. -/
structure Probe.Checkpoint (p : Probe Θ Ω O Id) where
  fuel : Nat
  frontier : List ((Ω ⊕ State p.sampler) × ℝ)
  valid : frontier = contributions (expectationSource p.sampler) fuel none

noncomputable def Probe.start (p : Probe Θ Ω O Id) : p.Checkpoint :=
  ⟨0, [(Sum.inr none, 1)], rfl⟩

/-- Advance the retained frontier itself; do not restart the completed prefix. -/
noncomputable def Probe.Checkpoint.advance {p : Probe Θ Ω O Id} (c : p.Checkpoint) (more : Nat) :
    p.Checkpoint where
  fuel := c.fuel + more
  frontier := WeightedResumption.sequence c.frontier (fun leaf => match leaf with
    | .inl answer => [(Sum.inl answer, 1)]
    | .inr pending => contributions (expectationSource p.sampler) more pending)
  valid := by
    rw [c.valid]
    convert (contributions_add (expectationSource p.sampler) c.fuel more none).symm using 1
    congr 2
    funext leaf
    cases leaf <;> rfl

/-- Splitting execution at a checkpoint preserves the complete weighted
frontier, not merely the set of completed values. -/
theorem Probe.Checkpoint.advance_correct {p : Probe Θ Ω O Id} (c : p.Checkpoint) (more : Nat) :
    (c.advance more).frontier = contributions (expectationSource p.sampler) (c.fuel+more) none :=
  (c.advance more).valid

theorem Probe.finished_expectation (p : Probe Θ Ω O Id) (f : Ω → ℝ) :
    evaluate ((p.start).advance 2).frontier (Sum.elim f (fun _ => 0)) =
      ∑ w, p.request.target w * f w := by
  rw [Probe.Checkpoint.advance_correct]
  exact source_linear p.sampler f

end FrozenProbes

end Mettapedia.Languages.MeTTa.PrimeCandidates.CertifiedInferenceOperations
