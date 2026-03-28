import Mettapedia.GSLT.Dynamics.PathIntegral
import Mathlib.Data.Complex.Basic

/-!
# Construction 10.1 and the Main Conservation Kernel

This file formalizes the constructive core of Meredith's
"Computation, Causality, and Consciousness" (2026), Part I, §10.

## Main Definitions

* `QuantumTraceEntry` — resource-aware trace entries with amplitudes and costs
* `QuantumState` — Construction 10.1 states `⟨P, τ, A⟩`
* `QuantumStep` — forward/backward reversible quantum-resource steps
* `conservedBalance` — account + trace ledger, invariant under `QuantumStep`
* `transitionProbability` — `|⟨Q|P⟩|²` for finite-support path families
* `LocalUnitaryWitness` — explicit one-step normalization witness
* `PathProbabilityNormalization` — explicit global normalization interface
* `CPTSymmetric` — explicit interface for the paper's CPT automorphism claim

## Design Note

The resource part of Theorem 10.1 is derivable from the reversible debit/credit
construction and is proved here. The probability and CPT parts need additional
global hypotheses beyond the current finite-support kernel, so this file makes
those hypotheses explicit instead of pretending they have already been earned.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §§7, 9, 10
- Feynman & Hibbs, "Quantum Mechanics and Path Integrals"
-/

namespace Mettapedia.GSLT

variable {S : GSLT} {A : Type*} {k : Nat}

/-- A resource-aware quantum trace entry stores the step, its amplitude, and its cost. -/
structure QuantumTraceEntry (S : GSLT) (A : Type*) (k : Nat) where
  /-- Source term before the rewrite step -/
  source : S.Term
  /-- Target term after the rewrite step -/
  target : S.Term
  /-- Proof that the source rewrites to the target -/
  step : S.Step source target
  /-- Complex amplitude attached to the step -/
  amplitude : Complex
  /-- Resource cost debited by the step -/
  cost : VectorialAccount A k

/-- A finite causal history in the quantum-resource reversible envelope. -/
abbrev QuantumTrace (S : GSLT) (A : Type*) (k : Nat) := List (QuantumTraceEntry S A k)

/-- Construction 10.1 state space: triples `⟨P, τ, A⟩`. -/
structure QuantumState (S : GSLT) (A : Type*) (k : Nat) where
  /-- Current term -/
  current : S.Term
  /-- Resource-aware trace -/
  history : QuantumTrace S A k
  /-- Current account value -/
  account : VectorialAccount A k

namespace QuantumState

/-- Initial quantum-resource state with empty trace. -/
def initial (t : S.Term) (account : VectorialAccount A k) : QuantumState S A k :=
  { current := t, history := [], account := account }

end QuantumState

namespace QuantumTraceEntry

/-- CPT/time-reversal acts on amplitudes by complex conjugation. -/
def cptConjugate (e : QuantumTraceEntry S A k) : QuantumTraceEntry S A k :=
  { e with amplitude := star e.amplitude }

@[simp] theorem cptConjugate_involutive (e : QuantumTraceEntry S A k) :
    cptConjugate (cptConjugate e) = e := by
  cases e
  simp [cptConjugate]

end QuantumTraceEntry

namespace QuantumState

/-- Candidate CPT/time-reversal transform: reverse the trace order and conjugate amplitudes. -/
def cptTransform (q : QuantumState S A k) : QuantumState S A k :=
  { current := q.current
    history := (q.history.map QuantumTraceEntry.cptConjugate).reverse
    account := q.account }

@[simp] theorem map_cptConjugate_comp (history : QuantumTrace S A k) :
    List.map (QuantumTraceEntry.cptConjugate ∘ QuantumTraceEntry.cptConjugate) history = history := by
  induction history with
  | nil => rfl
  | cons e rest ih =>
      simp [Function.comp, ih]

@[simp] theorem cptTransform_involutive (q : QuantumState S A k) :
    cptTransform (cptTransform q) = q := by
  cases q
  simp [cptTransform, List.map_map]

end QuantumState

/-- Total cost recorded in a quantum trace. -/
def traceAccount [Add A] [Zero A] : QuantumTrace S A k → VectorialAccount A k
  | [] => 0
  | e :: rest => e.cost + traceAccount rest

@[simp] theorem traceAccount_nil [Add A] [Zero A] :
    traceAccount (S := S) (A := A) (k := k) ([] : QuantumTrace S A k) = 0 := rfl

@[simp] theorem traceAccount_cons [Add A] [Zero A]
    (e : QuantumTraceEntry S A k) (rest : QuantumTrace S A k) :
    traceAccount (S := S) (A := A) (k := k) (e :: rest) = e.cost + traceAccount rest := rfl

@[simp] theorem traceAccount_map_cptConjugate [Add A] [Zero A]
    (history : QuantumTrace S A k) :
    traceAccount (S := S) (A := A) (k := k) (history.map QuantumTraceEntry.cptConjugate) =
      traceAccount history := by
  induction history with
  | nil => rfl
  | cons e rest ih =>
      simp [ih, QuantumTraceEntry.cptConjugate]

theorem traceAccount_append [AddCommMonoid A]
    (left right : QuantumTrace S A k) :
    traceAccount (S := S) (A := A) (k := k) (left ++ right) =
      traceAccount left + traceAccount right := by
  induction left with
  | nil =>
      funext i
      change traceAccount (S := S) (A := A) (k := k) right i =
        0 + traceAccount (S := S) (A := A) (k := k) right i
      simp
  | cons e rest ih =>
      funext i
      change e.cost i + traceAccount (S := S) (A := A) (k := k) (rest ++ right) i =
        (e.cost i + traceAccount (S := S) (A := A) (k := k) rest i) +
          traceAccount (S := S) (A := A) (k := k) right i
      rw [congrFun ih i]
      change e.cost i +
          (traceAccount (S := S) (A := A) (k := k) rest i +
            traceAccount (S := S) (A := A) (k := k) right i) =
        e.cost i + traceAccount (S := S) (A := A) (k := k) rest i +
          traceAccount (S := S) (A := A) (k := k) right i
      simp [add_assoc]

theorem traceAccount_reverse [AddCommMonoid A]
    (history : QuantumTrace S A k) :
    traceAccount (S := S) (A := A) (k := k) history.reverse = traceAccount history := by
  induction history with
  | nil =>
      funext i
      simp [traceAccount]
  | cons e rest ih =>
      funext i
      have happ :=
        congrFun (traceAccount_append (S := S) (A := A) (k := k) rest.reverse [e]) i
      have hih := congrFun ih i
      calc
        traceAccount (S := S) (A := A) (k := k) (List.reverse (e :: rest)) i
            = traceAccount (S := S) (A := A) (k := k) (rest.reverse ++ [e]) i := by
                simp [List.reverse_cons]
        _ = (traceAccount (S := S) (A := A) (k := k) rest.reverse +
              traceAccount (S := S) (A := A) (k := k) [e]) i := happ
        _ = traceAccount (S := S) (A := A) (k := k) rest.reverse i + e.cost i := by
                change traceAccount (S := S) (A := A) (k := k) rest.reverse i + (e.cost i + 0) =
                  traceAccount (S := S) (A := A) (k := k) rest.reverse i + e.cost i
                simp
        _ = traceAccount (S := S) (A := A) (k := k) rest i + e.cost i := by
                rw [hih]
        _ = e.cost i + traceAccount (S := S) (A := A) (k := k) rest i := by
                simp [add_comm]
        _ = traceAccount (S := S) (A := A) (k := k) (e :: rest) i := by
                rfl

namespace QuantumState

theorem cptTransform_traceAccount [AddCommMonoid A] (q : QuantumState S A k) :
    traceAccount (S := S) (A := A) (k := k) q.cptTransform.history = traceAccount q.history := by
  simp [QuantumState.cptTransform, traceAccount_reverse]

end QuantumState

/-- The conserved ledger quantity: liquid account plus what is recorded in the trace. -/
def conservedBalance [Add A] [Zero A] (q : QuantumState S A k) : VectorialAccount A k :=
  q.account + traceAccount q.history

namespace QuantumState

theorem cptTransform_conservedBalance [AddCommMonoid A] (q : QuantumState S A k) :
    conservedBalance (cptTransform q) = conservedBalance q := by
  funext i
  have htrace := congrFun (cptTransform_traceAccount (S := S) (A := A) (k := k) q) i
  simpa [conservedBalance, QuantumState.cptTransform] using congrArg (fun x => q.account i + x) htrace

end QuantumState

/-- Net account change between two states. -/
def netAccountChange [Sub A] (start finish : QuantumState S A k) : VectorialAccount A k :=
  fun i => finish.account i - start.account i

/-- A closed rewrite cycle returns to the same current term and the same trace boundary. -/
def ClosedRewriteCycle (start finish : QuantumState S A k) : Prop :=
  start.current = finish.current ∧ start.history = finish.history

/-- One quantum-resource step in the reversible envelope from Construction 10.1. -/
inductive QuantumStep (wm : WeightMap S Complex) (cm : CostMap S A k) [Add A] [Sub A] :
    QuantumState S A k → QuantumState S A k → Prop where
  /-- Forward step: debit the account and record the amplitude/cost in the trace. -/
  | forward {t u : S.Term} (h : S.Step t u)
      (history : QuantumTrace S A k) (account : VectorialAccount A k) :
      QuantumStep wm cm
        { current := t, history := history, account := account }
        { current := u
          history :=
            { source := t
              target := u
              step := h
              amplitude := wm.weight h
              cost := cm.cost h } :: history
          account := VectorialAccount.debit account (cm.cost h) }
  /-- Backward step: pop the trace head and credit back the same cost. -/
  | backward {t u : S.Term} (h : S.Step t u)
      (history : QuantumTrace S A k) (account : VectorialAccount A k) :
      QuantumStep wm cm
        { current := u
          history :=
            { source := t
              target := u
              step := h
              amplitude := wm.weight h
              cost := cm.cost h } :: history
          account := account }
        { current := t
          history := history
          account := VectorialAccount.credit account (cm.cost h) }

/-- Reflexive-transitive closure of `QuantumStep`. -/
inductive QuantumStepStar (wm : WeightMap S Complex) (cm : CostMap S A k) [Add A] [Sub A] :
    QuantumState S A k → QuantumState S A k → Prop where
  | refl (q : QuantumState S A k) : QuantumStepStar wm cm q q
  | step {q₁ q₂ q₃ : QuantumState S A k} :
      QuantumStep wm cm q₁ q₂ →
      QuantumStepStar wm cm q₂ q₃ →
      QuantumStepStar wm cm q₁ q₃

namespace QuantumStepStar

theorem trans {wm : WeightMap S Complex} {cm : CostMap S A k}
    [Add A] [Sub A]
    {q₁ q₂ q₃ : QuantumState S A k}
    (h₁ : QuantumStepStar wm cm q₁ q₂)
    (h₂ : QuantumStepStar wm cm q₂ q₃) :
    QuantumStepStar wm cm q₁ q₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep hrest ih => exact .step hstep (ih h₂)

end QuantumStepStar

/-- Forward and backward steps preserve the ledger quantity `account + trace`. -/
theorem conservedBalance_step [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStep wm cm q₁ q₂) :
    conservedBalance q₂ = conservedBalance q₁ := by
  cases h with
  | forward hstep history account =>
      funext i
      change (account i - cm.cost hstep i) + (cm.cost hstep i + traceAccount history i) =
        account i + traceAccount history i
      simp [sub_eq_add_neg, add_assoc]
  | backward hstep history account =>
      funext i
      change (account i + cm.cost hstep i) + traceAccount history i =
        account i + (cm.cost hstep i + traceAccount history i)
      simp [add_assoc]

/-- The ledger quantity is invariant along multi-step quantum-resource executions. -/
theorem conservedBalance_stepStar [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStepStar wm cm q₁ q₂) :
    conservedBalance q₂ = conservedBalance q₁ := by
  induction h with
  | refl _ => rfl
  | step hstep hrest ih =>
      exact ih.trans (conservedBalance_step (A := A) (k := k) hstep)

/-- If a quantum-resource execution returns to the same trace boundary,
    the account itself is unchanged. -/
theorem account_eq_of_history_eq [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStepStar wm cm q₁ q₂)
    (hhist : q₁.history = q₂.history) :
    q₂.account = q₁.account := by
  have hbal := conservedBalance_stepStar (A := A) (k := k) h
  have hbal' : q₂.account + traceAccount q₁.history = q₁.account + traceAccount q₁.history := by
    simpa [conservedBalance, hhist] using hbal
  funext i
  exact add_right_cancel (congrFun hbal' i)

/-- Theorem 10.1(i), via Theorem 7.1: closed cycles conserve the vectorial account. -/
theorem closedCycle_account_eq [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStepStar wm cm q₁ q₂)
    (hclosed : ClosedRewriteCycle q₁ q₂) :
    q₂.account = q₁.account := by
  exact account_eq_of_history_eq (A := A) (k := k) h hclosed.2

/-- Closed cycles have zero net account change. -/
theorem netAccountChange_eq_zero_of_closedCycle [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStepStar wm cm q₁ q₂)
    (hclosed : ClosedRewriteCycle q₁ q₂) :
    netAccountChange q₁ q₂ = 0 := by
  have hacc := closedCycle_account_eq (A := A) (k := k) h hclosed
  funext i
  change q₂.account i - q₁.account i = 0
  simp [congrFun hacc i]

/-- Resource conservation for initial-to-initial closed paths. -/
theorem resourceConservation_initialClosedPath [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {t : S.Term} {a₀ a₁ : VectorialAccount A k}
    (h :
      QuantumStepStar wm cm
        (QuantumState.initial (S := S) (A := A) (k := k) t a₀)
        (QuantumState.initial (S := S) (A := A) (k := k) t a₁)) :
    a₁ = a₀ := by
  simpa [QuantumState.initial] using
    closedCycle_account_eq (A := A) (k := k) (wm := wm) (cm := cm) h ⟨rfl, rfl⟩

/-- Transition probability for a finite-support path family: `|⟨Q|P⟩|²`. -/
def transitionProbability (wm : WeightMap S Complex)
    {t u : S.Term} (Γ : FinitePathFamily S t u) : ℝ :=
  Complex.normSq (transitionAmplitude wm Γ)

/-- The one-step path generated by a single rewrite step. -/
def oneStepPath {t u : S.Term} (h : S.Step t u) : S.RewritePath t u :=
  .cons h (.nil u)

/-- The transition probability contributed by a single rewrite step. -/
def oneStepTransitionProbability (wm : WeightMap S Complex)
    {t u : S.Term} (h : S.Step t u) : ℝ :=
  transitionProbability wm (FinitePathFamily.singleton (S := S) (oneStepPath h))

@[simp] theorem oneStepTransitionProbability_eq_normSq
    (wm : WeightMap S Complex) {t u : S.Term} (h : S.Step t u) :
    oneStepTransitionProbability (S := S) wm h = Complex.normSq (wm.weight h) := by
  rw [oneStepTransitionProbability, transitionProbability, transitionAmplitude_singleton]
  simp [oneStepPath, pathAmplitude]

/-- Explicit local unitarity witness: a finite family of outgoing one-step transitions
    whose squared amplitudes sum to `1`. -/
structure LocalUnitaryWitness (wm : WeightMap S Complex) where
  /-- Finite outgoing step family chosen at each term -/
  outgoing : S.Term → List S.LabeledStep
  /-- Every listed step really starts at the queried term -/
  source_mem : ∀ {t : S.Term} {e : S.LabeledStep}, e ∈ outgoing t → e.source = t
  /-- One-step probabilities normalize at each term -/
  normalized : ∀ t,
    ((outgoing t).map fun e => Complex.normSq (wm.weight e.step)).sum = 1

/-- Under an explicit local unitarity witness, one-step transition probabilities sum to `1`. -/
theorem oneStepProbabilityConservation
    {wm : WeightMap S Complex}
    (hU : LocalUnitaryWitness (S := S) wm) (t : S.Term) :
    ((hU.outgoing t).map fun e => oneStepTransitionProbability (S := S) wm e.step).sum = 1 := by
  simpa using hU.normalized t

/-- Explicit global normalization interface for finite-support path amplitudes. -/
structure PathProbabilityNormalization (wm : WeightMap S Complex) where
  /-- Chosen finite support of destination terms for each source term -/
  support : S.Term → List S.Term
  /-- Chosen finite-support path family for each source/target pair -/
  families : (t : S.Term) → (u : S.Term) → FinitePathFamily S t u
  /-- Total probability over the chosen support is normalized -/
  normalized : ∀ t,
    ((support t).map fun u => transitionProbability (S := S) wm (families t u)).sum = 1

/-- The explicit global probability-conservation interface yields the paper's
    normalization equation on the chosen finite support. -/
theorem transitionProbabilityConservation
    {wm : WeightMap S Complex}
    (hP : PathProbabilityNormalization (S := S) wm) (t : S.Term) :
    ((hP.support t).map fun u => transitionProbability (S := S) wm (hP.families t u)).sum = 1 :=
  hP.normalized t

namespace WeightMap

/-- Complex-conjugated weight map, the weight part of the paper's CPT transform. -/
def cptConjugate (wm : WeightMap S Complex) : WeightMap S Complex where
  weight := fun h => star (wm.weight h)

@[simp] theorem cptConjugate_weight (wm : WeightMap S Complex)
    {t u : S.Term} (h : S.Step t u) :
    (cptConjugate wm).weight h = star (wm.weight h) := rfl

end WeightMap

/-- Explicit interface for Theorem 10.1(iii): the candidate CPT transform
    acts as an automorphism of the reversible quantum-resource theory. -/
structure CPTSymmetric (wm : WeightMap S Complex) (cm : CostMap S A k) [Add A] [Sub A] where
  /-- Time reversal and complex conjugation send each step to a valid reversed step. -/
  preservesStep :
    ∀ {q₁ q₂ : QuantumState S A k}, QuantumStep wm cm q₁ q₂ →
      QuantumStep (WeightMap.cptConjugate wm) cm
        (QuantumState.cptTransform q₂) (QuantumState.cptTransform q₁)

/-- Theorem 10.1(i): proved resource component of the main conservation theorem. -/
theorem mainConservation_resource [AddGroup A]
    {wm : WeightMap S Complex} {cm : CostMap S A k}
    {q₁ q₂ : QuantumState S A k}
    (h : QuantumStepStar wm cm q₁ q₂)
    (hclosed : ClosedRewriteCycle q₁ q₂) :
    netAccountChange q₁ q₂ = 0 :=
  netAccountChange_eq_zero_of_closedCycle (A := A) (k := k) h hclosed

/-- Theorem 10.1(ii), conservative form: once a global finite-support normalization
    witness is provided, total transition probability is normalized. -/
theorem mainConservation_probability
    {wm : WeightMap S Complex}
    (hP : PathProbabilityNormalization (S := S) wm) (t : S.Term) :
    ((hP.support t).map fun u => transitionProbability (S := S) wm (hP.families t u)).sum = 1 :=
  transitionProbabilityConservation (S := S) hP t

/-- Theorem 10.1(iii), conservative form: expose the CPT-symmetry claim as an
    explicit automorphism interface over the candidate transform. -/
theorem mainConservation_cpt
    {wm : WeightMap S Complex} {cm : CostMap S A k} [Add A] [Sub A]
    (hCPT : CPTSymmetric (S := S) (A := A) (k := k) wm cm)
    {q₁ q₂ : QuantumState S A k} (h : QuantumStep wm cm q₁ q₂) :
    QuantumStep (WeightMap.cptConjugate wm) cm
      (QuantumState.cptTransform q₂) (QuantumState.cptTransform q₁) :=
  hCPT.preservesStep h

/-! ## Summary

This file establishes:

1. **QuantumState**: Construction 10.1 triples `⟨P, τ, A⟩`
2. **QuantumStep**: forward/backward debit-credit reversible dynamics
3. **mainConservation_resource**: Theorem 10.1(i), fully proved
4. **oneStepProbabilityConservation**: constructive one-step normalization result
5. **PathProbabilityNormalization**: explicit finite-support interface for 10.1(ii)
6. **QuantumState.cptTransform / CPTSymmetric**: explicit interface for 10.1(iii)

**Paper Coverage**: Construction 10.1; Theorem 10.1(i) proved; Theorem 10.1(ii)–(iii)
made explicit as normalization/symmetry interfaces with constructive finite support.

**No sorry statements** — the proved part is fully formalized, and the remaining
claims are isolated behind explicit hypotheses.
-/

end Mettapedia.GSLT
