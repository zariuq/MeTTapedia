import Mathlib.Data.Multiset.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge
import Mettapedia.Logic.PLNWorldModel

/-!
# Canonical Semantic WM: Factorization + Marginalization

This module records the **semantic world-model** core as a factorized valuation:

* The WM state is an explicit **factor list**.
* Revision = add factors (at the state level).
* Queries are answered by **exact VE** on that factorization.

This is the canonical “WM = factorized valuation + marginalization” form,
independent of any PLN rule heuristics.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace ValuationWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

section Generic

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

/-- A canonical full configuration chosen from variable-wise nonempty state
spaces. This is used only to evaluate constant scoped valuations after all
variables have been eliminated. -/
noncomputable def arbitraryConfig
    [∀ v, Nonempty (fg.stateSpace v)] :
    FullConfig V (fun v => fg.stateSpace v) :=
  fun v => Classical.choice (inferInstance : Nonempty (fg.stateSpace v))

/-- A factorized evidence source (explicit factor list). -/
def WMSource (fg : FactorGraph V K) : Type _ :=
  List (VariableElimination.Factor (fg := fg))

/-- A WM state is a **commutative ledger** of independent factorized sources. -/
def WMState (fg : FactorGraph V K) : Type _ :=
  Multiset (WMSource fg)

/-- Exact unnormalized weight for a constraint set from a WM factorization. -/
noncomputable def weight
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  VariableElimination.veQueryWeightList fg W constraints

/-- Exact unnormalized weight computed through the bundled scoped-valuation VE
lane. This uses the scoped elimination interface directly, then evaluates the
resulting constant valuation at a canonical full configuration. -/
noncomputable def scopedWeight
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [∀ v, Nonempty (fg.stateSpace v)] [CommSemiring K] : K := by
  classical
  let order : List V := (Finset.univ : Finset V).toList
  let fs := VariableElimination.veFactorList (fg := fg) W constraints
  let ψ :=
    (ScopedValuation.combineAll
      (V := V) (β := fun v => fg.stateSpace v) (K := K)
      (ScopedValuation.eliminateVars
        (V := V) (β := fun v => fg.stateSpace v) (K := K)
        (ValuationBridge.toScopedValuations (fg := fg) fs) order) :
      ScopedValuation V (fun v => fg.stateSpace v) K)
  exact
    ((ψ : Valuation V (fun v => fg.stateSpace v) K)).val
      (arbitraryConfig (fg := fg))

omit [DecidableEq V] in
private theorem valuationFullAssign_empty_eq_emptyAssign
    (x : FullConfig V (fun v => fg.stateSpace v)) :
    ValuationBridge.fullAssign (fg := fg) x (∅ : Finset V) =
      VariableElimination.Factor.emptyAssign (fg := fg) := by
  funext v hv
  simp at hv

omit [DecidableEq V] in
private theorem toValuation_val_arbitraryConfig_eq_evalConst
    [∀ v, Nonempty (fg.stateSpace v)]
    (φ : VariableElimination.Factor fg) (h : φ.scope = ∅) :
    (ValuationBridge.toValuation (fg := fg) φ).val (arbitraryConfig (fg := fg)) =
      VariableElimination.Factor.evalConst (φ := φ) h := by
  cases φ with
  | mk scope potential =>
      cases h
      simp [ValuationBridge.toValuation, VariableElimination.Factor.evalConst,
        valuationFullAssign_empty_eq_emptyAssign]

/-- The bundled scoped-valuation query lane computes the same exact weight as
the operational VE query surface. -/
theorem scopedWeight_eq_weight
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [∀ v, Nonempty (fg.stateSpace v)] [CommSemiring K] :
    scopedWeight (fg := fg) (W := W) constraints =
      weight (fg := fg) (W := W) constraints := by
  classical
  let order : List V := (Finset.univ : Finset V).toList
  let fs := VariableElimination.veFactorList (fg := fg) W constraints
  let φ :=
    VariableElimination.combineAll (fg := fg) fs
  let raw :=
    VariableElimination.sumOutAll (fg := fg) φ order
  have hscope : raw.scope = ∅ := by
    simpa [raw, φ, order] using
      (VariableElimination.sumOutAll_scope_univ (fg := fg) (f := φ))
  have hscoped :
      ((ScopedValuation.combineAll
          (V := V) (β := fun v => fg.stateSpace v) (K := K)
          (ScopedValuation.eliminateVars
            (V := V) (β := fun v => fg.stateSpace v) (K := K)
            (ValuationBridge.toScopedValuations (fg := fg) fs) order) :
          ScopedValuation V (fun v => fg.stateSpace v) K) :
        Valuation V (fun v => fg.stateSpace v) K) =
        ValuationBridge.toValuation (fg := fg) raw := by
    symm
    simpa [raw, φ, fs, order] using
      (ValuationBridge.sumOutAll_combineAll_via_scopedValuation
        (fg := fg) (fs := fs) (order := order))
  unfold scopedWeight weight
  simp only
  rw [hscoped]
  simpa [raw, φ, fs, order, VariableElimination.veQueryWeightList] using
    (toValuation_val_arbitraryConfig_eq_evalConst
      (fg := fg) (φ := raw) hscope)

/-- Total unnormalized weight (partition function of the WM state). -/
noncomputable def total
    (W : WMSource fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  weight (fg := fg) (W := W) []

end Generic

/-! ## BinaryEvidence extraction for ENNReal factors -/

section ENNReal

variable {V : Type*} [DecidableEq V]
variable {fg : FactorGraph V ENNReal}

/-- BinaryEvidence for a single factorized source: pos = constrained weight, neg = remainder. -/
noncomputable def sourceEvidence
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    BinaryEvidence :=
  let pos := weight (fg := fg) (W := W) constraints
  let tot := total (fg := fg) (W := W)
  ⟨pos, tot - pos⟩

/-- BinaryEvidence for a WM ledger: sum evidence from each independent source. -/
noncomputable def evidence
    (W : WMState fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    BinaryEvidence :=
  (W.map (fun src => sourceEvidence (fg := fg) (W := src) constraints)).sum

instance : AddCommMonoid (WMState fg) := by
  dsimp [WMState]
  infer_instance

instance : EvidenceType (WMState fg) :=
  { toAddCommMonoid := inferInstance }

/-- Factorized WM as a `BinaryWorldModel` instance (ledger-of-sources semantics). -/
noncomputable instance
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)] :
    BinaryWorldModel (WMState fg) (List (Σ v : V, fg.stateSpace v)) where
  evidence W q := evidence (fg := fg) (W := W) q
  evidence_add W₁ W₂ q := by
    classical
    let f := fun src => sourceEvidence (fg := fg) (W := src) q
    -- `WMState fg` is definitionally `Multiset (WMSource fg)`, but `W₁ + W₂` carries the
    -- `WMState` `AddCommMonoid` instance, so `Multiset.map_add` (stated for `Multiset`'s
    -- own `+`) no longer matches `rw` syntactically under Lean 4.31.  Build the proof in
    -- term mode (full defeq) from the genuinely-`Multiset` lemmas instead.
    have h :
        (Multiset.map f (W₁ + W₂)).sum =
          (Multiset.map f W₁).sum + (Multiset.map f W₂).sum :=
      (congrArg Multiset.sum (Multiset.map_add f W₁ W₂)).trans (Multiset.sum_add _ _)
    simpa [evidence, f] using h
  evidence_zero q := by
    classical
    -- `evidence 0 q = (Multiset.map _ (0 : WMState fg)).sum`; the zero world is the empty
    -- multiset, on which `map` and `sum` compute to `0` definitionally.
    show (Multiset.map (fun src => sourceEvidence (fg := fg) (W := src) q)
      (0 : Multiset (WMSource fg))).sum = 0
    rw [Multiset.map_zero, Multiset.sum_zero]

end ENNReal

end ValuationWorldModel

end Mettapedia.ProbabilityTheory.BayesianNetworks
