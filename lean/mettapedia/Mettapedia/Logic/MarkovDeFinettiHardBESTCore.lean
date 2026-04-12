import Mettapedia.Logic.MarkovDeFinettiHardEuler

/-!
# Markov de Finetti (Hard Direction) — BEST Core (Phase A)

This module introduces the graph/token counting layer used by the BEST theorem
formalization.  It is intentionally finite and concrete:

- `EulerGraph k` is a directed multigraph on `Fin k` given by edge multiplicities.
- `edgeTok` turns multiplicities into explicit edge tokens.
- `graphOfState` maps `MarkovState` to this graph representation.

The lemmas here are bookkeeping identities that connect existing trajectory
infrastructure (`stateFinset`, `flow_balance_stateOfTraj`) to the graph layer.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBESTCore

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardEuler

variable {k : ℕ}

/-- Directed multigraph on `Fin k`, encoded as edge multiplicities. -/
abbrev EulerGraph (k : ℕ) := Fin k → Fin k → ℕ

/-- Out-degree in the multiplicity graph. -/
def outDegG (G : EulerGraph k) (a : Fin k) : ℕ :=
  ∑ b : Fin k, G a b

/-- In-degree in the multiplicity graph. -/
def inDegG (G : EulerGraph k) (b : Fin k) : ℕ :=
  ∑ a : Fin k, G a b

/-- Total number of edge tokens in the graph. -/
def totalEdgeTokens (G : EulerGraph k) : ℕ :=
  ∑ a : Fin k, outDegG (k := k) G a

/-- Edge-token type: one token per multiplicity copy of each directed edge `(a,b)`. -/
def edgeTok (G : EulerGraph k) : Type :=
  Σ a : Fin k, Σ b : Fin k, Fin (G a b)

instance instFintypeEdgeTok (G : EulerGraph k) : Fintype (edgeTok (k := k) G) := by
  classical
  unfold edgeTok
  infer_instance

/-- Outgoing edge tokens at vertex `a`. -/
def outTok (G : EulerGraph k) (a : Fin k) : Type :=
  Σ b : Fin k, Fin (G a b)

instance instFintypeOutTok (G : EulerGraph k) (a : Fin k) :
    Fintype (outTok (k := k) G a) := by
  classical
  unfold outTok
  infer_instance

/-- Incoming edge tokens at vertex `b`. -/
def inTok (G : EulerGraph k) (b : Fin k) : Type :=
  Σ a : Fin k, Fin (G a b)

instance instFintypeInTok (G : EulerGraph k) (b : Fin k) :
    Fintype (inTok (k := k) G b) := by
  classical
  unfold inTok
  infer_instance

lemma card_outTok (G : EulerGraph k) (a : Fin k) :
    Fintype.card (outTok (k := k) G a) = outDegG (k := k) G a := by
  classical
  unfold outTok outDegG
  simp [Fintype.card_sigma]

lemma card_inTok (G : EulerGraph k) (b : Fin k) :
    Fintype.card (inTok (k := k) G b) = inDegG (k := k) G b := by
  classical
  unfold inTok inDegG
  simp [Fintype.card_sigma]

lemma totalEdgeTokens_eq_sum_card_outTok (G : EulerGraph k) :
    totalEdgeTokens (k := k) G = ∑ a : Fin k, Fintype.card (outTok (k := k) G a) := by
  simp [totalEdgeTokens, card_outTok]

lemma card_edgeTok (G : EulerGraph k) :
    Fintype.card (edgeTok (k := k) G) = totalEdgeTokens (k := k) G := by
  classical
  unfold edgeTok totalEdgeTokens outDegG
  simp [Fintype.card_sigma]

lemma totalEdgeTokens_eq_sum_inDeg (G : EulerGraph k) :
    totalEdgeTokens (k := k) G = ∑ b : Fin k, inDegG (k := k) G b := by
  classical
  unfold totalEdgeTokens outDegG inDegG
  have hprodA :
      (∑ a : Fin k, ∑ b : Fin k, G a b) =
        ∑ p : Fin k × Fin k, G p.1 p.2 := by
    simpa using (Fintype.sum_prod_type' (f := fun a b => G a b)).symm
  have hprodB :
      (∑ b : Fin k, ∑ a : Fin k, G a b) =
        ∑ p : Fin k × Fin k, G p.2 p.1 := by
    simpa using (Fintype.sum_prod_type' (f := fun b a => G a b)).symm
  have hswap :
      (∑ p : Fin k × Fin k, G p.2 p.1) =
        ∑ p : Fin k × Fin k, G p.1 p.2 := by
    refine (Fintype.sum_equiv (Equiv.prodComm (Fin k) (Fin k))
      (fun p => G p.2 p.1) (fun p => G p.1 p.2) ?_)
    intro p
    rfl
  exact hprodA.trans (hprodB.trans hswap).symm

lemma totalEdgeTokens_eq_sum_card_inTok (G : EulerGraph k) :
    totalEdgeTokens (k := k) G = ∑ b : Fin k, Fintype.card (inTok (k := k) G b) := by
  simp [totalEdgeTokens_eq_sum_inDeg, card_inTok]

/-- The multiplicity graph associated to a `MarkovState`. -/
def graphOfState (s : MarkovState k) : EulerGraph k :=
  s.counts.counts

@[simp] lemma graphOfState_apply (s : MarkovState k) (a b : Fin k) :
    graphOfState (k := k) s a b = s.counts.counts a b :=
  rfl

lemma outDeg_graphOfState_eq (s : MarkovState k) (a : Fin k) :
    outDegG (k := k) (graphOfState (k := k) s) a =
      MarkovDeFinettiHardEuler.outdeg (k := k) s a := by
  simp [graphOfState, outDegG, MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal]

lemma inDeg_graphOfState_eq (s : MarkovState k) (a : Fin k) :
    inDegG (k := k) (graphOfState (k := k) s) a =
      MarkovDeFinettiHardEuler.indeg (k := k) s a := by
  simp [graphOfState, inDegG, MarkovDeFinettiHardEuler.indeg]

lemma card_outTok_graphOfState_eq (s : MarkovState k) (a : Fin k) :
    Fintype.card (outTok (k := k) (graphOfState (k := k) s) a) =
      MarkovDeFinettiHardEuler.outdeg (k := k) s a := by
  simpa [card_outTok] using outDeg_graphOfState_eq (k := k) s a

lemma card_inTok_graphOfState_eq (s : MarkovState k) (a : Fin k) :
    Fintype.card (inTok (k := k) (graphOfState (k := k) s) a) =
      MarkovDeFinettiHardEuler.indeg (k := k) s a := by
  simpa [card_inTok] using inDeg_graphOfState_eq (k := k) s a

lemma totalEdgeTokens_graphOfState_eq_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) :
    totalEdgeTokens (k := k) (graphOfState (k := k) s) = N := by
  simpa [totalEdgeTokens, outDeg_graphOfState_eq] using
    (MarkovDeFinettiHardEuler.sum_outdeg_of_mem_stateFinset (k := k) (eN := s) hs)

lemma card_edgeTok_graphOfState_eq_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) :
    Fintype.card (edgeTok (k := k) (graphOfState (k := k) s)) = N := by
  simpa [card_edgeTok] using
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs

/-- Euler-trail balance equations for states that arise from length-`N` trajectories. -/
lemma flow_balance_graphOfState_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) (a : Fin k) :
    outDegG (k := k) (graphOfState (k := k) s) a +
      (if s.last = a then 1 else 0) =
    inDegG (k := k) (graphOfState (k := k) s) a +
      (if s.start = a then 1 else 0) := by
  rcases Finset.mem_image.1 hs with ⟨xs, hxs, hstate⟩
  subst hstate
  simpa [outDegG, inDegG, graphOfState] using
    (MarkovDeFinettiHardEuler.flow_balance_stateOfTraj (k := k) (xs := xs) (a := a))

/-- Graph-form predicate for Euler-trail degree balance with designated start/last. -/
def IsEulerTrailBalanced (s : MarkovState k) : Prop :=
  ∀ a : Fin k,
    outDegG (k := k) (graphOfState (k := k) s) a +
      (if s.last = a then 1 else 0) =
    inDegG (k := k) (graphOfState (k := k) s) a +
      (if s.start = a then 1 else 0)

lemma isEulerTrailBalanced_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) :
    IsEulerTrailBalanced (k := k) s := by
  intro a
  exact flow_balance_graphOfState_of_mem_stateFinset (k := k) hs a

lemma card_balance_graphOfState_of_mem_stateFinset
    {N : ℕ} {s : MarkovState k} (hs : s ∈ stateFinset k N) (a : Fin k) :
    Fintype.card (outTok (k := k) (graphOfState (k := k) s) a) +
      (if s.last = a then 1 else 0) =
    Fintype.card (inTok (k := k) (graphOfState (k := k) s) a) +
      (if s.start = a then 1 else 0) := by
  simpa [card_outTok_graphOfState_eq, card_inTok_graphOfState_eq] using
    flow_balance_graphOfState_of_mem_stateFinset (k := k) hs a

end MarkovDeFinettiHardBESTCore

end Mettapedia.Logic
