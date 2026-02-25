import Mettapedia.Logic.PLNXiDerivedBNRules
import Mettapedia.Logic.PLNWorldModelTyped

/-!
# PLN Xi Derived BN Rules (Typed Wrappers)

Typed WM-layer wrappers for BN-derived rewrite rules.

Current BN query carriers are untyped (`PLNQuery ...`). This module lifts them
into the typed WM layer via the canonical one-sort embedding:

- sort index: `PUnit`
- query family: `fun _ => Query`
- typed WM instance: `WorldModelSigma.ofWorldModelUnit`
-/

namespace Mettapedia.Logic.PLNXiDerivedBNRules.Typed

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

noncomputable section

instance instWorldModelSigmaUnit
    (State Query : Type*)
    [EvidenceType State] [WorldModel State Query] :
    WorldModelSigma State PUnit (fun _ : PUnit => Query) :=
  WorldModelSigma.ofWorldModelUnit State Query

/-! ## Generic Unit-Sort Lift -/

/-- Lift an untyped WM rewrite rule into the typed WM layer with one sort. -/
noncomputable def wmRewriteRuleToSigmaUnit
    {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    (r : WMRewriteRule State Query) :
    WorldModelSigma.WMRewriteRuleSigma State PUnit (fun _ : PUnit => Query) where
  side := r.side
  conclusion := ⟨PUnit.unit, r.conclusion⟩
  derive := r.derive
  sound := by
    intro hSide W
    simpa [WorldModelSigma.ofWorldModelUnit] using (r.sound hSide W)

/-! ## Chain BN Deduction -/

section ChainBNDeduction

open Mettapedia.Logic.PLNBNCompilation.ChainExample

variable
  [DecidableRel chainBN.graph.edges]
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
  [StandardBorelSpace chainBN.JointSpace]

/-- Typed (one-sort) wrapper of chain-BN deduction rewrite rule. -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := chainBN))
      PUnit
      (fun _ : PUnit => PLNQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaUnit
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)

/-- Side-condition transfer for the typed chain-BN deduction wrapper. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_side
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN)) :
    (xi_deduction_rewrite_of_chainBN_sigma valA valB valC hLMarkov).side := by
  simpa [xi_deduction_rewrite_of_chainBN_sigma, wmRewriteRuleToSigmaUnit] using
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)

end ChainBNDeduction

/-! ## Fork BN Source Rule -/

section ForkBNSourceRule

open Mettapedia.Logic.PLNBNCompilation.ForkExample

variable
  [DecidableRel forkBN.graph.edges]
  [∀ v : Three, Fintype (forkBN.stateSpace v)]
  [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
  [∀ v : Three, Inhabited (forkBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
  [StandardBorelSpace forkBN.JointSpace]

/-- Typed (one-sort) wrapper of fork-BN source-rule rewrite. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := forkBN))
      PUnit
      (fun _ : PUnit => PLNQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaUnit
    (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov)

/-- Side-condition transfer for the typed fork-BN source-rule wrapper. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_side
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds (bn := forkBN)) :
    (xi_sourceRule_rewrite_of_forkBN_sigma valA valB valC hLMarkov).side := by
  simpa [xi_sourceRule_rewrite_of_forkBN_sigma, wmRewriteRuleToSigmaUnit] using
    (xi_sourceRule_rewrite_of_forkBN_side valA valB valC hLMarkov hDSep)

end ForkBNSourceRule

/-! ## Collider BN Sink Rule -/

section ColliderBNSinkRule

open Mettapedia.Logic.PLNBNCompilation.ColliderExample

variable
  [DecidableRel colliderBN.graph.edges]
  [∀ v : Three, Fintype (colliderBN.stateSpace v)]
  [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
  [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace]

/-- Typed (one-sort) wrapper of collider-BN sink-rule rewrite. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := colliderBN))
      PUnit
      (fun _ : PUnit => PLNQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaUnit
    (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov)

/-- Side-condition transfer for the typed collider-BN sink-rule wrapper. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_side
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds (bn := colliderBN)) :
    (xi_sinkRule_rewrite_of_colliderBN_sigma valA valB hLMarkov).side := by
  simpa [xi_sinkRule_rewrite_of_colliderBN_sigma, wmRewriteRuleToSigmaUnit] using
    (xi_sinkRule_rewrite_of_colliderBN_side valA valB hLMarkov hDSep)

end ColliderBNSinkRule

end

end Mettapedia.Logic.PLNXiDerivedBNRules.Typed
