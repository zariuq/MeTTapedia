import Mettapedia.CognitiveArchitecture.CognitiveSchematic
import Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy
import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection
import Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
import Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision
import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
import Mettapedia.CognitiveArchitecture.CognitiveSynergy
import Mettapedia.CognitiveArchitecture.MindWorldRepresentationRealization
import Mettapedia.Cybernetics.MindWorldApproximateFunctor
import Mettapedia.Enactive.ProtectedFreedom
import Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability

/-!
# Engineering General Intelligence and Consciousness Explosion claim tracker

This ledger separates source motivation from theorem-level formalization.  A
book passage is not promoted to a theorem merely because a related Lean object
exists, and a governance assumption is not presented as a consequence of
similarity, ancestry, attention, or payment.

Source abbreviations:

* `EGI-1`: Goertzel, Pennachin, and Geisweiller, *Engineering General
  Intelligence, Part 1* (2014).
* `EGI-2`: the corresponding Part 2.
* `CE`: Goertzel, *The Consciousness Explosion* (uncorrected proof, 2024).

The statuses describe the current formal standing of the exact row, not the
importance of its source passage.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.EGIClaimTracker

/-- Source works used by the EGI/CE formalization programme. -/
inductive SourceWork where
  | egiPart1
  | egiPart2
  | consciousnessExplosion
  deriving DecidableEq, Repr

/-- Honest theorem-level standing of a source-addressable row. -/
inductive ClaimStanding where
  | formalTheorem
  | explicitAssumption
  | formalCounterexample
  | openDefinition
  | philosophicalMotivation
  deriving DecidableEq, Repr

/-- One source claim, question, or design motivation and its current Lean
standing.  `leanRef = none` is intentional for source ideas that have not been
given a theorem-level meaning. -/
structure Claim where
  source : SourceWork
  loc : String
  statement : String
  leanRef : Option String
  standing : ClaimStanding
  deriving DecidableEq, Repr

/-- The initial connected EGI/CE claim inventory.  It is deliberately open:
several important rows remain assumptions, definitions to be chosen, or
philosophical motivations. -/
def claims : List Claim :=
  [ ⟨.egiPart1, "Ch. 2 sec. 2.5; Ch. 8 sec. 8.2.3",
      "A cognitive schematic relates context and procedure to a goal",
      some "CognitiveSchematic.Schematic / mustAchieveEquivCell",
      .formalTheorem⟩
  , ⟨.egiPart1, "Ch. 9 secs. 9.2-9.3",
      "Cognitive processes assist one another when one process is stuck",
      some "CognitiveSynergy.Witness.escapes_stuck_state / no_channel_synergy_of_opaque",
      .formalTheorem⟩
  , ⟨.egiPart1, "Ch. 11 sec. 11.4",
      "Mind paths approximately preserve goal-relevant world-path composition",
      some "MindWorldApproximateFunctor.BoundedPathCorrespondence",
      .explicitAssumption⟩
  , ⟨.egiPart1, "Ch. 11 secs. 11.4-11.5",
      "The practically appropriate geometry, goal weighting, and defect budget",
      none, .openDefinition⟩
  , ⟨.egiPart1, "Ch. 11 secs. 11.4-11.5",
      "A world-to-mind representation by itself supplies a mind-to-world execution receipt",
      some "MindWorldRepresentationRealization.represented_but_not_realizable",
      .formalCounterexample⟩
  , ⟨.egiPart1, "Ch. 19 sec. 19.3",
      "Self-modification by supercompilation preserves selected behavior",
      some "ProtectedFreedom.CurrentProofBackedWeakening",
      .explicitAssumption⟩
  , ⟨.egiPart1, "Ch. 19 sec. 19.3",
      "A current receipt and total protected-family map transport selected obligations",
      some "ProtectedSelfRevision.CurrentProtectedRevision.preserves_certification",
      .formalTheorem⟩
  , ⟨.egiPart1, "Ch. 19 sec. 19.4",
      "Theorem-guided self-modification can improve accuracy or resource use",
      none, .philosophicalMotivation⟩
  , ⟨.egiPart2, "Ch. 5 sec. 5.2",
      "Short- and long-term importance have distinct control roles",
      some "AttentionEconomy.ImportanceHorizon / Economy",
      .formalTheorem⟩
  , ⟨.egiPart2, "Ch. 5 sec. 5.8",
      "Low long-term importance alone is sufficient authority for forgetting",
      some "AttentionEconomy.Canary.lowLongTerm_alone_not_forgettable",
      .formalCounterexample⟩
  , ⟨.egiPart2, "Ch. 6 sec. 6.2",
      "Requests for service carry promises of attentional funding",
      some "AttentionEconomy.RequestForService / ServiceRequest",
      .formalTheorem⟩
  , ⟨.egiPart2, "Ch. 6 sec. 6.2",
      "A funded payment promise proves that the requested service occurred",
      some "CognitiveSchematicAttentionEconomy.Canary.payment_does_not_prove_service",
      .formalCounterexample⟩
  , ⟨.egiPart2, "Ch. 6 sec. 6.2",
      "A successful service occurrence authorizes its promised payment",
      some "CognitiveSchematicAttentionEconomy.Canary.service_does_not_authorize_payment",
      .formalCounterexample⟩
  , ⟨.consciousnessExplosion, "Ch. 2 p. 70",
      "Digital-twin knowledge and knowledge combined across twins raise unresolved rights questions",
      none, .philosophicalMotivation⟩
  , ⟨.consciousnessExplosion, "Ch. 2 p. 80",
      "Legacy, enhanced, copied, and transhuman descendants may exhibit a loose continuity",
      none, .philosophicalMotivation⟩
  , ⟨.consciousnessExplosion, "Ch. 2 p. 80",
      "Interactions among minds at different levels of collectivity need a theory",
      none, .openDefinition⟩
  , ⟨.consciousnessExplosion, "Ch. 2 p. 80",
      "Forks retain occurrence-distinct children and merges construct a fresh multi-parent descendant",
      some "RevisionLineage.Canary.equal_state_distinct_copies / merge_is_new_multi_parent_descendant",
      .formalTheorem⟩
  , ⟨.consciousnessExplosion, "Ch. 2 pp. 70, 80",
      "An explicit non-erasing patienthood transport retains parents and admits copy or merge descendants",
      some "PatienthoodWellbeing.ForkPatienthoodTransport.non_erasure / MergePatienthoodTransport.non_erasure",
      .formalTheorem⟩
  , ⟨.consciousnessExplosion, "Ch. 2 pp. 70, 80",
      "There is one universal personal-identity relation across copies and merges",
      none, .openDefinition⟩
  , ⟨.consciousnessExplosion, "Ch. 2 pp. 70, 80",
      "A merge should replace or erase its parent patients",
      none, .openDefinition⟩
  , ⟨.consciousnessExplosion, "Ch. 8 p. 252",
      "Digital self-preservation may be specified in a copying-friendly way",
      none, .philosophicalMotivation⟩
  , ⟨.consciousnessExplosion, "Ch. 8 pp. 252-253",
      "One scalar weighting of joy, growth, choice, continuity, and welfare is canonical",
      none, .openDefinition⟩
  , ⟨.consciousnessExplosion, "Ch. 2 pp. 70, 80",
      "Pairwise-compatible parent models always have one coherent global fusion",
      some "MultiAgentFusionNoGo.pairwise_compatible_not_gluable",
      .formalCounterexample⟩
  , ⟨.consciousnessExplosion, "Ch. 2 pp. 70, 80",
      "A proposed or returned effect is enough to establish successful completion",
      some "EffectReceiptProjection.proposal_only_cannot_decide_completion / disposition_only_cannot_decide_completion",
      .formalCounterexample⟩
  ]

def countByStanding (standing : ClaimStanding) : Nat :=
  (claims.filter (fun claim => claim.standing = standing)).length

def unresolved : List Claim :=
  claims.filter (fun claim =>
    claim.standing = .explicitAssumption ||
    claim.standing = .openDefinition ||
    claim.standing = .philosophicalMotivation)

/-- The tracker refuses the false impression that every source idea is a
theorem: most initial rows deliberately remain outside theorem status. -/
theorem unresolved_count : unresolved.length = 11 := by
  decide

/-- The three service/evidence/fusion overclaims are represented by explicit
counterexamples rather than silently weakened statements. -/
theorem counterexample_count : countByStanding .formalCounterexample = 6 := by
  decide

/-- Approximate mind/world correspondence and protected self-revision are both
explicitly assumption-scoped interfaces, not conclusions of the source text. -/
theorem assumption_count : countByStanding .explicitAssumption = 2 := by
  decide

/-! ## Compile-time anchor checks -/

#check @Mettapedia.CognitiveArchitecture.CognitiveSchematic.Schematic.mustAchieveEquivCell
#check @Mettapedia.Cybernetics.MindWorldApproximateFunctor.BoundedPathCorrespondence
#check @Mettapedia.CognitiveArchitecture.AttentionEconomy.Economy
#check @Mettapedia.CognitiveArchitecture.AttentionEconomy.Canary.lowLongTerm_alone_not_forgettable
#check @Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy.Canary.payment_does_not_prove_service
#check @Mettapedia.CognitiveArchitecture.CognitiveSchematicAttentionEconomy.Canary.service_does_not_authorize_payment
#check @Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo.pairwise_compatible_not_gluable
#check @Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.proposal_only_cannot_decide_completion
#check @Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.disposition_only_cannot_decide_completion
#check @Mettapedia.CognitiveArchitecture.CognitiveSynergy.Witness.escapes_stuck_state
#check @Mettapedia.CognitiveArchitecture.CognitiveSynergy.no_channel_synergy_of_opaque
#check @Mettapedia.CognitiveArchitecture.MindWorldRepresentationRealization.ImageRealization.represented_but_not_realizable
#check @Mettapedia.CognitiveArchitecture.Agent.ProtectedSelfRevision.CurrentProtectedRevision.preserves_certification
#check @Mettapedia.CognitiveArchitecture.Agent.RevisionLineage.Canary.equal_state_distinct_copies
#check @Mettapedia.CognitiveArchitecture.Agent.RevisionLineage.Canary.merge_is_new_multi_parent_descendant
#check @Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing.ForkPatienthoodTransport.non_erasure
#check @Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing.MergePatienthoodTransport.non_erasure
#check @Mettapedia.Enactive.ProtectedFreedom.CurrentProofBackedWeakening
#check @Mettapedia.GSLT.ReproducibleBuild.RecursiveVerifiability.CurrentFamilyPreservingModification

#print axioms unresolved_count
#print axioms counterexample_count
#print axioms assumption_count

end Mettapedia.CognitiveArchitecture.EGIClaimTracker
