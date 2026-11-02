import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPartnerAdequacy
import Mettapedia.GSLT.Logic.BagSaturated
import Mettapedia.GSLT.Logic.BagHennessyMilner
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations

/-!
# ρ's least partners, presented by finitely many schemas

ρ composes in parallel, so a context is the bag of primes beside the hole and ρ's COMM is a reactive system on bags of
closed canonical primes (`rules`, one rule per closed COMM instance `for(y<-x)b | x!(v) ⇒ b[@v/y]`). There:

- **Reactions are ρ's canonical COMM reactions** (`reacts_iff`).
- **Saturated bisimilarity against every partner is ρ's partner bisimilarity** (`saturated_iff_canonical`,
  `semiSaturated_iff_partnerBisimilar`). Every span has relative pushouts, so the least labels characterize it
  semi-saturated: a least-labelled step of one process is answered by a reaction of the other in the label's context.
  With the front door's characterization of partner bisimilarity, the context-labelled native types of a closed process
  are determined by its least-labelled steps (`agree_iff_semiSaturated`).
- **The least labels, as rule schemas with metavariables** (`actIPO_iff_cases`). A least label is what the agent lacks of
  a COMM redex, and the two-prime redex meets the agent in one of four ways, so a closed process has finitely many
  label schemas: the empty label when it holds a whole redex; for each input prime `for(y<-x)b` it holds, the output
  `x!(?v)` on that channel with its payload a metavariable (`payloadSchema`); for each output prime `x!(v)` it holds,
  the input `for(y<-x)?b` on that channel with its body a metavariable (`bodySchema`); and the whole redex, when it
  holds neither prime. One schema stands for the infinitely many partners its instances are; each instance's result
  is the COMM reactum with the rest of the agent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.LeastPartners

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy (partnerSystem)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag (IsPrime Bag append fromProcess)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (GroundComm Reaction input output)
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO)
open Mettapedia.GSLT.BagRelativePushout (Obj bag bag_comp bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts SemiSaturatedBisimilar)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn)

/-! ## Bags of primes -/

/-- **The tokens of ρ's bags**: closed canonical primes. -/
abbrev Prime : Type := {pattern : Pattern // IsPrime pattern}

/-- The primes of a bag. -/
def primes (inventory : Bag) : Multiset Prime :=
  inventory.1.attach.map fun pattern => ⟨pattern.1, inventory.2 _ pattern.2⟩

/-- The bag of some primes. -/
def ofPrimes (tokens : Multiset Prime) : Bag :=
  ⟨tokens.map Subtype.val, fun pattern member => by
    obtain ⟨token, -, rfl⟩ := Multiset.mem_map.mp member
    exact token.2⟩

theorem val_primes (inventory : Bag) : (primes inventory).map Subtype.val = inventory.1 := by
  simp [primes, Multiset.map_map]

theorem ofPrimes_primes (inventory : Bag) : ofPrimes (primes inventory) = inventory :=
  Subtype.ext (val_primes inventory)

theorem primes_ofPrimes (tokens : Multiset Prime) : primes (ofPrimes tokens) = tokens :=
  Multiset.map_injective Subtype.val_injective (val_primes (ofPrimes tokens))

theorem primes_injective : Function.Injective primes := fun first second same => by
  rw [← ofPrimes_primes first, same, ofPrimes_primes]

theorem ofPrimes_add (first second : Multiset Prime) :
    ofPrimes (first + second) = append (ofPrimes first) (ofPrimes second) :=
  Subtype.ext (Multiset.map_add _ _ _)

theorem primes_append (first second : Bag) : primes (append first second) = primes first + primes second := by
  apply Multiset.map_injective Subtype.val_injective
  rw [val_primes, Multiset.map_add, val_primes, val_primes]
  rfl

/-! ## ρ's COMM as a reactive system on bags -/

/-- **One COMM instance as a reaction rule on bags of primes.** -/
def commRule (comm : GroundComm) : ReactionRule (Obj Prime) where
  codomain := Obj Prime
  redex := bag (primes comm.redex)
  reactum := bag (primes comm.reactum)

/-- **ρ's COMM rules**: one per closed COMM instance. -/
def rules (rule : ReactionRule (Obj Prime)) : Prop := ∃ comm : GroundComm, rule = commRule comm

/-- **A reaction of a bag is a canonical COMM reaction.** -/
theorem reacts_iff (agent next : Multiset Prime) :
    Reacts rules (bag agent) (bag next) ↔ Reaction (ofPrimes agent) (ofPrimes next) := by
  rw [Mettapedia.GSLT.BagSaturated.reacts_iff]
  constructor
  · rintro ⟨_, ⟨comm, rfl⟩, l, k, redexEq, reactumEq, contained, rfl⟩
    obtain rfl : primes comm.redex = l := bag_injective redexEq
    obtain rfl : primes comm.reactum = k := bag_injective reactumEq
    refine ⟨comm, ofPrimes (agent - primes comm.redex), ?_, ?_⟩
    · apply primes_injective
      rw [primes_ofPrimes, primes_append, primes_ofPrimes, add_tsub_cancel_of_le contained]
    · apply primes_injective
      rw [primes_ofPrimes, primes_append, primes_ofPrimes]
  · rintro ⟨comm, residue, agentEq, nextEq⟩
    have agentPrimes : agent = primes comm.redex + primes residue := by
      rw [← primes_ofPrimes agent, agentEq, primes_append]
    refine ⟨commRule comm, ⟨comm, rfl⟩, primes comm.redex, primes comm.reactum, rfl, rfl, ?_, ?_⟩
    · rw [agentPrimes]
      exact Multiset.le_add_right _ _
    · rw [← primes_ofPrimes next, nextEq, primes_append, agentPrimes, add_tsub_cancel_left]

/-! ## Saturated bisimilarity is partner bisimilarity -/

/-- **Saturated bisimilarity of bags against every partner is ρ's canonical partner bisimilarity.** -/
theorem saturated_iff_canonical (first second : Multiset Prime) :
    SaturatedBisimilarIn rules (fun _ => True) first second ↔
      CanonicalPartnerObservations.Bisimilar (ofPrimes first) (ofPrimes second) := by
  constructor
  · rintro ⟨relation, saturated, related⟩
    refine ⟨fun left right => relation (primes left) (primes right), ?_, by simpa only [primes_ofPrimes] using related⟩
    intro left right relatedHere partner
    obtain ⟨forth, back⟩ := saturated relatedHere (primes partner) trivial
    constructor
    · intro target reaction
      have reacts : Reacts rules (bag (primes left) ≫ bag (primes partner)) (bag (primes target)) := by
        rw [bag_comp, reacts_iff, ← primes_append, ofPrimes_primes, ofPrimes_primes]
        exact reaction
      obtain ⟨matched, matchedReacts, relatedNext⟩ := forth (primes target) reacts
      rw [bag_comp, reacts_iff, ← primes_append, ofPrimes_primes] at matchedReacts
      exact ⟨ofPrimes matched, matchedReacts, by simpa only [primes_ofPrimes] using relatedNext⟩
    · intro target reaction
      have reacts : Reacts rules (bag (primes right) ≫ bag (primes partner)) (bag (primes target)) := by
        rw [bag_comp, reacts_iff, ← primes_append, ofPrimes_primes, ofPrimes_primes]
        exact reaction
      obtain ⟨matched, matchedReacts, relatedNext⟩ := back (primes target) reacts
      rw [bag_comp, reacts_iff, ← primes_append, ofPrimes_primes] at matchedReacts
      exact ⟨ofPrimes matched, matchedReacts, by simpa only [primes_ofPrimes] using relatedNext⟩
  · rintro ⟨relation, admitted, related⟩
    refine ⟨fun left right => relation (ofPrimes left) (ofPrimes right), ?_, related⟩
    intro left right relatedHere context _
    obtain ⟨forth, back⟩ := admitted _ _ relatedHere (ofPrimes context)
    constructor
    · intro next reacts
      rw [bag_comp, reacts_iff, ofPrimes_add] at reacts
      obtain ⟨matched, reaction, relatedNext⟩ := forth _ reacts
      refine ⟨primes matched, ?_, by simpa only [ofPrimes_primes] using relatedNext⟩
      rw [bag_comp, reacts_iff, ofPrimes_add, ofPrimes_primes]
      exact reaction
    · intro next reacts
      rw [bag_comp, reacts_iff, ofPrimes_add] at reacts
      obtain ⟨matched, reaction, relatedNext⟩ := back _ reacts
      refine ⟨primes matched, ?_, by simpa only [ofPrimes_primes] using relatedNext⟩
      rw [bag_comp, reacts_iff, ofPrimes_add, ofPrimes_primes]
      exact reaction

/-- **No partner tells two closed processes apart exactly when they are semi-saturated bisimilar on least labels**:
partner bisimilarity is decided by least-labelled steps. -/
theorem semiSaturated_iff_partnerBisimilar (first second : RhoProcess) :
    SemiSaturatedBisimilar rules (bag (primes (fromProcess first))) (bag (primes (fromProcess second))) ↔
      (partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar first second := by
  rw [Mettapedia.GSLT.BagSaturated.semiSaturated_iff_saturated,
    ← Mettapedia.GSLT.BagHennessyMilner.saturatedBisimilarIn_iff (rules := rules),
    saturated_iff_canonical, ofPrimes_primes, ofPrimes_primes,
    CanonicalPartnerObservations.public_bisimilar_iff_canonical]

/-- **The front door's context-labelled native types of ρ are decided by least labels**: two closed processes agree on
the forward formulas under parallel partners exactly when they are semi-saturated bisimilar on least labels. -/
theorem agree_iff_semiSaturated (first second : RhoProcess) :
    Partners.frontDoor.AgreeOn (Formula.forwardOn Partners.isPartnerLabel) first.1 second.1 ↔
      SemiSaturatedBisimilar rules (bag (primes (fromProcess first))) (bag (primes (fromProcess second))) :=
  (Partners.agree_iff_partnerBisimilar first second).trans (semiSaturated_iff_partnerBisimilar first second).symm

/-! ## Least labels as schemas -/

/-- The input prime of a COMM instance. -/
def inputToken (comm : GroundComm) : Prime := ⟨input comm.inputChannel comm.body, comm.inputPrime⟩

/-- The output prime of a COMM instance. -/
def outputToken (comm : GroundComm) : Prime := ⟨output comm.outputChannel comm.payload, comm.outputPrime⟩

theorem inputToken_ne_outputToken (comm : GroundComm) : inputToken comm ≠ outputToken comm := fun same => by
  have := congrArg Subtype.val same
  simp [inputToken, outputToken, input, output] at this

theorem primes_redex (comm : GroundComm) : primes comm.redex = {inputToken comm, outputToken comm} := by
  apply Multiset.map_injective Subtype.val_injective
  rw [val_primes]
  rfl

/-- **ρ's least-labelled steps**: the label is what the agent lacks of a COMM redex, the result the reactum with what the
agent keeps. -/
theorem actIPO_iff {agent label target : Multiset Prime} :
    ActIPO rules (bag label) (bag agent) (bag target) ↔
      ∃ comm : GroundComm, label = primes comm.redex - agent ∧
        target = primes comm.reactum + (agent - primes comm.redex) := by
  rw [Mettapedia.GSLT.BagSaturated.actIPO_iff]
  constructor
  · rintro ⟨_, ⟨comm, rfl⟩, l, k, redexEq, reactumEq, rfl, rfl⟩
    obtain rfl : primes comm.redex = l := bag_injective redexEq
    obtain rfl : primes comm.reactum = k := bag_injective reactumEq
    exact ⟨comm, rfl, rfl⟩
  · rintro ⟨comm, rfl, rfl⟩
    exact ⟨commRule comm, ⟨comm, rfl⟩, _, _, rfl, rfl, rfl, rfl⟩

/-- What an agent lacks of a COMM redex: each of its two primes, unless the agent holds it. -/
theorem redex_sub (comm : GroundComm) (agent : Multiset Prime) :
    primes comm.redex - agent =
      (if inputToken comm ∈ agent then 0 else {inputToken comm}) +
        (if outputToken comm ∈ agent then 0 else {outputToken comm}) := by
  have distinct := inputToken_ne_outputToken comm
  rw [primes_redex]
  ext token
  rw [Multiset.count_sub, Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases isInput : token = inputToken comm <;> by_cases isOutput : token = outputToken comm <;>
    by_cases inputHeld : inputToken comm ∈ agent <;> by_cases outputHeld : outputToken comm ∈ agent <;> simp_all <;>
    first
      | (have := Multiset.one_le_count_iff_mem.mpr inputHeld; omega)
      | (have := Multiset.one_le_count_iff_mem.mpr outputHeld; omega)

/-- **The least labels of a closed process fall into finitely many schemas**: a least-labelled step fires a COMM instance
whose redex meets the agent in one of four ways, and its label is nothing (the agent holds the whole redex), the output
prime (the agent holds the input: the schema of that input, payload free), the input prime (the agent holds the output:
the schema of that output, body free), or the whole redex (the agent holds neither). -/
theorem actIPO_iff_cases {agent label target : Multiset Prime} :
    ActIPO rules (bag label) (bag agent) (bag target) ↔
      ∃ comm : GroundComm, target = primes comm.reactum + (agent - primes comm.redex) ∧
        ((inputToken comm ∈ agent ∧ outputToken comm ∈ agent ∧ label = 0) ∨
          (inputToken comm ∈ agent ∧ outputToken comm ∉ agent ∧ label = {outputToken comm}) ∨
          (inputToken comm ∉ agent ∧ outputToken comm ∈ agent ∧ label = {inputToken comm}) ∨
          (inputToken comm ∉ agent ∧ outputToken comm ∉ agent ∧ label = {inputToken comm, outputToken comm})) := by
  rw [actIPO_iff]
  refine exists_congr fun comm => ?_
  rw [redex_sub, and_comm]
  refine and_congr_right fun _ => ?_
  by_cases inAgent : inputToken comm ∈ agent <;> by_cases outAgent : outputToken comm ∈ agent <;>
    simp [inAgent, outAgent, Multiset.insert_eq_cons, Multiset.singleton_add]

/-- **The payload schema of an input prime**: an agent holding `for(y<-x)b` has, for every output `x!(v)` on that channel it
lacks, the least label `x!(v)`, and becomes the body instantiated by the payload beside the rest of the agent. The
payload `v` is the schema's metavariable. -/
theorem payloadSchema {agent : Multiset Prime} {channel body payload : Pattern}
    (inputPrime : IsPrime (input channel body)) (outputPrime : IsPrime (output channel payload))
    (holds : (⟨input channel body, inputPrime⟩ : Prime) ∈ agent)
    (lacks : (⟨output channel payload, outputPrime⟩ : Prime) ∉ agent) :
    ActIPO rules (bag {⟨output channel payload, outputPrime⟩}) (bag agent)
      (bag (primes (⟨channel, channel, body, payload, inputPrime, outputPrime, rfl⟩ : GroundComm).reactum +
        (agent - {⟨input channel body, inputPrime⟩, ⟨output channel payload, outputPrime⟩}))) :=
  actIPO_iff_cases.mpr ⟨⟨channel, channel, body, payload, inputPrime, outputPrime, rfl⟩, by rw [primes_redex]; rfl,
    Or.inr (Or.inl ⟨holds, lacks, rfl⟩)⟩

/-- **The body schema of an output prime**: an agent holding `x!(v)` has, for every input `for(y<-x)b` on that channel it
lacks, the least label `for(y<-x)b`, and becomes `b` instantiated by `v` beside the rest of the agent. The body `b` is
the schema's metavariable. -/
theorem bodySchema {agent : Multiset Prime} {channel body payload : Pattern}
    (inputPrime : IsPrime (input channel body)) (outputPrime : IsPrime (output channel payload))
    (holds : (⟨output channel payload, outputPrime⟩ : Prime) ∈ agent)
    (lacks : (⟨input channel body, inputPrime⟩ : Prime) ∉ agent) :
    ActIPO rules (bag {⟨input channel body, inputPrime⟩}) (bag agent)
      (bag (primes (⟨channel, channel, body, payload, inputPrime, outputPrime, rfl⟩ : GroundComm).reactum +
        (agent - {⟨input channel body, inputPrime⟩, ⟨output channel payload, outputPrime⟩}))) :=
  actIPO_iff_cases.mpr ⟨⟨channel, channel, body, payload, inputPrime, outputPrime, rfl⟩, by rw [primes_redex]; rfl,
    Or.inr (Or.inr (Or.inl ⟨lacks, holds, rfl⟩))⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.LeastPartners
