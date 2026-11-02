import Mettapedia.Logic.LinearHorn.Derivation
import Mettapedia.GSLT.Causality.ResourceProduct

/-!
# Pure resource firings and independent multiplicative Horn proofs

For a resource system with no reads, each source rule instance is a declared
Horn sequent. Every actual firing list constructs a proof with the same
rule-use list. Conversely, every identity/rule/tensor/cut proof sequentializes
to an actual firing list of the existing resource system.

The target proof judgment is defined independently in `Logic.LinearHorn`.
The equivalence keeps the complete final bag, including residual resources;
it assumes no weakening, contraction or emptying of a leftover frame. Reads,
guards, arbitrary linear-logic formulas and connection matings are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.System

open Mettapedia.Logic

universe uAtom uRule
variable {Atom : Type uAtom} [DecidableEq Atom] (system : System.{uAtom, uRule} Atom)

abbrev HornProof (before after : Multiset Atom) :=
  LinearHorn.Derivation (fun entry : system.Entry => system.consume entry.2)
    (fun entry : system.Entry => system.produce entry.2) before after

private theorem linear_step_frame {before after : Multiset Atom} {entry : system.Entry}
    (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (enabled : system.Enables before entry.2) (target : after = system.fire before entry.2)
    (frame : Multiset Atom) :
    system.Enables (before + frame) entry.2 ∧
      after + frame = system.fire (before + frame) entry.2 := by
  obtain ⟨residual, source, destination⟩ :=
    (system.enables_fire_iff_frame before after entry.2 (noReads entry)).mp ⟨enabled, target⟩
  apply (system.enables_fire_iff_frame (before + frame) (after + frame) entry.2 (noReads entry)).mpr
  exact ⟨residual + frame, by rw [source]; ac_rfl, by rw [destination]; ac_rfl⟩

theorem linear_fires_frame (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (frame : Multiset Atom) : ∀ (trace : List system.Entry) {before after : Multiset Atom},
      system.Fires trace before after → system.Fires trace (before + frame) (after + frame)
  | [], _, _, target => congrArg (· + frame) target
  | entry :: rest, before, after, fired => by
      obtain ⟨enabled, target⟩ := linear_step_frame system noReads fired.1 rfl frame
      refine ⟨enabled, ?_⟩
      rw [← target]
      exact linear_fires_frame noReads frame rest fired.2

theorem linear_fires_concat : ∀ (first second : List system.Entry) {before middle after : Multiset Atom},
    system.Fires first before middle → system.Fires second middle after →
      system.Fires (first ++ second) before after
  | [], second, before, middle, after, middleEquals, rest => by
      change middle = before at middleEquals
      subst middle
      exact rest
  | entry :: rest, second, before, middle, after, firstFires, secondFires =>
      ⟨firstFires.1, linear_fires_concat rest second firstFires.2 secondFires⟩

/-- Sequentialization follows proof structure: tensor juxtaposes independent
linear contexts, and cut composes the resulting firing lists. -/
theorem horn_proof_fires (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    {before after : Multiset Atom} (proof : system.HornProof before after) :
    system.Fires proof.uses before after := by
  induction proof with
  | identity context => rfl
  | rule declaration =>
      refine ⟨?_, ?_⟩
      · change system.consume declaration.2 + system.read declaration.2 ≤ system.consume declaration.2
        rw [noReads declaration, add_zero]
      · change system.produce declaration.2 = system.fire (system.consume declaration.2) declaration.2
        simp only [System.fire, tsub_self, zero_add]
  | @tensor left right left' right' first second leftRun rightRun =>
      have firstFramed := system.linear_fires_frame noReads left' first.uses leftRun
      have secondFramed := system.linear_fires_frame noReads right second.uses rightRun
      rw [add_comm left' right, add_comm right' right] at secondFramed
      exact system.linear_fires_concat first.uses second.uses firstFramed secondFramed
  | cut first second leftRun rightRun =>
      exact system.linear_fires_concat first.uses second.uses leftRun rightRun

/-- The converse constructs independent proof nodes, retaining each actual
source instance and its order; the residual frame is an identity proof. -/
theorem horn_proof_of_fires (noReads : ∀ entry : system.Entry, system.read entry.2 = 0) :
    ∀ (trace : List system.Entry) {before after : Multiset Atom}, system.Fires trace before after →
      ∃ proof : system.HornProof before after, proof.uses = trace
  | [], before, after, fired => by
      change after = before at fired
      subst after
      exact ⟨.identity before, rfl⟩
  | entry :: rest, before, after, fired => by
      obtain ⟨frame, source, destination⟩ :=
        (system.enables_fire_iff_frame before (system.fire before entry.2) entry.2 (noReads entry)).mp ⟨fired.1, rfl⟩
      obtain ⟨tail, tailUses⟩ := horn_proof_of_fires noReads rest fired.2
      have single : ∃ proof : system.HornProof before (system.fire before entry.2), proof.uses = [entry] := by
        rw [destination, source]
        exact ⟨.tensor (.identity frame) (.rule entry), rfl⟩
      obtain ⟨head, headUses⟩ := single
      refine ⟨.cut head tail, ?_⟩
      simp only [LinearHorn.Derivation.uses, headUses, tailUses, List.singleton_append]

theorem linear_fires_iff_horn_proof (noReads : ∀ entry : system.Entry, system.read entry.2 = 0)
    (trace : List system.Entry) (before after : Multiset Atom) :
    system.Fires trace before after ↔ ∃ proof : system.HornProof before after, proof.uses = trace := by
  constructor
  · exact system.horn_proof_of_fires noReads trace
  · rintro ⟨proof, rfl⟩
    exact system.horn_proof_fires noReads proof

end Mettapedia.GSLT.Causality.ResourceInteraction.System
