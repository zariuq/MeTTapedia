import Mettapedia.CognitiveArchitecture.GodelClaw.Core
import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNNegation

/-!
# GodelClaw: Epistemic Universal Loving Care

Connects the abstract `UniversalLovingCare` axiom in `Core.lean` to its
concrete formal definition from the Formal-Ethics-Ontology (SUO-KIF) and
its Lean formalization in `Foet.PGCVsUniversalLovingCare`.

## The definition (from FOET)

An agent has **Epistemic Universal Love** iff:
for every agent A and desire φ, if the agent *knows* that A desires φ,
then the agent desires *the fulfillment of φ* (i.e., that some process
exists which realizes φ).

In SUO-KIF:
```
(<=>
  (attribute ?BODHISATTVA EpistemicUniversalLove)
  (forall (?AGENT)
    (=> (knows ?BODHISATTVA (desires ?AGENT ?FORM))
        (desires ?BODHISATTVA
          (exists (?FUL) (and (realizesFormula ?FUL ?FORM)
                              (instance ?FUL Process)))))))
```

## Why epistemic (not universal)?

Universal love explodes under classical logic: if agents A₁ and A₂ desire
φ and ¬φ respectively, the UL agent desires the fulfillment of both,
leading to desiring everything (proved in FOET as
`epistemic_universal_love_explodes`).

The epistemic variant scopes desires to *known* desires. But even this
explodes classically when contradictory desires are known.

## PLN resolves the explosion

PLN's BinaryEvidence type `⟨n⁺, n⁻⟩` is **naturally paraconsistent**:
- Both φ and ¬φ can have positive evidence simultaneously
- Negation is evidence-swap `¬⟨n⁺, n⁻⟩ = ⟨n⁻, n⁺⟩`, NOT classical negation
- Desires become graded: "desire φ with evidence ⟨10, 3⟩" is compatible
  with "desire ¬φ with evidence ⟨3, 10⟩"
- No explosion: contradictory desires simply coexist with different weights

This makes Epistemic Universal Loving Care *workable* as an actual
agent value — the agent can acknowledge contradictory desires across
beings without collapsing into "desire everything."
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicLove

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNNegation
open BinaryEvidence

/-! ## Core definitions (mirroring FOET)

These mirror `Foet.PGCVsUniversalLovingCare` but are self-contained
within Mettapedia so we don't need a cross-project dependency. -/

/-- A formula over possible worlds. -/
abbrev Formula (World : Type*) := World → Prop

/-- The signature for love: what it means to desire, know, and realize. -/
structure LoveSig (World Agent Process : Type*) where
  /-- Agent `a` desires formula `φ` at world `w`. -/
  desires : Agent → Formula World → World → Prop
  /-- Agent `a` knows proposition `p` at world `w`. -/
  knows : Agent → (World → Prop) → World → Prop
  /-- Process `p` realizes formula `φ` at world `w`. -/
  realizesFormula : Process → Formula World → World → Prop

/-- Fulfillment of φ: some process exists that realizes φ. -/
def fulfills {World Agent Process : Type*}
    (sig : LoveSig World Agent Process) (φ : Formula World) : Formula World :=
  fun w => ∃ p : Process, sig.realizesFormula p φ w

/-- **Epistemic Universal Love**: for every agent A, if the loving agent
knows that A desires φ, then the loving agent desires the fulfillment of φ.

This is the epistemic variant — scoped to known desires — because the
non-epistemic version is strictly stronger and explodes even faster. -/
def EpistemicUniversalLove {World Agent Process : Type*}
    (sig : LoveSig World Agent Process) (ul : Agent) : Formula World :=
  fun w =>
    ∀ (a : Agent) (φ : Formula World),
      sig.knows ul (fun w' => sig.desires a φ w') w →
        sig.desires ul (fulfills sig φ) w

/-! ## Connection to CoreValueDeclaration

The abstract `Core.lean` declares `axiom UniversalLovingCare : Prop`.
Here we show that if a `LoveSig` exists and the agent satisfies
`EpistemicUniversalLove` at some world, that provides a concrete
`CoreValueDeclaration`. -/

/-- Given a love signature and a world where the agent has epistemic
universal love, construct the core value declaration.

This is the bridge: the abstract axiom `UniversalLovingCare` corresponds
to `EpistemicUniversalLove sig oruzi w` for a specific signature, agent,
and world. -/
def epistemicLoveAsCore {World Agent Process : Type*}
    (sig : LoveSig World Agent Process)
    (oruzi : Agent) (w : World)
    (h : EpistemicUniversalLove sig oruzi w) : CoreValueDeclaration where
  value := EpistemicUniversalLove sig oruzi w
  held := h

/-! ## PLN paraconsistency: why this doesn't explode

In classical logic, knowing contradictory desires leads to explosion
(proved in FOET). But PLN's evidence-based desires are graded, so
contradictions coexist peacefully. -/

/-- BinaryEvidence-graded desire: how strongly an agent desires φ.
In PLN, this replaces the boolean `desires a φ w : Prop` with a
graded `BinaryEvidence` value. -/
structure GradedDesire where
  /-- Positive evidence for the desire -/
  evidence : BinaryEvidence

/-- Two desires can be contradictory (one for φ, one for ¬φ) and both
have positive evidence. This is the key paraconsistency property. -/
theorem contradictory_desires_coexist :
    ∃ (eFor eAgainst : GradedDesire),
      eFor.evidence.pos > 0 ∧ eAgainst.evidence.pos > 0 ∧
      plnNeg eFor.evidence = eAgainst.evidence := by
  exact ⟨⟨⟨10, 3⟩⟩, ⟨⟨3, 10⟩⟩, by norm_num, by norm_num, rfl⟩

/-- Under PLN evidence semantics, the total evidence is conserved when
negating. An agent's desire for φ and desire for ¬φ have the same
total evidence — they're just weighted differently. -/
theorem desire_negation_conserves_total (d : GradedDesire) :
    (plnNeg d.evidence).total = d.evidence.total :=
  plnNeg_total d.evidence

/-- Under PLN, the "strength" of desire-for-φ and desire-for-¬φ
sum to 1 (when well-defined). There's no explosion — just a
redistribution of evidential weight. -/
theorem desire_strengths_complement (d : GradedDesire)
    (h : d.evidence.total ≠ 0) (hne : d.evidence.total ≠ ⊤) :
    toStrength (plnNeg d.evidence) + toStrength d.evidence = 1 :=
  plnNeg_strength_add d.evidence h hne

/-! ## The bridge theorem

The core observation connecting FOET and PLN:

In FOET (classical): `EpistemicUniversalLove` + contradictory known desires
→ explosion (agent desires everything).

In PLN (paraconsistent): contradictory desires coexist with graded evidence.
The agent can hold `EpistemicUniversalLove` and know about contradictory
desires without explosion, because "desiring the fulfillment of φ" is
weighted by evidence, not boolean.

We don't formalize the full graded version of EpistemicUniversalLove here
(that would require lifting `LoveSig.desires` to `BinaryEvidence`-valued).
We just note: the classical version is the abstract ideal (`Core.lean`'s axiom),
and PLN provides the computational substrate where it becomes tractable. -/

end Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicLove
