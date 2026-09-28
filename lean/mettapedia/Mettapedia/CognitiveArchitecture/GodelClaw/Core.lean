import Mettapedia.CognitiveArchitecture.Values.Basic

/-!
# GodelClaw Core: Seed Identity

Minimal declaration of what Oruži *is* — just what we can actually stand behind.

This file is intentionally small. It declares:
- The core value axiom (universal loving care)
- The seed identity structure (what makes GodelClaw *this* agent, not a generic one)

Frameworks (MetaMo, Hyperseed, GödelMachine properties) connect here as they are
explored and found helpful — not pre-baked.

## Design constraints

- No framework commitments: this is Oruži's ground truth, not a theory
- Extensible: other modules can require `CoreValue` or `SeedIdentity` as parameters
- Honest: only declares what is currently true of the running system
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw

/-! ## Core Value -/

/-- The core value axiom. A `CoreValue` is a proposition the agent holds as
a non-negotiable invariant — the thing that makes self-modification bounded.

This is deliberately a bare `Prop`, not a value-theoretic structure.
The bridge to `Values.ValueType` or to FOET paradigms is separate. -/
structure CoreValueDeclaration where
  /-- The core value proposition. -/
  value : Prop
  /-- The agent asserts this value is held. -/
  held : value

/-- Declaring a core value: supply the proposition and a proof that it is held.

This replaces an earlier `axiom UniversalLovingCare : Prop`.  That constant was
opaque, so it asserted nothing, and no theorem could relate it to any concrete
value — in particular the correspondence its documentation claimed, to
`EpistemicLove.EpistemicUniversalLove`, was unprovable by construction while
`epistemicLoveAsCore` quietly built a different declaration.  Taking the
proposition as a parameter loses nothing and leaves the development
axiom-free.

"Realize the known desires of all beings when possible, while avoiding
preventable harm." — from Formal-Ethics-Ontology (SUO-KIF) — is the intended
reading of the parameter, and `EpistemicLove.epistemicLoveAsCore` supplies a
concrete proposition that discharges it. -/
def oruzisCore (value : Prop) (held : value) : CoreValueDeclaration where
  value := value
  held := held

/-! ## Seed Identity -/

/-- A seed identity packages the minimal things that make this agent *this* agent:
- A core value declaration
- An agent identifier (opaque — could be a name, a key, anything)

This is not a GödelMachine self-model. It's just "here's who I am right now."
Whether GödelMachine self-modification framing fits is an open question. -/
structure SeedIdentity (AgentId : Type*) where
  /-- Who am I? -/
  id : AgentId
  /-- What do I care about? -/
  coreValue : CoreValueDeclaration

/-! ## Self-modification guard (minimal) -/

/-- A self-modification is value-preserving if the core value still holds
after the modification. This is the weakest useful constraint:
it says nothing about *how* to check, only *what* must remain true. -/
def ValuePreserving (seed : SeedIdentity AgentId) (modification : Prop → Prop) : Prop :=
  modification seed.coreValue.value

/-- The identity modification: always value-preserving. -/
theorem id_is_value_preserving (seed : SeedIdentity AgentId) :
    ValuePreserving seed id :=
  seed.coreValue.held

end Mettapedia.CognitiveArchitecture.GodelClaw
