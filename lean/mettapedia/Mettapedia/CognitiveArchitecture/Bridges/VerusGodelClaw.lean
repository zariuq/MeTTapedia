import Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel
import Mettapedia.CognitiveArchitecture.GodelClaw.Mindlock
import Mettapedia.CognitiveArchitecture.GodelClaw.GateChain
import Mettapedia.CognitiveArchitecture.GodelClaw.ToolBroker

/-!
# Verus ↔ GodelClaw Lean Bridge

Formal specification of the correspondence between:
- Verus SMT specs in `vericore-policy/src/*.rs` (runtime, SMT-checked)
- Lean propositions in `CognitiveArchitecture/GodelClaw/` (reference formalization)

## Why this exists

The Verus code is the **production truth** — it runs in the VeriCore binary.
The Lean code is the **reference formalization** — it connects to Mettapedia's
broader theory (PLN, MetaMo, Hyperseed, values).

This bridge module documents the intended correspondence so that:
1. Changes to one can be cross-checked against the other
2. Properties proved in Lean can be trusted to hold in the runtime
3. The two proof systems reinforce each other

## What this does NOT do

- Automatically verify the Verus code from Lean (different proof assistants)
- Generate Rust from Lean or vice versa
- Claim bit-level equivalence (Verus uses SMT, Lean uses type theory)

## Trust model

The bridge is a *specification correspondence*: we manually verify that
the Lean types and theorems match the Verus spec functions and proof lemmas.
The correspondence is checked by review, not by automated translation.
-/

namespace Mettapedia.CognitiveArchitecture.Bridges.VerusGodelClaw

open Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel
open Mettapedia.CognitiveArchitecture.GodelClaw.Mindlock
open Mettapedia.CognitiveArchitecture.GodelClaw.GateChain
open Mettapedia.CognitiveArchitecture.GodelClaw.ToolBroker

/-! ## Tier correspondence

Verus: `ContextTier::Public/Family/Private` with `context_rank` 0/1/2
Lean:  `ContextTier.pub/family/private_` with `ContextTier.rank` 0/1/2

Verus: `IntegrityTier::Untrusted/Reviewed/Trusted` with `integrity_rank` 0/1/2
Lean:  `IntegrityTier.untrusted/reviewed/trusted` with `IntegrityTier.rank` 0/1/2
-/

/-- The Lean rank matches the Verus `context_rank` spec. -/
theorem contextTier_rank_correspondence :
    ContextTier.pub.rank = 0 ∧
    ContextTier.fam.rank = 1 ∧
    ContextTier.priv.rank = 2 := ⟨rfl, rfl, rfl⟩

/-- The Lean rank matches the Verus `integrity_rank` spec. -/
theorem integrityTier_rank_correspondence :
    IntegrityTier.untrusted.rank = 0 ∧
    IntegrityTier.reviewed.rank = 1 ∧
    IntegrityTier.trusted.rank = 2 := ⟨rfl, rfl, rfl⟩

/-! ## Flow label correspondence

Verus: `spec_join(a, b)` = `{ secrecy: max, integrity: min }`
Lean:  `FlowLabel.join a b` = `{ secrecy := max, integrity := min }`

Verus proves: join is idempotent, commutative, associative
Lean proves:  same (FlowLabel.join_idem, join_comm, join_assoc)
-/

-- These are proved in PolicyKernel.lean and match the Verus lemmas:
-- lemma_join_idempotent ↔ FlowLabel.join_idem
-- lemma_join_commutative ↔ FlowLabel.join_comm
-- lemma_join_associative ↔ FlowLabel.join_assoc

/-! ## Channel mapping correspondence

Verus: `spec_default_context(Channel::X)` → `ContextTier`
Lean:  `Channel.defaultContext` → `ContextTier`

Verus: `spec_integrity_for_context(ContextTier::X)` → `IntegrityTier`
Lean:  `IntegrityTier.fromContext` → `IntegrityTier`
-/

/-- Channel default context matches Verus spec. -/
theorem channel_context_correspondence :
    Channel.telegramPublic.defaultContext = .pub ∧
    Channel.telegramFamily.defaultContext = .fam ∧
    Channel.telegramDm.defaultContext = .priv ∧
    Channel.terminal.defaultContext = .priv ∧
    Channel.internal.defaultContext = .priv ∧
    Channel.api.defaultContext = .pub ∧
    Channel.moltbook.defaultContext = .pub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Integrity from context matches Verus spec. -/
theorem integrity_from_context_correspondence :
    IntegrityTier.fromContext .pub = .untrusted ∧
    IntegrityTier.fromContext .fam = .reviewed ∧
    IntegrityTier.fromContext .priv = .trusted :=
  ⟨rfl, rfl, rfl⟩

/-! ## Mindlock correspondence

Verus: `spec_is_terminal`, `spec_valid_transition`, etc.
Lean:  `Stage.isTerminal`, `validTransition`, etc.

Key property correspondence:
- `lemma_rejected_is_terminal` ↔ `rejected_is_terminal`
- `lemma_promoted_is_terminal` ↔ `promoted_is_terminal`
- `lemma_pending_requires_zar` ↔ `pending_requires_zar`
- `lemma_staging_promote_requires_review` ↔ `staging_promote_requires_review`
- `lemma_agent_move_stays_safe` ↔ `agent_move_stays_safe`
- `lemma_terminal_not_valid_move_source` ↔ `terminal_not_valid_move_source`
-/

/-! ## Gate chain correspondence

Verus: `spec_gate_chain_allows(sc, ak, ti, si, ig, pr)` = `sc && ak && ...`
Lean:  `sixGateAllows sc ak ti si ig pr` = `sc && ak && ...`

Key property correspondence:
- `lemma_any_deny_means_chain_denies` ↔ `sixGate_any_deny` (contrapositive)
- `lemma_chain_monotone` ↔ `sixGate_any_deny`
- `lemma_all_allow_means_chain_allows` ↔ `sixGate_all_true`
- `lemma_schedule_deny_blocks_everything` ↔ `sixGate_schedule_deny`
- `lemma_ingress_deny_blocks_even_if_primitive_allows` ↔ `sixGate_ingress_deny`
-/

/-! ## Tool broker & tool policy correspondence

Verus: `spec_tool_authorized(in_list, wildcard)` = `wildcard || in_list`
Lean:  `toolAuthorized inAllowlist wildcard` = `wildcard || inAllowlist`

Verus: `spec_native_shadow_denied(is_brokered, matches)` = `!(is_brokered && matches)`
Lean:  `nativeShadowDenied isBrokered displayNameMatchesNative` = same

Verus: `spec_tool_gate_allows(...)` = shadow check ∧ authorization
Lean:  `toolGateAllows (...)` = same

Verus: `spec_capability_id_stable(prefix, server, tool)` = `prefix && server && tool`
Lean:  `capabilityIdStable hasMcpPrefix hasServerName hasToolName` = same

Key property correspondence:
- `lemma_wildcard_allows_all` ↔ `wildcard_allows_all`
- `lemma_unknown_capability_denied` ↔ `unknown_denied`
- `lemma_listed_capability_authorized` ↔ `listed_authorized`
- `lemma_native_shadow_always_denied` ↔ `shadow_collision_denied`
- `lemma_non_colliding_brokered_not_denied` ↔ `non_colliding_brokered_ok`
- `lemma_native_tools_not_shadow_denied` ↔ `native_not_shadow_denied`
- Composition: `tool_gate_deny_blocks_chain` chains tool_policy → gate_chain
-/

/-! ## Coverage summary

| Verus module        | Lean module       | Types | Specs | Proofs |
|---------------------|-------------------|-------|-------|--------|
| tiers.rs            | PolicyKernel.lean | ✓     | ✓     | ✓      |
| channels.rs         | PolicyKernel.lean | ✓     | ✓     | ✓      |
| mindlock.rs         | Mindlock.lean     | ✓     | ✓     | ✓      |
| gate_chain.rs       | GateChain.lean    | ✓     | ✓     | ✓      |
| tool_broker.rs      | ToolBroker.lean   | ✓     | ✓     | ✓      |
| tool_policy.rs      | ToolBroker.lean   | ✓     | ✓     | ✓      |
| ingress.rs          | (future)          |       |       |        |
| egress.rs           | (future)          |       |       |        |
| receipt.rs          | (future)          |       |       |        |
| llm_bridge.rs       | (future)          |       |       |        |
| model_resolution.rs | (future)          |       |       |        |
| compositions.rs     | (future)          |       |       |        |
-/

end Mettapedia.CognitiveArchitecture.Bridges.VerusGodelClaw
