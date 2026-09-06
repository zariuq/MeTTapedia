import Mathlib.Tactic

/-!
# GodelClaw Policy Kernel

Abstract Lean formalization of VeriCore's dual-lattice information flow model.
Mirrors `tiers.rs` and `channels.rs` Verus specs.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel

/-! ## Secrecy (Context) Tier -/

inductive ContextTier where
  | pub     -- Public
  | fam     -- Family
  | priv    -- Private
  deriving DecidableEq, Repr

instance : Fintype ContextTier :=
  ⟨{.pub, .fam, .priv}, by intro x; cases x <;> simp⟩

def ContextTier.rank : ContextTier → ℕ
  | .pub => 0
  | .fam => 1
  | .priv => 2

theorem ContextTier.pub_bot (c : ContextTier) : ContextTier.pub.rank ≤ c.rank := by
  cases c <;> simp [rank]

theorem ContextTier.priv_top (c : ContextTier) : c.rank ≤ ContextTier.priv.rank := by
  cases c <;> simp [rank]

/-- Secrecy max by rank. -/
def ContextTier.secMax (a b : ContextTier) : ContextTier :=
  if a.rank ≥ b.rank then a else b

theorem ContextTier.secMax_comm (a b : ContextTier) :
    a.secMax b = b.secMax a := by
  simp only [secMax]
  cases a <;> cases b <;> simp [rank]

theorem ContextTier.secMax_idem (a : ContextTier) :
    a.secMax a = a := by simp [secMax]

theorem ContextTier.secMax_assoc (a b c : ContextTier) :
    (a.secMax b).secMax c = a.secMax (b.secMax c) := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## Integrity Tier -/

inductive IntegrityTier where
  | untrusted
  | reviewed
  | trusted
  deriving DecidableEq, Repr

instance : Fintype IntegrityTier :=
  ⟨{.untrusted, .reviewed, .trusted}, by intro x; cases x <;> simp⟩

def IntegrityTier.rank : IntegrityTier → ℕ
  | .untrusted => 0
  | .reviewed => 1
  | .trusted => 2

/-- Integrity min by rank. -/
def IntegrityTier.intMin (a b : IntegrityTier) : IntegrityTier :=
  if a.rank ≤ b.rank then a else b

theorem IntegrityTier.intMin_comm (a b : IntegrityTier) :
    a.intMin b = b.intMin a := by
  simp only [intMin]
  cases a <;> cases b <;> simp [rank]

theorem IntegrityTier.intMin_idem (a : IntegrityTier) :
    a.intMin a = a := by simp [intMin]

theorem IntegrityTier.intMin_assoc (a b c : IntegrityTier) :
    (a.intMin b).intMin c = a.intMin (b.intMin c) := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## Flow Label -/

structure FlowLabel where
  secrecy : ContextTier
  integrity : IntegrityTier
  deriving DecidableEq

/-- Flow label join: secrecy rises (max), integrity drops (min). -/
def FlowLabel.join (a b : FlowLabel) : FlowLabel where
  secrecy := a.secrecy.secMax b.secrecy
  integrity := a.integrity.intMin b.integrity

theorem FlowLabel.join_comm (a b : FlowLabel) :
    a.join b = b.join a := by
  simp [join, ContextTier.secMax_comm, IntegrityTier.intMin_comm]

theorem FlowLabel.join_idem (a : FlowLabel) :
    a.join a = a := by
  simp [join, ContextTier.secMax_idem, IntegrityTier.intMin_idem]

theorem FlowLabel.join_assoc (a b c : FlowLabel) :
    (a.join b).join c = a.join (b.join c) := by
  exact congrArg₂ FlowLabel.mk
    (ContextTier.secMax_assoc a.secrecy b.secrecy c.secrecy)
    (IntegrityTier.intMin_assoc a.integrity b.integrity c.integrity)

/-! ## Channel Mapping -/

inductive Channel where
  | telegramPublic
  | telegramFamily
  | telegramDm
  | terminal
  | internal
  | api
  | moltbook
  deriving DecidableEq

instance : Fintype Channel :=
  ⟨{.telegramPublic, .telegramFamily, .telegramDm, .terminal, .internal, .api, .moltbook}, by intro x; cases x <;> simp⟩

def Channel.defaultContext : Channel → ContextTier
  | .telegramPublic | .api | .moltbook => .pub
  | .telegramFamily => .fam
  | .telegramDm | .internal | .terminal => .priv

/-- Integrity derived from context tier. -/
def IntegrityTier.fromContext : ContextTier → IntegrityTier
  | .pub => .untrusted
  | .fam => .reviewed
  | .priv => .trusted

/-- Context-to-integrity is monotone in rank. -/
theorem IntegrityTier.fromContext_rank_mono {a b : ContextTier}
    (h : a.rank ≤ b.rank) :
    (fromContext a).rank ≤ (fromContext b).rank := by
  cases a <;> cases b <;>
    simp [fromContext, IntegrityTier.rank, ContextTier.rank] at *

/-- Context-to-integrity is injective. -/
theorem IntegrityTier.fromContext_injective :
    Function.Injective fromContext := by
  intro a b h
  cases a <;> cases b <;> simp_all [fromContext]

/-- Default flow label for a channel. -/
def Channel.defaultLabel (ch : Channel) : FlowLabel where
  secrecy := ch.defaultContext
  integrity := IntegrityTier.fromContext ch.defaultContext

/-- Public channels are untrusted. -/
theorem Channel.public_untrusted :
    Channel.telegramPublic.defaultLabel.integrity = .untrusted := rfl

/-- Private channels (DM) are trusted. -/
theorem Channel.dm_trusted :
    Channel.telegramDm.defaultLabel.integrity = .trusted := rfl

/-- All public-facing channels map to untrusted. -/
theorem Channel.all_public_untrusted :
    Channel.api.defaultLabel.integrity = .untrusted ∧
    Channel.moltbook.defaultLabel.integrity = .untrusted ∧
    Channel.telegramPublic.defaultLabel.integrity = .untrusted :=
  ⟨rfl, rfl, rfl⟩

/-- All private channels map to trusted. -/
theorem Channel.all_private_trusted :
    Channel.telegramDm.defaultLabel.integrity = .trusted ∧
    Channel.internal.defaultLabel.integrity = .trusted ∧
    Channel.terminal.defaultLabel.integrity = .trusted :=
  ⟨rfl, rfl, rfl⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel
