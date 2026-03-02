import Mettapedia.Logic.GovernanceReasoning.Judgments

/-!
# Event Subsumption and Statement Identity

Formalizes the `is_complied_with_by` judgment from the governance-reasoning-engine
as a pure event-subsumption relation, plus backward-compatible statement IDs.

## Architecture

- §1 Role subsumption: abstract role assignment ⊆ concrete role assignment
- §2 Event subsumption: same predicate, role subsumption, same polarity
- §3 Core theorems: reflexivity, transitivity, role-contradiction exclusion
- §4 Total-roles lemma: full abstract roles ⇒ `sameEvent`
- §5 Statement identity wrapper (backward-compatible)
- §6 Judgment-level compliance bridge

## References

- governance-reasoning-engine/reason/judgement_level.metta lines 48-67
- GPT-5.2 Pro review (2026-03-02): separate event subsumption from judgment compliance
-/

namespace Mettapedia.Logic.GovernanceReasoning.Subsumption

open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.Bridge
open Mettapedia.Logic.GovernanceReasoning.Judgments

/-! ## §1 Role Subsumption

Every thematic role specified in the abstract eventuality must match in the
concrete one.  Unspecified roles (= `none`) in the abstract are unconstrained. -/

/-- Role subsumption: every role assigned in `abstract` must have the same
    value in `concrete`.  Roles not assigned in `abstract` are free. -/
def roleSubsumes
    (abstract concrete : ThematicRole → Option Entity) : Prop :=
  ∀ r : ThematicRole, ∀ a : Entity,
    abstract r = some a → concrete r = some a

theorem roleSubsumes_refl (ρ : ThematicRole → Option Entity) :
    roleSubsumes ρ ρ :=
  fun _ _ h => h

theorem roleSubsumes_trans
    {ρ₁ ρ₂ ρ₃ : ThematicRole → Option Entity}
    (h₁₂ : roleSubsumes ρ₁ ρ₂)
    (h₂₃ : roleSubsumes ρ₂ ρ₃) :
    roleSubsumes ρ₁ ρ₃ :=
  fun r a h => h₂₃ r a (h₁₂ r a h)

/-! ## §2 Event Subsumption

The pure event relation: abstract ⊑ concrete iff same predicate, roles
subsumed, and same polarity.

This is the Lean counterpart of `is_complied_with_by` from the
governance-reasoning-engine, factored as a pure event relation
rather than a judgment-level notion. -/

/-- Event subsumption: a concrete eventuality satisfies an abstract one
    when they share predicate and polarity, and every role specified
    in the abstract is matched in the concrete. -/
def eventSubsumes
    (abstract concrete : Eventuality Entity Pred) : Prop :=
  abstract.predicate = concrete.predicate ∧
  roleSubsumes abstract.roles concrete.roles ∧
  abstract.polarity = concrete.polarity

/-- Alias matching the governance-reasoning-engine name. -/
abbrev isCompliedWithBy := @eventSubsumes

/-! ## §3 Core Theorems -/

theorem eventSubsumes_refl (e : Eventuality Entity Pred) :
    eventSubsumes e e :=
  ⟨rfl, roleSubsumes_refl _, rfl⟩

theorem eventSubsumes_trans
    {e₁ e₂ e₃ : Eventuality Entity Pred}
    (h₁₂ : eventSubsumes e₁ e₂)
    (h₂₃ : eventSubsumes e₂ e₃) :
    eventSubsumes e₁ e₃ := by
  obtain ⟨hp₁₂, hr₁₂, hpol₁₂⟩ := h₁₂
  obtain ⟨hp₂₃, hr₂₃, hpol₂₃⟩ := h₂₃
  exact ⟨hp₁₂.trans hp₂₃, roleSubsumes_trans hr₁₂ hr₂₃, hpol₁₂.trans hpol₂₃⟩

/-- Role contradiction precludes event subsumption: if two eventualities
    disagree on a role value, the abstract cannot subsume the concrete. -/
theorem roleContradictory_not_eventSubsumes
    [DecidableEq Entity] [DecidableEq Pred]
    {ea ec : Eventuality Entity Pred}
    (hcontra : roleContradictory ea ec) :
    ¬ eventSubsumes ea ec := by
  intro ⟨_, hroles, _⟩
  obtain ⟨_, r, a, b, ha, hb, hab⟩ := hcontra
  have hca := hroles r a ha
  rw [hca] at hb
  exact hab (Option.some.inj hb)

/-! ## §4 Total Roles: Full Abstract Specification ⇒ sameEvent -/

/-- A role assignment is total when every thematic role is assigned. -/
def RolesTotal (ρ : ThematicRole → Option Entity) : Prop :=
  ∀ r, ∃ a, ρ r = some a

/-- If the abstract roles are total and subsumed by the concrete,
    then both role functions are equal. -/
theorem roleSubsumes_eq_of_total
    {ρ₁ ρ₂ : ThematicRole → Option Entity}
    (htotal : RolesTotal ρ₁)
    (hsub : roleSubsumes ρ₁ ρ₂) :
    ρ₁ = ρ₂ := by
  funext r
  obtain ⟨a, ha⟩ := htotal r
  rw [ha, hsub r a ha]

/-- When the abstract eventuality has total roles, subsumption implies `sameEvent`. -/
theorem eventSubsumes_implies_sameEvent_of_totalRoles
    [DecidableEq Entity] [DecidableEq Pred]
    {ea ec : Eventuality Entity Pred}
    (htotal : RolesTotal ea.roles)
    (hsub : eventSubsumes ea ec) :
    ea.sameEvent ec := by
  obtain ⟨hpred, hroles, _⟩ := hsub
  exact ⟨hpred, roleSubsumes_eq_of_total htotal hroles⟩

/-! ## §5 Statement Identity Wrapper

Backward-compatible wrapper adding an identity tag to `StatementJudgment`.
Does NOT modify the existing inductive — just wraps it.

Matches `(meta-triple $id ...)` from `governance-reasoning-engine/base/triple.metta`. -/

/-- A statement judgment tagged with an identity for higher-order reasoning. -/
structure IdStatementJudgment (Id Entity Pred : Type*) where
  /-- Statement identity tag (matches MeTTa `meta-triple id`). -/
  id : Id
  /-- The underlying statement judgment. -/
  statement : StatementJudgment Entity Pred

/-- Project away the ID to recover the plain statement. -/
def IdStatementJudgment.toJudgment {Id Entity Pred : Type*}
    (isj : IdStatementJudgment Id Entity Pred) :
    StatementJudgment Entity Pred :=
  isj.statement

/-- Governance analysis on ID-tagged statements equals analysis on projected statements. -/
theorem governanceAnalysisFromIdStatements_eq
    {Id : Type*}
    [DecidableEq Pred] [DecidableEq Entity]
    (sjs : List (IdStatementJudgment Id Entity Pred)) :
    governanceAnalysisFromStatements (sjs.map (·.statement)) =
      governanceAnalysisFromStatements (sjs.map IdStatementJudgment.toJudgment) := by
  rfl

/-! ## §6 Judgment-Level Compliance Bridge

The judgment-level compliance relation: an obligatory judgment is complied with
by a rexist judgment when the obligation's eventuality subsumes the rexist's. -/

/-- Judgment-level compliance: an obligatory judgment `jOb` is complied with by
    a rexist judgment `jRe` when the modalities are correct and the obligation's
    eventuality subsumes the rexist's eventuality.

    Matches `is_complied_with_by` at the judgment level from
    `governance-reasoning-engine/reason/judgement_level.metta`. -/
def obligationCompliedBy
    (jOb jRe : EventualityJudgment Entity Pred) : Prop :=
  jOb.modality = .obligatory ∧
  jRe.modality = .rexist ∧
  eventSubsumes jOb.eventuality jRe.eventuality

/-- Judgment-level violation: an obligation `jOb` is violated by
    a rexist judgment `jRe` when the forbidden eventuality subsumes the rexist's.

    Matches `is_violated_by` from the governance-reasoning-engine. -/
def prohibitionViolatedBy
    (jFb jRe : EventualityJudgment Entity Pred) : Prop :=
  jFb.modality = .forbidden ∧
  jRe.modality = .rexist ∧
  eventSubsumes jFb.eventuality jRe.eventuality

end Mettapedia.Logic.GovernanceReasoning.Subsumption
