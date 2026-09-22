import Mettapedia.Ethics.MoralUndecidability

/-!
# Rice's theorem for virtue possession

Target-centered virtue ethics judges acts: a response in a situation either hits
the virtue's target or it does not.  Agent-centered virtue ethics judges
*agents*: an agent possesses a virtue when it characteristically responds well
throughout the virtue's field.  This module asks where Rice's theorem lands
between the two.

Agents are program codes, as in `MoralUndecidability`; an agent's response in a
situation is what its code computes there.  A behavioral virtue fixes a field of
situations and a target relation on responses, and an agent possesses it when it
responds, and responds on target, at every situation of the field.

* **Possession is consequence-invariant** (`possessionCode_consequentialist`):
  it depends only on what the agent computes, so every nontrivial behavioral
  virtue has an undecidable possession problem (`possession_undecidable`).  The
  duty to respond is one such virtue; faithfully reporting the observed situation
  is another (`faithfulReport_possession_undecidable`).
* **The undecidability sits at the agent, not the act.**  Translating possession
  into target-centered terms gives one act judgment per situation of the field.
  Those act judgments involve no program, while deciding possession requires
  running the agent, which is where the halting problem enters — even when the
  field is a single situation and the target accepts every response.
* **Bounded possession escapes by reading more than consequences.**  Possession
  within an evaluation budget is decidable for a finite field and computable
  target (`boundedPossession_decidable`); possession is exactly bounded possession
  at some budget (`possesses_iff_exists_within`).  By the trilemma, a decidable
  nontrivial bounded check cannot be consequence-invariant
  (`boundedResponsiveness_not_consequentialist`): the budget is information about
  how an agent computes, not only what.  This is the resource-bound route out of
  Rice's theorem, and the computational content of certifying a disposition from
  finitely much observed behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.VirtuePossessionUndecidability

open Nat.Partrec (Code)
open Mettapedia.Ethics.MoralUndecidability

/-! ## Behavioral virtues and their possession -/

/-- A behaviorally specified virtue over program agents: the situations in which
it applies, and which responses in a situation hit its target. -/
structure BehavioralVirtue where
  field : ℕ → Prop
  target : ℕ → ℕ → Prop

/-- An agent possesses a behavioral virtue when, in every situation of the
field, it responds and its response hits the target. -/
def Possesses (virtue : BehavioralVirtue) (agent : ActionCode) : Prop :=
  ∀ situation, virtue.field situation →
    ∃ response ∈ agent.eval situation, virtue.target situation response

/-- The moral code of agents possessing a virtue. -/
def possessionCode (virtue : BehavioralVirtue) : MoralCode :=
  {agent | Possesses virtue agent}

/-- Possession depends only on what an agent computes. -/
theorem possessionCode_consequentialist (virtue : BehavioralVirtue) :
    Consequentialist (possessionCode virtue) := by
  intro first second same
  simp only [possessionCode, Set.mem_ofPred_eq, Possesses]
  rw [show first.eval = second.eval from same]

/-- **Rice's theorem for virtue possession.**  No computable judge decides
possession of a nontrivial behavioral virtue. -/
theorem possession_undecidable (virtue : BehavioralVirtue)
    (nontrivial : MorallyNontrivial (possessionCode virtue)) :
    ¬ DecidableMorality (possessionCode virtue) :=
  nontrivial_consequence_invariant_classifier_undecidable _
    (possessionCode_consequentialist virtue) nontrivial

/-! ## Specimens -/

/-- Responding at the base situation, with any response. -/
def responsiveness : BehavioralVirtue where
  field situation := situation = 0
  target _ _ := True

/-- Possessing responsiveness is exactly the existing responsiveness code, so the
virtue reading and the act-classifier reading pick out the same agents. -/
theorem possessionCode_responsiveness :
    possessionCode responsiveness = responsivenessCode := by
  ext agent
  simp only [possessionCode, responsivenessCode, Set.mem_ofPred_eq, Possesses,
    responsiveness, and_true, forall_eq]
  exact ⟨fun ⟨_, hmem⟩ => Part.dom_iff_mem.mpr ⟨_, hmem⟩, Part.dom_iff_mem.mp⟩

theorem responsiveness_possession_undecidable :
    ¬ DecidableMorality (possessionCode responsiveness) := by
  rw [possessionCode_responsiveness]
  exact responsivenessCode_undecidable

/-- Reporting, in every situation, exactly the situation observed. -/
def faithfulReport : BehavioralVirtue where
  field _ := True
  target situation response := response = situation

theorem faithfulReport_nontrivial :
    MorallyNontrivial (possessionCode faithfulReport) := by
  constructor
  · refine ⟨Code.id, ?_⟩
    intro situation _
    exact ⟨situation, by simp [Code.eval_id], rfl⟩
  · refine ⟨Code.zero, ?_⟩
    intro possesses
    obtain ⟨response, mem, onTarget⟩ := possesses 1 trivial
    simp only [Code.eval, faithfulReport] at mem onTarget
    have : response = 0 := Part.mem_some_iff.mp mem
    omega

/-- Faithful reporting cannot be computably audited either. -/
theorem faithfulReport_possession_undecidable :
    ¬ DecidableMorality (possessionCode faithfulReport) :=
  possession_undecidable faithfulReport faithfulReport_nontrivial

/-! ## Bounded possession -/

/-- A behavioral virtue with finitely many situations and a computable target. -/
structure FiniteBehavioralVirtue where
  field : List ℕ
  target : ℕ → ℕ → Bool
  target_primrec : Primrec₂ target

namespace FiniteBehavioralVirtue

/-- The behavioral virtue it specifies. -/
def toVirtue (virtue : FiniteBehavioralVirtue) : BehavioralVirtue where
  field situation := situation ∈ virtue.field
  target situation response := virtue.target situation response = true

/-- Whether an agent responds on target at every listed situation within an
evaluation budget. -/
def respondsWithin (virtue : FiniteBehavioralVirtue) (budget : ℕ)
    (agent : ActionCode) : Bool :=
  virtue.field.all fun situation =>
    (agent.evaln budget situation).any (virtue.target situation)

theorem respondsWithin_iff (virtue : FiniteBehavioralVirtue) (budget : ℕ)
    (agent : ActionCode) :
    virtue.respondsWithin budget agent = true ↔
      ∀ situation ∈ virtue.field, ∃ response ∈ agent.evaln budget situation,
        virtue.target situation response = true := by
  simp only [respondsWithin, List.all_eq_true, Option.any_eq_true]
  rfl

/-- The moral code of agents that possess the virtue within a budget. -/
def boundedPossessionCode (virtue : FiniteBehavioralVirtue) (budget : ℕ) :
    MoralCode :=
  {agent | virtue.respondsWithin budget agent = true}

/-- The bounded check is primitive recursive in the agent's code. -/
theorem respondsWithin_primrec (virtue : FiniteBehavioralVirtue) (budget : ℕ) :
    Primrec (virtue.respondsWithin budget) := by
  unfold respondsWithin
  induction virtue.field with
  | nil => exact Primrec.const true
  | cons situation rest ih =>
      have evaluated : Primrec fun agent : Code => agent.evaln budget situation :=
        Code.primrec_evaln.comp
          ((Primrec.const budget).pair Primrec.id |>.pair (Primrec.const situation))
      have head : Primrec fun agent : Code =>
          (agent.evaln budget situation).any (virtue.target situation) := by
        refine (Primrec.option_casesOn evaluated (Primrec.const false)
          (virtue.target_primrec.comp (Primrec.const situation) Primrec.snd).to₂).of_eq ?_
        intro agent
        cases agent.evaln budget situation <;> rfl
      exact (Primrec.and.comp head ih).of_eq fun agent => by simp [List.all_cons]

/-- **Bounded possession is decidable.** -/
theorem boundedPossession_decidable (virtue : FiniteBehavioralVirtue) (budget : ℕ) :
    DecidableMorality (virtue.boundedPossessionCode budget) :=
  ComputablePred.computable_iff.mpr
    ⟨virtue.respondsWithin budget, (virtue.respondsWithin_primrec budget).to_comp, rfl⟩

/-- Possession is bounded possession at some budget: bounded checks are sound,
and every possessing agent passes one. -/
theorem possesses_iff_exists_within (virtue : FiniteBehavioralVirtue)
    (agent : ActionCode) :
    Possesses virtue.toVirtue agent ↔
      ∃ budget, virtue.respondsWithin budget agent = true := by
  constructor
  · intro possesses
    suffices ∀ situations : List ℕ, (∀ situation ∈ situations, situation ∈ virtue.field) →
        ∃ budget, ∀ situation ∈ situations, ∃ response ∈ agent.evaln budget situation,
          virtue.target situation response = true by
      obtain ⟨budget, within⟩ := this virtue.field fun _ member => member
      exact ⟨budget, (virtue.respondsWithin_iff budget agent).mpr within⟩
    intro situations
    induction situations with
    | nil => exact fun _ => ⟨0, fun _ member => absurd member List.not_mem_nil⟩
    | cons situation rest ih =>
        intro inField
        obtain ⟨restBudget, restWithin⟩ :=
          ih fun other member => inField other (List.mem_cons_of_mem _ member)
        obtain ⟨response, mem, onTarget⟩ :=
          possesses situation (inField situation List.mem_cons_self)
        obtain ⟨headBudget, headMem⟩ := Code.evaln_complete.mp mem
        refine ⟨max headBudget restBudget, fun other member => ?_⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨response, Code.evaln_mono (le_max_left _ _) headMem, onTarget⟩
        · obtain ⟨otherResponse, otherMem, otherTarget⟩ := restWithin other member
          exact ⟨otherResponse, Code.evaln_mono (le_max_right _ _) otherMem, otherTarget⟩
  · rintro ⟨budget, within⟩ situation inField
    obtain ⟨response, mem, onTarget⟩ :=
      (virtue.respondsWithin_iff budget agent).mp within situation inField
    exact ⟨response, Code.evaln_sound mem, onTarget⟩

end FiniteBehavioralVirtue

/-! ## The budget is not a consequence -/

/-- Responding at the base situation, as a finite behavioral virtue. -/
def finiteResponsiveness : FiniteBehavioralVirtue where
  field := [0]
  target _ _ := true
  target_primrec := Primrec₂.const true

theorem boundedResponsiveness_nontrivial :
    MorallyNontrivial (finiteResponsiveness.boundedPossessionCode 1) := by
  constructor
  · refine ⟨Code.zero, ?_⟩
    show finiteResponsiveness.respondsWithin 1 Code.zero = true
    simp [FiniteBehavioralVirtue.respondsWithin, finiteResponsiveness, Code.evaln]
  · obtain ⟨silent, silentEval⟩ := Code.exists_code.mp Nat.Partrec.none
    refine ⟨silent, fun within => ?_⟩
    obtain ⟨response, mem, -⟩ :=
      (finiteResponsiveness.respondsWithin_iff 1 silent).mp within 0 List.mem_cons_self
    have := Code.evaln_sound mem
    simp [silentEval] at this

/-- **A decidable, nontrivial bounded check is not consequence-invariant.**  It
reads how long an agent takes, which its consequence profile does not record. -/
theorem boundedResponsiveness_not_consequentialist :
    ¬ Consequentialist (finiteResponsiveness.boundedPossessionCode 1) :=
  decidable_nontrivial_classifier_not_consequence_invariant _
    (finiteResponsiveness.boundedPossession_decidable 1)
    boundedResponsiveness_nontrivial

/-- And unbounded possession of the same virtue is undecidable. -/
theorem finiteResponsiveness_possession_undecidable :
    ¬ DecidableMorality (possessionCode finiteResponsiveness.toVirtue) := by
  have same : possessionCode finiteResponsiveness.toVirtue = responsivenessCode := by
    rw [← possessionCode_responsiveness]
    ext agent
    simp [possessionCode, Possesses, FiniteBehavioralVirtue.toVirtue,
      finiteResponsiveness, responsiveness]
  rw [same]
  exact responsivenessCode_undecidable

/-! ## Axiom audit -/

#print axioms possession_undecidable
#print axioms responsiveness_possession_undecidable
#print axioms faithfulReport_possession_undecidable
#print axioms FiniteBehavioralVirtue.boundedPossession_decidable
#print axioms FiniteBehavioralVirtue.possesses_iff_exists_within
#print axioms boundedResponsiveness_not_consequentialist
#print axioms finiteResponsiveness_possession_undecidable

end Mettapedia.Ethics.VirtuePossessionUndecidability
