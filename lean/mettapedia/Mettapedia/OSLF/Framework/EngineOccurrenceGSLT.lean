import Mettapedia.OSLF.Framework.PremiseAwareOccurrence
import Mettapedia.GSLT.Core.ProofRelevantJudgment
import Mettapedia.GSLT.Core.InteractionEvent

/-!
# Premise-aware engine occurrences as proof-relevant GSLT evidence

The existing finite-fuel engine returns a list of numbered occurrences.
The existing proof-relevant judgment construction turns an accepted
occurrence into an operational event. Erasing the event yields exactly
membership in the engine's reduct list, while the event still carries its
rule and alternative indices.

The construction is for one finite-fuel engine request. Its equation
relation is raw pattern equality; equation-modulo operational adequacy and
stability of indices across edits to an authored language are separate laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EngineOccurrenceGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.ProofRelevantJudgment
open Mettapedia.GSLT.Core.InteractionEvent

/-- An answer is witnessed by its exact numbered occurrence in the existing
premise-aware engine, at the chosen recursive fuel. -/
def judgment (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat) :
    Judgment Pattern Pattern where
  Evidence source target :=
    { occurrence : RewriteOccurrence //
      occurrence ∈ rewriteAtOccurrences base lang fuel source ∧
        occurrence.target = target }

/-- The generic proof-relevant GSLT of the executable occurrence judgment. -/
def system (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat) :
    ProofRelevantGSLT :=
  (judgment base lang fuel).system

/-- An accepted engine occurrence gives a one-step event with its original
local rule and alternative indices retained as data. -/
def acceptedEvent (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) (occurrence : RewriteOccurrence)
    (admitted : occurrence ∈ rewriteAtOccurrences base lang fuel source)
    (reaches : occurrence.target = target) :
    (system base lang fuel).Event where
  source := .query source
  target := .answer source target
  evidence := .accepted ⟨occurrence, admitted, reaches⟩

/-- Recover the same numbered occurrence from a selected operational step. -/
def eventOccurrence (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (event : (system base lang fuel).Event) :
    RewriteOccurrence := by
  cases event with
  | mk source target evidence =>
      cases evidence with
      | accepted receipt => exact receipt.val

@[simp] theorem acceptedEvent_occurrence
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) (occurrence : RewriteOccurrence)
    (admitted : occurrence ∈ rewriteAtOccurrences base lang fuel source)
    (reaches : occurrence.target = target) :
    eventOccurrence base lang fuel
      (acceptedEvent base lang fuel source target occurrence admitted reaches) =
        occurrence := rfl

/-- One interaction site names the rule position, authored rule name, and
local alternative position of an actual engine occurrence. -/
def eventSite (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (event : (system base lang fuel).Event) :
    Nat × String × Nat :=
  let occurrence := eventOccurrence base lang fuel event
  (occurrence.ruleIndex, occurrence.ruleName, occurrence.alternativeIndex)

@[simp] theorem acceptedEvent_site
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) (occurrence : RewriteOccurrence)
    (admitted : occurrence ∈ rewriteAtOccurrences base lang fuel source)
    (reaches : occurrence.target = target) :
    eventSite base lang fuel
      (acceptedEvent base lang fuel source target occurrence admitted reaches) =
        (occurrence.ruleIndex, occurrence.ruleName, occurrence.alternativeIndex) := rfl

/-- The same event family is an interaction presentation whose sites are
the engine's actual local rule and alternative positions. -/
def interactionPresentation (base : BasePremiseEvaluator)
    (lang : LanguageDef) (fuel : Nat) :
    InteractionPresentation (system base lang fuel).theory where
  Site := Nat × String × Nat
  Event := fun site source target =>
    { evidence : (system base lang fuel).steps.Evidence source target //
      eventSite base lang fuel ⟨source, target, evidence⟩ = site }
  sound := fun evidence =>
    (system base lang fuel).steps.erase evidence.val

/-- No semantic engine step is left without an occurrence-indexed site. -/
theorem interactionPresentation_complete
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat) :
    (interactionPresentation base lang fuel).Complete := by
  intro source target step
  obtain ⟨evidence⟩ := (system base lang fuel).steps.witness step
  exact ⟨⟨eventSite base lang fuel ⟨source, target, evidence⟩,
    ⟨evidence, rfl⟩⟩⟩

/-- Site annotation is an exact change of representation of one-step
evidence: it neither duplicates an occurrence nor forgets one. -/
def interactionEventEquiv
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : (system base lang fuel).theory.Term) :
    (Σ site, (interactionPresentation base lang fuel).Event site source target) ≃
      (system base lang fuel).steps.Evidence source target where
  toFun := fun tagged => tagged.2.val
  invFun := fun evidence =>
    ⟨eventSite base lang fuel ⟨source, target, evidence⟩, ⟨evidence, rfl⟩⟩
  left_inv := by
    intro tagged
    obtain ⟨site, evidence, siteEq⟩ := tagged
    subst site
    rfl
  right_inv := fun _ => rfl

/-- The extensional step relation of this event system is the original
engine result, including the premise evaluator and the selected fuel. -/
theorem step_iff_rewriteAt
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) :
    (system base lang fuel).theory.Step
        (.query source) (.answer source target) ↔
      target ∈ rewriteAt base lang fuel source := by
  change (judgment base lang fuel).theory.Step
    (.query source) (.answer source target) ↔
      target ∈ rewriteAt base lang fuel source
  rw [Judgment.query_step_answer_iff]
  constructor
  · rintro ⟨⟨occurrence, admitted, reaches⟩⟩
    rw [← rewriteAtOccurrences_targets]
    exact List.mem_map.mpr ⟨occurrence, admitted, reaches⟩
  · intro returned
    have indexed : target ∈
        (rewriteAtOccurrences base lang fuel source).map RewriteOccurrence.target := by
      rw [rewriteAtOccurrences_targets]
      exact returned
    obtain ⟨occurrence, admitted, reaches⟩ := List.mem_map.mp indexed
    exact ⟨⟨occurrence, admitted, reaches⟩⟩

/-- The GSLT step is also exactly the independently defined bounded
premise-aware contextual judgment, not merely an executable list member. -/
theorem step_iff_stepAt
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) :
    (system base lang fuel).theory.Step
        (.query source) (.answer source target) ↔
      StepAt base lang fuel source target :=
  (step_iff_rewriteAt base lang fuel source target).trans
    mem_rewriteAt_iff_stepAt

/-- Quantifying over the explicit fuel recovers precisely the least
contextual relation generated by the authored premise-aware rules. -/
theorem some_fuel_step_iff_step
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (source target : Pattern) :
    (∃ fuel, (system base lang fuel).theory.Step
      (.query source) (.answer source target)) ↔
      Step base lang source target := by
  simpa only [step_iff_rewriteAt] using
    (exists_mem_rewriteAt_iff_step (base := base) (lang := lang)
      (source := source) (target := target))

/-- Source and target alone can forget a selected occurrence. The exact
condition for two fixed-endpoint event witnesses to differ is that their
numbered occurrences differ. -/
theorem acceptedEvent_ne_of_occurrence_ne
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) (first second : RewriteOccurrence)
    (firstAdmitted : first ∈ rewriteAtOccurrences base lang fuel source)
    (secondAdmitted : second ∈ rewriteAtOccurrences base lang fuel source)
    (firstReaches : first.target = target)
    (secondReaches : second.target = target)
    (different : first ≠ second) :
    acceptedEvent base lang fuel source target first firstAdmitted firstReaches ≠
      acceptedEvent base lang fuel source target second secondAdmitted secondReaches := by
  intro same
  have equalOccurrences := congrArg (eventOccurrence base lang fuel) same
  simpa only [acceptedEvent_occurrence] using different equalOccurrences

#print axioms acceptedEvent_occurrence
#print axioms interactionPresentation_complete
#print axioms interactionEventEquiv
#print axioms step_iff_rewriteAt
#print axioms step_iff_stepAt
#print axioms some_fuel_step_iff_step
#print axioms acceptedEvent_ne_of_occurrence_ne

end Mettapedia.OSLF.Framework.EngineOccurrenceGSLT
