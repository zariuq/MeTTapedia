import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# Constructor data for a scoped recursive premise

A scoped step premise requests a child reduction in its declared binder
extension. A successful request contains an exact selected oracle occurrence,
the returned candidate, and the assignment obtained by matching that
candidate. This is the recursive constructor data required by an indexed
operational presentation; equal candidates may still occupy different list
positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedStepConstructorFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

/-- A child request names its full local context, source and selected target.
The selected ordinal is retained separately from the endpoint pair. -/
structure ChildRequest (Evidence : Type) where
  ambient : Nat
  source : Pattern
  target : Pattern
  ordinal : Nat
  evidence : Evidence

/-- Exact constructor data for one successful scoped-premise result. The
stored oracle position prevents two equal events from collapsing. -/
def AdmittedChild {Evidence : Type} (oracle : StepOracle Evidence)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (initial final : Assignment)
    (event : PremiseEvent Evidence) (child : ChildRequest Evidence) : Prop :=
  child.ambient = localDepth + ambient ∧
    instantiateAt? rule spec ambient (.premise index 0 0) [] localDepth
      initial source = some child.source ∧
    child.source.isWellScopedAt child.ambient = true ∧
    ((child.evidence, child.target), child.ordinal) ∈
      (oracle child.ambient child.source).zipIdx ∧
    child.target.isWellScopedAt child.ambient = true ∧
    final ∈ matchAt rule spec ambient (.premise index 0 1) [] localDepth
      initial target child.target ∧
    event = .step index child.ordinal child.evidence

/-- Step results are exactly the constructor data of recursive requests
indexed by the premise's extended context. The theorem also retains the
selected oracle occurrence and the actual final matching assignment. -/
theorem mem_stepResults_iff {Evidence : Type} (oracle : StepOracle Evidence)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (initial final : Assignment) (event : PremiseEvent Evidence) :
    (event, final) ∈ stepResults oracle rule spec ambient index localDepth
      source target initial ↔
      ∃ child, AdmittedChild oracle rule spec ambient index localDepth
        source target initial final event child := by
  unfold stepResults
  cases instantiated : instantiateAt? rule spec ambient
      (.premise index 0 0) [] localDepth initial source with
  | none =>
      constructor
      · intro h
        simp at h
      · rintro ⟨child, _, sourceEq, _⟩
        rw [instantiated] at sourceEq
        cases sourceEq
  | some body =>
      dsimp only
      by_cases sourceScoped : body.isWellScopedAt (localDepth + ambient) = true
      · simp only [sourceScoped, if_true, List.mem_flatMap]
        constructor
        · rintro ⟨⟨⟨evidence, candidate⟩, ordinal⟩, selected, result⟩
          by_cases candidateScoped :
              candidate.isWellScopedAt (localDepth + ambient) = true
          · simp only [candidateScoped, if_true, List.mem_map] at result
            obtain ⟨completed, matched, resultEq⟩ := result
            have ⟨eventEq, finalEq⟩ := Prod.mk.inj resultEq
            subst event
            subst final
            refine ⟨⟨localDepth + ambient, body, candidate, ordinal,
              evidence⟩, rfl, instantiated, sourceScoped, selected,
              candidateScoped, matched, rfl⟩
          · simp [candidateScoped] at result
        · rintro ⟨child, context, sourceEq, sourceScoped,
            selected, candidateScoped, matched, eventEq⟩
          cases child with
          | mk childAmbient childSource childTarget ordinal evidence =>
              dsimp at context sourceEq sourceScoped selected candidateScoped matched eventEq
              have childSourceEq : childSource = body :=
                Option.some.inj (sourceEq.symm.trans instantiated)
              subst childSource
              subst childAmbient
              subst event
              refine ⟨((evidence, childTarget), ordinal), selected, ?_⟩
              simp only [candidateScoped, if_true, List.mem_map]
              exact ⟨final, matched, rfl⟩
      · constructor
        · intro h
          simp [sourceScoped] at h
        · rintro ⟨child, context, sourceEq, childScoped, _⟩
          have childSourceEq : child.source = body :=
            Option.some.inj (sourceEq.symm.trans instantiated)
          rw [context, childSourceEq] at childScoped
          exact False.elim (sourceScoped childScoped)

/-- A one-premise run exposes exactly one recursive child frame and keeps
its selected event in the ordered history. This is the base case for the
finite list polynomial of conditional scoped premises. -/
theorem singleScopedRun_hasChild {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (step : ScopedStepPremise)
    (initial final : Assignment) (history : List (PremiseEvent Evidence))
    (wellScoped : step.isWellScopedAt ambient = true)
    (run : (final, history) ∈
      runPremises oracle relEnv lang rule spec ambient 0
        [.scopedStep step] initial) :
    ∃ event child,
      history = [event] ∧
      AdmittedChild oracle rule spec ambient 0 step.binders.length
        step.source step.target initial final event child := by
  simp only [runPremises, List.mem_flatMap, List.mem_map] at run
  obtain ⟨⟨event, intermediate⟩, first, ⟨last, tail⟩,
    rest, result⟩ := run
  have endEq : (last, tail) = (intermediate, []) := by
    simpa [runPremises] using rest
  have ⟨lastEq, tailEq⟩ := Prod.mk.inj endEq
  subst last
  subst tail
  have ⟨finalEq, historyEq⟩ := Prod.mk.inj result
  subst final
  subst history
  have childResult : (event, intermediate) ∈
      stepResults oracle rule spec ambient 0 step.binders.length
        step.source step.target initial := by
    simpa [premiseResults, wellScoped] using first
  obtain ⟨child, valid⟩ :=
    (mem_stepResults_iff oracle rule spec ambient 0 step.binders.length
      step.source step.target initial intermediate event).mp childResult
  exact ⟨event, child, rfl, valid⟩

/-- Finishing a rule leaves its selected premise history intact. -/
theorem finish?_history {Evidence : Type}
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (captured completed : Assignment)
    (history : List (PremiseEvent Evidence)) (firing : RuleFiring Evidence)
    (finished : finish? rule spec ambient captured completed history =
      some firing) :
    firing.history = history := by
  unfold finish? at finished
  cases result : reduct? rule spec ambient completed with
  | none => simp [result] at finished
  | some target =>
      by_cases targetScoped : target.isWellScopedAt ambient = true
      · simp [result, targetScoped] at finished
        cases finished
        rfl
      · simp [result, targetScoped] at finished

end Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
