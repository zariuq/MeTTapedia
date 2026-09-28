import Mettapedia.OSLF.Syntax.ScopedStepConstructorFrame

/-!
# Ordered constructor frames for conditional premises

An authored conditional rule has a list of premises. Each recursive premise
contributes a context-indexed child request; each nonrecursive premise
contributes a selected base result. The inductive list retains intermediate
assignments and each event in order. Its inhabitation is compared with the
actual premise runner, rather than assumed from a rule-algebra field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedPremiseFrameLists

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame

/-- A selected premise outcome. Recursive cases expose the requested child
and its local context. Base cases retain the selected root result. -/
inductive PremiseFrame {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat) :
    Premise → Assignment → Assignment → PremiseEvent Evidence → Type where
  | scopedStep {step initial final event}
      (wellScoped : step.isWellScopedAt ambient = true)
      (child : ChildRequest Evidence)
      (admitted : AdmittedChild oracle rule spec ambient index
        step.binders.length step.source step.target initial final event child) :
      PremiseFrame oracle relEnv lang rule spec ambient index
        (.scopedStep step) initial final event
  | congruence {source target initial final event}
      (child : ChildRequest Evidence)
      (admitted : AdmittedChild oracle rule spec ambient index 0
        source target initial final event child) :
      PremiseFrame oracle relEnv lang rule spec ambient index
        (.congruence source target) initial final event
  | freshness {condition initial final event}
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.freshness condition) initial) :
      PremiseFrame oracle relEnv lang rule spec ambient index
        (.freshness condition) initial final event
  | relationQuery {relation arguments initial final event}
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.relationQuery relation arguments) initial) :
      PremiseFrame oracle relEnv lang rule spec ambient index
        (.relationQuery relation arguments) initial final event
  | forAll {collection parameter body initial final event}
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.forAll collection parameter body) initial) :
      PremiseFrame oracle relEnv lang rule spec ambient index
        (.forAll collection parameter body) initial final event

/-- One premise result exists exactly when it has a selected constructor
frame. This compares actual scoped matching with the abstract child request. -/
theorem premiseFrame_nonempty_iff {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat)
    (premise : Premise) (initial final : Assignment)
    (event : PremiseEvent Evidence) :
    Nonempty (PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event) ↔
      (event, final) ∈ premiseResults oracle relEnv lang rule spec
        ambient index premise initial := by
  cases premise with
  | scopedStep step =>
      by_cases wellScoped : step.isWellScopedAt ambient = true
      · simp only [premiseResults, wellScoped, if_true]
        constructor
        · rintro ⟨frame⟩
          cases frame with
          | scopedStep _ child admitted =>
              exact (mem_stepResults_iff oracle rule spec ambient index
                step.binders.length step.source step.target initial
                final event).mpr ⟨child, admitted⟩
        · intro selected
          obtain ⟨child, admitted⟩ :=
            (mem_stepResults_iff oracle rule spec ambient index
              step.binders.length step.source step.target initial
              final event).mp selected
          exact ⟨.scopedStep wellScoped child admitted⟩
      · constructor
        · rintro ⟨frame⟩
          cases frame with
          | scopedStep checked _ _ => exact False.elim (wellScoped checked)
        · intro selected
          simp [premiseResults, wellScoped] at selected
  | congruence source target =>
      change Nonempty (PremiseFrame oracle relEnv lang rule spec ambient index
          (.congruence source target) initial final event) ↔
        (event, final) ∈ stepResults oracle rule spec ambient index 0
          source target initial
      constructor
      · rintro ⟨frame⟩
        cases frame with
        | congruence child admitted =>
            exact (mem_stepResults_iff oracle rule spec ambient index 0
              source target initial final event).mpr ⟨child, admitted⟩
      · intro selected
        obtain ⟨child, admitted⟩ :=
          (mem_stepResults_iff oracle rule spec ambient index 0
            source target initial final event).mp selected
        exact ⟨.congruence child admitted⟩
  | freshness condition =>
      change Nonempty (PremiseFrame oracle relEnv lang rule spec ambient index
          (.freshness condition) initial final event) ↔
        (event, final) ∈ rootResults relEnv lang spec ambient index
          (.freshness condition) initial
      constructor
      · rintro ⟨frame⟩
        cases frame with
        | freshness selected => exact selected
      · exact fun selected => ⟨.freshness selected⟩
  | relationQuery relation arguments =>
      change Nonempty (PremiseFrame oracle relEnv lang rule spec ambient index
          (.relationQuery relation arguments) initial final event) ↔
        (event, final) ∈ rootResults relEnv lang spec ambient index
          (.relationQuery relation arguments) initial
      constructor
      · rintro ⟨frame⟩
        cases frame with
        | relationQuery selected => exact selected
      · exact fun selected => ⟨.relationQuery selected⟩
  | forAll collection parameter body =>
      change Nonempty (PremiseFrame oracle relEnv lang rule spec ambient index
          (.forAll collection parameter body) initial final event) ↔
        (event, final) ∈ rootResults relEnv lang spec ambient index
          (.forAll collection parameter body) initial
      constructor
      · rintro ⟨frame⟩
        cases frame with
        | forAll selected => exact selected
      · exact fun selected => ⟨.forAll selected⟩

/-- A complete, ordered conditional-premise derivation retains every
intermediate assignment and each selected event. -/
inductive RunFrame {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) :
    Nat → List Premise → Assignment → Assignment →
      List (PremiseEvent Evidence) → Type where
  | nil {index initial} :
      RunFrame oracle relEnv lang rule spec ambient index [] initial initial []
  | cons {index premise rest initial intermediate final event history}
      (head : PremiseFrame oracle relEnv lang rule spec ambient index
        premise initial intermediate event)
      (tail : RunFrame oracle relEnv lang rule spec ambient
        (index + 1) rest intermediate final history) :
      RunFrame oracle relEnv lang rule spec ambient index
        (premise :: rest) initial final (event :: history)

/-- The executor's ordered premise run is inhabited exactly when the
independent constructor-list derivation is inhabited. Unlike endpoint-only
relations, this comparison keeps assignment transitions and event order. -/
theorem runFrame_nonempty_iff {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat)
    (premises : List Premise) (initial final : Assignment)
    (history : List (PremiseEvent Evidence)) :
    Nonempty (RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) ↔
      (final, history) ∈ runPremises oracle relEnv lang rule spec
        ambient index premises initial := by
  induction premises generalizing index initial final history with
  | nil =>
      constructor
      · rintro ⟨frame⟩
        cases frame
        simp [runPremises]
      · intro selected
        have equality : (final, history) = (initial, []) := by
          simpa [runPremises] using selected
        obtain ⟨finalEq, historyEq⟩ := Prod.mk.inj equality
        subst final
        subst history
        exact ⟨.nil⟩
  | cons premise rest inductionHypothesis =>
      constructor
      · rintro ⟨frame⟩
        cases frame with
        | cons head tail =>
            simp only [runPremises, List.mem_flatMap, List.mem_map]
            exact ⟨(_, _),
              (premiseFrame_nonempty_iff oracle relEnv lang rule spec
                ambient index premise initial _ _).mp ⟨head⟩,
              (_, _),
              (inductionHypothesis (index + 1) _ _ _).mp ⟨tail⟩,
              rfl⟩
      · intro selected
        simp only [runPremises, List.mem_flatMap, List.mem_map] at selected
        obtain ⟨⟨event, intermediate⟩, headSelected,
          ⟨last, tailHistory⟩, tailSelected, resultEq⟩ := selected
        have ⟨lastEq, historyEq⟩ := Prod.mk.inj resultEq
        subst final
        subst history
        obtain ⟨head⟩ :=
          (premiseFrame_nonempty_iff oracle relEnv lang rule spec
            ambient index premise initial intermediate event).mpr
              headSelected
        obtain ⟨tail⟩ :=
          (inductionHypothesis (index + 1) intermediate last tailHistory).mpr
            tailSelected
        exact ⟨.cons head tail⟩

end Mettapedia.OSLF.Binding.ScopedPremiseFrameLists
