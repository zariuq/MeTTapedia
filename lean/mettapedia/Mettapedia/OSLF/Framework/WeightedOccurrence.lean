import Mettapedia.OSLF.MeTTaIL.Match
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.NormNum

/-!
# Labeled weighted occurrences over OSLF reductions

This module separates four objects that must not be inferred from one another:

* the authored reduction rules;
* concrete rule/match occurrences;
* the support relation obtained by forgetting occurrence identity;
* externally supplied nonnegative rates.

Rates are an enrichment of occurrences, not fields added to `LanguageDef`.
The executable OSLF helper currently returns a list of reducts.  The
`rewriteOccurrences` adapter retains the rule and local alternative indices
and proves that projecting its targets recovers that existing list exactly.

The finite pushforward operation at the end records the algebra needed when
an implementation has several representations of one semantic occurrence:
rates add over fibers.  Genuinely distinct semantic occurrences remain
distinct and therefore both contribute.
-/

namespace Mettapedia.OSLF.Framework.WeightedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open scoped BigOperators

universe u v

/-- A labeled transition-occurrence system.  An occurrence includes enough
identity that its target is functional once the source state is fixed. -/
structure OccurrenceSystem (State : Type u) (Event : Type v) where
  enabled : State → Event → Prop
  target : State → Event → State

namespace OccurrenceSystem

/-- Support erases event identity but not legality. -/
def Step (system : OccurrenceSystem State Event) (source target : State) : Prop :=
  ∃ event, system.enabled source event ∧ system.target source event = target

end OccurrenceSystem

/-- A nonnegative rate enrichment of a labeled occurrence system. -/
structure WeightedOccurrenceSystem (State : Type u) (Event : Type v)
    extends OccurrenceSystem State Event where
  rate : State → Event → NNReal

namespace WeightedOccurrenceSystem

/-- Positive-rate support.  Zero-rate occurrences remain legal in the base
system but are absent from the stochastic support. -/
def WeightedStep (system : WeightedOccurrenceSystem State Event)
    (source target : State) : Prop :=
  ∃ event, system.enabled source event ∧ 0 < system.rate source event ∧
    system.target source event = target

/-- Positive rates on every enabled occurrence make weighted support exactly
the underlying legal support. -/
theorem weightedStep_iff_step
    (system : WeightedOccurrenceSystem State Event)
    (positive : ∀ source event, system.enabled source event →
      0 < system.rate source event) :
    system.WeightedStep source target ↔ system.toOccurrenceSystem.Step source target := by
  constructor
  · rintro ⟨event, enabled, _ratePositive, targetEq⟩
    exact ⟨event, enabled, targetEq⟩
  · rintro ⟨event, enabled, targetEq⟩
    exact ⟨event, enabled, positive source event enabled, targetEq⟩

end WeightedOccurrenceSystem

/-! ## Concrete occurrence projection for the executable OSLF helper -/

/-- A concrete top-level rewrite occurrence.  The two indices distinguish
duplicate rules and duplicate matcher alternatives without pretending that
they are globally stable semantic names. -/
structure RewriteOccurrence where
  ruleIndex : Nat
  ruleName : String
  alternativeIndex : Nat
  target : Pattern
deriving DecidableEq, Repr

/-- All accepted alternatives contributed by one authored rule. -/
def ruleOccurrences (ruleIndex : Nat) (rule : RewriteRule) (term : Pattern) :
    List RewriteOccurrence :=
  (applyRule rule term).zipIdx.map fun (target, alternativeIndex) =>
    { ruleIndex
      ruleName := rule.name
      alternativeIndex
      target }

/-- All concrete top-level occurrences, retaining the authored rule and local
matcher-alternative positions. -/
def rewriteOccurrencesFrom (ruleIndex : Nat) (rules : List RewriteRule)
    (term : Pattern) : List RewriteOccurrence :=
  match rules with
  | [] => []
  | rule :: rest =>
      ruleOccurrences ruleIndex rule term ++
        rewriteOccurrencesFrom (ruleIndex + 1) rest term

/-- All concrete top-level occurrences, retaining the authored rule and local
matcher-alternative positions. -/
def rewriteOccurrences (language : LanguageDef) (term : Pattern) :
    List RewriteOccurrence :=
  rewriteOccurrencesFrom 0 language.rewrites term

private theorem ruleOccurrences_targets (ruleIndex : Nat)
    (rule : RewriteRule) (term : Pattern) :
    (ruleOccurrences ruleIndex rule term).map RewriteOccurrence.target =
      applyRule rule term := by
  simp [ruleOccurrences, List.map_map, Function.comp_def,
    List.zipIdx_map_fst]

private theorem rewriteOccurrencesFrom_targets (ruleIndex : Nat)
    (rules : List RewriteRule) (term : Pattern) :
    (rewriteOccurrencesFrom ruleIndex rules term).map RewriteOccurrence.target =
      rules.flatMap fun rule => applyRule rule term := by
  induction rules generalizing ruleIndex with
  | nil => rfl
  | cons rule rest inductionHypothesis =>
      simp [rewriteOccurrencesFrom, ruleOccurrences_targets,
        inductionHypothesis]

/-- Forgetting occurrence identity recovers the existing executable OSLF
reduct list, including its order and duplicate multiplicity. -/
theorem rewriteOccurrences_targets (language : LanguageDef) (term : Pattern) :
    (rewriteOccurrences language term).map RewriteOccurrence.target =
      rewriteStep language term := by
  exact rewriteOccurrencesFrom_targets 0 language.rewrites term

/-- Membership in ordinary reduction support is exactly target membership of
some labeled occurrence. -/
theorem target_mem_rewriteStep_iff (language : LanguageDef)
    (term target : Pattern) :
    target ∈ rewriteStep language term ↔
      ∃ occurrence ∈ rewriteOccurrences language term,
        occurrence.target = target := by
  rw [← rewriteOccurrences_targets]
  simp

/-- Target support induced by an external rate assignment. -/
def WeightedRewriteSupport (language : LanguageDef) (term : Pattern)
    (rate : RewriteOccurrence → NNReal) (target : Pattern) : Prop :=
  ∃ occurrence ∈ rewriteOccurrences language term,
    0 < rate occurrence ∧ occurrence.target = target

/-- If every admitted occurrence has positive rate, rate erasure recovers
ordinary executable rewrite support exactly. -/
theorem weightedRewriteSupport_iff
    (language : LanguageDef) (term : Pattern)
    (rate : RewriteOccurrence → NNReal)
    (positive : ∀ occurrence ∈ rewriteOccurrences language term,
      0 < rate occurrence) :
    WeightedRewriteSupport language term rate target ↔
      target ∈ rewriteStep language term := by
  rw [target_mem_rewriteStep_iff]
  constructor
  · rintro ⟨occurrence, member, _ratePositive, targetEq⟩
    exact ⟨occurrence, member, targetEq⟩
  · rintro ⟨occurrence, member, targetEq⟩
    exact ⟨occurrence, member, positive occurrence member, targetEq⟩

/-! ## Finite occurrence pushforward -/

/-- Sum rates over the fiber of an occurrence map.  This is the rate on a
semantic occurrence after forgetting administrative occurrence identity. -/
def pushforwardRate {Concrete Semantic : Type*}
    [Fintype Concrete] [DecidableEq Semantic]
    (forget : Concrete → Semantic) (rate : Concrete → NNReal)
    (semantic : Semantic) : NNReal :=
  ∑ concrete, if forget concrete = semantic then rate concrete else 0

/-- Pushforward neither creates nor destroys total rate: it redistributes the
same mass among semantic fibers. -/
theorem sum_pushforwardRate {Concrete Semantic : Type*}
    [Fintype Concrete] [Fintype Semantic] [DecidableEq Semantic]
    (forget : Concrete → Semantic) (rate : Concrete → NNReal) :
    (∑ semantic, pushforwardRate forget rate semantic) = ∑ concrete, rate concrete := by
  classical
  simp [pushforwardRate, Finset.sum_comm]

section FiberExamples

def forgetAdministrative : Bool → Unit
  | _ => ()

def administrativeRate : Bool → NNReal
  | false => 1
  | true => 2

/-- Administrative alternatives contribute through one summed fiber. -/
example : pushforwardRate forgetAdministrative administrativeRate
    () = 3 := by
  norm_num [pushforwardRate, forgetAdministrative, administrativeRate]

def genuineRate : Bool → NNReal
  | false => 1
  | true => 1

/-- Two genuinely distinct opportunities both contribute to total hazard. -/
example : (∑ event, genuineRate event) = 2 := by
  norm_num [genuineRate]

/-- Collapsing genuine multiplicity to one unit rate would be observably
wrong, even when both events happen to reach the same state. -/
example : (∑ event, genuineRate event) ≠ 1 := by
  norm_num [genuineRate]

end FiberExamples

end Mettapedia.OSLF.Framework.WeightedOccurrence
