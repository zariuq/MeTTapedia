import Mettapedia.Logic.BDD.ProbMeTTaSourceSurface

/-!
# ProbMeTTa Literal State Space

This file models the explicit mutable spaces used by
`/home/zar/claude/ProbMeTTa/lib_prob.metta`:

- `&prob-facts`
- `&prob-templates`
- `clear-prob!`
- `prob-wmc-env`

The state layer is still pure Lean: operations return a new state instead of
mutating a MeTTa space in place. The important point is that the source-level
containers are explicit now, so the top-level runtime no longer jumps directly
from surface syntax to a normalized `ProbMeTTaSourceProgram`.

Positive example:
- `addRegisteredProbFact` really appends a new `(id, prob, atom)` entry to the
  `&prob-facts` layer and advances the fresh-id supply.

Negative example:
- this file does not model byte-for-byte MeTTa side effects or caching order.
  It formalizes the semantic state carried by those source operators.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics

/-- Pure state model for the literal ProbMeTTa spaces. -/
structure ProbMeTTaSpaceState (σ : LPSignature) where
  numProbFacts : ℕ
  nextFreshId : ℕ
  factIds : Fin numProbFacts → ℕ
  probFacts : Fin numProbFacts → GroundAtom σ
  probs : ProbAssignment numProbFacts
  probs_le_one : ∀ i, probs i ≤ 1
  normalRules : List (NormalClause σ)
  probTemplates : List (ENNReal × GroundAtom σ)
  templates_le_one : ∀ tpl ∈ probTemplates, tpl.1 ≤ 1
  factIds_injective : Function.Injective factIds
  factIds_lt_nextFresh : ∀ i, factIds i < nextFreshId
  facts_injective : Function.Injective probFacts
  applyCacheCleared : Bool

/-- Forget the literal spaces down to the normalized semantic program used by
the already-proved ProbMeTTa source surface. -/
def ProbMeTTaSpaceState.toSourceProgram {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) :
    ProbMeTTaSourceProgram σ state.numProbFacts where
  probFacts := state.probFacts
  probs := state.probs
  probs_le_one := state.probs_le_one
  normalRules := state.normalRules
  facts_injective := state.facts_injective

/-- The literal `prob-wmc-env` source operator returns the registered
`(id, prob)` pairs from `&prob-facts`. -/
def ProbMeTTaSpaceState.probWmcEnvEntries {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) : List (ℕ × ENNReal) :=
  List.ofFn fun i => (state.factIds i, state.probs i)

@[simp] theorem ProbMeTTaSpaceState.probWmcEnvEntries_length {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) :
    state.probWmcEnvEntries.length = state.numProbFacts := by
  simp [ProbMeTTaSpaceState.probWmcEnvEntries]

/-- Initial literal state after clearing all probabilistic spaces. -/
def clearProb {σ : LPSignature} : ProbMeTTaSpaceState σ where
  numProbFacts := 0
  factIds := Fin.elim0
  probFacts := Fin.elim0
  probs := Fin.elim0
  probs_le_one := by intro i; exact i.elim0
  normalRules := []
  probTemplates := []
  templates_le_one := by intro tpl h; simp at h
  factIds_injective := by intro i; exact i.elim0
  factIds_lt_nextFresh := by intro i; exact i.elim0
  facts_injective := by intro i; exact i.elim0
  nextFreshId := 0
  applyCacheCleared := true

@[simp] theorem clearProb_numProbFacts {σ : LPSignature} :
    (clearProb (σ := σ)).numProbFacts = 0 := rfl

@[simp] theorem clearProb_probTemplates {σ : LPSignature} :
    (clearProb (σ := σ)).probTemplates = [] := rfl

@[simp] theorem clearProb_normalRules {σ : LPSignature} :
    (clearProb (σ := σ)).normalRules = [] := rfl

/-- Remove every registered probabilistic fact, preserving the fresh-id
counter and the other source spaces. -/
def ProbMeTTaSpaceState.removeAllProbFacts {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) : ProbMeTTaSpaceState σ where
  numProbFacts := 0
  factIds := Fin.elim0
  probFacts := Fin.elim0
  probs := Fin.elim0
  probs_le_one := by intro i; exact i.elim0
  normalRules := state.normalRules
  probTemplates := state.probTemplates
  templates_le_one := state.templates_le_one
  factIds_injective := by intro i; exact i.elim0
  factIds_lt_nextFresh := by intro i; exact i.elim0
  facts_injective := by intro i; exact i.elim0
  nextFreshId := state.nextFreshId
  applyCacheCleared := state.applyCacheCleared

/-- Remove every probabilistic template from `&prob-templates`. -/
def ProbMeTTaSpaceState.removeAllProbTemplates {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) : ProbMeTTaSpaceState σ where
  numProbFacts := state.numProbFacts
  factIds := state.factIds
  probFacts := state.probFacts
  probs := state.probs
  probs_le_one := state.probs_le_one
  normalRules := state.normalRules
  probTemplates := []
  templates_le_one := by intro tpl h; simp at h
  factIds_injective := state.factIds_injective
  factIds_lt_nextFresh := state.factIds_lt_nextFresh
  facts_injective := state.facts_injective
  nextFreshId := state.nextFreshId
  applyCacheCleared := state.applyCacheCleared

/-- Clear the explicit apply-cache flag. -/
def ProbMeTTaSpaceState.clearApplyCache {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) : ProbMeTTaSpaceState σ where
  numProbFacts := state.numProbFacts
  factIds := state.factIds
  probFacts := state.probFacts
  probs := state.probs
  probs_le_one := state.probs_le_one
  normalRules := state.normalRules
  probTemplates := state.probTemplates
  templates_le_one := state.templates_le_one
  factIds_injective := state.factIds_injective
  factIds_lt_nextFresh := state.factIds_lt_nextFresh
  facts_injective := state.facts_injective
  nextFreshId := state.nextFreshId
  applyCacheCleared := true

/-- Pure-functional `clear-prob!`: remove rules, templates, registered facts,
and mark the apply-cache as cleared while preserving the fresh-id counter. -/
def ProbMeTTaSpaceState.clearSpaces {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) : ProbMeTTaSpaceState σ :=
  { (state.removeAllProbFacts.removeAllProbTemplates.clearApplyCache) with
    normalRules := [] }

/-- Add a source-level probabilistic template `(prob-template p goal)` to
`&prob-templates`. -/
def ProbMeTTaSpaceState.addProbTemplate {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ)
    (p : ENNReal) (hp : p ≤ 1)
    (goal : GroundAtom σ) : ProbMeTTaSpaceState σ where
  numProbFacts := state.numProbFacts
  factIds := state.factIds
  probFacts := state.probFacts
  probs := state.probs
  probs_le_one := state.probs_le_one
  normalRules := state.normalRules
  probTemplates := (p, goal) :: state.probTemplates
  templates_le_one := by
    intro tpl htpl
    rcases List.mem_cons.mp htpl with h | h
    · simpa [h] using hp
    · exact state.templates_le_one tpl h
  factIds_injective := state.factIds_injective
  factIds_lt_nextFresh := state.factIds_lt_nextFresh
  facts_injective := state.facts_injective
  nextFreshId := state.nextFreshId
  applyCacheCleared := state.applyCacheCleared

/-- Register a fresh probabilistic fact in `&prob-facts`, as `prob-id` does
when it materializes a template into a BDD variable. -/
def ProbMeTTaSpaceState.addRegisteredProbFact {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ)
    (p : ENNReal) (hp : p ≤ 1)
    (goal : GroundAtom σ)
    (hfreshAtom : ∀ i, state.probFacts i ≠ goal) :
    ProbMeTTaSpaceState σ where
  numProbFacts := state.numProbFacts + 1
  factIds := extendFinFn state.factIds state.nextFreshId
  probFacts := extendFinFn state.probFacts goal
  probs := extendFinFn state.probs p
  probs_le_one := by
    intro i
    by_cases hi : i.1 < state.numProbFacts
    · simpa [extendFinFn, hi] using state.probs_le_one ⟨i.1, hi⟩
    · simpa [extendFinFn, hi] using hp
  normalRules := state.normalRules
  probTemplates := state.probTemplates
  templates_le_one := state.templates_le_one
  factIds_injective := extendFinFn_injective state.factIds_injective (by
    intro i
    have hi := state.factIds_lt_nextFresh i
    omega)
  factIds_lt_nextFresh := by
    intro i
    by_cases hi : i.1 < state.numProbFacts
    · have hlt := state.factIds_lt_nextFresh ⟨i.1, hi⟩
      simpa [extendFinFn, hi] using Nat.lt_trans hlt (Nat.lt_succ_self state.nextFreshId)
    · have hEq : i = Fin.last state.numProbFacts := by
        apply Fin.ext
        have : i.1 = state.numProbFacts := by omega
        simpa using this
      subst hEq
      simp [extendFinFn]
  facts_injective := extendFinFn_injective state.facts_injective hfreshAtom
  nextFreshId := state.nextFreshId + 1
  applyCacheCleared := state.applyCacheCleared

/-- Add a normalized rule to `&self`. -/
def ProbMeTTaSpaceState.addRule {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ)
    (body : ProbMeTTaBody σ) (head : GroundAtom σ) : ProbMeTTaSpaceState σ where
  numProbFacts := state.numProbFacts
  factIds := state.factIds
  probFacts := state.probFacts
  probs := state.probs
  probs_le_one := state.probs_le_one
  normalRules := { head := head, body := bodyGoals body } :: state.normalRules
  probTemplates := state.probTemplates
  templates_le_one := state.templates_le_one
  factIds_injective := state.factIds_injective
  factIds_lt_nextFresh := state.factIds_lt_nextFresh
  facts_injective := state.facts_injective
  nextFreshId := state.nextFreshId
  applyCacheCleared := state.applyCacheCleared

@[simp] theorem ProbMeTTaSpaceState.clearSpaces_probTemplates {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) :
    state.clearSpaces.probTemplates = [] := by
  rfl

@[simp] theorem ProbMeTTaSpaceState.clearSpaces_normalRules {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) :
    state.clearSpaces.normalRules = [] := by
  rfl

@[simp] theorem ProbMeTTaSpaceState.clearSpaces_numProbFacts {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ) :
    state.clearSpaces.numProbFacts = 0 := by
  rfl

theorem ProbMeTTaSpaceState.addRegisteredProbFact_toSourceProgram_eq
    {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ)
    (p : ENNReal) (hp : p ≤ 1)
    (goal : GroundAtom σ)
    (hfreshAtom : ∀ i, state.probFacts i ≠ goal) :
    (state.addRegisteredProbFact p hp goal hfreshAtom).toSourceProgram =
      state.toSourceProgram.addProbFact p hp goal hfreshAtom := by
  rfl

theorem ProbMeTTaSpaceState.addRule_toSourceProgram_eq
    {σ : LPSignature}
    (state : ProbMeTTaSpaceState σ)
    (body : ProbMeTTaBody σ) (head : GroundAtom σ) :
    (state.addRule body head).toSourceProgram =
      state.toSourceProgram.probRule body head := by
  rfl

end Mettapedia.Logic.BDDCore
