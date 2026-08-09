import Mettapedia.Logic.BDD.ProbMeTTaSourceSyntax
import Mettapedia.Logic.LP.Matching

/-!
# ProbMeTTa Literal Matching Semantics

This file formalizes the literal source-level nonground fallback

`(match &self (rule $goal $_) $goal)`

from `/home/zar/claude/ProbMeTTa/lib_prob.metta`.

The key design choice is to model the fallback as a **list of matching ground
heads**, not as a single arbitrary witness. That matches the source `match`
operator better: MeTTa can return multiple matching heads via
`collapse (superpose ...)`.

Positive example:
- if a rule head matches the query pattern under LP matching, it appears in
  `literalMatchingHeads`.

Negative example:
- this file does not formalize the full MeTTa pattern engine or `collapse`
  evaluation order. It isolates just the head-selection layer needed by the
  nonground `?prob` / `?prob-given` branch.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP

/-- A ground rule head is selected by the literal ProbMeTTa fallback when the
source goal pattern matches it under LP one-sided matching. -/
def ProbMeTTaSourceProgram.matchesRuleHead {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (_prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ) (head : GroundAtom σ) : Prop :=
  ∃ θ : Subst σ, matchAtom goal head = .success θ

/-- Literal source-level `match &self (rule $goal $_) $goal`: collect every
ground rule head that matches the goal pattern. -/
def ProbMeTTaSourceProgram.literalMatchingHeads {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ) : List (GroundAtom σ) :=
  prog.ruleHeads.filterMap fun head =>
    match matchAtom goal head with
    | .success _ => some head
    | .failure => none

theorem ProbMeTTaSourceProgram.literalMatchingHeads_mem_iff
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ) (head : GroundAtom σ) :
    head ∈ prog.literalMatchingHeads goal ↔
      head ∈ prog.ruleHeads ∧ prog.matchesRuleHead goal head := by
  unfold ProbMeTTaSourceProgram.literalMatchingHeads
  unfold ProbMeTTaSourceProgram.matchesRuleHead
  constructor
  · intro h
    rw [List.mem_filterMap] at h
    rcases h with ⟨cand, hcand, hsome⟩
    cases hmatch : matchAtom goal cand with
    | failure =>
        simp [hmatch] at hsome
    | success θ =>
        simp [hmatch] at hsome
        subst hsome
        exact ⟨hcand, ⟨θ, hmatch⟩⟩
  · rintro ⟨hhead, ⟨θ, hθ⟩⟩
    rw [List.mem_filterMap]
    refine ⟨head, hhead, ?_⟩
    simp [hθ]

theorem ProbMeTTaSourceProgram.literalMatchingHeads_subset_ruleHeads
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ) (head : GroundAtom σ)
    (h : head ∈ prog.literalMatchingHeads goal) :
    head ∈ prog.ruleHeads :=
  (prog.literalMatchingHeads_mem_iff goal head).1 h |>.1

/-- A literal match witness keeps the actual source query pattern in scope,
instead of collapsing immediately to the older membership-only witness. -/
abbrev ProbMeTTaSourceProgram.LiteralHeadWitness {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ) := { head : GroundAtom σ // head ∈ prog.literalMatchingHeads goal }

/-- Any literal match witness induces a rule-head witness in the older
normalized source syntax. -/
def ProbMeTTaSourceProgram.literalWitnessToHeadWitness
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : ProbMeTTaSourceProgram σ n)
    (goal : Atom σ)
    (w : prog.LiteralHeadWitness goal) : prog.HeadWitness :=
  ⟨w.1, prog.literalMatchingHeads_subset_ruleHeads goal w.1 w.2⟩

/-- Once a literal source match has selected a concrete head, the exact `?prob`
semantics continue on that head. -/
noncomputable def ProbMeTTaSourceProgram.probExactMatchedLiteral
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (w : prog.LiteralHeadWitness goal) : ENNReal :=
  prog.probExact s w.1

/-- Literal-source conditional fallback: after head selection, continue with
the explicit source operators already formalized for `?prob-given`. -/
noncomputable def ProbMeTTaSourceProgram.probGivenMatchedLiteral
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ)
    (w : prog.LiteralHeadWitness goal)
    (evidence : List (GroundAtom σ)) : ENNReal :=
  prog.probGivenViaOperatorsExact s w.1 evidence

@[simp] theorem ProbMeTTaSourceProgram.probExactMatchedLiteral_eq
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (w : prog.LiteralHeadWitness goal) :
    prog.probExactMatchedLiteral s goal w = prog.probExact s w.1 := rfl

@[simp] theorem ProbMeTTaSourceProgram.probGivenMatchedLiteral_eq
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ)
    (w : prog.LiteralHeadWitness goal)
    (evidence : List (GroundAtom σ)) :
    prog.probGivenMatchedLiteral s goal w evidence =
      prog.probGivenViaOperatorsExact s w.1 evidence := rfl

theorem ProbMeTTaSourceProgram.probExactMatchedLiteral_eq_matchedHead
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (w : prog.LiteralHeadWitness goal) :
    prog.probExactMatchedLiteral s goal w =
      prog.probExactMatchedHead s (prog.literalWitnessToHeadWitness goal w) := by
  rfl

theorem ProbMeTTaSourceProgram.probGivenMatchedLiteral_eq_matchedHead
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (w : prog.LiteralHeadWitness goal)
    (evidence : List (GroundAtom σ)) :
    prog.probGivenMatchedLiteral s goal w evidence =
      prog.probGivenViaOperatorsMatchedHead
        s (prog.literalWitnessToHeadWitness goal w) evidence := by
  rfl

/-- Literal nonground ProbMeTTa semantics as a list of exact probabilities, one
for each matching rule head selected by the source `match`. -/
noncomputable def ProbMeTTaSourceProgram.probExactLiteralFallbackValues
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) : List ENNReal :=
  (prog.literalMatchingHeads goal).map fun head => prog.probExact s head

/-- Literal nonground conditional semantics as a list of exact conditional
probabilities, one for each matching rule head. -/
noncomputable def ProbMeTTaSourceProgram.probGivenLiteralFallbackValues
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (evidence : List (GroundAtom σ)) : List ENNReal :=
  (prog.literalMatchingHeads goal).map fun head =>
    prog.probGivenViaOperatorsExact s head evidence

theorem ProbMeTTaSourceProgram.probExactMatchedLiteral_mem_fallbackValues
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ) (w : prog.LiteralHeadWitness goal) :
    prog.probExactMatchedLiteral s goal w ∈
      prog.probExactLiteralFallbackValues s goal := by
  unfold ProbMeTTaSourceProgram.probExactMatchedLiteral
  unfold ProbMeTTaSourceProgram.probExactLiteralFallbackValues
  exact List.mem_map.mpr ⟨w.1, w.2, rfl⟩

theorem ProbMeTTaSourceProgram.probGivenMatchedLiteral_mem_fallbackValues
    {σ : LPSignature} {n : ℕ}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goal : Atom σ)
    (w : prog.LiteralHeadWitness goal)
    (evidence : List (GroundAtom σ)) :
    prog.probGivenMatchedLiteral s goal w evidence ∈
      prog.probGivenLiteralFallbackValues s goal evidence := by
  unfold ProbMeTTaSourceProgram.probGivenMatchedLiteral
  unfold ProbMeTTaSourceProgram.probGivenLiteralFallbackValues
  exact List.mem_map.mpr ⟨w.1, w.2, rfl⟩

end Mettapedia.Logic.BDDCore
