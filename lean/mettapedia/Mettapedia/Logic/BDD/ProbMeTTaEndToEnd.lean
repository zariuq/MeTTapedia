import Mettapedia.Logic.BDD.ProbMeTTaBridge
import Mettapedia.Logic.BDD.ProbMeTTaLiteralMatching
import Mettapedia.Logic.BDD.ProbMeTTaPresentation
import Mettapedia.Logic.BDD.ProbMeTTaADRuntimeCore

/-!
# ProbMeTTa End-to-End Theorem Collection

This file states the honest end-to-end theorem chain for the now-formalized
literal ProbMeTTa layers:

- explicit literal state (`ProbMeTTaSpaceState`)
- literal nonground head selection (`ProbMeTTaLiteralMatching`)
- exact source semantics (`ProbMeTTaSourceSyntax`)
- runtime/BDD bridge (`ProbMeTTaRuntimeCore` / `ProbMeTTaBridge`)
- literal top-level rounding (`ProbMeTTaPresentation`)

Positive example:
- for a ground query, the literal state-space runtime produces an ordered BDD
  whose WMC is exactly the source probability, and the displayed answer is the
  explicit `round-to 5` presentation of that exact value.

Negative example:
- this file does not claim byte-for-byte replay of MeTTa reduction order.
  It states semantic equivalence between the literal layers we modeled and the
  already-proved BDD/source semantics.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP

/-- Exact `?prob` semantics for the literal state-space layer. -/
noncomputable def ProbMeTTaSpaceState.evalProbExact
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) : ENNReal :=
  state.toSourceProgram.probExact s q

/-- Exact `?prob-given` semantics for the literal state-space layer. -/
noncomputable def ProbMeTTaSpaceState.evalProbGivenExact
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) : ENNReal :=
  state.toSourceProgram.probGivenViaOperatorsExact s q evidence

/-- Literal nonground `?prob` fallback values: one exact value per matching
head produced by the source `match &self (rule $goal $_) $goal`. -/
noncomputable def ProbMeTTaSpaceState.evalProbLiteralMatches
    {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (goal : Atom σ) : List ENNReal :=
  state.toSourceProgram.probExactLiteralFallbackValues s goal

/-- Literal nonground `?prob-given` fallback values. -/
noncomputable def ProbMeTTaSpaceState.evalProbGivenLiteralMatches
    {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (goal : Atom σ) (evidence : List (GroundAtom σ)) : List ENNReal :=
  state.toSourceProgram.probGivenLiteralFallbackValues s goal evidence

@[simp] theorem ProbMeTTaSpaceState.evalProbExact_eq
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) :
    state.evalProbExact s q = state.toSourceProgram.probExact s q := rfl

@[simp] theorem ProbMeTTaSpaceState.evalProbGivenExact_eq
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    state.evalProbGivenExact s q evidence =
      state.toSourceProgram.probGivenViaOperatorsExact s q evidence := rfl

@[simp] theorem ProbMeTTaSpaceState.evalProbLiteralMatches_eq
    {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (goal : Atom σ) :
    state.evalProbLiteralMatches s goal =
      (state.toSourceProgram.literalMatchingHeads goal).map
        (fun head => state.toSourceProgram.probExact s head) := by
  rfl

@[simp] theorem ProbMeTTaSpaceState.evalProbGivenLiteralMatches_eq
    {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (goal : Atom σ) (evidence : List (GroundAtom σ)) :
    state.evalProbGivenLiteralMatches s goal evidence =
      (state.toSourceProgram.literalMatchingHeads goal).map
        (fun head => state.toSourceProgram.probGivenViaOperatorsExact s head evidence) := by
  rfl

/-- Ground-query exact theorem for the literal state space: there is an ordered
BDD computing the literal state's exact `?prob` value. -/
theorem probmetta_literalState_bdd_exact
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) :
    ∃ f : BDD state.numProbFacts,
      f.Ordered none ∧
      bdd_wmc f state.toSourceProgram.probWmcEnv = state.evalProbExact s q ∧
      (∀ a, f.eval a = true ↔
        queryHoldsNormalA state.toSourceProgram.toNormalProbLogProgram s q a) := by
  classical
  rcases state.toSourceProgram.probQueryBDD_spec s q with ⟨hord, hwmc, hiff⟩
  refine ⟨state.toSourceProgram.probQueryBDD s q, hord, ?_, hiff⟩
  unfold ProbMeTTaSpaceState.evalProbExact ProbMeTTaSourceProgram.probExact
  rfl

/-- Ground-query exact theorem for the literal state space and explicit
conditioning operators. -/
theorem probmetta_literalState_conditioning_exact
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    state.evalProbGivenExact s q evidence =
      bdd_wmc (state.toSourceProgram.probQueryEvidenceBDD s q evidence)
        state.toSourceProgram.probWmcEnv /
      bdd_wmc (state.toSourceProgram.probEvidenceBDD s evidence)
        state.toSourceProgram.probWmcEnv := by
  rfl

/-- Literal top-level `?prob` output is exactly the explicit `round-to 5`
presentation of the exact state-space semantics. -/
theorem probmetta_literalState_presentProb_eq_roundTo5
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) :
    state.presentProb s q = roundTo5 (state.evalProbExact s q).toReal := by
  rfl

/-- Literal top-level `?prob-given` output is exactly the explicit `round-to 5`
presentation of the exact conditional semantics. -/
theorem probmetta_literalState_presentProbGiven_eq_roundTo5
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    state.presentProbGiven s q evidence =
      roundTo5 (state.evalProbGivenExact s q evidence).toReal := by
  rfl

/-- The honest end-to-end theorem for ground `?prob`: explicit literal state,
exact BDD semantics, and top-level rounded presentation all line up. -/
theorem probmetta_literal_runtime_eq_proved_semantics
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) :
    ∃ f : BDD state.numProbFacts,
      f.Ordered none ∧
      bdd_wmc f state.toSourceProgram.probWmcEnv = state.evalProbExact s q ∧
      state.presentProb s q = roundTo5 (state.evalProbExact s q).toReal := by
  obtain ⟨f, hord, hwmc, _hiff⟩ := probmetta_literalState_bdd_exact state s q
  exact ⟨f, hord, hwmc, probmetta_literalState_presentProb_eq_roundTo5 state s q⟩

/-- The honest end-to-end theorem for ground `?prob-given`. -/
theorem probmetta_literal_runtime_given_eq_proved_semantics
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    state.evalProbGivenExact s q evidence =
      bdd_wmc (state.toSourceProgram.probQueryEvidenceBDD s q evidence)
        state.toSourceProgram.probWmcEnv /
      bdd_wmc (state.toSourceProgram.probEvidenceBDD s evidence)
        state.toSourceProgram.probWmcEnv ∧
    state.presentProbGiven s q evidence =
      roundTo5 (state.evalProbGivenExact s q evidence).toReal := by
  exact ⟨probmetta_literalState_conditioning_exact state s q evidence,
    probmetta_literalState_presentProbGiven_eq_roundTo5 state s q evidence⟩

end Mettapedia.Logic.BDDCore
