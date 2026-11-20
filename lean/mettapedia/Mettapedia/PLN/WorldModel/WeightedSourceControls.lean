import Mettapedia.PLN.WorldModel.WeightedSourceExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByValue
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns

/-!
# Shared draws, scoring, and source-level sharing controls

The general finite compiler handles named draw coordinates. These controls
also evaluate the actual source's native by-value let and by-name repeated
execution specimens, under an explicitly uniform choice model. The source
semantics supplies answer bags; probability is an additional valuation.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WeightedSourceControls

open scoped ENNReal
open Mettapedia.Logic.BDDCore Mettapedia.Logic.BDDCore.StatePredicates
open Mettapedia.PLN.WorldModel.WeightedSourcePrograms
open Mettapedia.Machines.GuardConjunctionCompiler (Guard)
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

@[simp] private theorem zero_ne_one {n : Nat} : (BDD.zero : BDD n) ≠ .one := by intro h; cases h
@[simp] private theorem one_ne_zero {n : Nat} : (BDD.one : BDD n) ≠ .zero := by intro h; cases h

def shared : Body 1 := .ret (.both (.atom 0) (.atom 0))
def independent : Body 2 := .ret (.both (.atom 0) (.atom 1))
noncomputable def fair {n : Nat} : Fin n → ℝ≥0∞ := fun _ => 1 / 2

theorem compile_shared : compile shared id = [(1, bit (0 : Fin 1))] := by
  simp [compile, shared, resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg, bit, bddVar, bddNot, apply, mk]

theorem shared_mass : shared.mass fair id = 1 / 2 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair]), compile_shared]
  norm_num [Circuit.count, bit, bddVar, mk, bdd_wmc, fair]

theorem compile_independent : compile independent id =
    [(1, ⟨.node 0 .zero (.node 1 .zero .one), by
      exact .node (by intro b impossible; cases impossible) .zero
        (.node (by intro b same; cases same; decide) .zero .one (by decide)) (by decide)⟩)] := by
  simp [compile, independent, resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg, bit, bddVar, bddNot, apply, mk]

theorem independent_mass : independent.mass fair id = 1 / 4 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair]), compile_independent]
  norm_num [Circuit.count, bdd_wmc, fair]
  rw [← ENNReal.mul_inv (by left; norm_num) (by left; norm_num)]
  norm_num

/-- The source compiler therefore preserves the different laws of shared and fresh draws. -/
theorem sharing_changes_probability : shared.mass fair id ≠ independent.mass fair id := by
  rw [shared_mass, independent_mass]
  norm_num

noncomputable def scored : Body 1 := .branch (.atom 0)
  (.score (3 / 4) (.ret (.constant true)))
  (.score (1 / 4) (.ret (.constant false)))

theorem scored_numerator : scored.mass fair id = 3 / 8 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair])]
  norm_num [scored, compile, Circuit.count, Circuit.scale, Circuit.restrict,
    resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg,
    bit, bddVar, bddNot, apply, mk, bdd_wmc, fair]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]

theorem scored_normalizer : scored.mass fair (fun _ => true) = 1 / 2 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair])]
  norm_num [scored, compile, Circuit.count, Circuit.scale, Circuit.restrict,
    resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg,
    bit, bddVar, bddNot, apply, mk, bdd_wmc, fair]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]

theorem scored_posterior : scored.posterior fair id = some (3 / 4) := by
  norm_num [Body.posterior, scored_normalizer, scored_numerator]
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num [ENNReal.div_eq_top]) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

def onlyHeads : Body 1 := .observe (.atom 0) (.ret (.constant true))

theorem observed_mass : onlyHeads.mass fair (fun _ => true) = 1 / 2 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair])]
  norm_num [onlyHeads, compile, Circuit.count, Circuit.scale, Circuit.restrict,
    resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg,
    bit, bddVar, bddNot, apply, mk, bdd_wmc, fair]

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage
open Elaboration

/-- A supplied uniform valuation of terminal occurrences. This agrees with
fair independent binary choices for the balanced native specimens below;
unbalanced choice trees generally induce a different terminal valuation. -/
noncomputable def uniformHit (bag : Multiset (Set MClosed)) (target : MClosed) : ℝ≥0∞ := by
  classical
  exact (bag.map fun readings => if target ∈ readings then (1 : ℝ≥0∞) else 0).sum / bag.card

private def readPair : MClosed → Option (Int × Int)
  | .op (.tup 3) (.cons (.op (.sym "pair") .nil)
      (.cons (.op (.num first) .nil) (.cons (.op (.num second) .nil) .nil))) => some (first, second)
  | _ => none

@[simp] private theorem pair_eq_iff (a b c d : Int) :
    ctuple [csym "pair", cnum a, cnum b] = ctuple [csym "pair", cnum c, cnum d] ↔ a = c ∧ b = d := by
  constructor
  · intro same
    have decoded := congrArg readPair same
    exact Prod.mk.inj (Option.some.inj decoded)
  · rintro ⟨rfl, rfl⟩
    rfl

def bothHigh : MClosed := ctuple [csym "pair", cnum 2, cnum 2]

theorem native_let_mass : uniformHit
    (Config.answers (D := ExampleHeld.D)
      (⟨⟨9, 0, ExampleByValue.sp⟩, ExampleByValue.finalBag⟩ : Config mkeys [] () MTy)) bothHigh =
        shared.mass fair id := by
  rw [ExampleByValue.final_answers, shared_mass]
  norm_num [uniformHit, bothHigh]

theorem native_fresh_mass : uniformHit
    (Config.answers (D := ExampleHeld.D)
      (⟨⟨10, 0, ExampleHeldRuns.sp⟩, ExampleHeldRuns.finalBag⟩ : Config mkeys [] () MTy)) bothHigh =
        independent.mass fair id := by
  rw [ExampleHeldRuns.runs_answers, independent_mass]
  norm_num [uniformHit, bothHigh]

/-- A native source `let` samples once and both uses retain that draw.
The uniform valuation is justified here by one fair binary source choice. -/
theorem native_let_control :
    ∃ C, Runs ExampleHeld.D (elaborate (ExampleHeld.reading false) ExampleByValue.surfaceV)
        ExampleHeld.supply
        (Config.initial (fun _ => 0) (elabQuery (ExampleHeld.reading false)
          ExampleByValue.surfaceV ExampleHeld.querySurface)) C ∧
      Config.Quiescent (D := ExampleHeld.D)
        (elaborate (ExampleHeld.reading false) ExampleByValue.surfaceV) ExampleHeld.supply C ∧
      uniformHit (Config.answers (D := ExampleHeld.D) C) bothHigh = shared.mass fair id := by
  obtain ⟨C, run, done, rows⟩ := ExampleByValue.byValue_example
  refine ⟨C, run, done, ?_⟩
  rw [rows, shared_mass]
  norm_num [uniformHit, bothHigh]

/-- Running the held computation at each use produces two fresh fair choices. -/
theorem native_fresh_control :
    ∃ C, Runs ExampleHeld.D (elaborate (ExampleHeld.reading true) ExampleHeld.surface)
        ExampleHeld.supply
        (Config.initial (fun _ => 0) (elabQuery (ExampleHeld.reading true)
          ExampleHeld.surface ExampleHeld.querySurface)) C ∧
      Config.Quiescent (D := ExampleHeld.D)
        (elaborate (ExampleHeld.reading true) ExampleHeld.surface) ExampleHeld.supply C ∧
      uniformHit (Config.answers (D := ExampleHeld.D) C) bothHigh = independent.mass fair id := by
  obtain ⟨C, run, done, rows⟩ := ExampleHeldRuns.runs_example
  refine ⟨C, run, done, ?_⟩
  rw [rows, independent_mass]
  norm_num [uniformHit, bothHigh]

/-- Missing and infinite normalization mass both refuse a posterior. -/
theorem failed_posterior : (Body.fail : Body 1).posterior fair id = none := by
  simp [Body.posterior, Body.mass]

theorem infinite_score_refused : (Body.score ⊤ (Body.ret (.constant true)) : Body 1).posterior fair id = none := by
  have mass : (Body.score ⊤ (Body.ret (.constant true)) : Body 1).mass fair (fun _ => true) = ⊤ := by
    rw [← compile_mass _ _ (fun _ => by norm_num [fair])]
    simp [compile, Circuit.count, Circuit.scale, resultDiagram, choose, truth,
      compileGuard, disj, conj, neg, bddNot, apply, bdd_wmc]
  simp [Body.posterior, mass]

/-- Uniform terminal counting is not the fair-choice law of an unbalanced tree:
`choice a (choice b c)` assigns mass one half to `a`, not one third. -/
theorem unbalanced_uniform_is_wrong :
    uniformHit {{cnum 1}, {cnum 2}, {cnum 3}} (cnum 1) = 1 / 3 ∧
      shared.mass fair id ≠ uniformHit {{cnum 1}, {cnum 2}, {cnum 3}} (cnum 1) := by
  have distinct12 : (cnum 1 : MClosed) ≠ cnum 2 := by intro same; cases same
  have distinct13 : (cnum 1 : MClosed) ≠ cnum 3 := by intro same; cases same
  have uniform : uniformHit {{cnum 1}, {cnum 2}, {cnum 3}} (cnum 1) = 1 / 3 := by
    norm_num [uniformHit, distinct12, distinct13]
  refine ⟨uniform, ?_⟩
  rw [shared_mass, uniform]
  norm_num

/-- A fair choice between `a` and a second fair choice between `b` and `c`. -/
def unbalanced : Body 2 := .branch (.atom 0) (.ret (.constant true))
  (.branch (.atom 1) (.ret (.constant false)) (.ret (.constant false)))

theorem unbalanced_first_probability : unbalanced.mass fair id = 1 / 2 := by
  rw [← compile_mass _ _ (fun _ => by norm_num [fair])]
  norm_num [unbalanced, compile, Circuit.count, Circuit.scale, Circuit.restrict,
    resultDiagram, choose, compileGuard, truth, falsity, conj, disj, neg,
    bit, bddVar, bddNot, apply, mk, bdd_wmc, fair]

/-- Uniform terminal counting assigns `a` one third; fair binary choices assign
it one half. The difference persists even though both models have three leaves. -/
theorem unbalanced_uniform_counterexample :
    uniformHit {{bothHigh}, {ctuple [csym "pair", cnum 2, cnum 1]},
      {ctuple [csym "pair", cnum 1, cnum 2]}} bothHigh ≠ unbalanced.mass fair id := by
  rw [unbalanced_first_probability]
  norm_num [uniformHit, bothHigh]

#print axioms sharing_changes_probability
#print axioms scored_posterior
#print axioms native_let_mass
#print axioms native_fresh_mass
#print axioms native_let_control
#print axioms native_fresh_control

end Mettapedia.PLN.WorldModel.WeightedSourceControls
