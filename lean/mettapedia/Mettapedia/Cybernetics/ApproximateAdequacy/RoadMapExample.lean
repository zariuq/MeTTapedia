import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric
import Mettapedia.Cybernetics.ApproximateAdequacy.DefectLaws
import Mettapedia.Cybernetics.ApproximateAdequacy.Hosting
import Mettapedia.GSLT.Scope.RevisionWorkflow

/-!
# Worked example: the road map under revision

Lane A's road map (`Mettapedia.GSLT.Scope.RoadMap`): major roads `a–b–d`,
minor roads `a–c–d`, evidence counts per road, and the answer "is `d`
reachable from `a`".  Four of its worlds matter here: every road open
(`allOpen`), only the major roads open (`majorOnly`), and each after road
`b–d` receives a closed report (`detour`, `blocked`).  The answer is yes in the
first three and no in `blocked`.

**The model under test keeps the present answer**: its state is the answer,
and it predicts that no revision changes it.  Each notion, computed:

| notion | at `allOpen` | at `majorOnly` |
|---|---|---|
| (a) correspondence defect | `0` | `0` |
| (b) Girard–Pappas drift | `0` | no bound below `1` |
| (c) bisimulation metric, `c = r = 1/2` | `0` | `1/3` |
| (d) hosting the present answer | leaks the next answer | — |
| (e) update-square error | `0` | `1` |
| (f) goal-weighted defect | `0` | `0` |

* (a) and (f): the keep model is a functor on the world's revision processes
  (`keepCorrespondence_exact`), so every defect and every weighted average of
  defects is `0` (`keep_averageDefect`), at both worlds alike.
* (b): with road `b–d` closing, `allOpen` and the model state are
  approximately bisimilar at precision `0` (`allOpen_approxBisimilar`), while
  no approximate bisimulation below `1` relates `majorOnly` to the model
  state (`majorOnly_not_approxBisimilar`).
* (c): with `b–d` closing with probability `r = 1/2` per step, at discount
  `1/2`, the bisimulation metric is `0` at `allOpen` (`metric_allOpen`) and
  exactly `1/3` at `majorOnly` (`metric_majorOnly`), the solution of
  `d = c (r + (1 - r) d)`: the present answers agree, the futures do not, and
  the metric weighs the difference by its probability and delay.
* (d): the model's universe `{allOpen}` validates "d stays reachable after
  `b–d` closes", which the theory "d is reachable" does not entail, so it hosts
  that theory at no error below the sentence's weight (`keep_not_epsHosts`);
  the universe `{allOpen, majorOnly}` hosts it at error `0`
  (`both_zeroHosts`).
* (e): the square of the keep update against closing `b–d` errs by `1`
  (`keep_square`, `keep_not_square`); lane A's `answer_not_supports_close`
  shows no abstract update on answers does better.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy.RoadMapExample

open Finset _root_.CategoryTheory
open Mettapedia.GSLT.Scope
open Mettapedia.Cybernetics.MindWorldApproximation
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.Logic.TheoryModel

/-! ## Stages of the road map -/

/-- Four worlds of the road map. -/
inductive Stage
  | allOpen
  | majorOnly
  | detour
  | blocked
  deriving DecidableEq

instance : Fintype Stage where
  elems := {.allOpen, .majorOnly, .detour, .blocked}
  complete x := by cases x <;> simp

theorem sum_stage {M : Type*} [AddCommMonoid M] (f : Stage → M) :
    ∑ x, f x = f .allOpen + (f .majorOnly + (f .detour + f .blocked)) := by
  rw [show (Finset.univ : Finset Stage) = {.allOpen, .majorOnly, .detour, .blocked} from rfl]
  simp

/-- **Each stage is a world of lane A's road map.** -/
def Stage.world : Stage → RoadMap.World
  | .allOpen => RoadMap.allOpen
  | .majorOnly => RoadMap.majorOnly
  | .detour => RoadMap.close .bd RoadMap.allOpen
  | .blocked => RoadMap.close .bd RoadMap.majorOnly

/-- Closing `b–d` moves between stages. -/
def Stage.close : Stage → Stage
  | .allOpen => .detour
  | .majorOnly => .blocked
  | .detour => .detour
  | .blocked => .blocked

/-- The answer at a stage: lane A's answer at its world. -/
def Stage.answer (s : Stage) : Bool :=
  RoadMap.answer s.world

theorem answer_allOpen : Stage.allOpen.answer = true := by decide
theorem answer_majorOnly : Stage.majorOnly.answer = true := by decide
theorem answer_detour : Stage.detour.answer = true := by decide
theorem answer_blocked : Stage.blocked.answer = false := by decide

/-- **The stages track lane A's revision on answers**: closing `b–d` in the
world of a stage has the answer of the next stage. -/
theorem answer_close (s : Stage) :
    RoadMap.answer (RoadMap.close .bd s.world) = s.close.answer := by
  cases s <;> decide

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The answer as a number. -/
def answerValue (s : Stage) : 𝕜 :=
  if s.answer then 1 else 0

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem answerValue_eq : answerValue (𝕜 := 𝕜) .allOpen = 1 ∧ answerValue (𝕜 := 𝕜) .majorOnly = 1 ∧
    answerValue (𝕜 := 𝕜) .detour = 1 ∧ answerValue (𝕜 := 𝕜) .blocked = 0 := by
  simp [answerValue, answer_allOpen, answer_majorOnly, answer_detour, answer_blocked]

/-- The model's belief as a number. -/
def beliefValue (b : Bool) : 𝕜 :=
  if b then 1 else 0

/-! ## (c) The probabilistic world and the keep model -/

/-- Road `b–d` receives a closed report with probability `r` at each step. -/
def worldTrans (r : 𝕜) (_ : Unit) : Stage → Stage → 𝕜
  | .allOpen => fun x => if x = .detour then r else if x = .allOpen then 1 - r else 0
  | .majorOnly => fun x => if x = .blocked then r else if x = .majorOnly then 1 - r else 0
  | .detour => dirac .detour
  | .blocked => dirac .blocked

/-- **The world chain.** -/
def worldChain (r : 𝕜) (r_nonneg : 0 ≤ r) (r_le : r ≤ 1) :
    LabelledMarkovChain 𝕜 Unit Unit Stage where
  trans := worldTrans r
  isDistribution a s := by
    cases s <;>
      first
        | exact isDistribution_dirac _
        | exact ⟨fun x => by cases x <;> simp [worldTrans, r_nonneg, r_le],
            by rw [sum_stage]; simp [worldTrans]⟩
  observe _ := answerValue

/-- **The keep model**: its state is the answer, which never changes. -/
def keepChain : LabelledMarkovChain 𝕜 Unit Unit Bool where
  trans _ b := dirac b
  isDistribution _ b := isDistribution_dirac b
  observe _ := beliefValue

/-- The coupling bound at `c = r = 1/2`. -/
def keepBound : Stage → Bool → 𝕜
  | .allOpen, true => 0
  | .detour, true => 0
  | .majorOnly, true => 1 / 3
  | .blocked, false => 0
  | _, _ => 1

theorem keepBound_nonneg (s : Stage) (b : Bool) : 0 ≤ keepBound (𝕜 := 𝕜) s b := by
  cases s <;> cases b <;> norm_num [keepBound]

theorem keepBound_le_one (s : Stage) (b : Bool) : keepBound (𝕜 := 𝕜) s b ≤ 1 := by
  cases s <;> cases b <;> norm_num [keepBound]

/-- **The coupling bound** between the world and the keep model. -/
theorem keepBound_couplingBound :
    CouplingBound (worldChain (1 / 2 : 𝕜) (by norm_num) (by norm_num)) keepChain (1 / 2)
      keepBound where
  nonneg := keepBound_nonneg
  observe_le _ s b := by
    cases s <;> cases b <;>
      simp [worldChain, keepChain, keepBound, answerValue, beliefValue, answer_allOpen,
        answer_majorOnly, answer_detour, answer_blocked]
  step_le a s b := by
    let ω := Coupling.independent
      ((worldChain (1 / 2 : 𝕜) (by norm_num) (by norm_num)).isDistribution a s)
      ((keepChain (𝕜 := 𝕜)).isDistribution a b)
    have cost : ω.cost keepBound = expect (worldTrans (1 / 2 : 𝕜) a s) fun x => keepBound x b :=
      Coupling.cost_of_eq_dirac_right ω rfl _
    refine ⟨ω, ?_⟩
    rw [cost]
    cases s <;> cases b <;> simp [expect, sum_stage, worldTrans, keepBound, dirac] <;> norm_num

/-- The world chain over `ℝ` with closing probability `1/2`. -/
noncomputable def world : LabelledMarkovChain ℝ Unit Unit Stage :=
  worldChain (1 / 2) (by norm_num) (by norm_num)

/-- **At `allOpen` the metric is `0`**: the model state keeps the right
answer forever. -/
theorem metric_allOpen : bisimulationMetric world keepChain (1 / 2) .allOpen true = 0 :=
  le_antisymm (bisimulationMetric_le keepBound_couplingBound (by norm_num) _ _)
    (bisimulationMetric_nonneg (by norm_num) (by norm_num) _ _)

/-- **At `majorOnly` the metric is exactly `1/3`**, the solution of
`d = c (r · 1 + (1 - r) d)` at `c = r = 1/2`. -/
theorem metric_majorOnly : bisimulationMetric world keepChain (1 / 2) .majorOnly true = 1 / 3 := by
  apply le_antisymm
  · exact bisimulationMetric_le keepBound_couplingBound (by norm_num) _ _
  · have blocked : 1 ≤ bisimulationMetric world keepChain (1 / 2) .blocked true := by
      have lower := abs_eval_sub_le_bisimulationMetric (P := world) (Q := keepChain) (c := 1 / 2)
        (by norm_num) (by norm_num) (.observe ()) .blocked true
      have atWorld : (FunctionalExpression.observe () : FunctionalExpression ℝ Unit Unit).eval world
          (1 / 2) .blocked = 0 := by
        simp [FunctionalExpression.eval, world, worldChain, answerValue, answer_blocked]
      have atModel : (FunctionalExpression.observe () : FunctionalExpression ℝ Unit Unit).eval
          keepChain (1 / 2) true = 1 := by
        simp [FunctionalExpression.eval, keepChain, beliefValue]
      rw [atWorld, atModel] at lower
      norm_num at lower
      exact lower
    have fixed := mul_kantorovich_bisimulationMetric_le (P := world) (Q := keepChain)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () .majorOnly true
    have forced := kantorovich_of_eq_dirac_right (μ := world.trans () .majorOnly)
      (ν := keepChain.trans () true) (world.isDistribution () .majorOnly) (y₀ := true) rfl
      (bisimulationMetric world keepChain (1 / 2))
    rw [forced] at fixed
    change 1 / 2 * expect (worldTrans (1 / 2 : ℝ) () .majorOnly)
      (fun x => bisimulationMetric world keepChain (1 / 2) x true) ≤
        bisimulationMetric world keepChain (1 / 2) .majorOnly true at fixed
    simp [expect, sum_stage, worldTrans] at fixed
    linarith

/-! ## (b) Girard–Pappas drift under the deterministic revision -/

/-- **At `allOpen` the drift is `0`.** -/
theorem allOpen_approxBisimilar :
    ApproxBisimilar (fun a b : ℝ => |a - b|) (fun s s' => Stage.close s = s')
      (fun b b' => id b = b')
      answerValue beliefValue 0 Stage.allOpen true := by
  rw [approxBisimilar_update_iff fun a b => abs_sub_comm a b]
  intro n
  have along : ∀ n, Stage.close^[n] .allOpen = .allOpen ∨ Stage.close^[n] .allOpen = .detour := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with same | same <;> rw [same] <;> exact Or.inr rfl
  rcases along n with same | same <;>
    simp [same, Function.iterate_id, answerValue, beliefValue, answer_allOpen, answer_detour]

/-- **At `majorOnly` no approximate bisimulation below `1` exists.** -/
theorem majorOnly_not_approxBisimilar {ε : ℝ} (small : ε < 1) :
    ¬ ApproxBisimilar (fun a b : ℝ => |a - b|) (fun s s' => Stage.close s = s')
      (fun b b' => id b = b') answerValue beliefValue ε Stage.majorOnly true := by
  rw [approxBisimilar_update_iff fun a b => abs_sub_comm a b]
  intro close
  have atOne := close 1
  simp [Stage.close, answerValue, beliefValue, answer_blocked] at atOne
  linarith

/-! ## (e) The update square -/

/-- **The keep update errs by `1` against closing `b–d`.** -/
theorem keep_square :
    ApproxSquare (fun a b : ℝ => |a - b|) answerValue answerValue Stage.close id 1 := by
  intro s
  cases s <;> simp [Stage.close, answerValue, answer_allOpen, answer_majorOnly, answer_detour,
    answer_blocked]

theorem keep_not_square {ε : ℝ} (small : ε < 1) :
    ¬ ApproxSquare (fun a b : ℝ => |a - b|) answerValue answerValue Stage.close id ε := by
  intro square
  have atMajor := square .majorOnly
  simp [Stage.close, answerValue, answer_majorOnly, answer_blocked] at atMajor
  linarith

/-! ## (a) and (f): the keep model is a functor -/

/-- Revision processes: `n` closed reports on `b–d`. -/
instance : MulAction (Multiplicative ℕ) Stage where
  smul n s := Stage.close^[Multiplicative.toAdd n] s
  one_smul _ := rfl
  mul_smul m n s := by
    change Stage.close^[Multiplicative.toAdd (m * n)] s =
      Stage.close^[Multiplicative.toAdd m] (Stage.close^[Multiplicative.toAdd n] s)
    rw [toAdd_mul, Function.iterate_add_apply]

/-- **The keep model as a correspondence** over the answer view: every process
is modelled by the identity on answers. -/
noncomputable def keepCorrespondence :
    PathCorrespondence (ActionCategory (Multiplicative ℕ) Stage) (UpdateObject ℝ) :=
  updateCorrespondence answerValue (fun _ => fun y => y) (evaluationGeometry ℝ)

theorem keepCorrespondence_exact : keepCorrespondence.Exact :=
  updateCorrespondence_exact rfl fun _ _ => rfl

/-- **Every weighted average of its defects is `0`**, at `majorOnly` as at
`allOpen`. -/
theorem keep_averageDefect {ι : Type*} (w : FiniteWeighting ℝ ι)
    (pairs : ι → ComposablePair (ActionCategory (Multiplicative ℕ) Stage)) :
    averageDefect keepCorrespondence w pairs = 0 :=
  averageDefect_eq_zero_of_exact keepCorrespondence_exact w pairs

/-! ## (d) Hosting the present answer -/

/-- Sentences: the answer now, and after `b–d` closes. -/
inductive Sentence
  | now
  | next
  deriving DecidableEq

/-- Satisfaction at a stage. -/
def Sat (s : Stage) : Sentence → Prop
  | .now => s.answer = true
  | .next => s.close.answer = true

/-- Both sentences tested with weight `1`. -/
def testBoth : SentenceWeighting Sentence where
  support := {.now, .next}
  weight _ := 1
  weight_pos _ _ := one_pos

/-- **The keep model's universe leaks the next answer.** -/
theorem keep_not_epsHosts {ε : ℚ} (small : ε < 1) :
    ¬ EpsHosts Sat testBoth {.allOpen} {.now} ε := by
  intro hosts
  have validated : Sentence.next ∈ consequencesIn Sat {Stage.allOpen} {.now} := by
    intro s member
    rw [member.1]
    exact answer_detour
  have weight := weight_le_of_leak hosts (by simp [testBoth]) validated (m := Stage.majorOnly)
    (by
      intro φ member
      rw [Set.mem_singleton_iff] at member
      subst member
      exact answer_majorOnly)
    (by change ¬ Stage.blocked.answer = true; rw [answer_blocked]; decide)
  change (1 : ℚ) ≤ ε at weight
  linarith

/-- **With `majorOnly` in the universe, the present answer is hosted
exactly.** -/
theorem both_zeroHosts : EpsHosts Sat testBoth {.allOpen, .majorOnly} {.now} 0 := by
  rw [zeroHosts_iff_twins]
  intro s model
  have now : s.answer = true := model rfl
  cases s
  · exact ⟨.allOpen, ⟨by simp, fun _ member => by rw [member]; exact answer_allOpen⟩,
      fun φ _ => Iff.rfl⟩
  · exact ⟨.majorOnly, ⟨by simp, fun _ member => by rw [member]; exact answer_majorOnly⟩,
      fun φ _ => Iff.rfl⟩
  · refine ⟨.allOpen, ⟨by simp, fun _ member => by rw [member]; exact answer_allOpen⟩,
      fun φ _ => ?_⟩
    cases φ
    · exact ⟨fun _ => answer_allOpen, fun _ => answer_detour⟩
    · exact ⟨fun _ => answer_detour, fun _ => answer_detour⟩
  · exact absurd now (by rw [answer_blocked]; decide)

end Mettapedia.Cybernetics.ApproximateAdequacy.RoadMapExample
