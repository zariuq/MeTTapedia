import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Contention
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalHistoriesControls

/-!
# The race identity on the step: two independent races

Two races of the step, for every substitution action. `headsX` and `tailsX` both take the occurrence
`ux` (weights `1` and `3`); `headsY` and `tailsY` both take `uy` (weights `2` and `2`). Nothing of one
race touches the other, so they are two components that do not interfere.

* **The step's jump chain** (`Race.traceProb`) gives each of the two linearizations of the causal
  history "`tailsX` and `headsY`" likelihood `3/16` (`linearizations`): the global race total is `8`
  before the first firing and `4` after it.
* **Their sum is the product of the two races' own likelihoods** `3/4 · 1/2`, the same numbers as the
  rate systems `coinA` and `coinB` of `CausalHistoriesControls` (`step_history_product`).
* **Here Meredith's local normalization is exact** (`local_exact`): with sharing contention each race
  is its own contention set, and the local likelihood of either linearization is the history's
  `3/8`. On a non-interfering program, normalization inside contention sets is the race identity; on
  the inhibition program of `Contention.Controls` it gives mass `2`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories.StepControls

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (PredicateQuery)
open Race (Reflexive admitted total traceProb)
open Contention (SharesTake Queried admitted_eq_filter contentionTotal localProb)

universe uS

/-- The tokens. -/
inductive Tok where
  | u
  | v
  | out
  deriving DecidableEq

/-- The occurrence identities. -/
inductive Site where
  | ux
  | uy
  | x1
  | x2
  | y1
  | y2
  deriving DecidableEq

/-- `ux` carries `u`, `uy` carries `v`, the outcomes `out`. -/
def label : Site → Tok
  | .ux => .u
  | .uy => .v
  | _ => .out

variable {S : Type uS} (A : SubstitutionAction Tok S)

/-- A ground firing that takes one occurrence and makes one outcome. -/
def single (taken : Site) (token : Tok) (made : Site) : Firing Tok S Site :=
  ⟨⟨[token], [], [], [], [.out]⟩, [], ⟨[taken], [], [made]⟩⟩

def headsX : Firing Tok S Site := single .ux .u .x1
def tailsX : Firing Tok S Site := single .ux .u .x2
def headsY : Firing Tok S Site := single .uy .v .y1
def tailsY : Firing Tok S Site := single .uy .v .y2

def alphabet : List (Firing Tok S Site) := [headsX, tailsX, headsY, tailsY]

/-- The weights: `1` and `3` for the first race, `2` and `2` for the second. -/
def weight (f : Firing Tok S Site) : ℝ :=
  if f.selection.made = [.x1] then 1 else if f.selection.made = [.x2] then 3 else 2

def E0 : Configuration Tok Site := ⟨[], {.ux, .uy}⟩
def Ex : Configuration Tok Site := ⟨[(.u, .u)], {.uy, .x2}⟩
def Ey : Configuration Tok Site := ⟨[(.v, .v)], {.ux, .y1}⟩
def Exy : Configuration Tok Site := ⟨[(.u, .u), (.v, .v)], {.x2, .y1}⟩
def Eyx : Configuration Tok Site := ⟨[(.v, .v), (.u, .u)], {.y1, .x2}⟩

theorem config_ext {C D : Configuration Tok Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem single_queried (taken : Site) (token : Tok) (made : Site) (labelled : label taken = token)
    (outcome : label made = .out) :
    Queried label (single (S := S) taken token made) [] :=
  ⟨⟨by simp [single, labelled], rfl, rfl, rfl, by simp [single, outcome], rfl,
    List.nodup_singleton _, List.nodup_singleton _⟩, rfl⟩

theorem alphabet_queried : ∀ f ∈ alphabet (S := S), Queried label f ((fun _ => []) f) := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact single_queried _ _ _ rfl rfl

theorem reflexive_E0 : Reflexive E0.equations := by unfold Race.Reflexive; decide
theorem reflexive_Ex : Reflexive Ex.equations := by unfold Race.Reflexive; decide
theorem reflexive_Ey : Reflexive Ey.equations := by unfold Race.Reflexive; decide
theorem reflexive_Exy : Reflexive Exy.equations := by unfold Race.Reflexive; decide
theorem reflexive_Eyx : Reflexive Eyx.equations := by unfold Race.Reflexive; decide

theorem result_tailsX : (tailsX (S := S)).result label E0 = Ex := config_ext rfl (of_decide_eq_true rfl)
theorem result_headsY : (headsY (S := S)).result label E0 = Ey := config_ext rfl (of_decide_eq_true rfl)
theorem result_tailsX_headsY : (headsY (S := S)).result label Ex = Exy :=
  config_ext rfl (of_decide_eq_true rfl)
theorem result_headsY_tailsX : (tailsX (S := S)).result label Ey = Eyx :=
  config_ext rfl (of_decide_eq_true rfl)

theorem admitted_E0 : admitted A label (alphabet (S := S)) E0 = [headsX, tailsX, headsY, tailsY] := by
  rw [admitted_eq_filter (fun _ => []) alphabet_queried reflexive_E0]
  rfl

theorem admitted_Ex : admitted A label (alphabet (S := S)) Ex = [headsY, tailsY] := by
  rw [admitted_eq_filter (fun _ => []) alphabet_queried reflexive_Ex]
  rfl

theorem admitted_Ey : admitted A label (alphabet (S := S)) Ey = [headsX, tailsX] := by
  rw [admitted_eq_filter (fun _ => []) alphabet_queried reflexive_Ey]
  rfl

theorem admitted_Exy : admitted A label (alphabet (S := S)) Exy = [] := by
  rw [admitted_eq_filter (fun _ => []) alphabet_queried reflexive_Exy]
  rfl

theorem admitted_Eyx : admitted A label (alphabet (S := S)) Eyx = [] := by
  rw [admitted_eq_filter (fun _ => []) alphabet_queried reflexive_Eyx]
  rfl

theorem headsX_ne_tailsX : (headsX (S := S)) ≠ tailsX := by simp [headsX, tailsX, single]
theorem headsY_ne_tailsX : (headsY (S := S)) ≠ tailsX := by simp [headsY, tailsX, single]
theorem tailsY_ne_tailsX : (tailsY (S := S)) ≠ tailsX := by simp [tailsY, tailsX, single]
theorem tailsY_ne_headsY : (tailsY (S := S)) ≠ headsY := by simp [tailsY, headsY, single]
theorem headsX_ne_headsY : (headsX (S := S)) ≠ headsY := by simp [headsX, headsY, single]
theorem tailsX_ne_headsY : (tailsX (S := S)) ≠ headsY := by simp [tailsX, headsY, single]

theorem weights :
    weight (headsX (S := S)) = 1 ∧ weight (tailsX (S := S)) = 3 ∧ weight (headsY (S := S)) = 2 ∧
      weight (tailsY (S := S)) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [weight, headsX, tailsX, headsY, tailsY, single]

theorem total_E0 : Race.total A label alphabet weight E0 = 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := weights (S := S)
  simp [Race.total, admitted_E0, h1, h2, h3, h4]
  norm_num

theorem total_Ex : Race.total A label alphabet weight Ex = 4 := by
  obtain ⟨_, _, h3, h4⟩ := weights (S := S)
  simp [Race.total, admitted_Ex, h3, h4]
  norm_num

theorem total_Ey : Race.total A label alphabet weight Ey = 4 := by
  obtain ⟨h1, h2, _, _⟩ := weights (S := S)
  simp [Race.total, admitted_Ey, h1, h2]
  norm_num

/-- **Both linearizations of the causal history have likelihood `3/16`** under the step's jump
chain, and both end where nothing is admitted. -/
theorem linearizations :
    traceProb A label alphabet id weight [tailsX, headsY] E0 = 3 / 16 ∧
      traceProb A label alphabet id weight [headsY, tailsX] E0 = 3 / 16 ∧
      admitted A label (alphabet (S := S)) ((headsY (S := S)).result label ((tailsX (S := S)).result label E0)) = [] ∧
      admitted A label (alphabet (S := S)) ((tailsX (S := S)).result label ((headsY (S := S)).result label E0)) = [] := by
  obtain ⟨_, h2, h3, _⟩ := weights (S := S)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [traceProb, admitted_E0, admitted_Ex, result_tailsX, total_E0, total_Ex, headsX_ne_tailsX,
      headsY_ne_tailsX, tailsY_ne_tailsX, tailsY_ne_headsY, h2, h3]
    norm_num
  · simp [traceProb, admitted_E0, admitted_Ey, result_headsY, total_E0, total_Ey, headsX_ne_headsY,
      tailsX_ne_headsY, tailsY_ne_headsY, headsX_ne_tailsX, h2, h3]
    norm_num
  · rw [result_tailsX, result_tailsX_headsY]
    exact admitted_Exy A
  · rw [result_headsY, result_headsY_tailsX]
    exact admitted_Eyx A

/-- **The race identity on the step**: the sum over the two linearizations is the product of the
two races' own likelihoods, those of the rate systems `coinA` and `coinB`. -/
theorem step_history_product :
    traceProb A label alphabet id weight [tailsX, headsY] E0 +
        traceProb A label alphabet id weight [headsY, tailsX] E0 =
      pathProb Controls.coinA .start [(.tails, 3)] * pathProb Controls.coinB .start [(.heads, 2)] := by
  obtain ⟨-, -, -, a, b⟩ := Controls.history_product
  rw [(linearizations A).1, (linearizations A).2.1, a, b]
  norm_num

/-- **Meredith's local normalization is exact here**: each race is its own sharing contention set,
and either linearization gets the history's likelihood `3/8`. -/
theorem local_exact :
    localProb A label alphabet weight SharesTake E0 [tailsX, headsY] = 3 / 8 ∧
      localProb A label alphabet weight SharesTake E0 [headsY, tailsX] = 3 / 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := weights (S := S)
  have cx : contentionTotal A label alphabet weight SharesTake E0 tailsX = 4 := by
    simp [contentionTotal, admitted_E0, SharesTake, headsX, tailsX, headsY, tailsY, single, weight]
    norm_num
  have cy : contentionTotal A label alphabet weight SharesTake E0 headsY = 4 := by
    simp [contentionTotal, admitted_E0, SharesTake, headsX, tailsX, headsY, tailsY, single, weight]
    norm_num
  have cxy : contentionTotal A label alphabet weight SharesTake Ex headsY = 4 := by
    simp [contentionTotal, admitted_Ex, SharesTake, headsY, tailsY, single, weight]
    norm_num
  have cyx : contentionTotal A label alphabet weight SharesTake Ey tailsX = 4 := by
    simp [contentionTotal, admitted_Ey, SharesTake, headsX, tailsX, single, weight]
    norm_num
  constructor
  · simp only [localProb, cx, result_tailsX, cxy, h2, h3]
    norm_num
  · simp only [localProb, cy, result_headsY, cyx, h2, h3]
    norm_num

#print axioms admitted_E0
#print axioms linearizations
#print axioms step_history_product
#print axioms local_exact

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories.StepControls

end
