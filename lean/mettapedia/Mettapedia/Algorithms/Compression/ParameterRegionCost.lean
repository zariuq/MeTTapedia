import Mettapedia.Algorithms.Compression.ParameterRegion
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Output-sensitive work for occurrence products

The existing resumable parameter frontier retains ordered occurrences. Its
meter charges frame dispatch, both child-frontier list passes, and the prefix
cells copied by `children`. Payload decoding, allocation metadata, arithmetic
bit complexity and native runtime costs are separate.

An empty-domain preflight is needed for an output-sensitive bound: an empty
last factor must not require expansion of every preceding combination.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ParameterRegionCost

open ParameterRegion

variable {α : Type*}

def count (domains : List (List α)) : Nat := (domains.map List.length).prod

theorem product_length (domains : List (List α)) : (product domains).length = count domains := by
  induction domains with
  | nil => rfl
  | cons choices rest ih =>
      simp [product, List.length_flatMap, ih, count]

def NonemptyDomains (domains : List (List α)) : Prop := ∀ choices ∈ domains, choices ≠ []

theorem count_positive (domains : List (List α)) (inhabited : NonemptyDomains domains) :
    0 < count domains := by
  induction domains with
  | nil => exact Nat.zero_lt_one
  | cons choices rest ih =>
      have head := List.length_pos_iff.mpr (inhabited choices (by simp))
      have tail := ih (fun choice member => inhabited choice (by simp [member]))
      exact Nat.mul_pos head tail

theorem count_eq_zero_of_empty (domains : List (List α)) (empty : ¬NonemptyDomains domains) :
    count domains = 0 := by
  induction domains with
  | nil => exact False.elim (empty (by simp [NonemptyDomains]))
  | cons choices rest ih =>
      by_cases head : choices = []
      · simp [count, head]
      · have tail : ¬NonemptyDomains rest := by
          intro nonempty
          apply empty
          intro choice member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ head
          · exact nonempty choice later
        change choices.length * count rest = 0
        rw [ih tail, Nat.mul_zero]

theorem size_bound (domains : List (List α)) (inhabited : NonemptyDomains domains) :
    size domains ≤ (domains.length + 1) * count domains := by
  induction domains with
  | nil => exact Nat.le_refl _
  | cons choices rest ih =>
      have tail : NonemptyDomains rest := fun choice member => inhabited choice (by simp [member])
      have scaled := Nat.mul_le_mul_left choices.length (ih tail)
      have positive := count_positive (choices :: rest) inhabited
      change 0 < choices.length * count rest at positive
      change 1 + choices.length * size rest ≤ (rest.length + 1 + 1) * (choices.length * count rest)
      nlinarith

theorem input_visits_bound (domains : List (List α)) (inhabited : NonemptyDomains domains) :
    (domains.map List.length).sum ≤ domains.length * count domains := by
  induction domains with
  | nil => exact Nat.le_refl _
  | cons choices rest ih =>
      have headPositive := List.length_pos_iff.mpr (inhabited choices (by simp))
      have tail : NonemptyDomains rest := fun choice member => inhabited choice (by simp [member])
      have tailPositive := count_positive rest tail
      have headBound : choices.length ≤ choices.length * count rest :=
        Nat.le_mul_of_pos_right _ tailPositive
      have tailBound : (rest.map List.length).sum ≤ choices.length * (rest.length * count rest) :=
        (ih tail).trans (Nat.le_mul_of_pos_left _ headPositive)
      change choices.length + (rest.map List.length).sum ≤ (rest.length + 1) * (choices.length * count rest)
      calc
        _ ≤ choices.length * count rest + choices.length * (rest.length * count rest) :=
          Nat.add_le_add headBound tailBound
        _ = _ := by ring

def prefixCells : Nat → List (List α) → Nat
  | _, [] => 0
  | chosen, choices :: rest => choices.length * (chosen + 1 + prefixCells (chosen + 1) rest)

def treeCharge : Nat → List (List α) → Nat
  | _, [] => 1
  | chosen, choices :: rest =>
      1 + 2 * choices.length + choices.length * (chosen + 1) + choices.length * treeCharge (chosen + 1) rest

theorem treeCharge_identity (chosen : Nat) (domains : List (List α)) :
    treeCharge chosen domains + 2 = 3 * size domains + prefixCells chosen domains := by
  induction domains generalizing chosen with
  | nil => rfl
  | cons choices rest ih =>
      have scaled := congrArg (choices.length * ·) (ih (chosen + 1))
      simp only [treeCharge, size, prefixCells]
      nlinarith

theorem prefixCells_bound (chosen : Nat) (domains : List (List α)) :
    prefixCells chosen domains ≤ (chosen + domains.length) * (size domains - 1) := by
  induction domains generalizing chosen with
  | nil => simp [prefixCells, size]
  | cons choices rest ih =>
      have cancel := Nat.sub_add_cancel (size_positive rest)
      simp only [prefixCells, size, List.length_cons]
      have reduced : 1 + choices.length * size rest - 1 = choices.length * size rest := by omega
      rw [reduced]
      calc
        _ ≤ choices.length * (chosen + 1 + (chosen + 1 + rest.length) * (size rest - 1)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left (ih (chosen + 1)) _)
        _ ≤ choices.length * ((chosen + 1 + rest.length) + (chosen + 1 + rest.length) * (size rest - 1)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (by omega) _)
        _ = (chosen + 1 + rest.length) * choices.length * ((size rest - 1) + 1) := by ring
        _ = _ := by rw [cancel]; ring

theorem treeCharge_bound (chosen : Nat) (domains : List (List α)) (inhabited : NonemptyDomains domains) :
    treeCharge chosen domains ≤ (3 + chosen + domains.length) * (domains.length + 1) * count domains := by
  have identity := treeCharge_identity chosen domains
  have prefixes := prefixCells_bound chosen domains
  have small : prefixCells chosen domains ≤ (chosen + domains.length) * size domains :=
    prefixes.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have sized := Nat.mul_le_mul_left (3 + chosen + domains.length) (size_bound domains inhabited)
  nlinarith

def potential (frontier : Frontier α) : Nat :=
  (frontier.map fun frame => treeCharge frame.1.length frame.2).sum

theorem potential_append (first second : Frontier α) : potential (first ++ second) = potential first + potential second := by
  simp [potential, List.sum_append]

theorem potential_children (chosen choices : List α) (rest : List (List α)) :
    potential (children chosen choices rest) = choices.length * treeCharge (chosen.length + 1) rest := by
  simp [potential, children, List.map_map, Function.comp_def]

def stepCharge : Frontier α → Nat
  | [] => 0
  | (_, []) :: _ => 1
  | (chosen, choices :: _) :: _ => 1 + 2 * choices.length + choices.length * (chosen.length + 1)

theorem pending_charge {before after : Frontier α} (stepped : tick before = .pending after) :
    stepCharge before + potential after = potential before := by
  cases before with
  | nil => cases stepped
  | cons frame tail =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => cases stepped
      | cons choices rest =>
          cases stepped
          rw [potential_append, potential_children]
          simp [stepCharge, potential, treeCharge, Nat.add_assoc]

theorem yield_charge {before after : Frontier α} {answer : List α} (stepped : tick before = .yield answer after) :
    stepCharge before + potential after = potential before := by
  cases before with
  | nil => cases stepped
  | cons frame tail =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => cases stepped; rfl
      | cons => cases stepped

def metered : Nat → Frontier α → Nat × (List (List α) × Frontier α)
  | 0, frontier => (0, [], frontier)
  | fuel + 1, frontier =>
      match tick frontier with
      | .done => (0, [], [])
      | .pending next =>
          let later := metered fuel next
          (stepCharge frontier + later.1, later.2)
      | .yield answer next =>
          let later := metered fuel next
          (stepCharge frontier + later.1, answer :: later.2.1, later.2.2)

theorem metered_erases (fuel : Nat) (frontier : Frontier α) :
    (metered fuel frontier).2 = run fuel frontier := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : tick frontier with
      | done => simp [metered, run, stepped]
      | pending next => simpa [metered, run, stepped] using ih next
      | yield answer next =>
          simpa [metered, run, stepped] using congrArg
            (fun pair : List (List α) × Frontier α => (answer :: pair.1, pair.2)) (ih next)

theorem metered_conserves (fuel : Nat) (frontier : Frontier α) :
    (metered fuel frontier).1 + potential (metered fuel frontier).2.2 = potential frontier := by
  induction fuel generalizing frontier with
  | zero => simp [metered]
  | succ fuel ih =>
      cases stepped : tick frontier with
      | done =>
          have empty := (done_iff frontier).mp stepped
          subst frontier
          rfl
      | pending next =>
          have charged := pending_charge stepped
          simpa only [metered, stepped, Nat.add_assoc, ih next] using charged
      | yield answer next =>
          have charged := yield_charge stepped
          simpa only [metered, stepped, Nat.add_assoc, ih next] using charged

theorem metered_prefix_bound (fuel : Nat) (frontier : Frontier α) :
    (metered fuel frontier).1 ≤ potential frontier := by
  have conserved := metered_conserves fuel frontier
  omega

theorem metered_complete_charge (fuel : Nat) (frontier : Frontier α) (enough : work frontier ≤ fuel) :
    (metered fuel frontier).1 = potential frontier := by
  have conserved := metered_conserves fuel frontier
  rw [metered_erases, run_complete fuel frontier enough] at conserved
  simpa [potential] using conserved

def screen : List (List α) → Bool × Nat
  | [] => (true, 0)
  | [] :: _ => (false, 1)
  | (_ :: _) :: rest =>
      let later := screen rest
      (later.1, later.2 + 1)

theorem screen_exact (domains : List (List α)) : (screen domains).1 = true ↔ NonemptyDomains domains := by
  induction domains with
  | nil => simp [screen, NonemptyDomains]
  | cons choices rest ih =>
      cases choices with
      | nil => simp [screen, NonemptyDomains]
      | cons head tail => simpa [screen, NonemptyDomains] using ih

theorem screen_cost (domains : List (List α)) : (screen domains).2 ≤ domains.length := by
  induction domains with
  | nil => rfl
  | cons choices rest ih =>
      cases choices with
      | nil => simp [screen]
      | cons head tail => simpa only [screen, List.length_cons] using Nat.add_le_add_right ih 1

def prepare (domains : List (List α)) : Frontier α :=
  if (screen domains).1 then [([], domains)] else []

theorem prepare_exact (domains : List (List α)) : values (prepare domains) = product domains := by
  by_cases inhabited : NonemptyDomains domains
  · simp [prepare, (screen_exact domains).mpr inhabited, values]
  · have refused : (screen domains).1 = false := Bool.eq_false_iff.mpr
      (fun yes => inhabited ((screen_exact domains).mp yes))
    have empty : product domains = [] := List.length_eq_zero_iff.mp
      ((product_length domains).trans (count_eq_zero_of_empty domains inhabited))
    simp [prepare, refused, values, empty]

theorem prepared_prefix_cost (domains : List (List α)) (fuel : Nat) :
    (screen domains).2 + (metered fuel (prepare domains)).1 ≤
      domains.length + (3 + domains.length) * (domains.length + 1) * count domains := by
  have preparation := screen_cost domains
  have running := metered_prefix_bound fuel (prepare domains)
  by_cases inhabited : NonemptyDomains domains
  · have bounded := treeCharge_bound 0 domains inhabited
    have ready : prepare domains = [([], domains)] := by simp [prepare, (screen_exact domains).mpr inhabited]
    rw [ready] at running ⊢
    simp only [potential,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, List.length_nil] at running
    simp only [Nat.add_zero] at bounded
    omega
  · have refused : (screen domains).1 = false := Bool.eq_false_iff.mpr
      (fun yes => inhabited ((screen_exact domains).mp yes))
    have ready : prepare domains = [] := by simp [prepare, refused]
    rw [ready] at running ⊢
    simp only [potential, List.map_nil, List.sum_nil] at running
    omega

theorem prepared_complete_order (domains : List (List α)) :
    (metered (work (prepare domains)) (prepare domains)).2.1 = product domains := by
  rw [metered_erases, complete_order, prepare_exact]

theorem metered_resume (first second : Nat) (frontier : Frontier α) :
    (metered (first + second) frontier).2 =
      let before := (metered first frontier).2
      let after := (metered second before.2).2
      (before.1 ++ after.1, after.2) := by
  simp only [metered_erases]
  exact run_resume first second frontier

theorem metered_resume_charge (first second : Nat) (frontier : Frontier α) :
    (metered (first + second) frontier).1 =
      (metered first frontier).1 + (metered second (metered first frontier).2.2).1 := by
  have one := metered_conserves first frontier
  have two := metered_conserves second (metered first frontier).2.2
  have joined := metered_conserves (first + second) frontier
  have residual := congrArg (fun result : List (List α) × Frontier α => result.2)
    (metered_resume first second frontier)
  dsimp only at residual
  rw [residual] at joined
  omega

namespace Controls

theorem duplicates_are_four_occurrences :
    (metered 20 (prepare ([[7, 7], [8, 8]] : List (List Nat)))).2.1 =
      [[7, 8], [7, 8], [7, 8], [7, 8]] := by decide +kernel

theorem empty_last_factor_skips_exponential_frontier :
    prepare ([[1, 2], [3, 4], []] : List (List Nat)) = [] ∧
      (screen ([[1, 2], [3, 4], []] : List (List Nat))).2 = 3 := by decide +kernel

theorem unscreened_empty_output_can_still_cost :
    product ([[1, 2], [3, 4], []] : List (List Nat)) = [] ∧
      treeCharge 0 ([[1, 2], [3, 4], []] : List (List Nat)) = 29 := by decide +kernel

theorem zero_budget_retains_the_work :
    (metered 0 (prepare ([[7]] : List (List Nat)))).2 = ([], [([], [[7]])]) := by decide +kernel

theorem empty_conjunction_still_yields_once :
    (metered 1 (prepare ([] : List (List Nat)))).2 = ([[]], []) := by decide +kernel

end Controls

end Mettapedia.Algorithms.Compression.ParameterRegionCost
