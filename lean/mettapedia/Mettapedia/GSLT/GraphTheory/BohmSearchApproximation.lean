import Mettapedia.GSLT.GraphTheory.BohmObservations
import Mettapedia.GSLT.GraphTheory.HeadSearchAdequacy

/-!
# Bounded search as information about the mathematical Böhm tree

Depth and head-search fuel are separate parameters. Unknown subtrees carry
bottom information without asserting unsolvability. Every returned node is
sound, increasing fuel retains information, and at each fixed depth a finite
budget eventually recovers the uncapped mathematical observation exactly.
Information is a partial order on finite trees, so an exact observation stays
exact under every larger budget.
-/

namespace Mettapedia.GSLT.GraphTheory

/-- Partial information retains node labels and every ordered argument slot. -/
inductive BohmTree.InformationLE : BohmTree → BohmTree → Prop where
  | bottom (tree : BohmTree) : InformationLE .bot tree
  | node {numLams head : Nat} {children results : List BohmTree} :
      List.Forall₂ InformationLE children results →
      InformationLE (.node numLams head children) (.node numLams head results)

namespace BohmTree.InformationLE

/-! The information order is a partial order on finite trees. -/

theorem refl : ∀ tree : BohmTree, InformationLE tree tree
  | .bot => .bottom _
  | .node _ _ children => .node (forall₂_refl children)
where
  forall₂_refl : ∀ children : List BohmTree, List.Forall₂ InformationLE children children
    | [] => .nil
    | child :: rest => .cons (refl child) (forall₂_refl rest)

theorem trans : ∀ {first second third : BohmTree},
    InformationLE first second → InformationLE second third → InformationLE first third
  | .bot, _, _, _, _ => .bottom _
  | .node _ _ _, _, _, .node below, .node above => .node (forall₂_trans below above)
where
  forall₂_trans : ∀ {first second third : List BohmTree},
      List.Forall₂ InformationLE first second → List.Forall₂ InformationLE second third →
        List.Forall₂ InformationLE first third
    | [], _, _, .nil, .nil => .nil
    | _ :: _, _, _, .cons below belowRest, .cons above aboveRest =>
        .cons (trans below above) (forall₂_trans belowRest aboveRest)

theorem antisymm : ∀ {first second : BohmTree},
    InformationLE first second → InformationLE second first → first = second
  | .bot, .bot, _, _ => rfl
  | .node numLams head _, _, .node below, .node above =>
      congrArg (BohmTree.node numLams head) (forall₂_antisymm below above)
where
  forall₂_antisymm : ∀ {first second : List BohmTree},
      List.Forall₂ InformationLE first second → List.Forall₂ InformationLE second first →
        first = second
    | [], _, .nil, .nil => rfl
    | _ :: _, _, .cons below belowRest, .cons above aboveRest =>
        congrArg₂ List.cons (antisymm below above) (forall₂_antisymm belowRest aboveRest)

/-- Only bottom lies below bottom. -/
theorem eq_bot_of_le_bot {tree : BohmTree} (below : InformationLE tree .bot) : tree = .bot :=
  antisymm below (.bottom tree)

end BohmTree.InformationLE

namespace BohmSearch

/-- `budget d` is the head-search fuel at a node with remaining depth `d`. -/
def observe (budget : Nat → Nat) : Nat → LambdaTerm → BohmTree
  | 0, _ => .bot
  | depth + 1, term =>
      match toHNF (budget (depth + 1)) term with
      | none => .bot
      | some hnf =>
          match extractHNF hnf with
          | none => .bot
          | some (numLams, head, arguments) =>
              .node numLams head (arguments.map (observe budget depth))

/-- The older depth-dependent evaluator is an instance of the common observer. -/
theorem original_eq (depth : Nat) (term : LambdaTerm) :
    bohmTree depth term = observe (fun d => d * (d + 1) + 1) depth term := by
  induction depth generalizing term with
  | zero => rfl
  | succ depth ih =>
      simp only [bohmTree, observe]
      cases search : toHNF ((depth + 1) * (depth + 1 + 1) + 1) term with
      | none => simp only
      | some hnf =>
          simp only
          cases headForm : extractHNF hnf with
          | none => simp only
          | some value =>
              rcases value with ⟨numLams, head, arguments⟩
              simp only
              congr 1
              exact List.map_congr_left (fun argument _ => ih argument)

/-- Returned nodes are genuine information, even if searches below them exhaust. -/
theorem sound (budget : Nat → Nat) (depth : Nat) (term : LambdaTerm) :
    BohmTree.InformationLE (observe budget depth term) (BohmObservation.tree depth term) := by
  induction depth generalizing term with
  | zero =>
      exact .bottom _
  | succ depth ih =>
      cases search : toHNF (budget (depth + 1)) term with
      | none => simp only [observe, search]; exact .bottom _
      | some hnf =>
          cases headForm : extractHNF hnf with
          | none => simp only [observe, search, headForm]; exact .bottom _
          | some value =>
              rcases value with ⟨numLams, head, arguments⟩
              rw [BohmObservation.tree_node_of_reaches (toHNF_sound search).1 headForm]
              simp only [observe, search, headForm]
              apply BohmTree.InformationLE.node
              exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
                (List.forall₂_same.mpr (fun argument _ => ih argument)))

/-- More fuel can expose information, but cannot change a previously found node. -/
theorem monotone {first second : Nat → Nat} (budgets : ∀ d, first d ≤ second d)
    (depth : Nat) (term : LambdaTerm) :
    BohmTree.InformationLE (observe first depth term) (observe second depth term) := by
  induction depth generalizing term with
  | zero => exact .bottom _
  | succ depth ih =>
      cases search : toHNF (first (depth + 1)) term with
      | none => simp only [observe, search]; exact .bottom _
      | some hnf =>
          have later := toHNF_result_stable search (budgets (depth + 1))
          cases headForm : extractHNF hnf with
          | none => simp only [observe, search, later, headForm]; exact .bottom _
          | some value =>
              rcases value with ⟨numLams, head, arguments⟩
              simp only [observe, search, later, headForm]
              apply BohmTree.InformationLE.node
              exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
                (List.forall₂_same.mpr (fun argument _ => ih argument)))

/-- An observation is exact as soon as it contains the information of the
exact tree. -/
theorem eq_tree_iff (budget : Nat → Nat) (depth : Nat) (term : LambdaTerm) :
    observe budget depth term = BohmObservation.tree depth term ↔
      BohmTree.InformationLE (BohmObservation.tree depth term) (observe budget depth term) :=
  ⟨fun exact => exact ▸ BohmTree.InformationLE.refl _,
    fun contains => BohmTree.InformationLE.antisymm (sound budget depth term) contains⟩

/-- An exact observation stays exact under every larger budget. -/
theorem exact_of_le {first second : Nat → Nat} (budgets : ∀ d, first d ≤ second d)
    {depth : Nat} {term : LambdaTerm}
    (exact : observe first depth term = BohmObservation.tree depth term) :
    observe second depth term = BohmObservation.tree depth term :=
  BohmTree.InformationLE.antisymm (sound second depth term)
    (exact ▸ monotone budgets depth term)

theorem original_sound (depth : Nat) (term : LambdaTerm) :
    BohmTree.InformationLE (bohmTree depth term) (BohmObservation.tree depth term) := by
  rw [original_eq]
  exact sound _ _ _

private theorem finite_threshold {P : Nat → LambdaTerm → Prop}
    (eventual : ∀ term, ∃ threshold, ∀ fuel, threshold ≤ fuel → P fuel term)
    (arguments : List LambdaTerm) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel → ∀ argument ∈ arguments, P fuel argument := by
  induction arguments with
  | nil => exact ⟨0, fun _ _ _ member => False.elim (List.not_mem_nil member)⟩
  | cons argument arguments ih =>
      obtain ⟨headThreshold, headEventually⟩ := eventual argument
      obtain ⟨tailThreshold, tailEventually⟩ := ih
      refine ⟨max headThreshold tailThreshold, ?_⟩
      intro fuel large child member
      rcases List.mem_cons.mp member with rfl | member
      · exact headEventually fuel ((Nat.le_max_left _ _).trans large)
      · exact tailEventually fuel ((Nat.le_max_right _ _).trans large) child member

/-- Every fixed finite-depth mathematical observation is eventually recovered
exactly. This does not provide a computable bound or decide unsolvability. -/
theorem eventual_exact (depth : Nat) (term : LambdaTerm) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      observe (fun _ => fuel) depth term = BohmObservation.tree depth term := by
  classical
  induction depth generalizing term with
  | zero =>
      refine ⟨0, fun _ _ => ?_⟩
      exact ((BohmObservation.tree_eq_iff 0 term .bot).mpr (.zero term)).symm
  | succ depth ih =>
      by_cases solvable : term.Solvable
      · obtain ⟨headFuel, hnf, success⟩ := (solvable_iff_search_exists term).mp solvable
        have headSome := (extractHNF_isSome_eq_isHNF hnf).trans (toHNF_sound success).2
        cases headForm : extractHNF hnf with
        | none => simp only [headForm, Option.isSome_none, Bool.false_eq_true] at headSome
        | some value =>
            rcases value with ⟨numLams, head, arguments⟩
            obtain ⟨childFuel, childrenEventually⟩ := finite_threshold ih arguments
            refine ⟨max headFuel childFuel, ?_⟩
            intro fuel large
            have search := toHNF_result_stable success ((Nat.le_max_left _ _).trans large)
            rw [BohmObservation.tree_node_of_reaches (toHNF_sound success).1 headForm]
            simp only [observe, search, headForm]
            congr 1
            exact List.map_congr_left
              (fun child member => childrenEventually fuel
                ((Nat.le_max_right _ _).trans large) child member)
      · refine ⟨0, fun fuel _ => ?_⟩
        rw [(BohmObservation.tree_bot_iff depth term).mpr solvable]
        simp only [observe, unsolvable_toHNF_none solvable fuel]

/-- Equality of semantic trees permits differing finite-budget results; the
executions must agree after sufficiently large budgets at every fixed depth. -/
theorem family_eq_iff_eventual_agreement (first second : LambdaTerm) :
    BohmObservation.family first = BohmObservation.family second ↔
      ∀ depth, ∃ threshold, ∀ fuel, threshold ≤ fuel →
        observe (fun _ => fuel) depth first = observe (fun _ => fuel) depth second := by
  constructor
  · intro same depth
    obtain ⟨firstThreshold, firstExact⟩ := eventual_exact depth first
    obtain ⟨secondThreshold, secondExact⟩ := eventual_exact depth second
    refine ⟨max firstThreshold secondThreshold, ?_⟩
    intro fuel large
    rw [firstExact fuel ((Nat.le_max_left _ _).trans large),
      secondExact fuel ((Nat.le_max_right _ _).trans large)]
    exact (BohmObservation.family_eq_iff first second).mp same depth
  · intro eventual
    apply (BohmObservation.family_eq_iff first second).mpr
    intro depth
    obtain ⟨threshold, agrees⟩ := eventual depth
    obtain ⟨firstThreshold, firstExact⟩ := eventual_exact depth first
    obtain ⟨secondThreshold, secondExact⟩ := eventual_exact depth second
    let fuel := max threshold (max firstThreshold secondThreshold)
    have firstLarge : firstThreshold ≤ fuel :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have secondLarge : secondThreshold ≤ fuel :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact (firstExact fuel firstLarge).symm.trans
      ((agrees fuel (Nat.le_max_left _ _)).trans (secondExact fuel secondLarge))

end BohmSearch

end Mettapedia.GSLT.GraphTheory
