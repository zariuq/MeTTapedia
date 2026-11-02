import Mettapedia.ProbabilityTheory.BayesianNetworks.VEBridge

/-!
# Separator factorization as valuation elimination

Private coordinates can be eliminated independently only when the other factors
respect their declared scopes. The list law below iterates the existing
single-variable distributive law. Its numerical readout is the separator sum,
with the separator weight included exactly once.

This is an algebraic factorization certificate. It does not infer stochastic
independence from distinct variable names or replace graphical d-separation.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.SeparatorFactorization

open scoped BigOperators NNReal ENNReal

section Elimination

variable {V K : Type*} [DecidableEq V] {β : V → Type*}
variable [∀ v, Fintype (β v)] [CommSemiring K]

/-- The existing distributive law, iterated without re-proving its arithmetic. -/
theorem sumOutAll_combine (first second : Valuation V β K) (order : List V)
    (respects : RespectsScope second) (outside : ∀ v ∈ order, v ∉ second.scope) :
    sumOutAll (combine first second) order = combine (sumOutAll first order) second := by
  induction order generalizing first with
  | nil => rfl
  | cons v rest ih =>
    simp only [sumOutAll, List.foldl_cons]
    rw [sumOut_combine_of_not_mem v respects (outside v (by simp))]
    exact ih _ (fun v hv => outside v (by simp [hv]))

theorem sumOutAll_respects (factor : Valuation V β K) (order : List V)
    (respects : RespectsScope factor) : RespectsScope (sumOutAll factor order) := by
  induction order generalizing factor with
  | nil => exact respects
  | cons v rest ih => exact ih _ (respectsScope_sumOut respects v)

/-- Two private blocks leave a product of messages on their shared separator. -/
theorem separated_elimination (first second : Valuation V β K) (left right : List V)
    (firstRespects : RespectsScope first) (secondRespects : RespectsScope second)
    (leftPrivate : ∀ v ∈ left, v ∉ second.scope)
    (rightPrivate : ∀ v ∈ right, v ∉ (sumOutAll first left).scope) :
    sumOutAll (combine first second) (left ++ right) =
      combine (sumOutAll first left) (sumOutAll second right) := by
  have append : sumOutAll (combine first second) (left ++ right) =
      sumOutAll (sumOutAll (combine first second) left) right := by
    simp only [sumOutAll, List.foldl_append]
  rw [append]
  rw [sumOutAll_combine first second left secondRespects leftPrivate, combine_comm]
  rw [sumOutAll_combine second (sumOutAll first left) right
    (sumOutAll_respects first left firstRespects) rightPrivate, combine_comm]

end Elimination

/-! ## Three variable blocks as an existing factor graph -/

inductive Block where
  | left | separator | right
  deriving DecidableEq

instance : Fintype Block where
  elems := {.left, .separator, .right}
  complete b := by cases b <;> simp

universe u

abbrev blockSpace (X S Y : Type u) : Block → Type u
  | .left => X
  | .separator => S
  | .right => Y

def configuration {X S Y : Type u} (x : X) (s : S) (y : Y) : ∀ b, blockSpace X S Y b
  | .left => x
  | .separator => s
  | .right => y

def configEquiv (X S Y : Type u) : (X × S × Y) ≃ (∀ b, blockSpace X S Y b) where
  toFun p := configuration p.1 p.2.1 p.2.2
  invFun x := (x .left, x .separator, x .right)
  left_inv _ := rfl
  right_inv x := by funext b; cases b <;> rfl

variable {X S Y : Type u} {K : Type*}

@[reducible] instance blockSpaceFintype [Fintype X] [Fintype S] [Fintype Y] (b : Block) :
    Fintype (blockSpace X S Y b) := by cases b <;> dsimp [blockSpace] <;> infer_instance

@[reducible] instance blockSpaceDecidableEq [DecidableEq X] [DecidableEq S] [DecidableEq Y] (b : Block) :
    DecidableEq (blockSpace X S Y b) := by cases b <;> infer_instance

noncomputable abbrev graph (left : X → S → K) (separator : S → K) (right : S → Y → K) :
    FactorGraph Block K where
  stateSpace := blockSpace X S Y
  factors := Block
  scope
    | .left => {.left, .separator}
    | .separator => {.separator}
    | .right => {.separator, .right}
  potential
    | .left, x => left (x .left (by simp)) (x .separator (by simp))
    | .separator, x => separator (x .separator (by simp))
    | .right, x => right (x .separator (by simp)) (x .right (by simp))

@[reducible] instance factorsFintype (left : X → S → K) (separator : S → K) (right : S → Y → K) :
    Fintype (graph left separator right).factors := inferInstanceAs (Fintype Block)

@[reducible] instance statesFintype [Fintype X] [Fintype S] [Fintype Y]
    (left : X → S → K) (separator : S → K) (right : S → Y → K) (b : Block) :
    Fintype ((graph left separator right).stateSpace b) :=
  inferInstanceAs (Fintype (blockSpace X S Y b))

private noncomputable def leftValuation (left : X → S → K) (separator : S → K) [Mul K] :
    Valuation Block (blockSpace X S Y) K :=
  ⟨{.left, .separator}, fun x => left (x .left) (x .separator) * separator (x .separator)⟩

private noncomputable def rightValuation (right : S → Y → K) :
    Valuation Block (blockSpace X S Y) K :=
  ⟨{.separator, .right}, fun x => right (x .separator) (x .right)⟩

private theorem left_respects (left : X → S → K) (separator : S → K) [Mul K] :
    RespectsScope (leftValuation (Y := Y) left separator) := by
  intro x y agree
  change left (x .left) (x .separator) * separator (x .separator) = _
  rw [agree .left (by simp [leftValuation]), agree .separator (by simp [leftValuation])]
  rfl

private theorem right_respects (right : S → Y → K) :
    RespectsScope (rightValuation (X := X) right) := by
  intro x y agree
  change right (x .separator) (x .right) = _
  rw [agree .separator (by simp [rightValuation]), agree .right (by simp [rightValuation])]
  rfl

/-- The numeric separator identity is read from certified scope elimination. -/
theorem fixed_separator [Fintype X] [Fintype S] [Fintype Y] [CommSemiring K]
    (left : X → S → K) (separator : S → K) (right : S → Y → K) (s : S) :
    (∑ y, ∑ x, left x s * separator s * right s y) =
      (∑ x, left x s) * separator s * ∑ y, right s y := by
  classical
  cases isEmpty_or_nonempty X with
  | inl empty => simp
  | inr inhabited =>
    cases isEmpty_or_nonempty Y with
    | inl empty => simp
    | inr inhabitedY =>
      let first := leftValuation (Y := Y) left separator
      let second := rightValuation (X := X) right
      have certified := separated_elimination first second [.left] [.right]
        (left_respects left separator) (right_respects right)
        (by intro b hb; simp only [List.mem_singleton] at hb; subst b; simp [second, rightValuation])
        (by intro b hb; simp only [List.mem_singleton] at hb; subst b
            simp [sumOutAll, sumOut_scope, first, leftValuation])
      have atConfiguration := congrArg (fun factor => factor.val
        (configuration (Classical.arbitrary X) s (Classical.arbitrary Y))) certified
      have nested : (∑ y, ∑ x, left x s * separator s * right s y) =
          (∑ x, left x s * separator s) * ∑ y, right s y := by
        simpa [first, second, leftValuation, rightValuation, sumOutAll, sumOut, combine,
          update, configuration, blockSpaceFintype] using atConfiguration
      simpa only [← Finset.sum_mul] using nested

def graphConfiguration (left : X → S → K) (separator : S → K) (right : S → Y → K)
    (x : X) (s : S) (y : Y) : (graph left separator right).FullConfig := configuration x s y

def graphConfigEquiv (left : X → S → K) (separator : S → K) (right : S → Y → K) :
    (X × S × Y) ≃ (graph left separator right).FullConfig := configEquiv X S Y

theorem graph_joint [CommSemiring K]
    (left : X → S → K) (separator : S → K) (right : S → Y → K)
    (x : X) (s : S) (y : Y) :
    (graph left separator right).unnormalizedJoint (graphConfiguration left separator right x s y) =
      left x s * separator s * right s y := by
  have enumeration : (Finset.univ : Finset Block) = {.left, .separator, .right} := by
    ext b
    cases b <;> simp
  calc
    _ = ∏ b : Block, (match b with
      | .left => left x s
      | .separator => separator s
      | .right => right s y) := by
        apply Finset.prod_congr rfl
        intro b _
        cases b <;> rfl
    _ = _ := by rw [enumeration]; simp [mul_assoc]

/-- The partition function of the existing factor-graph carrier is the separator readout. -/
theorem graph_partitionFunction [Fintype X] [Fintype S] [Fintype Y] [CommSemiring K]
    (left : X → S → K) (separator : S → K) (right : S → Y → K) :
    (graph left separator right).partitionFunction =
      ∑ s, separator s * (∑ x, left x s) * ∑ y, right s y := by
  classical
  let : Fintype ((graph left separator right).FullConfig) :=
    inferInstanceAs (Fintype (∀ b, blockSpace X S Y b))
  change (∑ x : (graph left separator right).FullConfig,
    (graph left separator right).unnormalizedJoint x) = _
  rw [← (graphConfigEquiv left separator right).sum_comp]
  change (∑ p : X × S × Y, (graph left separator right).unnormalizedJoint
    (graphConfiguration left separator right p.1 p.2.1 p.2.2)) = _
  simp only [graph_joint, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm, fixed_separator]
  ac_rfl

/-- The separator graph uses the same complete operational VE readout, including
the library's scope-covering factors for otherwise unused variables. -/
theorem graph_veQueryWeight [Fintype X] [Fintype S] [Fintype Y]
    [DecidableEq X] [DecidableEq S] [DecidableEq Y] [CommSemiring K]
    (left : X → S → K) (separator : S → K) (right : S → Y → K) :
    VariableElimination.veQueryWeightList (graph left separator right)
        (VariableElimination.factorsOfGraph (fg := graph left separator right)) [] =
      (graph left separator right).partitionFunction := by
  rw [VariableElimination.veQueryWeightList_eq_weightOfConstraintsList]
  simp only [VariableElimination.weightOfConstraintsList]
  simp [VariableElimination.combineAll_factorsOfGraph_potential_eq_unnormalizedJoint,
    FactorGraph.partitionFunction]
  rfl

/-- Formula-event factorization. Disjoint blocks are represented by distinct
coordinate carriers, and the full source weight is explicitly factorized. -/
theorem event_partition [Fintype X] [Fintype S] [Fintype Y] [CommSemiring K]
    (first : X → S → Bool) (second : S → Y → Bool)
    (wx : X → K) (ws : S → K) (wy : Y → K) :
    (∑ s, ∑ y, ∑ x, if first x s && second s y then wx x * ws s * wy y else 0) =
      ∑ s, ws s * (∑ x, if first x s then wx x else 0) * ∑ y, if second s y then wy y else 0 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [show ws s * (∑ x, if first x s then wx x else 0) =
    (∑ x, if first x s then wx x else 0) * ws s from mul_comm _ _]
  rw [← fixed_separator (fun x s => if first x s then wx x else 0) ws
    (fun s y => if second s y then wy y else 0) s]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  cases first x s <;> cases second s y <;> simp

/-- Empty separator with its neutral singleton weight gives a plain product. -/
theorem decomposable_and [Fintype X] [Fintype Y] [CommSemiring K]
    (first : X → Bool) (second : Y → Bool) (wx : X → K) (wy : Y → K) :
    (∑ y, ∑ x, if first x && second y then wx x * wy y else 0) =
      (∑ x, if first x then wx x else 0) * ∑ y, if second y then wy y else 0 := by
  simpa using event_partition (S := PUnit) (fun x _ => first x) (fun _ y => second y)
    wx (fun _ => 1) wy

/-- Deterministic alternatives add under any common finite weight table.
Variable-disjointness is not the condition for this OR law. -/
theorem deterministic_or {Ω : Type*} [Fintype Ω] [CommSemiring K]
    (first second : Ω → Bool) (weight : Ω → K)
    (exclusive : ∀ world, ¬ (first world = true ∧ second world = true)) :
    (∑ world, if first world || second world then weight world else 0) =
      (∑ world, if first world then weight world else 0) +
        ∑ world, if second world then weight world else 0 := by
  classical
  simp only [← Finset.sum_filter]
  have union : (Finset.univ.filter fun world => (first world || second world) = true) =
      (Finset.univ.filter fun world => first world = true) ∪
      (Finset.univ.filter fun world => second world = true) := by ext world; simp
  rw [union]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro world hf hs
  exact exclusive world ⟨(Finset.mem_filter.mp hf).2, (Finset.mem_filter.mp hs).2⟩

namespace Controls

/-- Reusing the same private variable is not an empty-separator product. -/
theorem shared_variable_outside_separator :
    ¬ Disjoint ({0} : Finset (Fin 1)) {0} ∧
      (∑ bit : Bool, if bit && bit then (1/2 : ℝ≥0) else 0) = 1/2 ∧
      ((∑ bit : Bool, if bit then (1/2 : ℝ≥0) else 0) *
        ∑ bit : Bool, if bit then (1/2 : ℝ≥0) else 0) = 1/4 := by
  norm_num [Fintype.sum_bool]

/-- Correct coordinate scopes do not license product weights for a correlated prior. -/
theorem correlated_private_weights :
    (∑ x : Bool, ∑ y : Bool, if x && y then (if x = y then (1/2 : ℝ≥0) else 0) else 0) = 1/2 ∧
      ((∑ x : Bool, if x then (1/2 : ℝ≥0) else 0) *
        ∑ y : Bool, if y then (1/2 : ℝ≥0) else 0) = 1/4 := by
  norm_num [Fintype.sum_bool]

theorem independent_private_bits :
    (∑ y : Bool, ∑ x : Bool, if x && y then (1/2 : ℝ≥0) * (1/2) else 0) = 1/4 := by
  rw [decomposable_and (fun x => x) (fun y => y) (fun _ => (1/2 : ℝ≥0)) (fun _ => 1/2)]
  norm_num [Fintype.sum_bool]

def copyTrue (privateBit separatorBit : Bool) : ℝ≥0 :=
  if privateBit = separatorBit ∧ privateBit = true then 1 else 0

theorem common_parent_separator :
    (graph copyTrue (fun _ : Bool => (1/2 : ℝ≥0)) (fun s y => copyTrue y s)).partitionFunction = 1/2 := by
  rw [graph_partitionFunction]
  simp only [Fintype.sum_bool]
  norm_num [copyTrue]

/-- The scope guard rejects a factor that reads a hidden shared variable. -/
theorem dishonest_scope_rejected :
    ¬ RespectsScope (⟨({.right} : Finset Block), fun x : FullConfig Block (fun _ => Bool) =>
      x .left⟩ : Valuation Block (fun _ => Bool) Bool) := by
  intro respects
  have same : agreeOn (fun _ : Block => false) (fun b => b == Block.left) ({.right} : Finset Block) := by
    intro b member
    have equal : b = Block.right := Finset.mem_singleton.mp member
    subst b
    decide
  have impossible := respects _ _ same
  change false = true at impossible
  exact Bool.noConfusion impossible

end Controls

end Mettapedia.ProbabilityTheory.BayesianNetworks.SeparatorFactorization
