import Mettapedia.Logic.RandomClosure
import Mettapedia.Logic.BDD.CertifiedProgramProbability
import Mettapedia.ProbabilityTheory.BayesianNetworks.SeparatorFactorization

/-!
# Closure responses of positive probabilistic programs

Positive source rules construct a finitary closure operator, whose least-model
interpretation is the existing stratified ProbLog semantics. The commonality
extraction law therefore observes the supplied program, without a new model
counter or an assumed response-table specification.

Negation is outside this closure representation. Shared random choices must
remain a conditioning separator; disjoint private labels alone are not a
probabilistic independence certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.ClosureResponseCounting

open scoped BigOperators NNReal ENNReal
open LP NormalProgramSemantics ClarkCompletion NormalCompletion RandomClosure
open Mettapedia.ProbabilityTheory

variable {σ : LPSignature}

def positiveStrata (σ : LPSignature) : Stratification σ := fun _ => 0

def Positive (rules : List (NormalClause σ)) : Prop :=
  ∀ c ∈ rules, ∀ g ∈ c.body, ∃ a, g = GoalLit.pos a

def checkPositive (rules : List (NormalClause σ)) : Bool :=
  rules.all fun c => c.body.all fun g => match g with | .pos _ => true | _ => false

theorem checkPositive_correct (rules : List (NormalClause σ)) : checkPositive rules = true ↔ Positive rules := by
  simp only [checkPositive, List.all_eq_true, Positive]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro _
  apply forall_congr'
  intro g
  cases g <;> simp

def ruleRelation (rules : List (NormalClause σ)) (premises : List (GroundAtom σ)) (head : GroundAtom σ) : Prop :=
  ∃ c ∈ rules, c.head = head ∧ positiveBody c = premises

/-- The positive-body projection of the whole source. Its interpretation as
program execution requires `Positive`; private scopes are supplied separately. -/
def programComponent (rules : List (NormalClause σ)) (base : Set (GroundAtom σ)) : Component (GroundAtom σ) where
  scope := Set.univ
  rules := ruleRelation rules
  base := base
  base_scoped := Set.subset_univ _
  rule_scoped _ _ _ := ⟨Set.mem_univ _, fun _ _ => Set.mem_univ _⟩

theorem component_closed_iff_step (rules : List (NormalClause σ)) (positive : Positive rules)
    (base interpretation negative : Set (GroundAtom σ)) :
    (programComponent rules base).closure.IsClosed interpretation ↔
      base ∪ T_normal rules interpretation negative ⊆ interpretation := by
  rw [Component.closed_iff]
  constructor
  · rintro ⟨baseInside, closed⟩ a (inBase | ⟨c, member, rfl, body⟩)
    · exact baseInside inBase
    · exact closed (positiveBody c) c.head ⟨c, member, rfl, rfl⟩
        (fun b hb => body (.pos b) ((mem_positiveBody c b).mp hb))
  · intro closed
    refine ⟨fun a ha => closed (Or.inl ha), ?_⟩
    rintro premises head ⟨c, member, rfl, rfl⟩ body
    apply closed
    refine Or.inr ⟨c, member, rfl, ?_⟩
    intro g hg
    obtain ⟨a, rfl⟩ := positive c member g hg
    exact body a ((mem_positiveBody c a).mpr hg)

theorem program_closure_eq_lfp (rules : List (NormalClause σ)) (positive : Positive rules)
    (base seed negative : Set (GroundAtom σ)) :
    (programComponent rules base).closure seed = (T_normal_orderHom rules (base ∪ seed) negative).lfp := by
  let component := programComponent rules base
  let C := component.closure seed
  let operator := T_normal_orderHom rules (base ∪ seed) negative
  have inside : base ∪ seed ⊆ C := Set.union_subset (component.base_le seed) (component.closure.le_closure seed)
  have derivedClosed := component.rules_closed seed
  have complete : (programComponent rules (base ∪ seed)).closure.IsClosed C :=
    (Component.closed_iff _ _).mpr ⟨inside, derivedClosed⟩
  have below : operator.lfp ⊆ C := OrderHom.lfp_le _ ((component_closed_iff_step rules positive _ _ _).mp complete)
  have fixed : (programComponent rules (base ∪ seed)).closure.IsClosed operator.lfp :=
    (component_closed_iff_step rules positive _ _ _).mpr (OrderHom.map_lfp operator).le
  obtain ⟨baseAndSeed, rulesClosed⟩ := (Component.closed_iff _ _).mp fixed
  have originalClosed : component.closure.IsClosed operator.lfp :=
    (Component.closed_iff _ _).mpr ⟨fun a ha => baseAndSeed (Or.inl ha), rulesClosed⟩
  exact Set.Subset.antisymm (component.closure.closure_min (fun a ha => baseAndSeed (Or.inr ha)) originalClosed) below

theorem positive_stratified (rules : List (NormalClause σ)) (positive : Positive rules) :
    ∀ c ∈ rules, respectsStratification c (positiveStrata σ) := by
  intro c hc g hg
  obtain ⟨a, rfl⟩ := positive c hc g hg
  exact le_rfl

theorem program_closure_eq_model (rules : List (NormalClause σ)) (positive : Positive rules)
    (base seed : Set (GroundAtom σ)) :
    (programComponent rules base).closure seed = fullStratifiedModel rules (base ∪ seed) (positiveStrata σ) := by
  apply (stable_iff_eq_full rules (base ∪ seed) (positiveStrata σ) (positive_stratified rules positive) _).mp
  apply (stable_iff _ _ _).mpr
  exact program_closure_eq_lfp rules positive base seed _

variable [DecidableEq (GroundAtom σ)] {n : Nat}

noncomputable def seedRules (seed : Finset (GroundAtom σ)) : List (NormalClause σ) :=
  seed.toList.map fun a => ⟨a, []⟩

noncomputable def addSeeds (prog : ProbMeTTaSourceProgram σ n) (seed : Finset (GroundAtom σ)) : ProbMeTTaSourceProgram σ n :=
  { prog with normalRules := prog.normalRules ++ seedRules seed }

omit [DecidableEq (GroundAtom σ)] in
theorem positive_addSeeds (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (seed : Finset (GroundAtom σ)) : Positive (addSeeds prog seed).normalRules := by
  intro c hc g hg
  rcases List.mem_append.mp hc with original | added
  · exact positive c original g hg
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp added
    cases hg

omit [DecidableEq (GroundAtom σ)] in
theorem seedRules_closure (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (seed : Finset (GroundAtom σ)) :
    (programComponent (rules ++ seedRules seed) base).closure =
      (programComponent rules (base ∪ (seed : Set (GroundAtom σ)))).closure := by
  apply ClosureOperator.ext_isClosed
  intro candidate
  rw [Component.closed_iff, Component.closed_iff]
  constructor
  · rintro ⟨baseInside, closed⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      rcases ha with old | new
      · exact baseInside old
      · apply closed [] a
        · refine ⟨⟨a, []⟩, List.mem_append_right rules ?_, rfl, rfl⟩
          exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr new, rfl⟩
        · intro b hb
          cases hb
    · rintro p a ⟨c, hc, head, body⟩ hs
      exact closed p a ⟨c, List.mem_append_left _ hc, head, body⟩ hs
  · rintro ⟨baseInside, closed⟩
    refine ⟨fun a ha => baseInside (Or.inl ha), ?_⟩
    rintro p a ⟨c, hc, head, body⟩ hs
    rcases List.mem_append.mp hc with original | added
    · exact closed p a ⟨c, original, head, body⟩ hs
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp added
      change b = a at head
      subst a
      exact baseInside (Or.inr (Finset.mem_toList.mp hb))

omit [DecidableEq (GroundAtom σ)] in
theorem seedRules_apply (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (seed : Finset (GroundAtom σ)) :
    (programComponent (rules ++ seedRules seed) base).closure ∅ =
      (programComponent rules base).closure (seed : Set (GroundAtom σ)) := by
  rw [seedRules_closure]
  change {a | FinitaryClosure.close (ruleRelation rules) (fun b => b ∈ (base ∪ (seed : Set (GroundAtom σ))) ∪ ∅) a} =
    {a | FinitaryClosure.close (ruleRelation rules) (fun b => b ∈ base ∪ (seed : Set (GroundAtom σ))) a}
  rw [Set.union_empty]

/-- Unchecked positive-body projection; `sourceProbability` checks admission. -/
def projectionResponse (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (choice : Fin n → Bool) : ClosureOperator (Set boundary) :=
  response (boundary : Set (GroundAtom σ))
    (programComponent prog.normalRules (chosenFacts prog.probFacts choice)).closure

theorem projectionResponse_seed (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (seed : Finset boundary) (choice : Fin n → Bool) (query : boundary) :
    query ∈ projectionResponse prog boundary choice (seed : Set boundary) ↔
      query ∈ projectionResponse (addSeeds prog (seed.image Subtype.val)) boundary choice ∅ := by
  change query.val ∈ (programComponent prog.normalRules (chosenFacts prog.probFacts choice)).closure
      (expand (boundary : Set (GroundAtom σ)) (seed : Set boundary)) ↔
    query.val ∈ (programComponent (prog.normalRules ++ seedRules (seed.image Subtype.val))
      (chosenFacts prog.probFacts choice)).closure (expand (boundary : Set (GroundAtom σ)) ∅)
  have empty : expand (boundary : Set (GroundAtom σ)) ∅ = ∅ := by simp [expand]
  have embedded : expand (boundary : Set (GroundAtom σ)) (seed : Set boundary) =
      (seed.image Subtype.val : Set (GroundAtom σ)) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · intro member
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp member
      exact ⟨b, hb, rfl⟩
  rw [empty, embedded, seedRules_apply]

omit [DecidableEq (GroundAtom σ)] in
theorem projectionResponse_model (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom σ)) (choice : Fin n → Bool) (query : boundary) :
    query ∈ projectionResponse prog boundary choice ∅ ↔
      LP.GoalLit.holdsNormal prog.toNormalProbLogProgram (positiveStrata σ) choice (.pos query.val) := by
  rw [← source_goal prog (positiveStrata σ) choice (.pos query.val)]
  change query.val ∈ (programComponent prog.normalRules (chosenFacts prog.probFacts choice)).closure
    (expand (boundary : Set (GroundAtom σ)) ∅) ↔ _
  have empty : expand (boundary : Set (GroundAtom σ)) ∅ = ∅ := by simp [expand]
  rw [empty, program_closure_eq_model _ positive]
  simp only [Set.union_empty, goalLitHoldsIn]

noncomputable def sourceWeight (prog : ProbMeTTaSourceProgram σ n) (choice : Fin n → Bool) : ℝ :=
  (TseitinCounting.productWeight (choiceProbability prog) choice : ℝ)

noncomputable def projectionCount (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (query : boundary) : ℝ := extract (sourceWeight prog) (projectionResponse prog boundary) ∅ query

omit [DecidableEq (GroundAtom σ)] in
theorem projectionCount_nonneg (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (query : boundary) : 0 ≤ projectionCount prog boundary query := by
  rw [projectionCount, extract_correct]
  apply Finset.sum_nonneg
  intro choice _
  split_ifs <;> first | exact NNReal.coe_nonneg _ | exact le_rfl

omit [DecidableEq (GroundAtom σ)] in
theorem projectionCount_eq_queryProb (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom σ)) (query : boundary) :
    ENNReal.ofReal (projectionCount prog boundary query) =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent prog (positiveStrata σ) [.pos query.val]
          (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) := by
  classical
  rw [projectionCount, extract_correct, ENNReal.ofReal_sum_of_nonneg]
  · rw [WMPLNBDDWMCExact.queryProb_eq_weightedSat _ prog.probs_le_one]
    simp only [weightedSat, Equiv.apply_symm_apply]
    apply Finset.sum_congr rfl
    intro choice _
    have agrees : sourceEvent prog (positiveStrata σ) [.pos query.val] choice = true ↔
        query ∈ projectionResponse prog boundary choice ∅ := by
      rw [sourceEvent_true prog (positiveStrata σ) [.pos query.val] choice]
      simpa only [List.mem_singleton, forall_eq] using (projectionResponse_model prog positive boundary choice query).symm
    change ENNReal.ofReal (if query ∈ projectionResponse prog boundary choice ∅ then sourceWeight prog choice else 0) =
      if sourceEvent prog (positiveStrata σ) [.pos query.val] choice = true then assignmentWeight prog.probs choice else 0
    by_cases holds : query ∈ projectionResponse prog boundary choice ∅
    · simp only [if_pos holds, if_pos (agrees.mpr holds), sourceWeight, ENNReal.ofReal_coe_nnreal,
        TseitinCounting.coe_productWeight, coe_choiceProbability]
    · simp only [if_neg holds, if_neg (fun h => holds (agrees.mp h)), ENNReal.ofReal_zero]
  · intro choice _
    split_ifs <;> first | exact NNReal.coe_nonneg _ | exact le_rfl

universe u v
theorem agrees_with_certified_count {τ : LPSignature.{u, u, v, u}} [DecidableEq (GroundAtom τ)]
    (method : ClausificationCounting.Method)
    (prog : ProbMeTTaSourceProgram τ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom τ)) (query : boundary) :
    CertifiedProgramProbability.probability? method prog [.pos query.val] =
      some (ENNReal.ofReal (projectionCount prog boundary query)) := by
  exact (CertifiedProgramProbability.probability?_eq_queryProb method prog (positiveStrata τ)
    (positive_stratified prog.normalRules positive) [.pos query.val]).trans
      (congrArg some (projectionCount_eq_queryProb prog positive boundary query).symm)

noncomputable def seededProjectionCount (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (seed : Finset boundary) (query : boundary) : ℝ :=
  preparedExtract (sourceWeight prog) (projectionResponse prog boundary) (seed : Set boundary) query

theorem seededProjectionCount_eq_projectionCount (prog : ProbMeTTaSourceProgram σ n) (boundary : Finset (GroundAtom σ))
    (seed : Finset boundary) (query : boundary) :
    seededProjectionCount prog boundary seed query = projectionCount (addSeeds prog (seed.image Subtype.val)) boundary query := by
  classical
  rw [seededProjectionCount, preparedExtract_eq_extract, projectionCount, extract_correct, extract_correct]
  apply Finset.sum_congr rfl
  intro choice _
  simp only [projectionResponse_seed prog boundary seed choice query]
  rfl

theorem seededProjectionCount_eq_queryProb (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom σ)) (seed : Finset boundary) (query : boundary) :
    ENNReal.ofReal (seededProjectionCount prog boundary seed query) =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent (addSeeds prog (seed.image Subtype.val)) (positiveStrata σ) [.pos query.val]
          (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) := by
  rw [seededProjectionCount_eq_projectionCount]
  exact projectionCount_eq_queryProb _ (positive_addSeeds prog positive _) boundary query

section SourcePartition
variable {I : Type*} [Fintype I] {World : I → Type*} [∀ i, Fintype (World i)]

omit [DecidableEq (GroundAtom σ)] [Fintype I] in
/-- A syntactic partition is checked at the rule and base-fact level. No response
table, least-model equality, or counting result is assumed. -/
theorem partition_closure (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (components : I → Component (GroundAtom σ))
    (basePartition : (⋃ i, (components i).base) = base)
    (rulePartition : ∀ premises head,
      (∃ i, (components i).rules premises head) ↔ ruleRelation rules premises head) :
    (Component.combineFamily components).closure = (programComponent rules base).closure := by
  have ruleEquality : (Component.combineFamily components).rules = ruleRelation rules := by
    funext premises head
    exact propext (rulePartition premises head)
  apply ClosureOperator.ext
  intro seed
  change {a | FinitaryClosure.close (Component.combineFamily components).rules
    (fun b => b ∈ (Component.combineFamily components).base ∪ seed) a} = _
  rw [ruleEquality]
  change {a | FinitaryClosure.close (ruleRelation rules) (fun b => b ∈ (⋃ i, (components i).base) ∪ seed) a} = _
  rw [basePartition]
  rfl

/-- Independent local choices and a checked source partition connect the fast
factored expression directly to the existing ProbLog query probability. -/
theorem factored_queryProb (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom σ)) (seed : Finset boundary) (query : boundary)
    (components : ∀ i, World i → Component (GroundAtom σ))
    (worlds : (∀ i, World i) ≃ (Fin n → Bool)) (weight : ∀ i, World i → ℝ)
    (factor : ∀ world, sourceWeight prog (worlds world) = ∏ i, weight i (world i))
    (inside : ∀ i w, (boundary : Set (GroundAtom σ)) ⊆ (components i w).scope)
    (separated : ∀ i j, i ≠ j → ∀ x y,
      (components i x).scope ∩ (components j y).scope ⊆ (boundary : Set (GroundAtom σ)))
    (bases : ∀ world, (⋃ i, (components i (world i)).base) = chosenFacts prog.probFacts (worlds world))
    (rules : ∀ (world : ∀ i, World i) premises head,
      (∃ i, (components i (world i)).rules premises head) ↔ ruleRelation prog.normalRules premises head) :
    ENNReal.ofReal (∑ family ∈ (avoiding (seed : Set boundary) query).powerset,
      (-1 : ℝ) ^ family.card * ∏ i, commonality (weight i)
        (fun w => response (boundary : Set (GroundAtom σ)) (components i w).closure) family) =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent (addSeeds prog (seed.image Subtype.val)) (positiveStrata σ) [.pos query.val]
          (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) := by
  classical
  have mass := component_query_mass components (boundary : Set (GroundAtom σ)) inside separated weight (seed : Set boundary) query
  apply (congrArg ENNReal.ofReal mass).trans
  rw [← seededProjectionCount_eq_queryProb prog positive boundary seed query,
    seededProjectionCount, preparedExtract_eq_extract, extract_correct]
  congr 1
  apply Fintype.sum_equiv worlds
  intro world
  rw [partition_closure prog.normalRules _ (fun i => components i (world i)) (bases world) (rules world)]
  simp only [projectionResponse, factor]

end SourcePartition

section SharedChoices
variable {L R : Type*} {H X Y : Type u} [CompleteLattice L] [Fintype H] [Fintype X] [Fintype Y] [CommSemiring R]

/-- The shared choice is counted once, outside the independent private sums. -/
theorem conditioned_commonality (shared : H → R) (left : X → H → R) (right : H → Y → R)
    (c : H → X → ClosureOperator L) (d : H → Y → ClosureOperator L) (family : Finset L) :
    (∑ h, commonality (fun world : X × Y => left world.1 h * shared h * right h world.2)
      (fun world => join (c h world.1) (d h world.2)) family) =
        ∑ h, commonality (left · h) (c h) family * shared h * commonality (right h) (d h) family := by
  classical
  apply Finset.sum_congr rfl
  intro h _
  let l : X → H → R := fun x h => if Closes (c h x) family then left x h else 0
  let r : H → Y → R := fun h y => if Closes (d h y) family then right h y else 0
  have separated := BayesianNetworks.SeparatorFactorization.fixed_separator l shared r h
  change _ = (∑ x, l x h) * shared h * ∑ y, r h y
  rw [← separated, commonality, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases first : Closes (c h x) family <;> by_cases second : Closes (d h y) family <;>
    simp [l, r, first, second]

end SharedChoices

inductive ResponseError where
  | nonpositiveProgram
  deriving DecidableEq, Repr

/-- The public entry checks positivity before using the positive projection. -/
noncomputable def sourceProbability (prog : ProbMeTTaSourceProgram σ n)
    (boundary : Finset (GroundAtom σ)) (seed : Finset boundary) (query : boundary) : Except ResponseError ℝ≥0∞ :=
  if checkPositive prog.normalRules then
    .ok (ENNReal.ofReal (seededProjectionCount prog boundary seed query))
  else .error .nonpositiveProgram

omit [DecidableEq (GroundAtom σ)] in
theorem sourceProbability_unsupported (prog : ProbMeTTaSourceProgram σ n)
    (boundary : Finset (GroundAtom σ)) (seed : Finset boundary) (query : boundary) :
    sourceProbability prog boundary seed query = .error .nonpositiveProgram ↔ ¬ Positive prog.normalRules := by
  simp only [sourceProbability]
  split_ifs with positive
  · simp [(checkPositive_correct _).mp positive]
  · have absent : ¬ Positive prog.normalRules := fun h => positive ((checkPositive_correct _).mpr h)
    simp [absent]

theorem sourceProbability_correct (prog : ProbMeTTaSourceProgram σ n) (positive : Positive prog.normalRules)
    (boundary : Finset (GroundAtom σ)) (seed : Finset boundary) (query : boundary) :
    sourceProbability prog boundary seed query = .ok
      (Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent (addSeeds prog (seed.image Subtype.val)) (positiveStrata σ) [.pos query.val]
          (WMPLNBDDWMCExact.worldAssignmentEquiv n world))) := by
  rw [sourceProbability, if_pos ((checkPositive_correct _).mpr positive), seededProjectionCount_eq_queryProb _ positive]

section ConditionalObservation
variable {B Ω : Type*} [Fintype B] [Fintype Ω]
open scoped Classical

/-- Normalization is performed once, after unnormalized commonality extraction. -/
noncomputable def conditionalResponse (weight : Ω → ℝ≥0) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) : Option ℝ≥0∞ :=
  if (∑ world, weight world) = 0 then none else
    some (ENNReal.ofReal (extract (fun world => (weight world : ℝ)) c seed query) /
      (∑ world, weight world : ℝ≥0))

theorem conditionalResponse_correct (weight : Ω → ℝ≥0) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) :
    conditionalResponse weight c seed query =
      (FiniteFunctionalExtension.observationMass weight id).query (fun world => decide (query ∈ c world seed)) := by
  rw [conditionalResponse, extract_correct]
  have numerator : ENNReal.ofReal (∑ world, if query ∈ c world seed then (weight world : ℝ) else 0) =
      ((∑ world, if query ∈ c world seed then weight world else 0 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · push_cast
      apply Finset.sum_congr rfl
      intro world _
      split_ifs <;> simp
    · intro world _
      split_ifs <;> first | exact NNReal.coe_nonneg _ | exact le_rfl
  rw [numerator]
  simp only [MassSemantics.query, MassSemantics.queryProb, FiniteFunctionalExtension.observationMass,
    ENNReal.coe_eq_zero, id_eq, decide_eq_true_eq]
  split_ifs <;> rfl

@[simp] theorem conditionalResponse_none_iff (weight : Ω → ℝ≥0) (c : Ω → ClosureOperator (Set B))
    (seed : Set B) (query : B) : conditionalResponse weight c seed query = none ↔ (∑ world, weight world) = 0 := by
  simp [conditionalResponse]

end ConditionalObservation

namespace Controls
open NormalCompletion.Controls

theorem self_loop_positive : Positive loopRules := (checkPositive_correct _).mp (by decide)

theorem self_loop_count_zero :
    ENNReal.ofReal (projectionCount loopSource {atom ()} ⟨atom (), Finset.mem_singleton_self _⟩) = 0 := by
  have agrees := agrees_with_certified_count .full loopSource self_loop_positive {atom ()}
    ⟨atom (), Finset.mem_singleton_self _⟩
  rw [CertifiedProgramProbability.Controls.self_loop_answers_zero] at agrees
  exact (Option.some.inj agrees).symm

theorem negative_program_is_outside_response_contract : ¬ Positive negativeRules := by
  intro positive
  have := (checkPositive_correct negativeRules).mpr positive
  have rejected : checkPositive negativeRules = false := by decide
  simp [rejected] at this

theorem impossible_evidence_has_no_answer :
    conditionalResponse (fun _ : Unit => (0 : ℝ≥0))
      (fun _ => ClosureOperator.id (Set Unit)) ∅ () = none := by simp

theorem zero_probability_is_an_answer :
    conditionalResponse (fun _ : Unit => (1 : ℝ≥0))
      (fun _ => ClosureOperator.id (Set Unit)) ∅ () = some 0 := by
  rw [conditionalResponse, extract_correct]
  simp

end Controls

end Mettapedia.Logic.BDDCore.ClosureResponseCounting
