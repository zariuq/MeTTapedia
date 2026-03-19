import Mettapedia.Logic.BDD.Compilation

/-!
# Stratified Semantics for Normal Logic Programs

Defines stratified fixed-point semantics for logic programs with
negation-as-failure (NAF) in rule bodies. This extends the definite-clause
`leastHerbrandModel` from `Semantics.lean` to handle `NormalClause`s
(ground rules with `GoalLit` bodies including `.neg` atoms).

**Key insight:** `T_normal` with a fixed negative interpretation `negI` is
monotone in the positive interpretation `I`. This enables per-stratum
least fixpoint computation via `OrderHom.lfp`.

## Architecture

The stratified model layers normal rules on top of the definite-clause
`leastHerbrandModel` (the "base LHM"):

1. Base: `leastHerbrandModel (residualKBa prog a)` — from definite clauses
2. Stratum 0: lfp of `(base ∪ T_normal(rules_0, ·, base))`
3. Stratum k+1: lfp of `(M_k ∪ T_normal(rules_{k+1}, ·, M_k))`
4. Full model: `⋃ k, M_k`

## References

- Apt, Blair & Walker (1988): "Towards a theory of declarative knowledge"
- Lloyd (1987): "Foundations of Logic Programming" §15
- Fierens et al. (2015): ProbLog distribution semantics

0 sorry.
-/

namespace Mettapedia.Logic.LP

open Mettapedia.Logic.BDDCore
open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation

/-! ## §1 Stratification -/

/-- A stratification assigns each ground atom a stratum number. -/
def Stratification (σ : LPSignature) := GroundAtom σ → ℕ

/-- A normal clause respects a stratification:
    - positive body atoms have stratum ≤ head stratum
    - negative body atoms have stratum **strictly <** head stratum
    - inequality constraints are always allowed

    This ensures NAF is only applied to atoms whose truth value is
    fully determined at a lower stratum. -/
def respectsStratification {σ : LPSignature}
    (c : NormalClause σ) (s : Stratification σ) : Prop :=
  ∀ g ∈ c.body, match g with
    | .pos a => s a ≤ s c.head
    | .neg a => s a < s c.head
    | .neq _ _ => True

/-- A list of normal clauses is stratifiable if there exists a stratification
    respected by all clauses. -/
def isStratifiable {σ : LPSignature} (rules : List (NormalClause σ)) : Prop :=
  ∃ s : Stratification σ, ∀ c ∈ rules, respectsStratification c s

/-! ## §2 Normal Clause Body Satisfaction -/

/-- A goal literal holds w.r.t. positive interpretation `I` and
    negative interpretation `negI`.
    - `.pos a`: `a ∈ I`
    - `.neg a`: `a ∉ negI` (NAF: atom is absent from the completed model)
    - `.neq a b`: `a ≠ b` (static) -/
def goalLitHoldsIn {σ : LPSignature}
    (I negI : Set (GroundAtom σ)) : GoalLit σ → Prop
  | .pos a => a ∈ I
  | .neg a => a ∉ negI
  | .neq a b => a ≠ b

/-- All body literals of a normal clause hold w.r.t. `I` and `negI`. -/
def normalClauseBodyHolds {σ : LPSignature}
    (c : NormalClause σ) (I negI : Set (GroundAtom σ)) : Prop :=
  ∀ g ∈ c.body, goalLitHoldsIn I negI g

/-! ## §3 T_normal Operator -/

/-- Immediate consequence operator for normal clauses.
    Returns the set of head atoms whose bodies are satisfied
    w.r.t. positive interpretation `I` and negative interpretation `negI`. -/
noncomputable def T_normal {σ : LPSignature}
    (rules : List (NormalClause σ)) (I negI : Set (GroundAtom σ)) :
    Set (GroundAtom σ) :=
  { a | ∃ c ∈ rules, c.head = a ∧ normalClauseBodyHolds c I negI }

/-- **Monotonicity of T_normal in I** (with fixed negI).
    If `I ⊆ J`, then `T_normal rules I negI ⊆ T_normal rules J negI`.

    This is the key property enabling per-stratum lfp. The positive body
    atoms grow with I, while negative body atoms are checked against the
    fixed `negI`. -/
theorem T_normal_mono_I {σ : LPSignature}
    (rules : List (NormalClause σ)) (negI : Set (GroundAtom σ)) :
    Monotone (fun I => T_normal rules I negI) := by
  intro I J hIJ a ⟨c, hc, hhead, hbody⟩
  refine ⟨c, hc, hhead, fun g hg => ?_⟩
  have hg' := hbody g hg
  cases g with
  | pos ga => exact hIJ hg'
  | neg ga => exact hg'
  | neq ga gb => exact hg'

/-- T_normal combined with a base set, as an OrderHom for lfp. -/
noncomputable def T_normal_orderHom {σ : LPSignature}
    (rules : List (NormalClause σ)) (base negI : Set (GroundAtom σ)) :
    Set (GroundAtom σ) →o Set (GroundAtom σ) where
  toFun I := base ∪ T_normal rules I negI
  monotone' := by
    intro I J hIJ
    apply Set.union_subset_union_right
    exact T_normal_mono_I rules negI hIJ

/-! ## §4 Stratified Fixed Point -/

/-- Rules whose head is at stratum exactly `k`. -/
def rulesAtStratum {σ : LPSignature}
    (rules : List (NormalClause σ)) (s : Stratification σ) (k : ℕ) :
    List (NormalClause σ) :=
  rules.filter (fun c => s c.head = k)

/-- The stratified model at stratum `k`.

    - Stratum 0: lfp of `(base ∪ T_normal(rules_0, ·, base))`
      where `base` is the definite-clause LHM.
      NAF at stratum 0 is evaluated against `base` (the definite LHM).
    - Stratum k+1: lfp of `(M_k ∪ T_normal(rules_{k+1}, ·, M_k))`
      NAF at stratum k+1 is evaluated against M_k (accumulated model). -/
noncomputable def stratifiedModel {σ : LPSignature}
    (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (s : Stratification σ) : ℕ → Set (GroundAtom σ)
  | 0 => OrderHom.lfp (T_normal_orderHom (rulesAtStratum rules s 0) base base)
  | k + 1 =>
    let M_k := stratifiedModel rules base s k
    OrderHom.lfp (T_normal_orderHom (rulesAtStratum rules s (k + 1)) M_k M_k)

/-- The full stratified model: union over all strata. -/
noncomputable def fullStratifiedModel {σ : LPSignature}
    (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (s : Stratification σ) : Set (GroundAtom σ) :=
  ⋃ k, stratifiedModel rules base s k

/-! ## §5 Accumulation: M_k ⊆ M_{k+1} -/

/-- The base set is contained in every stratum's model. -/
private theorem base_le_lfp_T_normal {σ : LPSignature}
    (rules : List (NormalClause σ)) (base negI : Set (GroundAtom σ)) :
    base ⊆ OrderHom.lfp (T_normal_orderHom rules base negI) := by
  -- lfp f is a fixpoint: lfp f = f(lfp f) = base ∪ T_normal(rules, lfp f, negI)
  -- So base ⊆ base ∪ ... = lfp f
  have hfp : (T_normal_orderHom rules base negI) (OrderHom.lfp (T_normal_orderHom rules base negI)) =
    OrderHom.lfp (T_normal_orderHom rules base negI) := OrderHom.map_lfp _
  intro a ha
  rw [← hfp]
  exact Set.mem_union_left _ ha

theorem base_subset_stratifiedModel {σ : LPSignature}
    (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (s : Stratification σ) (k : ℕ) :
    base ⊆ stratifiedModel rules base s k := by
  induction k with
  | zero => exact base_le_lfp_T_normal _ base base
  | succ k ih =>
    intro a ha
    exact base_le_lfp_T_normal _ (stratifiedModel rules base s k) _ (ih ha)

/-- Strata accumulate: `stratifiedModel k ⊆ stratifiedModel (k + 1)`. -/
theorem stratifiedModel_mono {σ : LPSignature}
    (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (s : Stratification σ) (k : ℕ) :
    stratifiedModel rules base s k ⊆ stratifiedModel rules base s (k + 1) := by
  intro a ha
  exact base_le_lfp_T_normal _ (stratifiedModel rules base s k) _ ha

/-- Every stratum is contained in the full model. -/
theorem stratifiedModel_subset_full {σ : LPSignature}
    (rules : List (NormalClause σ)) (base : Set (GroundAtom σ))
    (s : Stratification σ) (k : ℕ) :
    stratifiedModel rules base s k ⊆ fullStratifiedModel rules base s :=
  Set.subset_iUnion _ k

/-! ## §6 Query Semantics for Normal Programs -/

/-- Query holds under assignment `a` for a normal ProbLog program
    with stratification `s`.

    The base is the definite-clause LHM; normal rules layer on top
    using stratified fixed-point with NAF evaluated against
    the accumulated model at each stratum. -/
def queryHoldsNormalA {σ : LPSignature} {n : ℕ}
    (prog : NormalProbLogProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  q ∈ fullStratifiedModel prog.normalRules
    (leastHerbrandModel (residualKBa prog.toProbLogProgram a)) s

/-! ## §7 Compatibility: Empty Normal Rules → Definite LHM -/

/-- When there are no normal rules, `T_normal` returns the empty set. -/
theorem T_normal_nil {σ : LPSignature}
    (I negI : Set (GroundAtom σ)) :
    T_normal ([] : List (NormalClause σ)) I negI = ∅ := by
  ext a; simp [T_normal]

/-- When there are no normal rules, each stratum's model equals the base. -/
theorem stratifiedModel_nil {σ : LPSignature}
    (base : Set (GroundAtom σ)) (s : Stratification σ) (k : ℕ) :
    stratifiedModel ([] : List (NormalClause σ)) base s k = base := by
  induction k with
  | zero =>
    apply le_antisymm
    · apply OrderHom.lfp_le
      intro a ha
      show a ∈ base
      simp only [T_normal_orderHom, OrderHom.coe_mk, Set.mem_union] at ha
      rcases ha with hb | ht
      · exact hb
      · simp [T_normal, rulesAtStratum] at ht
    · exact base_subset_stratifiedModel [] base s 0
  | succ k ih =>
    apply le_antisymm
    · apply OrderHom.lfp_le
      intro a ha
      show a ∈ base
      simp only [T_normal_orderHom, OrderHom.coe_mk, Set.mem_union] at ha
      rcases ha with hm | ht
      · rwa [ih] at hm
      · simp [T_normal, rulesAtStratum] at ht
    · exact base_subset_stratifiedModel [] base s (k + 1)

/-- When there are no normal rules, the full stratified model equals the base. -/
theorem fullStratifiedModel_nil {σ : LPSignature}
    (base : Set (GroundAtom σ)) (s : Stratification σ) :
    fullStratifiedModel ([] : List (NormalClause σ)) base s = base := by
  ext a
  simp only [fullStratifiedModel, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    rwa [stratifiedModel_nil] at hk
  · intro ha
    exact ⟨0, by rwa [stratifiedModel_nil]⟩

/-- **Compatibility theorem**: when `normalRules` is empty,
    `queryHoldsNormalA` coincides with `queryHoldsA`.

    This ensures the normal-program semantics is a conservative
    extension of the definite-clause semantics. -/
theorem queryHoldsNormalA_empty_iff {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n) (s : Stratification σ)
    (q : GroundAtom σ) (a : Fin n → Bool)
    (hempty : prog.normalRules = []) :
    queryHoldsNormalA prog s q a ↔ queryHoldsA prog.toProbLogProgram q a := by
  unfold queryHoldsNormalA queryHoldsA
  rw [hempty, fullStratifiedModel_nil]

/-! ## §8 Goal Literal Interpretation in Stratified Model -/

/-- Interpretation of a goal literal in the stratified model. -/
def GoalLit.holdsNormal {σ : LPSignature} {n : ℕ}
    (prog : NormalProbLogProgram σ n)
    (s : Stratification σ) (a : Fin n → Bool) : GoalLit σ → Prop
  | .pos ga => queryHoldsNormalA prog s ga a
  | .neg ga => ¬ queryHoldsNormalA prog s ga a
  | .neq ga gb => ga ≠ gb

/-- The base (definite LHM) is contained in the full stratified model. -/
theorem baseLHM_subset_fullStratifiedModel {σ : LPSignature} {n : ℕ}
    (prog : NormalProbLogProgram σ n) (s : Stratification σ)
    (a : Fin n → Bool) :
    leastHerbrandModel (residualKBa prog.toProbLogProgram a) ⊆
      fullStratifiedModel prog.normalRules
        (leastHerbrandModel (residualKBa prog.toProbLogProgram a)) s := by
  intro q hq
  exact stratifiedModel_subset_full _ _ s 0 (base_subset_stratifiedModel _ _ s 0 hq)

/-- If `queryHoldsA` holds (atom in definite LHM), then `queryHoldsNormalA` holds. -/
theorem queryHoldsA_implies_queryHoldsNormalA {σ : LPSignature} {n : ℕ}
    (prog : NormalProbLogProgram σ n) (s : Stratification σ)
    (q : GroundAtom σ) (a : Fin n → Bool)
    (h : queryHoldsA prog.toProbLogProgram q a) :
    queryHoldsNormalA prog s q a :=
  baseLHM_subset_fullStratifiedModel prog s a h

end Mettapedia.Logic.LP
