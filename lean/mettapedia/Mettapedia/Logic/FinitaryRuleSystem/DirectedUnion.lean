import Mettapedia.Logic.Derivation

/-!
# Directed unions of finitary rule systems

Every derivation in a directed union of monotone finitary rule systems already
belongs to one stage.  Consequently, if every stage rejects a distinguished
bottom judgment, then the union rejects it as well.

This is a syntactic compactness theorem about finite derivations.  It neither
constructs a semantic model nor lets a theory certify its own consistency.
The adversarial control shows why directed monotonicity is load-bearing: two
separately bottom-free rule sets can derive bottom after an undirected union.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open Mettapedia.Logic

universe u v

variable {J : Type u} {I : Type v}

/-- The pointwise union of an indexed family of rule predicates. -/
def UnionRules (rules : I → List J → J → Prop) : List J → J → Prop :=
  fun premises conclusion => ∃ i, rules i premises conclusion

/-- Rule inclusion along the stage order. -/
def MonotoneRules [Preorder I] (rules : I → List J → J → Prop) : Prop :=
  ∀ {i k : I}, i ≤ k → ∀ {premises : List J} {conclusion : J},
    rules i premises conclusion → rules k premises conclusion

/-- No derivation concludes the distinguished bottom judgment. -/
def NoBottom (rules : List J → J → Prop) (bottom : J) : Prop :=
  ¬ Derives rules bottom

/-- Finitely many already-staged premises can be lifted to one common upper
stage. -/
theorem premises_at_common_stage [SemilatticeSup I]
    {rules : I → List J → J → Prop} (monotone : MonotoneRules rules) :
    ∀ (premises : List J),
      (∀ premise ∈ premises, ∃ i, Derives (rules i) premise) →
      ∀ base : I, ∃ upper : I, base ≤ upper ∧
        ∀ premise ∈ premises, Derives (rules upper) premise := by
  intro premises
  induction premises with
  | nil =>
      intro _available base
      exact ⟨base, le_rfl, by simp⟩
  | cons head tail ih =>
      intro available base
      obtain ⟨headStage, headDerivation⟩ :=
        available head (by simp)
      obtain ⟨tailStage, baseLeTail, tailDerivations⟩ :=
        ih (fun premise member => available premise (by simp [member])) base
      refine ⟨tailStage ⊔ headStage,
        baseLeTail.trans le_sup_left, ?_⟩
      intro premise member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact headDerivation.mono
          (fun _premises _conclusion rule =>
            monotone le_sup_right rule)
      · exact (tailDerivations premise inTail).mono
          (fun _premises _conclusion rule =>
            monotone le_sup_left rule)

/-- Finite-support theorem: every derivation in a directed monotone union is
already a derivation at one stage. -/
theorem derives_union_exists_stage [SemilatticeSup I]
    {rules : I → List J → J → Prop} (monotone : MonotoneRules rules)
    {judgment : J} (derivation : Derives (UnionRules rules) judgment) :
    ∃ i, Derives (rules i) judgment := by
  refine Derives.least (fun judgment => ∃ i, Derives (rules i) judgment) ?_
    derivation
  intro premises conclusion rule subderivations
  obtain ⟨base, baseRule⟩ := rule
  obtain ⟨upper, baseLeUpper, upperSubderivations⟩ :=
    premises_at_common_stage monotone premises subderivations base
  exact ⟨upper, Derives.node premises conclusion
    (monotone baseLeUpper baseRule) upperSubderivations⟩

/-- Directed-union no-bottom theorem.  The conclusion uses only the finite
support of each derivation and stagewise no-bottom hypotheses. -/
theorem directedUnion_noBottom [SemilatticeSup I]
    {rules : I → List J → J → Prop} (monotone : MonotoneRules rules)
    (bottom : J) (stagewise : ∀ i, NoBottom (rules i) bottom) :
    NoBottom (UnionRules rules) bottom := by
  intro derivation
  obtain ⟨i, staged⟩ := derives_union_exists_stage monotone derivation
  exact stagewise i staged

namespace Canary

/-! ### Positive control: bounded axioms -/

/-- Stage `bound` admits exactly axioms `some n` with `n ≤ bound`; `none` is
bottom. -/
def BoundedAxioms (bound : Nat) : List (Option Nat) → Option Nat → Prop :=
  fun premises conclusion =>
    premises = [] ∧ ∃ n, n ≤ bound ∧ conclusion = some n

theorem boundedAxioms_monotone : MonotoneRules BoundedAxioms := by
  intro i k hik premises conclusion rule
  rcases rule with ⟨rfl, n, hni, rfl⟩
  exact ⟨rfl, n, hni.trans hik, rfl⟩

theorem boundedAxioms_noBottom (bound : Nat) :
    NoBottom (BoundedAxioms bound) none := by
  intro derivation
  exact Derives.least (fun judgment => judgment ≠ none) (by
    intro premises conclusion rule _subderivations
    rcases rule with ⟨_rfl, n, _hn, rfl⟩
    simp) derivation rfl

/-- The directed union of all bounded stages remains bottom-free. -/
theorem boundedAxioms_union_noBottom :
    NoBottom (UnionRules BoundedAxioms) none :=
  directedUnion_noBottom boundedAxioms_monotone none boundedAxioms_noBottom

/-- Positive inhabitance: stage `n` really derives its newest axiom. -/
theorem boundedAxioms_derives (n : Nat) :
    Derives (BoundedAxioms n) (some n) :=
  .node [] (some n) ⟨rfl, n, le_rfl, rfl⟩ (by simp)

/-! ### Negative control: an undirected union -/

/-- The left system supplies `true`; the right system consumes `true` to
derive bottom, but supplies no premise of its own. -/
inductive SplitRules : Bool → List Bool → Bool → Prop where
  | seed : SplitRules false [] true
  | close : SplitRules true [true] false

theorem splitRules_false_noBottom : NoBottom (SplitRules false) false := by
  intro derivation
  have impossible := Derives.least (fun judgment => judgment = true) (by
    intro premises conclusion rule _subderivations
    cases rule
    rfl) derivation
  exact Bool.noConfusion impossible

theorem splitRules_true_derives_nothing (judgment : Bool) :
    ¬ Derives (SplitRules true) judgment := by
  intro derivation
  induction derivation with
  | node premises conclusion rule _subderivations ih =>
      cases rule with
      | close => exact ih true (by simp)

theorem splitRules_true_noBottom : NoBottom (SplitRules true) false :=
  splitRules_true_derives_nothing false

def splitSeed : Derives (UnionRules SplitRules) true :=
  .node [] true ⟨false, SplitRules.seed⟩ (by simp)

/-- The undirected union invents a cross-stage proof of bottom. -/
def splitUnionDerivesBottom : Derives (UnionRules SplitRules) false :=
  .node [true] false ⟨true, SplitRules.close⟩ (by
    intro premise member
    have hp : premise = true := by simpa using member
    subst premise
    exact splitSeed)

/-- The split family is not monotone along the Boolean order, exactly the
hypothesis needed to exclude its cross-stage proof. -/
theorem splitRules_not_monotone : ¬ MonotoneRules SplitRules := by
  intro monotone
  have impossible : SplitRules true [] true :=
    monotone (show false ≤ true by decide) SplitRules.seed
  cases impossible

/-- Negative boundary: stagewise no-bottom alone does not protect an
undirected union. -/
theorem splitUnion_not_noBottom :
    ¬ NoBottom (UnionRules SplitRules) false := by
  intro noBottom
  exact noBottom splitUnionDerivesBottom

end Canary

/-! ## Axiom audit -/

#print axioms premises_at_common_stage
#print axioms derives_union_exists_stage
#print axioms directedUnion_noBottom
#print axioms Canary.boundedAxioms_union_noBottom
#print axioms Canary.splitUnionDerivesBottom
#print axioms Canary.splitRules_not_monotone

end Mettapedia.Logic.FinitaryRuleSystem
