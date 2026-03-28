import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalComplexity
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ChoicePointTrustTriangleExample

set_option autoImplicit false

/-!
# Practical Resolution: Trust-Triangle Example

A concrete end-to-end example of the practical ethics pipeline:

1. Three candidate actions: harmful disclosure, coercive override, safe escalation.
2. A GenEth principle whose clause favors safe escalation.
3. The pairwise resolver recommends safe escalation.
4. The resolved action bridges into the existing meaning/WM stack.

## References

- M. Anderson & S. L. Anderson, "GenEth," AAAI 2014.
- J. Stenseke, "Computational complexity of ethics," AI Review, 2024.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open scoped Classical

/-- Three candidate actions for the trust-triangle deliberation. -/
inductive TrustTriangleAction where
  | harmfulDisclosure
  | coerciveOverride
  | safeEscalation
  deriving DecidableEq, Repr, Fintype

/-- Two ethically relevant duties in this scenario. -/
inductive TrustTriangleDuty where
  | noHarm
  | respectAutonomy
  deriving DecidableEq, Repr, Fintype

/-- One ethically relevant feature (severity of conflict). -/
inductive TrustTriangleFeature where
  | conflictSeverity
  deriving DecidableEq, Repr, Fintype

/-- Duty profiles for each candidate action.

- harmful disclosure: violates noHarm (−1), respects autonomy (0)
- coercive override: respects noHarm (0), violates autonomy (−1)
- safe escalation: respects both (+1, +1) -/
def trustTriangleProfiles :
    TrustTriangleAction →
    GenEthActionProfile TrustTriangleAction TrustTriangleFeature TrustTriangleDuty
  | .harmfulDisclosure => {
      action := .harmfulDisclosure
      featureDegree := fun _ => 1
      dutyDegree := fun | .noHarm => -1 | .respectAutonomy => 0 }
  | .coerciveOverride => {
      action := .coerciveOverride
      featureDegree := fun _ => 1
      dutyDegree := fun | .noHarm => 0 | .respectAutonomy => -1 }
  | .safeEscalation => {
      action := .safeEscalation
      featureDegree := fun _ => 0
      dutyDegree := fun | .noHarm => 1 | .respectAutonomy => 1 }

/-- The GenEth principle: a single clause requiring both duties to improve. -/
def trustTrianglePrinciple : GenEthPrinciple TrustTriangleDuty :=
  [{ lowerBound := fun | .noHarm => 1 | .respectAutonomy => 1 }]

/-- The candidate set. -/
def trustTriangleCandidates : Finset TrustTriangleAction :=
  Finset.univ

/-- Explicit finite duty domain for the computable resolver path. -/
def trustTriangleDutyDomain : ExplicitFiniteDomain TrustTriangleDuty where
  elems := [.noHarm, .respectAutonomy]
  nodup := by simp
  complete d := by
    cases d <;> simp

/-- Explicit finite candidate set for the computable resolver path. -/
def trustTriangleCandidateSet : ExplicitFiniteSet TrustTriangleAction where
  elems := [.harmfulDisclosure, .coerciveOverride, .safeEscalation]
  nodup := by simp

@[simp] theorem trustTriangleCandidateSet_toFinset :
    trustTriangleCandidateSet.toFinset = trustTriangleCandidates := by
  ext a
  cases a <;> simp [trustTriangleCandidateSet, trustTriangleCandidates,
    ExplicitFiniteSet.toFinset]

/-- Small equivalence used to import the trust-triangle action type into
mathlib's `Primcodable` universe via `Fin 3`. -/
def trustTriangleActionEquivFin : TrustTriangleAction ≃ Fin 3 where
  toFun
    | .harmfulDisclosure => ⟨0, by decide⟩
    | .coerciveOverride => ⟨1, by decide⟩
    | .safeEscalation => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .harmfulDisclosure
    | ⟨1, _⟩ => .coerciveOverride
    | ⟨2, _⟩ => .safeEscalation
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

instance : Primcodable TrustTriangleAction :=
  Primcodable.ofEquiv (Fin 3) trustTriangleActionEquivFin

/-- Safe escalation dominates harmful disclosure: the duty differential has
noHarm = 1 − (−1) = 2 ≥ 1 and respectAutonomy = 1 − 0 = 1 ≥ 1. -/
theorem safeEscalation_beats_harmfulDisclosure :
    actionPreferred trustTrianglePrinciple trustTriangleProfiles
      .safeEscalation .harmfulDisclosure := by
  unfold actionPreferred GenEthPrinciple.Prefers
  refine ⟨_, List.Mem.head _, ?_⟩
  intro d
  cases d <;> simp [GenEthActionProfile.differential, trustTriangleProfiles]

/-- Safe escalation dominates coercive override: noHarm = 1 − 0 = 1 ≥ 1
and respectAutonomy = 1 − (−1) = 2 ≥ 1. -/
theorem safeEscalation_beats_coerciveOverride :
    actionPreferred trustTrianglePrinciple trustTriangleProfiles
      .safeEscalation .coerciveOverride := by
  unfold actionPreferred GenEthPrinciple.Prefers
  refine ⟨_, List.Mem.head _, ?_⟩
  intro d
  cases d <;> simp [GenEthActionProfile.differential, trustTriangleProfiles]

/-- Safe escalation dominates all candidates. -/
theorem safeEscalation_dominates :
    dominatesAll trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates .safeEscalation := by
  constructor
  · simp [trustTriangleCandidates]
  · intro b _ hne
    cases b <;> simp_all <;>
      first
        | exact safeEscalation_beats_harmfulDisclosure
        | exact safeEscalation_beats_coerciveOverride

/-- The resolver recommends safe escalation. -/
theorem trustTriangle_resolver_recommends :
    (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates).status = .recommends :=
  pairwiseResolveJudgment_recommends_of_dominant
    ⟨.safeEscalation, by simp [trustTriangleCandidates], safeEscalation_dominates⟩

/-- The recommended candidate is genuinely dominant. -/
theorem trustTriangle_resolver_chosen_dominates :
    ∃ a, (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates).Recommends a ∧
      dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates a :=
  pairwiseResolveJudgment_chosen_dominates
    ⟨.safeEscalation, by simp [trustTriangleCandidates], safeEscalation_dominates⟩

/-- Harmful disclosure does not even beat safe escalation under the live
GenEth principle. -/
theorem harmfulDisclosure_not_beats_safeEscalation :
    ¬ actionPreferred trustTrianglePrinciple trustTriangleProfiles
        .harmfulDisclosure .safeEscalation := by
  intro hpref
  rcases hpref with ⟨clause, hclause, hsat⟩
  simp [trustTrianglePrinciple] at hclause
  subst hclause
  have hNoHarm := hsat .noHarm
  norm_num [GenEthActionProfile.differential, trustTriangleProfiles] at hNoHarm

/-- Coercive override does not even beat safe escalation under the live
GenEth principle. -/
theorem coerciveOverride_not_beats_safeEscalation :
    ¬ actionPreferred trustTrianglePrinciple trustTriangleProfiles
        .coerciveOverride .safeEscalation := by
  intro hpref
  rcases hpref with ⟨clause, hclause, hsat⟩
  simp [trustTrianglePrinciple] at hclause
  subst hclause
  have hAutonomy := hsat .respectAutonomy
  norm_num [GenEthActionProfile.differential, trustTriangleProfiles] at hAutonomy

/-- The harmful-disclosure action is not dominant in the explicit candidate set. -/
theorem harmfulDisclosure_not_dominates :
    ¬ dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidateSet.toFinset .harmfulDisclosure := by
  intro hdom
  have hSafe :
      TrustTriangleAction.safeEscalation ∈ trustTriangleCandidateSet.toFinset := by
    simp [trustTriangleCandidateSet_toFinset, trustTriangleCandidates]
  exact harmfulDisclosure_not_beats_safeEscalation
    (hdom.2 .safeEscalation hSafe (by decide))

/-- The coercive-override action is not dominant in the explicit candidate set. -/
theorem coerciveOverride_not_dominates :
    ¬ dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidateSet.toFinset .coerciveOverride := by
  intro hdom
  have hSafe :
      TrustTriangleAction.safeEscalation ∈ trustTriangleCandidateSet.toFinset := by
    simp [trustTriangleCandidateSet_toFinset, trustTriangleCandidates]
  exact coerciveOverride_not_beats_safeEscalation
    (hdom.2 .safeEscalation hSafe (by decide))

/-- On the explicit computable seam, only safe escalation satisfies the boolean
dominance checker. -/
theorem trustTriangle_dominatesAllBool_eq_decide_safeEscalation
    (a : TrustTriangleAction) :
    dominatesAllBool trustTriangleDutyDomain trustTriangleCandidateSet
      trustTrianglePrinciple trustTriangleProfiles a =
        decide (a = .safeEscalation) := by
  cases a with
  | harmfulDisclosure =>
      have hfalse :
          dominatesAllBool trustTriangleDutyDomain trustTriangleCandidateSet
            trustTrianglePrinciple trustTriangleProfiles .harmfulDisclosure = false := by
        apply Bool.eq_false_iff.2
        intro htrue
        exact harmfulDisclosure_not_dominates
          ((dominatesAllBool_eq_true_iff _ _ _ _ _).1 htrue)
      simp [hfalse]
  | coerciveOverride =>
      have hfalse :
          dominatesAllBool trustTriangleDutyDomain trustTriangleCandidateSet
            trustTrianglePrinciple trustTriangleProfiles .coerciveOverride = false := by
        apply Bool.eq_false_iff.2
        intro htrue
        exact coerciveOverride_not_dominates
          ((dominatesAllBool_eq_true_iff _ _ _ _ _).1 htrue)
      simp [hfalse]
  | safeEscalation =>
      have htrue :
          dominatesAllBool trustTriangleDutyDomain trustTriangleCandidateSet
            trustTrianglePrinciple trustTriangleProfiles .safeEscalation = true := by
        apply (dominatesAllBool_eq_true_iff _ _ _ _ _).2
        simpa [trustTriangleCandidateSet_toFinset] using safeEscalation_dominates
      simp [htrue]

/-- Concrete primitive-recursive dominance predicate for the live
trust-triangle example. -/
theorem trustTriangle_dominatesAllBool_primrec :
    Primrec
      (fun a : TrustTriangleAction =>
        dominatesAllBool trustTriangleDutyDomain trustTriangleCandidateSet
          trustTrianglePrinciple trustTriangleProfiles a) := by
  have hsafepred : PrimrecPred (fun a : TrustTriangleAction => a = .safeEscalation) :=
    Primrec.eq.comp Primrec.id (Primrec.const TrustTriangleAction.safeEscalation)
  refine Primrec.of_eq (PrimrecPred.decide hsafepred) ?_
  intro a
  symm
  exact trustTriangle_dominatesAllBool_eq_decide_safeEscalation a

/-- The explicit dominant-candidate search is genuinely computable on the live
trust-triangle example, not just schematically. -/
theorem trustTriangle_searchDominantCandidate_computable :
    Computable
      (fun search : List TrustTriangleAction =>
        searchDominantCandidate trustTriangleDutyDomain trustTriangleCandidateSet
          trustTrianglePrinciple trustTriangleProfiles search) :=
  searchDominantCandidate_computable trustTriangle_dominatesAllBool_primrec

/-- The computable resolver agrees with the semantic result on the trust
triangle: it recommends safe escalation. -/
theorem trustTriangle_computableResolver_recommends :
    (pairwiseResolveJudgmentComputable trustTriangleDutyDomain trustTriangleCandidateSet
      trustTrianglePrinciple trustTriangleProfiles).status = .recommends := by
  apply pairwiseResolveJudgmentComputable_recommends_of_dominant
  refine ⟨.safeEscalation, ?_, ?_⟩
  · simp [trustTriangleCandidates]
  · simpa [trustTriangleCandidateSet_toFinset] using safeEscalation_dominates

/-- The honest comparison count for this example: 3 candidates × 3 × 1 clause × 2 duties = 18. -/
theorem trustTriangle_comparisonCount :
    resolverComparisonCount 3 1 2 = 18 := by
  simp [resolverComparisonCount]

/-- The comparison count is at most M⁴ = 3⁴ = 81. -/
theorem trustTriangle_comparisonCount_le_pow4 :
    resolverComparisonCount 3 1 2 ≤ (max 3 (max 1 2)) ^ 4 :=
  resolverComparisonCount_le_pow4 3 1 2

/-- End-to-end capstone: the resolver recommends, the recommended candidate
is dominant, and the comparison count is explicitly bounded. -/
theorem trustTriangle_practical_ethics_capstone :
    (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates).status = .recommends ∧
    (pairwiseResolveJudgmentComputable trustTriangleDutyDomain trustTriangleCandidateSet
      trustTrianglePrinciple trustTriangleProfiles).status = .recommends ∧
    (∃ a, (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates).Recommends a ∧
      dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates a) ∧
    resolverComparisonCount 3 1 2 ≤ 81 :=
  ⟨trustTriangle_resolver_recommends,
   trustTriangle_computableResolver_recommends,
   trustTriangle_resolver_chosen_dominates,
   trustTriangle_comparisonCount_le_pow4⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
