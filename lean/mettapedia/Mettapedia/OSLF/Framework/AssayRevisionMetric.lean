import Mettapedia.OSLF.Framework.LogicalMetric
import Mettapedia.OSLF.Framework.StructuralInspectionAssays

/-!
# Confinement of finite revision walks and retained assay certificates

Finite walks of revisions smaller than one fixed dyadic radius remain in
that radius. Agreement therefore retains all earlier complete observation
readouts. For authored sequences of structural hypotheses these are actual
Boolean tests, and satisfaction certificates transport at the retained
stages. Testing prices remain the separately computed inspection accounts.

The stages here are declared structural tests. Identifying them with a
particular greatest-fixed-point unfolding sequence needs its own comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.AssayRevision

open LogicalMetric

attribute [local instance] PiNat.dist

universe u v

variable {X : Type u} {Answers : Nat → Type v}

theorem finite_walk_confined (scheme : ObservationScheme X Answers)
    (walk : Nat → X) (depth count : Nat)
    (small : ∀ position < count,
      scheme.distance (walk position) (walk (position + 1)) < (1 / 2 : ℝ) ^ depth) :
    scheme.distance (walk 0) (walk count) < (1 / 2 : ℝ) ^ depth := by
  induction count with
  | zero => rw [scheme.distance_self]; positivity
  | succ count inductionHypothesis =>
      have previous := inductionHypothesis (fun position bound =>
        small position (Nat.lt_succ_of_lt bound))
      exact lt_of_le_of_lt (scheme.distance_triangle_nonarch (walk 0) (walk count) (walk (count + 1)))
        (max_lt previous (small count (Nat.lt_succ_self count)))

theorem earlier_answer_preserved (scheme : ObservationScheme X Answers)
    {first second : X} {depth stage : Nat}
    (close : scheme.distance first second < (1 / 2 : ℝ) ^ depth) (earlier : stage ≤ depth) :
    scheme.satisfies stage first = scheme.satisfies stage second :=
  PiNat.apply_eq_of_dist_lt close earlier

theorem finite_walk_answers_preserved (scheme : ObservationScheme X Answers)
    (walk : Nat → X) (depth count : Nat)
    (small : ∀ position < count,
      scheme.distance (walk position) (walk (position + 1)) < (1 / 2 : ℝ) ^ depth)
    {stage : Nat} (earlier : stage ≤ depth) :
    scheme.satisfies stage (walk 0) = scheme.satisfies stage (walk count) :=
  earlier_answer_preserved scheme (finite_walk_confined scheme walk depth count small) earlier

open InstrumentObservations

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]

abbrev Hypothesis (Symbols : Type u) (arity : Symbols → Nat) := Nat → Formula Symbols arity

def structuralScheme :
    ObservationScheme (Hypothesis Symbols arity) (fun _ => Tree Symbols arity → Bool) where
  satisfies stage hypothesis := evaluate (hypothesis stage)

theorem retained_structural_answer {first second : Hypothesis Symbols arity}
    {depth stage : Nat}
    (close : structuralScheme.distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (tree : Tree Symbols arity) :
    evaluate (first stage) tree = evaluate (second stage) tree :=
  congrFun (earlier_answer_preserved structuralScheme close earlier) tree

theorem retained_structural_satisfaction {first second : Hypothesis Symbols arity}
    {depth stage : Nat}
    (close : structuralScheme.distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (tree : Tree Symbols arity) :
    Satisfies (first stage) tree ↔ Satisfies (second stage) tree := by
  rw [← evaluate_iff (first stage) tree, ← evaluate_iff (second stage) tree,
    retained_structural_answer close earlier tree]

theorem retained_structural_certificate {first second : Hypothesis Symbols arity}
    {depth stage : Nat}
    (close : structuralScheme.distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (branch : Mettapedia.GSLT.Causality.ComplementaryAssay.Verdict)
    (tree : Tree Symbols arity) :
    TestCertificate (first stage) branch tree ↔ TestCertificate (second stage) branch tree := by
  cases branch with
  | confirm => exact retained_structural_satisfaction close earlier tree
  | refute => exact not_congr (retained_structural_satisfaction close earlier tree)

end Mettapedia.OSLF.Framework.AssayRevision
