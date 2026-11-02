import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep

/-!
# Principal-answer transport of conditional occurrence composition

Each constituent guard uses its own equation prefix and physical observation
world. A final answer alone cannot justify an earlier guard. With a principal
interface at both prefixes, the existing inspectable conditional composite
preserves admission under substitution in both directions.

Original output shape and occurrence resource tests remain explicit. This is
conditional sequential composition; atomic replacement under interference
requires its additional observation and mover conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalComposition

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

theorem pair_holds_iff (A : SubstitutionAction T S) (answer : S) (label : O → T)
    (first second : RuleInstance T) (left right : Selection O) (before : Configuration T O)
    (leftObserved rightObserved : List T)
    (leftPrincipal : A.PrincipalOn (left.problem label first before) answer leftObserved)
    (rightPrincipal : A.PrincipalOn
      (right.problem label second (left.result label first before)) answer rightObserved)
    (leftShape : (ShapeTest.ofSelection first left).Holds label)
    (rightShape : (ShapeTest.ofSelection second right).Holds label)
    (leftEnabled : Enabled label before.present left.commit)
    (rightEnabled : Enabled label (left.result label first before).present right.commit)
    (leftArguments : ∀ check ∈ first.checks, ∀ term ∈ check.terms, term ∈ leftObserved)
    (rightArguments : ∀ check ∈ second.checks, ∀ term ∈ check.terms, term ∈ rightObserved)
    (leftValues : ∀ occurrence ∈ before.present, label occurrence ∈ leftObserved)
    (rightValues : ∀ occurrence ∈ (left.result label first before).present,
      label occurrence ∈ rightObserved) :
    (ConditionalComposite.compilePair label first second left right).Holds A label before ↔
      (ConditionalComposite.compilePair (fun occurrence => A.apply answer (label occurrence))
        (first.map (A.apply answer)) (second.map (A.apply answer)) left right).Holds A
          (fun occurrence => A.apply answer (label occurrence))
          (SubstitutionStability.configuration A answer before) := by
  rw [ConditionalComposite.holds_pair_iff, ConditionalComposite.holds_pair_iff,
    SubstitutionStability.result_map]
  exact and_congr
    (PrincipalStep.valid_iff A label leftPrincipal leftShape leftEnabled leftArguments leftValues)
    (PrincipalStep.valid_iff A label rightPrincipal rightShape rightEnabled rightArguments rightValues)

/-- The net equations and physical occurrence result commute with the same
whole-configuration substitution. Admission is the separate theorem above;
this equality alone does not establish equal event traces. -/
theorem pair_result_map (A : SubstitutionAction T S) (answer : S) (label : O → T)
    (first second : RuleInstance T) (left right : Selection O) (before : Configuration T O) :
    (ConditionalComposite.compilePair (fun occurrence => A.apply answer (label occurrence))
      (first.map (A.apply answer)) (second.map (A.apply answer)) left right).result
        (SubstitutionStability.configuration A answer before) =
      SubstitutionStability.configuration A answer
        ((ConditionalComposite.compilePair label first second left right).result before) := by
  apply congrArg₂ Configuration.mk
  · simp only [ConditionalComposite.result, ConditionalComposite.compilePair,
      ConditionalComposite.addedEquations, Selection.equations, RuleInstance.map,
      SubstitutionStability.configuration, SubstitutionAction.applyStore,
      List.map_append, List.zipWith_map_left, List.map_zipWith]
  · rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalComposition
