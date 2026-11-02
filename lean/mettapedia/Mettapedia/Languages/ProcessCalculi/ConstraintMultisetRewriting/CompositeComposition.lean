import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalComposition

/-!
# Associative conditional composition at the configuration observation

Occurrence preconditions and unresolved equations compose as data. A later
check is transported through the earlier equations and store effect, while
earlier checks retain their own prefix. The resulting admission condition is
equivalent to sequential admission, and the resulting configuration agrees.

Associativity concerns that admission condition and final configuration. It
does not identify event traces or justify atomic replacement under interference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

namespace ConditionalComposite

/-- Total composition of store effects, used only for transporting a check's
world. This record is not advertised as an enabled atomic commit. -/
def transportEffect (first second : Commit O T) : Commit O T :=
  ⟨first.taken ∪ second.taken, ∅, (first.made \ second.taken) ∪ second.made, []⟩

theorem fire_transportEffect (world : Finset O) (first second : Commit O T) :
    fire world (transportEffect first second) = fire (fire world first) second := by
  ext o
  simp only [fire, transportEffect, Finset.mem_union, Finset.mem_sdiff]
  tauto

def transportCheck (first : ConditionalComposite T O) (check : TransportedCheck T O) :
    TransportedCheck T O :=
  ⟨first.equations ++ check.equations, transportEffect first.effect check.effect, check.check⟩

theorem transportCheck_holds (A : SubstitutionAction T S) (label : O → T)
    (first : ConditionalComposite T O) (check : TransportedCheck T O)
    (before : Configuration T O) :
    (transportCheck first check).Holds A label before ↔ check.Holds A label (first.result before) := by
  simp only [transportCheck, TransportedCheck.Holds, result, List.append_assoc, fire_transportEffect]

def compose (label : O → T) (first second : ConditionalComposite T O) : ConditionalComposite T O :=
  ⟨first.resources.and (second.resources.before label first.effect),
    first.effect.compose second.effect, first.equations ++ second.equations,
    first.shapes ++ second.shapes, first.checks ++ second.checks.map (transportCheck first)⟩

/-- Resource correctness is proved for constructors of conditional composites;
it is not an assumed equation between the composite and its source execution. -/
def ResourceSound (label : O → T) (composite : ConditionalComposite T O) : Prop :=
  ∀ world, composite.resources.Holds label world → Enabled label world composite.effect

theorem compilePair_resourceSound (label : O → T) (first second : RuleInstance T)
    (left right : Selection O) : ResourceSound label (compilePair label first second left right) := by
  intro world admitted
  obtain ⟨one, two⟩ :=
    (CommitPrecondition.sequential_holds_iff label left.commit right.commit world).mp admitted
  exact Commit.compose_enabled one two

theorem resourceSound_compose (label : O → T) {first second : ConditionalComposite T O}
    (firstSound : ResourceSound label first) (secondSound : ResourceSound label second) :
    ResourceSound label (compose label first second) := by
  intro world admitted
  obtain ⟨one, transported⟩ := (CommitPrecondition.and_holds_iff _ _ label world).mp admitted
  have firstEnabled := firstSound world one
  have two := (CommitPrecondition.before_holds_iff second.resources firstEnabled).mp transported
  exact Commit.compose_enabled firstEnabled (secondSound _ two)

theorem holds_compose_iff (A : SubstitutionAction T S) (label : O → T)
    {first second : ConditionalComposite T O} (firstSound : ResourceSound label first)
    (before : Configuration T O) :
    (compose label first second).Holds A label before ↔
      first.Holds A label before ∧ second.Holds A label (first.result before) := by
  have checksSplit :
      (∀ check ∈ (compose label first second).checks, check.Holds A label before) ↔
        (∀ check ∈ first.checks, check.Holds A label before) ∧
        ∀ check ∈ second.checks, check.Holds A label (first.result before) := by
    simp only [compose, List.forall_mem_append, List.forall_mem_map, transportCheck_holds]
  constructor
  · rintro ⟨shapes, resources, consistent, checks⟩
    obtain ⟨leftShapes, rightShapes⟩ := (List.forall_mem_append).mp shapes
    obtain ⟨leftResources, transported⟩ :=
      (CommitPrecondition.and_holds_iff _ _ label before.present).mp resources
    have rightResources := (CommitPrecondition.before_holds_iff second.resources
      (firstSound before.present leftResources)).mp transported
    have rightConsistent : A.Consistent ((first.result before).equations ++ second.equations) := by
      simpa only [compose, result, List.append_assoc] using consistent
    have leftConsistent : A.Consistent (before.equations ++ first.equations) := by
      obtain ⟨σ, solved⟩ := rightConsistent
      exact ⟨σ, (A.models_append _ _ _).mp solved |>.1⟩
    obtain ⟨leftChecks, rightChecks⟩ := checksSplit.mp checks
    exact ⟨⟨leftShapes, leftResources, leftConsistent, leftChecks⟩,
      ⟨rightShapes, rightResources, rightConsistent, rightChecks⟩⟩
  · rintro ⟨⟨leftShapes, leftResources, leftConsistent, leftChecks⟩,
      ⟨rightShapes, rightResources, rightConsistent, rightChecks⟩⟩
    refine ⟨List.forall_mem_append.mpr ⟨leftShapes, rightShapes⟩,
      (CommitPrecondition.and_holds_iff _ _ label before.present).mpr ⟨leftResources, ?_⟩,
      ?_, checksSplit.mpr ⟨leftChecks, rightChecks⟩⟩
    · exact (CommitPrecondition.before_holds_iff second.resources
        (firstSound before.present leftResources)).mpr rightResources
    · simpa only [compose, result, List.append_assoc] using rightConsistent

theorem result_compose (A : SubstitutionAction T S) (label : O → T)
    {first second : ConditionalComposite T O} (firstSound : ResourceSound label first)
    (secondSound : ResourceSound label second) (before : Configuration T O)
    (admitted : (compose label first second).Holds A label before) :
    (compose label first second).result before = second.result (first.result before) := by
  obtain ⟨one, two⟩ := (holds_compose_iff A label firstSound before).mp admitted
  apply congrArg₂ Configuration.mk
  · simp only [compose, result, List.append_assoc]
  · exact Commit.compose_fire (firstSound _ one.2.1) (secondSound _ two.2.1)

/-- Grouping preserves the conditional interface, including every original
check prefix. No normalization erases checks using vanished variables. -/
theorem holds_associative (A : SubstitutionAction T S) (label : O → T)
    {first second third : ConditionalComposite T O} (firstSound : ResourceSound label first)
    (secondSound : ResourceSound label second) (before : Configuration T O) :
    (compose label (compose label first second) third).Holds A label before ↔
      (compose label first (compose label second third)).Holds A label before := by
  have firstSecondSound := resourceSound_compose label firstSound secondSound
  constructor
  · intro admitted
    obtain ⟨firstSecond, thirdHolds⟩ :=
      (holds_compose_iff A label firstSecondSound before).mp admitted
    obtain ⟨firstHolds, secondHolds⟩ := (holds_compose_iff A label firstSound before).mp firstSecond
    rw [result_compose A label firstSound secondSound before firstSecond] at thirdHolds
    apply (holds_compose_iff A label firstSound before).mpr
    exact ⟨firstHolds, (holds_compose_iff A label secondSound (first.result before)).mpr
      ⟨secondHolds, thirdHolds⟩⟩
  · intro admitted
    obtain ⟨firstHolds, secondThird⟩ := (holds_compose_iff A label firstSound before).mp admitted
    obtain ⟨secondHolds, thirdHolds⟩ :=
      (holds_compose_iff A label secondSound (first.result before)).mp secondThird
    have firstSecond := (holds_compose_iff A label firstSound before).mpr ⟨firstHolds, secondHolds⟩
    rw [← result_compose A label firstSound secondSound before firstSecond] at thirdHolds
    exact (holds_compose_iff A label firstSecondSound before).mpr ⟨firstSecond, thirdHolds⟩

theorem result_associative (A : SubstitutionAction T S) (label : O → T)
    {first second third : ConditionalComposite T O} (firstSound : ResourceSound label first)
    (secondSound : ResourceSound label second) (thirdSound : ResourceSound label third)
    (before : Configuration T O)
    (admitted : (compose label (compose label first second) third).Holds A label before) :
    (compose label (compose label first second) third).result before =
      (compose label first (compose label second third)).result before := by
  have firstSecondSound := resourceSound_compose label firstSound secondSound
  have secondThirdSound := resourceSound_compose label secondSound thirdSound
  obtain ⟨firstSecond, thirdHolds⟩ :=
    (holds_compose_iff A label firstSecondSound before).mp admitted
  obtain ⟨firstHolds, secondHolds⟩ := (holds_compose_iff A label firstSound before).mp firstSecond
  have regrouped := (holds_associative A label firstSound secondSound before).mp admitted
  obtain ⟨_, secondThird⟩ := (holds_compose_iff A label firstSound before).mp regrouped
  rw [result_compose A label firstSecondSound thirdSound before admitted,
    result_compose A label firstSound secondSound before firstSecond,
    result_compose A label firstSound secondThirdSound before regrouped,
    result_compose A label secondSound thirdSound (first.result before) secondThird]

end ConditionalComposite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
