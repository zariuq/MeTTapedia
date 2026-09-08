import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRestriction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationExamples

/-!
# Retained proofs and retained computation have different dependencies

A restriction of the existing qualified transparent signature retains the
second type alias and its unfolding equation, but omits the declaration of
the first alias produced by that equation. The source judgment survives and
every restricted judgment reflects to the source. Nevertheless the retained
step leaves the refined typing judgment.

Adding the missing body declaration repairs this example. The repaired
restriction has qualified conversion and preserves arbitrary contextual
runs, not just the displayed unfolding. Both restrictions genuinely remove
other source declarations and computation. This separates proof replay from
qualification of an independently executing smaller kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.RestrictionPreservation

open Dependencies Declaration
open Dependencies.Examples (aliasName extraName)
open ConstantExpansion.Examples (secondAliasName signature rules)

variable {n : Nat}

/-- The optional entry supplies the declaration required by the reduct,
not by typing the original constant at its declared universe. -/
def manifest (retainBody : Bool) : List (Requirement Tower.Head) :=
  [.constantType secondAliasName (sortTm Tower.zero),
   .rootStep 0 (.const secondAliasName) (.const aliasName)] ++
    if retainBody then [.constantType aliasName (sortTm Tower.zero)] else []

def selected (retainBody : Bool) : Rules Tower.Head :=
  restrict rules (manifest retainBody)

theorem manifest_valid (retainBody : Bool) : HoldsAll rules (manifest retainBody) := by
  have first : rules.constantType secondAliasName = some (sortTm Tower.zero) := by decide
  have second : rules.constantType aliasName = some (sortTm Tower.zero) := by decide
  have body : signature.valueOf? secondAliasName = some (.const aliasName) := by decide
  cases retainBody <;>
    simp only [manifest, Bool.false_eq_true, if_false, List.append_nil, if_true,
      List.cons_append, List.nil_append, holdsAll_cons, holdsAll_nil, and_true,
      Requirement.Holds]
  · exact ⟨first, RootStep.delta (base := Tower.rules) body⟩
  · exact ⟨first, RootStep.delta (base := Tower.rules) body, second⟩

theorem selected_lookup (retainBody : Bool) :
    (selected retainBody).constantType secondAliasName = some (sortTm Tower.zero) := by
  have first : rules.constantType secondAliasName = some (sortTm Tower.zero) := by decide
  change (if secondAliasName ∈ constantNames (manifest retainBody) then
    rules.constantType secondAliasName else none) = some (sortTm Tower.zero)
  rw [if_pos (constantName_mem (type := sortTm Tower.zero) (by simp [manifest]))]
  exact first

theorem omitted_body_lookup : (selected false).constantType aliasName = none := by
  simp [selected, restrict, constantNames, manifest, aliasName, secondAliasName]

theorem retained_body_lookup :
    (selected true).constantType aliasName = some (sortTm Tower.zero) := by
  have second : rules.constantType aliasName = some (sortTm Tower.zero) := by decide
  change (if aliasName ∈ constantNames (manifest true) then
    rules.constantType aliasName else none) = some (sortTm Tower.zero)
  rw [if_pos (constantName_mem (type := sortTm Tower.zero) (by simp [manifest]))]
  exact second

/-- This is the identical admitted source term for either manifest. -/
theorem original_judgment (retainBody : Bool) (context : Tower.Ctx n)
    (formed : ContextFormation (selected retainBody) context) :
    Judgment (selected retainBody) context (.const secondAliasName) (sortTm Tower.zero) :=
  ⟨formed, .const (selected_lookup retainBody) (.headType (.sort _)) (.sort _)⟩

theorem retained_step (retainBody : Bool) :
    (selected retainBody).computation.step
      (.const secondAliasName : Tower.Tm n) (.const aliasName) := by
  exact RetainedRoot.rename Fin.elim0
    (RetainedRoot.seed (n := 0) (left := .const secondAliasName)
      (right := .const aliasName) (by simp [manifest]))

theorem omitted_body_untypable {context : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing (selected false) context (.const aliasName) type := by
  intro typing
  obtain ⟨_, _, lookup, _, _⟩ := typing.constFormation
  rw [omitted_body_lookup] at lookup
  cases lookup

/-- Neither source validity of the manifest nor global no-invention of
restricted judgments certifies the retained reduction. -/
theorem retained_proof_not_preservation :
    HoldsAll rules (manifest false) ∧
      Judgment (selected false) (.nil : Tower.Ctx 0)
        (.const secondAliasName) (sortTm Tower.zero) ∧
      ¬ RootPreservation (selected false) := by
  refine ⟨manifest_valid false, original_judgment false .nil .nil, ?_⟩
  intro preserves
  exact omitted_body_untypable
    (preserves .nil (original_judgment false .nil .nil).typing (retained_step false))

/-- A conversion derivation can use the retained equation under an erasing
lambda, although its final type is unchanged. Formation of the endpoints
does not demand formation of every intermediate conversion term. -/
def conversionExcursion :
    Conv (selected false).headEq (sortTm Tower.zero : Tower.Tm 0)
      (sortTm Tower.zero) (selected false).computation :=
  .trans _ _ _
    (.symm _ _ (.rel _ _ (.betaPi (sortTm Tower.zero) (.const secondAliasName))))
    (.trans _ _ _
      (.rel _ _ (.congAppArg (.root (retained_step false))))
      (.rel _ _ (.betaPi (sortTm Tower.zero) (.const aliasName))))

/-- The failing manifest can replay a real typing proof that uses its root,
not only a proof that ignores every retained computation rule. -/
theorem retained_conversion_judgment :
    Judgment (selected false) (.nil : Tower.Ctx 0)
      (.const secondAliasName) (sortTm Tower.zero) :=
  ⟨.nil, .conv (original_judgment false .nil .nil).typing
    (.headType (.sort _)) (.sort _) conversionExcursion⟩

/-- All the usual reflection guarantees still hold in the failing example. -/
theorem judgment_reflects (retainBody : Bool) {context : Tower.Ctx n}
    {term type : Tower.Tm n} (judgment : Judgment (selected retainBody) context term type) :
    Judgment rules context term type :=
  restrict_judgment_reflects (manifest_valid retainBody) judgment

private theorem retained_shape (retainBody : Bool) {left right : Tower.Tm n}
    (step : RetainedRoot (manifest retainBody) left right) :
    left = .const secondAliasName ∧ right = .const aliasName := by
  induction step with
  | seed member =>
      cases retainBody <;>
        simp only [manifest, Bool.false_eq_true, if_false, List.append_nil, if_true,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      · rcases member with member | member <;> cases member
        exact ⟨rfl, rfl⟩
      · rcases member with member | member | member <;> cases member
        exact ⟨rfl, rfl⟩
  | rename rho _ ih =>
      rcases ih with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | substitute sigma _ ih =>
      rcases ih with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

def expandedBodies : ConstantExpansion.Bodies Tower.Head :=
  fun name => if name = secondAliasName then .const aliasName else .const name

/-- Both manifestations have the same well-behaved conversion relation;
conversion qualification does not make an omitted constant declaration exist. -/
def conversionQualification (retainBody : Bool) :
    ConstantExpansion.Qualification (selected retainBody) where
  bodies := expandedBodies
  constants := by
    intro name
    by_cases same : name = secondAliasName
    · subst name
      change Conv Tower.HeadEq (.const secondAliasName) (.const aliasName)
        (selected retainBody).computation
      exact .rel _ _ (.root (retained_step retainBody))
    · simp only [expandedBodies, if_neg same]
      exact .refl _
  roots := by
    intro n left right step
    obtain ⟨rfl, rfl⟩ := retained_shape retainBody step
    have same : ConstantExpansion.expand expandedBodies (.const secondAliasName : Tower.Tm n) =
        ConstantExpansion.expand expandedBodies (.const aliasName) := by
      simp [ConstantExpansion.expand, expandedBodies, aliasName, secondAliasName,
        liftClosed, rename]
    rw [same]
    exact .refl _

/-- Retaining the produced declaration supplies the actual body typing,
which can replay any conversion/cumulativity tail on the redex. -/
theorem repaired_root_preservation : RootPreservation (selected true) := by
  intro n context source target type formed typing step
  obtain ⟨rfl, rfl⟩ := retained_shape true step
  have body : Typing (selected true) (.nil : Tower.Ctx 0)
      (.const aliasName) (sortTm Tower.zero) :=
    .const retained_body_lookup (.headType (.sort _)) (.sort _)
  exact typing.unfoldConstant (selected_lookup true) body

private theorem include_pure (retainBody : Bool) (requirement : Requirement Tower.Head)
    (valid : requirement.Holds Tower.rules) : requirement.Holds (selected retainBody) := by
  cases requirement with
  | constantType name type => cases valid
  | rootStep k left right => exact valid.elim
  | _ => exact valid

/-- The repaired smaller package preserves arbitrary finite contextual
computation, with its original dependent displayed type. -/
theorem repaired_runs_preserve {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (judgment : Judgment (selected true) context source type)
    (steps : ConversionCoherence.StepStar (selected true) source target) :
    Judgment (selected true) context target type := by
  apply judgment.steps_preserve
    (restrict_universeRegularity rules (manifest true)
      (towerUniverseRegularity.includeSignature signature))
    ((conversionQualification true).piConversionBoundary Tower.headEq_symmetric)
    ((conversionQualification true).sigmaConversionBoundary Tower.headEq_symmetric)
    ?_ repaired_root_preservation steps
  intro n context head next u typed equality
  exact typing_transfer (include_pure true) (towerHeadPreservation (Γ := context) typed equality)

/-- The repair keeps a genuinely smaller package, not the full source under
a new name. In particular the polymorphic identity declaration is omitted. -/
theorem repair_removes_unused :
    rules.constantType extraName =
      some (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) ∧
      (selected true).constantType extraName = none := by
  constructor
  · decide
  · simp [selected, restrict, constantNames, manifest, extraName, aliasName, secondAliasName]

/-- The first alias's own unfolding is still removed after the repair;
restoring its declaration did not reinstall its computation. -/
theorem repair_removes_unused_computation :
    rules.computation.step (.const aliasName : Tower.Tm 0) (.head .legacyGround) ∧
      ¬ (selected true).computation.step
        (.const aliasName : Tower.Tm 0) (.head .legacyGround) := by
  refine ⟨RootStep.delta (base := Tower.rules) (signature := signature)
    (name := aliasName) (value := .head .legacyGround) (by decide), ?_⟩
  intro retained
  have impossible := (retained_shape true retained).1
  exact (by decide : (Tm.const aliasName : Tower.Tm 0) ≠ .const secondAliasName) impossible

theorem repaired_unfolding :
    Judgment (selected true) (.nil : Tower.Ctx 0) (.const aliasName) (sortTm Tower.zero) :=
  repaired_runs_preserve (original_judgment true .nil .nil)
    (.tail .refl (.root (retained_step true)))

/-- The original source already has contextual preservation. The failure
above is introduced by the restriction, not inherited from an unsafe source. -/
theorem source_runs_preserve {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (judgment : Judgment rules context source type)
    (steps : ConversionCoherence.StepStar rules source target) :
    Judgment rules context target type :=
  PreservationExamples.actual_runs_preserve judgment steps

#print axioms retained_proof_not_preservation
#print axioms conversionExcursion
#print axioms retained_conversion_judgment
#print axioms judgment_reflects
#print axioms conversionQualification
#print axioms repaired_root_preservation
#print axioms repaired_runs_preserve
#print axioms repair_removes_unused
#print axioms repair_removes_unused_computation
#print axioms repaired_unfolding

end FormationSensitive.RestrictionPreservation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
