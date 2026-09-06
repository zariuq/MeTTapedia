import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveSubjectReduction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDelta
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDependencies

/-!
# Pure and transparent-definition preservation instances

The actual Tower universe policy preserves primitive head typing. Together
with the pure conversion boundaries this closes contextual subject reduction
for the root-empty Tower. A second construction supports nonempty transparent
signatures: checked bodies discharge root preservation, while qualified
expansion supplies Pi/Sigma conversion boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {n : Nat}

/-- Installing a signature preserves every refined base derivation. This
is a monotonicity theorem, not a claim that every signature is sound. -/
theorem Typing.includeSignature {base : Rules Head} (signature : Declaration.Signature Head)
    {Γ : Ctx Head n} {term type : Tm Head n} (typing : Typing base Γ term type) :
    Typing (Declaration.extendRules base signature) Γ term type := by
  apply Dependencies.typing_transfer ?_ typing
  intro requirement valid
  cases requirement with
  | constantType name type => exact Declaration.combinedType_of_base base signature valid
  | rootStep k left right => exact Declaration.RootStep.inherited valid
  | _ => exact valid

theorem UniverseRegularity.includeSignature {base : Rules Head}
    (universes : UniverseRegularity base) (signature : Declaration.Signature Head) :
    UniverseRegularity (Declaration.extendRules base signature) where
  head_target := universes.head_target
  join_target := universes.join_target
  cumulative_target := universes.cumulative_target
  universe_typed := universes.universe_typed

theorem HeadPreservation.includeSignature {base : Rules Head}
    (heads : HeadPreservation base) (signature : Declaration.Signature Head) :
    HeadPreservation (Declaration.extendRules base signature) := by
  intro n Γ head next u typed equality
  exact (heads (Γ := Γ) typed equality).includeSignature signature

/-- Only actual transparent bodies and their actual combined declaration
types are checked. The contextual closure is supplied by subject reduction. -/
theorem rootPreservationOfDefinitions (base : Rules Head)
    (signature : Declaration.Signature Head)
    (baseEmpty : base.computation = RootComputation.empty)
    (declaredEmpty : signature.computation = RootComputation.empty)
    (checked : ∀ name body, signature.valueOf? name = some body →
      ∃ declared, (Declaration.extendRules base signature).constantType name = some declared ∧
        Typing (Declaration.extendRules base signature) .nil body declared) :
    RootPreservation (Declaration.extendRules base signature) := by
  intro n Γ source target type context typing equation
  cases equation with
  | inherited inherited => rw [baseEmpty] at inherited; exact inherited.elim
  | @delta name body lookup =>
      obtain ⟨declared, known, bodyTyped⟩ := checked name body lookup
      exact typing.unfoldConstant known bodyTyped
  | declared declared => rw [declaredEmpty] at declared; exact declared.elim

/-- The concrete semantic level equality preserves the concrete Tower head
typing. Successor levels are compared semantically, not assumed identical. -/
theorem towerHeadPreservation : HeadPreservation Tower.rules := by
  intro n Γ head next u typed equality
  cases typed with
  | legacyGround =>
      cases next with
      | legacyGround => exact .headType .legacyGround
      | sort level => exact False.elim equality
  | sort level =>
      cases next with
      | legacyGround => exact False.elim equality
      | sort nextLevel =>
          apply Typing.conv (.headType (Tower.HeadTyping.sort nextLevel))
            (.headType (Tower.HeadTyping.sort (.succ level))) (Tower.IsUniverse.sort _)
          apply Relation.EqvGen.rel
          apply Step.head
          intro valuation
          exact congrArg Nat.succ (equality valuation).symm

theorem towerRootPreservation : RootPreservation Tower.rules := by
  intro n Γ source target type context typing impossible
  exact impossible.elim

/-- No preservation or conversion-boundary hypothesis remains for the
actual root-empty cumulative presentation. -/
theorem Judgment.steps_preserve_tower {Γ : Tower.Ctx n}
    {source target type : Tower.Tm n} (judgment : Judgment Tower.rules Γ source type)
    (steps : ConversionCoherence.StepStar Tower.rules source target) :
    Judgment Tower.rules Γ target type :=
  judgment.steps_preserve towerUniverseRegularity Tower.piConversionBoundary
    (PureConversion.sigmaConversionBoundary Tower.rules rfl Tower.headEq_symmetric)
    towerHeadPreservation towerRootPreservation steps

/-- General beta/delta/contextual preservation for a qualified transparent
signature over a root-empty base. Every premise concerns the base policy,
primitive definitions or conversion expansion; preservation is the conclusion. -/
theorem Judgment.steps_preserve_definitions {base : Rules Head}
    {signature : Declaration.Signature Head}
    (baseEmpty : base.computation = RootComputation.empty)
    (declaredEmpty : signature.computation = RootComputation.empty)
    (universes : UniverseRegularity base) (heads : HeadPreservation base)
    (symmetric : Std.Symm base.headEq)
    (qualification : ConstantExpansion.Qualification (Declaration.extendRules base signature))
    (checked : ∀ name body, signature.valueOf? name = some body →
      ∃ declared, (Declaration.extendRules base signature).constantType name = some declared ∧
        Typing (Declaration.extendRules base signature) .nil body declared)
    {Γ : Ctx Head n} {source target type : Tm Head n}
    (judgment : Judgment (Declaration.extendRules base signature) Γ source type)
    (steps : ConversionCoherence.StepStar (Declaration.extendRules base signature) source target) :
    Judgment (Declaration.extendRules base signature) Γ target type :=
  judgment.steps_preserve (universes.includeSignature signature)
    (qualification.piConversionBoundary symmetric) (qualification.sigmaConversionBoundary symmetric)
    (heads.includeSignature signature)
    (rootPreservationOfDefinitions base signature baseEmpty declaredEmpty checked) steps

#print axioms Typing.includeSignature
#print axioms UniverseRegularity.includeSignature
#print axioms HeadPreservation.includeSignature
#print axioms rootPreservationOfDefinitions
#print axioms towerHeadPreservation
#print axioms towerRootPreservation
#print axioms Judgment.steps_preserve_tower
#print axioms Judgment.steps_preserve_definitions

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
