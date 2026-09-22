import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSubjectReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDelta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependencies

/-! # Signature transport and qualified definition preservation -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
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

/-- Refinement formation premises survive a source-prefix extension as well
as raw typing. Existing selected declarations and roots are retained. -/
theorem Typing.monoSignature {base : Rules Head} {prior later : Declaration.Signature Head}
    (extension : prior.Extends later) {context : Ctx Head n} {term type : Tm Head n}
    (typed : Typing (Declaration.extendRules base prior) context term type) :
    Typing (Declaration.extendRules base later) context term type := by
  apply Dependencies.typing_transfer ?_ typed
  intro requirement valid
  cases requirement with
  | constantType name type => exact extension.preservesCombinedType base valid
  | rootStep scope left right =>
      cases valid with
      | inherited root => exact Declaration.RootStep.inherited root
      | delta lookup => exact Declaration.RootStep.delta (extension.valueOf lookup)
      | declared root => exact Declaration.RootStep.declared (extension.computation root)
  | _ => exact valid

theorem UniverseRegularity.includeSignature {base : Rules Head}
    (universes : UniverseRegularity base) (signature : Declaration.Signature Head) :
    UniverseRegularity (Declaration.extendRules base signature) where
  head_target := universes.head_target
  join_target := universes.join_target
  cumulative_target := universes.cumulative_target
  universe_typed := universes.universe_typed

/-- Context formation transports through the same signature inclusion as
its type derivations; no extra declaration-soundness premise is needed. -/
theorem ContextFormation.includeSignature {base : Rules Head} {context : Ctx Head n}
    (formed : ContextFormation base context) (signature : Declaration.Signature Head) :
    ContextFormation (Declaration.extendRules base signature) context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typed.includeSignature signature) universeWitness

theorem Judgment.includeSignature {base : Rules Head}
    {context : Ctx Head n} {term type : Tm Head n}
    (judgment : Judgment base context term type) (signature : Declaration.Signature Head) :
    Judgment (Declaration.extendRules base signature) context term type :=
  ⟨judgment.context.includeSignature signature, judgment.typing.includeSignature signature⟩

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


end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
