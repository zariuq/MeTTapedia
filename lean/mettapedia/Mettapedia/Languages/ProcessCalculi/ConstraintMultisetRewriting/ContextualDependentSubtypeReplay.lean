import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm

/-!
# Replaying declarative subtyping as a checking certificate

The existing type-normalization derivation provides a well-founded traversal
of the source type. A true cumulative subtype judgment is replayed by the
actual BelowAlgorithm relation, with conversion certificates for equal
domains and recursive certificates for dependent codomains.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSubtypeReplay

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head : Type} {R : Rules Head}

theorem expands {n : Nat} {Γ : Ctx Head n} {first second earlierFirst earlierSecond : Tm Head n}
    (proof : BelowAlgorithm R Γ first second)
    (firstRed : TypedEquality.Reduces R earlierFirst first)
    (secondRed : TypedEquality.Reduces R earlierSecond second) :
    BelowAlgorithm R Γ earlierFirst earlierSecond := by
  cases proof with
  | conv comparison => exact .conv ((Algorithm.expands comparison) firstRed secondRed)
  | universes first second cumulative => exact .universes (firstRed.trans first) (secondRed.trans second) cumulative
  | pi first second domains bodies => exact .pi (firstRed.trans first) (secondRed.trans second) domains bodies
  | sigma first second domains bodies => exact .sigma (firstRed.trans first) (secondRed.trans second) domains bodies

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

def ReplaysBelow (statement : AlgorithmicStatement Head) : Prop :=
  ∀ {n : Nat} (Γ : Ctx Head n) (first compared : Tm Head n),
    (statement = .types Γ first compared ∨ statement = .typesW Γ first compared) →
    CtxFormed S.R Γ → IsType S.R Γ first →
    ∀ second, IsType S.R Γ second → Below S.R Γ first second → BelowAlgorithm S.R Γ first second

variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (complete : AlgorithmicComplete S.R S.roles)

include facts complete in
theorem rigid_replay {n : Nat} {Γ : Ctx Head n} {first second : Tm Head n}
    (shape : RigidShape S.R S.roles Γ first) (formed : CtxFormed S.R Γ)
    (below : Below S.R Γ first second) : BelowAlgorithm S.R Γ first second :=
  .conv (TypeEq.algorithm (S := S) complete (shape.rigid facts formed below) formed)

include facts algebra complete in
theorem algorithmic_replays_below {statement : AlgorithmicStatement Head}
    (proof : Algorithmic S.R S.roles statement) : ReplaysBelow (S := S) statement := by
  induction proof with
  | @types n Γ first first' compared compared' firstRed secondRed firstForm secondForm comparison ih =>
      intro k Δ lhs rhs index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      have reducedBelow : Below S.R Γ _ second := .subTrans firstRed.typeEq.symm.below below
      exact expands (ih Γ _ _ (.inr rfl) formed firstRed.targetType second secondType reducedBelow)
        firstRed.red.reduces .refl
  | @heads n Γ head other level same firstTyped secondTyped universeWitness =>
      intro k Δ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      rcases S.levels.universe_decided head with isUniverse | notUniverse
      · obtain ⟨upper, upperUniverse, equal, cumulative⟩ := (Below.universe_iff facts algebra formed isUniverse).mp below
        obtain ⟨normal, red, normalUniverse⟩ := IsType.universe_whnf facts formed secondType upperUniverse equal
        have sameHead := TypeEq.head_injective facts (equal.symm.trans S.levels red.typeEq) formed
        exact .universes .refl red.red.reduces (algebra.same_right cumulative sameHead)
      · exact rigid_replay facts complete (.head notUniverse) formed below
  | @pi n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro k Δ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      have extended : CtxFormed S.R (.snoc Γ domain) := .snoc formed domainType
      obtain ⟨a, b, equal, domainEqual, bodyBelow⟩ := (Below.pi_iff facts formed firstType).mp below
      rcases IsType.pi_or facts formed secondType with ⟨a', b', red⟩ | impossible
      · obtain ⟨domainChange, bodyChange⟩ := TypeEq.pi_injective facts
          (equal.symm.trans S.levels red.typeEq) formed
        have finalDomain := domainEqual.trans S.levels domainChange
        have finalBody : Below S.R (.snoc Γ domain) body b' :=
          .subTrans bodyBelow (Below.ctxConv bodyChange.below domainEqual.symm)
        exact .pi .refl red.red.reduces (TypeEq.algorithm (S := S) complete finalDomain formed)
          (ihBody (.snoc Γ domain) body body' (.inl rfl) extended
            (Below.isTypes (S := S) finalBody extended).1 b' (Below.isTypes (S := S) finalBody extended).2 finalBody)
      · exact False.elim (impossible a b equal)
  | @sigma n Γ domain domain' body body' domainType domains bodies ihDomain ihBody =>
      intro k Δ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      have extended : CtxFormed S.R (.snoc Γ domain) := .snoc formed domainType
      obtain ⟨a, b, equal, domainBelow, bodyBelow⟩ := (Below.sigma_iff facts formed firstType).mp below
      rcases IsType.sigma_or facts formed secondType with ⟨a', b', red⟩ | impossible
      · obtain ⟨domainChange, bodyChange⟩ := TypeEq.sigma_injective facts
          (equal.symm.trans S.levels red.typeEq) formed
        have finalDomain : Below S.R Γ domain a' := .subTrans domainBelow domainChange.below
        have finalBody : Below S.R (.snoc Γ domain) body b' :=
          .subTrans bodyBelow (Below.ctxBelow bodyChange.below domainBelow)
        exact .sigma .refl red.red.reduces
          (ihDomain Γ domain domain' (.inl rfl) formed domainType a' (Below.isTypes (S := S) finalDomain formed).2 finalDomain)
          (ihBody (.snoc Γ domain) body body' (.inl rfl) extended
            (Below.isTypes (S := S) finalBody extended).1 b' (Below.isTypes (S := S) finalBody extended).2 finalBody)
      · exact False.elim (impossible a b equal)
  | id carriers lefts rights ihCarrier ihLeft ihRight =>
      intro n Γ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      exact rigid_replay facts complete .id formed below
  | inductiveType role type =>
      intro n Γ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      exact rigid_replay facts complete (.inductiveType role) formed below
  | neutralTypes neutral other universeWitness comparison ih =>
      intro n Γ first compared index
      rcases index with index | index <;> cases index
      intro formed firstType second secondType below
      exact rigid_replay facts complete (.neutral neutral) formed below
  | _ =>
      intro n Γ first compared index
      rcases index with index | index <;> cases index

include facts algebra complete in
theorem below_replay {n : Nat} {Γ : Ctx Head n} {first second : Tm Head n}
    (formed : CtxFormed S.R Γ) (firstType : IsType S.R Γ first) (secondType : IsType S.R Γ second)
    (below : Below S.R Γ first second) : BelowAlgorithm S.R Γ first second :=
  algorithmic_replays_below facts algebra complete (complete.types firstType.refl formed)
    Γ first first (.inl rfl) formed firstType second secondType below

end ContextualDependentSubtypeReplay
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
