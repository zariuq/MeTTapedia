import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Lifting
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationFundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PurePackages

/-!
# Soundness of candidate derivations in the set interpretation, through elaboration

The set interpretation gives values to annotated terms, and every derivation of the annotated
judgment holds in every set model of its package (`CDerivable.sound`, in
`TowerInterpretation.Soundness`). A candidate derivation carries no domains; it is interpreted
through its elaboration.

**Candidate derivations, through elaboration.** For an annotation with the facts the lifting
needs (`LiftingFacts`), every candidate derivation over a formed context is the erasure of an
annotated derivation over a formed annotated context (`Derivable.elaborates`), and that
annotated statement holds in every set model of the annotation
(`Derivable.sound_elaborated`). So every such candidate statement lies in the annotated
fragment (`Derivable.inAnnotatedImage`). A closed candidate type without abstractions whose
annotation is empty in a set model has no closed candidate inhabitant
(`Derivable.no_closed_inhabitant`).

**Rigid packages** (`Derivable.sound_rigid`): a package without root computation whose declared
types have no abstraction has the lifting facts (`LiftingFacts.ofRigid`), so every derivation
over a formed context is sound through its elaboration, in every set model of its annotation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality

/-- The context of a candidate statement is formed. -/
def Statement.CtxFormed {Head : Type} (R : Rules Head) : Statement Head → Prop
  | .typing Γ _ _ => Normalization.CtxFormed R Γ
  | .equality Γ _ _ _ => Normalization.CtxFormed R Γ
  | .sub Γ _ _ => Normalization.CtxFormed R Γ

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated

universe u

variable {Head : Type} {R : Rules Head} {P : ChurchRules R} {heads : Head → ZFSet.{u}}
  {consts : DeclName → ZFSet.{u}}

/-! ## Candidate derivations, through elaboration -/

section Elaboration

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : Normalization.LevelModel R L)
  (facts : LiftingFacts P)
include levels facts

/-- **Every candidate derivation over a formed context elaborates**: it is the erasure of an
annotated derivation over a formed annotated context. -/
theorem Derivable.elaborates {statement : Statement Head} (derivation : Derivable R statement)
    (formed : statement.CtxFormed R) :
    ∃ s : CStatement Head, s.CtxFormed P ∧ CDerivable P s ∧ s.erase = statement := by
  cases statement with
  | typing Γ t A =>
      obtain ⟨Γ', formed', rfl⟩ := lift_ctxFormed levels facts formed
      obtain ⟨t', A', rfl, rfl, typing⟩ := lifts levels facts derivation formed' rfl
      exact ⟨.typing Γ' t' A', formed', typing, rfl⟩
  | equality Γ a b A =>
      obtain ⟨Γ', formed', rfl⟩ := lift_ctxFormed levels facts formed
      obtain ⟨a', b', A', rfl, rfl, rfl, equal⟩ := lifts levels facts derivation formed' rfl
      exact ⟨.equality Γ' a' b' A', formed', equal, rfl⟩
  | sub Γ A B =>
      obtain ⟨Γ', formed', rfl⟩ := lift_ctxFormed levels facts formed
      obtain ⟨A', B', rfl, rfl, below⟩ := lifts levels facts derivation formed' rfl
      exact ⟨.sub Γ' A' B', formed', below, rfl⟩

/-- **Soundness of every candidate derivation over a formed context, through elaboration**: it
is the erasure of an annotated derivation whose statement holds in every set model of the
annotation. -/
theorem Derivable.sound_elaborated (model : SetModel heads consts P)
    {statement : Statement Head} (derivation : Derivable R statement)
    (formed : statement.CtxFormed R) :
    ∃ s : CStatement Head, CDerivable P s ∧ s.erase = statement ∧
      Holds heads consts s := by
  obtain ⟨s, -, d, e⟩ := Derivable.elaborates levels facts derivation formed
  exact ⟨s, d, e, CDerivable.sound model d⟩

/-- **Every candidate derivation over a formed context lies in the annotated fragment**: it is
the erasure of its elaboration. -/
theorem Derivable.inAnnotatedImage {statement : Statement Head}
    (derivation : Derivable R statement) (formed : statement.CtxFormed R) :
    InAnnotatedImage P statement := by
  obtain ⟨s, -, d, e⟩ := Derivable.elaborates levels facts derivation formed
  exact ⟨s, d, e⟩

/-- **Relative consistency through elaboration.** A closed candidate type without abstractions
whose only annotation has an empty value in a set model of the annotation has no closed
candidate inhabitant: a typing would elaborate to a typing at that annotation, which holds in
the model. -/
theorem Derivable.no_closed_inhabitant (model : SetModel heads consts P)
    {A : Tm Head 0} (lf : lamFree A = true)
    (empty : ∀ z, z ∉ ev heads consts (liftTm A) Fin.elim0) (t : Tm Head 0) :
    ¬ Derivable R (.typing .nil t A) := by
  intro typing
  obtain ⟨s, -, e, holds⟩ :=
    Derivable.sound_elaborated levels facts model typing Normalization.CtxFormed.nil
  cases s with
  | typing Γ t' A' =>
      simp only [CStatement.erase, Statement.typing.injEq] at e
      obtain ⟨rfl, -, -, hA⟩ := e
      cases Γ with
      | nil =>
          have same : A' = liftTm A := by
            rw [CTm.eq_liftTm_of_lamFree (t := A') (by rw [eq_of_heq hA]; exact lf),
              eq_of_heq hA]
          subst same
          exact empty _ (holds Fin.elim0 (sat_nil heads consts Fin.elim0))
  | equality Γ a b A' => simp only [CStatement.erase, reduceCtorEq] at e
  | sub Γ A' B' => simp only [CStatement.erase, reduceCtorEq] at e

end Elaboration

/-! ## Rigid packages -/

/-- **Soundness of every derivation of a rigid package, through elaboration.** For a package
without root computation whose declared types have no abstraction, with its universe laws, a
reading of its heads and strong normalization of typed terms, every derivation over a formed
context is the erasure of an annotated derivation that holds in every set model of the
annotation: the declared constants at values in the values of their declared types. -/
theorem Derivable.sound_rigid {L : Type} [UniverseLevel.LevelOrder L] (rigid : R.Rigid)
    (levels : Normalization.LevelModel R L) (algebra : Normalization.CumulativeAlgebra R)
    (read : HeadReading R) (ground : GroundHeadEq R) {u₀ : Head} (hu₀ : R.isUniverse u₀)
    (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, Normalization.CtxFormed R Γ →
      Typed R Γ t A → StrongNormalization.SN R t)
    (model : SetModel heads consts P) {statement : Statement Head}
    (derivation : Derivable R statement) (formed : statement.CtxFormed R) :
    ∃ s : CStatement Head, CDerivable P s ∧ s.erase = statement ∧
      Holds heads consts s :=
  Derivable.sound_elaborated levels (LiftingFacts.ofRigid levels algebra read ground hu₀ sn rigid)
    model derivation formed

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
