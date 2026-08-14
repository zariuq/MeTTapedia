import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalModel

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-faithful class semantics for Henkin (1950).

`GeneralModel` in the trusted HOL semantics interprets the proposition type `o`
as ambient meta-`Prop`, which is exactly what makes the direct bridge from the
canonical quotient model force excluded middle. This file records a different
paper-facing endpoint: class-valued models whose proposition carrier has its
own truth predicate.

This keeps the existing canonical quotient construction usable as a genuine
semantic witness, rather than only as a bridge-obstruction interface.
-/

/-- A paper-facing class general model carries typed semantic objects directly,
with a separate truth predicate on the proposition carrier. Term denotation is
left primitive so quotient-based models such as the canonical class model can
instantiate it without forcing function carriers to be meta-level functions. -/
structure ClassGeneralModel where
  Carrier : HTy → Type
  denoteTerm :
    {Γ : Ctx Atom} → {τ : HTy} →
      (∀ {τ : HTy}, Var Γ τ → Carrier τ) →
      Term Γ τ → Carrier τ
  truth : Carrier o → Prop

namespace ClassGeneralModel

/-- Variable assignments into a class general model. -/
abbrev Assignment (M : ClassGeneralModel) (Γ : Ctx Atom) : Type :=
  ∀ {τ : HTy}, Var Γ τ → M.Carrier τ

/-- The unique assignment on the empty context. -/
def emptyAssignment (M : ClassGeneralModel) : Assignment M [] := by
  intro τ v
  cases v

/-- Extend an assignment with a value for a newly bound head variable. -/
def extend (M : ClassGeneralModel)
    (ν : Assignment M Γ) (x : M.Carrier σ) :
    Assignment M (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ν v

/-- Open formulas denote by applying the model's proposition-truth predicate
to the denotation of the corresponding proposition-typed term. -/
def denoteFormula (M : ClassGeneralModel)
    (ν : Assignment M Γ) (φ : Formula Γ) : Prop :=
  M.truth (M.denoteTerm ν φ)

/-- Closed-sentence satisfaction in a class general model. -/
def models (M : ClassGeneralModel) (φ : Sentence) : Prop :=
  M.denoteFormula M.emptyAssignment φ

end ClassGeneralModel

/-- Satisfiability of a closed theory in the class-semantics sense. -/
def SatisfiableInClassGeneral (T : ClosedTheorySet) : Prop :=
  ∃ M : ClassGeneralModel, ∀ φ : Sentence, φ ∈ T → M.models φ

/-- A paper-facing class description model is a class general model whose
description operator selects witnesses for arbitrary predicate terms in
context. This is the class-valued counterpart of Henkin's `iota_sound`
condition. -/
structure ClassDescriptionModel extends ClassGeneralModel where
  iota_sound :
    ∀ {Γ : Ctx Atom} {α : HTy}
      (ν : ClassGeneralModel.Assignment toClassGeneralModel Γ)
      (p : Term Γ (Pred α)),
      (∃ x : Carrier α,
        toClassGeneralModel.denoteFormula
          (toClassGeneralModel.extend ν x)
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)
            : Formula (α :: Γ))) →
      toClassGeneralModel.denoteFormula ν
        (.app p (iotaTerm p) : Formula Γ)

/-- Satisfiability of a closed theory in the class semantics with the paper's
description-operator condition. -/
def SatisfiableInClassDescription (T : ClosedTheorySet) : Prop :=
  ∃ M : ClassDescriptionModel, ∀ φ : Sentence, φ ∈ T → M.toClassGeneralModel.models φ

/-- Closed-theory form of the paper's description axiom: every closed
representative instance of axiom 11 belongs to the theory. This is exactly the
assumption needed to upgrade the canonical class model to a class description
model. -/
def DescriptionAxiomClosed (T : ClosedTheorySet) : Prop :=
  ∀ {α : HTy} (ρ : RepresentativeAssignment [α, Pred α]),
    closeFormula ρ (axiom11 (α := α)) ∈ T

namespace CanonicalClassModel

/-- Every canonical class model is already a class general model. -/
noncomputable def toClassGeneralModel (M : CanonicalClassModel) : ClassGeneralModel where
  Carrier := M.Carrier
  denoteTerm := fun ν t => M.denoteTerm ν t
  truth := M.PropClassHolds

@[simp] theorem toClassGeneralModel_denoteFormula_iff
    (M : CanonicalClassModel)
    (ν : M.toClassGeneralModel.Assignment Γ)
    (φ : Formula Γ) :
    M.toClassGeneralModel.denoteFormula ν φ ↔ M.denoteFormula ν φ :=
  M.propClassHolds_denoteTerm_iff ν φ

@[simp] theorem toClassGeneralModel_models_iff
    (M : CanonicalClassModel) (φ : Sentence) :
    M.toClassGeneralModel.models φ ↔ M.denoteFormula M.emptyAssignment φ := by
  change
    M.toClassGeneralModel.denoteFormula M.toClassGeneralModel.emptyAssignment φ ↔
      M.denoteFormula M.emptyAssignment φ
  have hEmpty :
      (M.toClassGeneralModel.emptyAssignment : M.toClassGeneralModel.Assignment []) =
        (M.emptyAssignment : M.toClassGeneralModel.Assignment []) := by
    funext τ v
    cases v
  have hDenote :
      M.toClassGeneralModel.denoteFormula M.toClassGeneralModel.emptyAssignment φ ↔
        M.denoteFormula M.toClassGeneralModel.emptyAssignment φ :=
    M.toClassGeneralModel_denoteFormula_iff M.toClassGeneralModel.emptyAssignment φ
  cases hEmpty
  exact hDenote

/-- Any closed theory already satisfiable in the canonical class semantics is
also satisfiable in the paper-facing class general-model interface. -/
theorem satisfiableInClassGeneral_of_classSatisfiable
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T) :
    SatisfiableInClassGeneral T := by
  rcases hClass with ⟨M, rfl, hM⟩
  refine ⟨M.toClassGeneralModel, ?_⟩
  intro φ hφ
  exact (M.toClassGeneralModel_models_iff φ).2 (hM φ hφ)

/-- Theorem 1 in a paper-facing class general semantics: under Henkin's
pp. 86-88 maximal-theory hypotheses, the closed theory is satisfiable in a
genuine class model built from the canonical quotient semantics. -/
theorem theorem1_classGeneral
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T) :
    SatisfiableInClassGeneral T :=
  satisfiableInClassGeneral_of_classSatisfiable <|
    CanonicalClassModel.theorem1_canonicalClassSatisfiable hT hEx hAll

/-- A canonical class model upgrades to a class description model once the
closed theory contains every representative instance of Henkin's axiom 11. -/
def toCanonicalDescriptionModel
    (M : CanonicalClassModel)
    (hA11 : DescriptionAxiomClosed M.T) :
    CanonicalDescriptionModel where
  toCanonicalClassModel := M
  axiom11_holds := by
    intro α ν
    exact
      (holds_iff_closeFormula_of_realizes
        (T := M.T)
        M.completeConsistent
        M.existsWitness
        M.allCounterexample
        (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
        (φ := axiom11 (α := α))).2 <|
        hA11 (ClassAssignment.chooseRepresentatives ν)

end CanonicalClassModel

namespace CanonicalClassModel.CanonicalDescriptionModel

/-- A packaged canonical description model induces a paper-facing class
description model. -/
noncomputable def toClassDescriptionModel
    (M : CanonicalClassModel.CanonicalDescriptionModel) :
    ClassDescriptionModel where
  toClassGeneralModel := M.toCanonicalClassModel.toClassGeneralModel
  iota_sound := by
    intro Γ α ν p hp
    rcases hp with ⟨x, hx⟩
    have hx' :
        M.toCanonicalClassModel.denoteFormula
          (M.toCanonicalClassModel.toClassGeneralModel.extend ν x)
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)
            : Formula (α :: Γ)) := by
      exact
        (M.toCanonicalClassModel.toClassGeneralModel_denoteFormula_iff
          (M.toCanonicalClassModel.toClassGeneralModel.extend ν x)
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)
            : Formula (α :: Γ))).1 hx
    have hRes :
        M.toCanonicalClassModel.denoteFormula ν
          (.app p (iotaTerm p) : Formula Γ) :=
      M.denoteFormula_app_iotaTerm_of_exists_general ν p ⟨x, hx'⟩
    exact
      (M.toCanonicalClassModel.toClassGeneralModel_denoteFormula_iff
        ν
        (.app p (iotaTerm p) : Formula Γ)).2 hRes

/-- Every canonical description model supplies the closed-theory axiom-11
instances needed for the constructor above. -/
theorem descriptionAxiomClosed
    (M : CanonicalClassModel.CanonicalDescriptionModel) :
    DescriptionAxiomClosed M.T := by
  intro α ρ
  exact
    M.closeFormula_axiom11_mem_of_realizes
      (ν := RepresentativeAssignment.toClassAssignment M.T ρ)
      (hρ := RepresentativeAssignment.realizes_toClassAssignment M.T ρ)

/-- Every packaged canonical description model satisfies its underlying closed
theory in the paper-facing class description semantics. -/
theorem satisfiableInClassDescription
    (M : CanonicalClassModel.CanonicalDescriptionModel) :
    SatisfiableInClassDescription M.T := by
  refine ⟨M.toClassDescriptionModel, ?_⟩
  intro φ hφ
  exact
    (M.toCanonicalClassModel.toClassGeneralModel_models_iff φ).2 <|
      CanonicalClassModel.theorem1_canonicalClassModel_milestone
        (M := M.toCanonicalClassModel)
        hφ

end CanonicalClassModel.CanonicalDescriptionModel

/-- Exact class-semantics Theorem 1 for the full paper language, under the
explicit closed-theory description-axiom assumption. This avoids the excluded-
middle obstruction in the current `GeneralModel` interface while preserving a
genuine semantic satisfiability theorem. -/
theorem theorem1_classDescription
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (hA11 : DescriptionAxiomClosed T) :
    SatisfiableInClassDescription T := by
  let M : CanonicalClassModel :=
    { T := T
      completeConsistent := hT
      existsWitness := hEx
      allCounterexample := hAll }
  exact
    CanonicalClassModel.CanonicalDescriptionModel.satisfiableInClassDescription
      (M := M.toCanonicalDescriptionModel hA11)

end Mettapedia.AutoBooks.Codex.Henkin1950
