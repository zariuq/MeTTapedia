import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelIsomorphisms
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCarrierTransportProjections

/-!
# Replacing represented program and event objects

Program and event objects may be replaced through specified isomorphisms
that commute with the endpoints. At every target stage this gives an
equivalence of generalized event fibers. Operational actions transport
through these equivalences after reading the source model along the program
isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.TypeTheory

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {M' : List (MetaArity S)}
variable {equations : List (EqAxiom S M')}

namespace EventObjects

variable {P Q : SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)}
variable (E : EventObjects P.interpretation.model) (F : EventObjects Q.interpretation.model) (p : P ≅ Q)

/-- Specified replacement objects, with their actual endpoint comparisons. -/
structure IsomorphicAlong where
  event : ∀ Γ s, E.event Γ s ≅ F.event Γ s
  source : ∀ Γ s, (event Γ s).hom ≫ F.source Γ s = E.source Γ s ≫ p.hom.underlying.power Γ s
  target : ∀ Γ s, (event Γ s).hom ≫ F.target Γ s = E.target Γ s ≫ p.hom.underlying.power Γ s

variable {E F p} (i : IsomorphicAlong E F p)

/-- The function-object component of a program isomorphism. -/
def programPowerIso (Γ : Ctx S) (s : S.Srt) : P.interpretation.model.power Γ s ≅ Q.interpretation.model.power Γ s where
  hom := p.hom.underlying.power Γ s
  inv := p.inv.underlying.power Γ s
  hom_inv_id := congrArg (fun f => f.underlying.power Γ s) p.hom_inv_id
  inv_hom_id := congrArg (fun f => f.underlying.power Γ s) p.inv_hom_id

/-- The replacement data are an endpoint-preserving event map. -/
def IsomorphicAlong.hom : E.Hom F p.hom where
  event := fun Γ s => (i.event Γ s).hom
  source := i.source
  target := i.target

theorem IsomorphicAlong.inv_source (Γ : Ctx S) (s : S.Srt) :
    (i.event Γ s).inv ≫ E.source Γ s = F.source Γ s ≫ p.inv.underlying.power Γ s := by
  apply (cancel_mono (programPowerIso (p := p) Γ s).hom).mp
  simp only [Category.assoc, programPowerIso]
  rw [← i.source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact (Category.comp_id _).symm.trans
    (congrArg (F.source Γ s ≫ ·) (programPowerIso (p := p) Γ s).inv_hom_id.symm)

theorem IsomorphicAlong.inv_target (Γ : Ctx S) (s : S.Srt) :
    (i.event Γ s).inv ≫ E.target Γ s = F.target Γ s ≫ p.inv.underlying.power Γ s := by
  apply (cancel_mono (programPowerIso (p := p) Γ s).hom).mp
  simp only [Category.assoc, programPowerIso]
  rw [← i.target, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact (Category.comp_id _).symm.trans
    (congrArg (F.target Γ s ≫ ·) (programPowerIso (p := p) Γ s).inv_hom_id.symm)

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of generalized event fibers at every stage. -/
def IsomorphicAlong.stageEquiv (Z : D) (j : Judgment (P.interpretation.model.stage Z)) :
    E.StageEvent Z j ≃ F.StageEvent Z (mapJudgment (stageMap p.hom Z) j) where
  toFun := i.hom.stage Z j
  invFun e :=
    ⟨e.1 ≫ (i.event j.1 j.2.1).inv, by
      constructor
      · exact (Category.assoc _ _ _).trans
          ((congrArg (e.1 ≫ ·) (i.inv_source _ _)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ p.inv.underlying.power j.1 j.2.1) e.2.1).trans
                ((congrArg (· ≫ p.inv.underlying.power j.1 j.2.1)
                    (elemEquiv_stageElemMap p.hom j.2.2.1)).trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg (P.interpretation.model.elemEquiv j.2.2.1 ≫ ·)
                      (programPowerIso (p := p) j.1 j.2.1).hom_inv_id).trans (Category.comp_id _)))))))
      · exact (Category.assoc _ _ _).trans
          ((congrArg (e.1 ≫ ·) (i.inv_target _ _)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ p.inv.underlying.power j.1 j.2.1) e.2.2).trans
                ((congrArg (· ≫ p.inv.underlying.power j.1 j.2.1)
                    (elemEquiv_stageElemMap p.hom j.2.2.2)).trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg (P.interpretation.model.elemEquiv j.2.2.2 ≫ ·)
                      (programPowerIso (p := p) j.1 j.2.1).hom_inv_id).trans (Category.comp_id _)))))))⟩
  left_inv e := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).trans
      ((congrArg (e.1 ≫ ·) (i.event j.1 j.2.1).hom_inv_id).trans (Category.comp_id _))
  right_inv e := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).trans
      ((congrArg (e.1 ≫ ·) (i.event j.1 j.2.1).inv_hom_id).trans (Category.comp_id _))

/-- The stage equivalences are natural in generalized stages. -/
theorem IsomorphicAlong.stage_restage {Z Z' : D} (h : Z' ⟶ Z)
    (j : Judgment (P.interpretation.model.stage Z)) (e : E.StageEvent Z j) :
    HEq (i.hom.stage Z' (mapJudgment (P.interpretation.model.stageRestage h) j)
      (E.restage h e)) (F.restage h (i.hom.stage Z j e)) := by
  apply F.stageEvent_heq
  · exact (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ j).symm.trans
      ((congrArg (fun φ => mapJudgment φ j) (stageMap_restage p.hom h).symm).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ j))
  · exact heq_of_eq (Category.assoc _ _ _)

end EventObjects

namespace CategoricalModel

variable {R : List (LocalRule S)}
variable (N : CategoricalModel R equations (D := D))
variable (P : SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations))
variable (E : EventObjects P.interpretation.model) (p : P ≅ N.program)
variable (i : EventObjects.IsomorphicAlong E N.objects p)

set_option backward.isDefEq.respectTransparency false in
/-- The replacement stage model uses the actual replacement event fibers. -/
def replacementStage (Z : D) : SubstitutionModel R (P.interpretation.model.stage Z) :=
  ((N.stageModel Z).pullback (stageMap p.hom Z)).transportCarrier
    (fun j => (i.stageEquiv Z j).symm)

/-- Reading a replacement event through the event isomorphism preserves actions. -/
def replacementStageHom (Z : D) : SubstitutionModel.Hom R _
    (replacementStage N P E p i Z) ((N.stageModel Z).pullback (stageMap p.hom Z)) :=
  ((N.stageModel Z).pullback (stageMap p.hom Z)).transportCarrierInvHom
    (fun j => (i.stageEquiv Z j).symm)

/-- Replacing the event representation in the reverse direction also preserves actions. -/
def replacementStageInvHom (Z : D) : SubstitutionModel.Hom R _
    ((N.stageModel Z).pullback (stageMap p.hom Z)) (replacementStage N P E p i Z) :=
  ((N.stageModel Z).pullback (stageMap p.hom Z)).transportCarrierHom
    (fun j => (i.stageEquiv Z j).symm)

private def changeStageTarget {A : BindingCloneAlgebra.Algebra S}
    {X Y Y' : SubstitutionModel R A} (same : Y = Y')
    (f : SubstitutionModel.Hom R A X Y) : SubstitutionModel.Hom R A X Y' := same ▸ f

private theorem changeStageTarget_apply {A : BindingCloneAlgebra.Algebra S}
    {X Y Y' : SubstitutionModel R A} (same : Y = Y')
    (f : SubstitutionModel.Hom R A X Y) (j : Judgment A) (e : X.carrier j) :
    HEq ((changeStageTarget same f).evidence.toFun () j e) (f.evidence.toFun () j e) := by
  cases same
  rfl

/-- Restaging is transported as a map of the replacement operational models. -/
def replacementRestageHom {Z Z' : D} (h : Z' ⟶ Z) :
    SubstitutionModel.Hom R _ (replacementStage N P E p i Z)
      ((replacementStage N P E p i Z').pullback (P.interpretation.model.stageRestage h)) := by
  let first := SubstitutionModel.Hom.ofIsHom R _ _
    (SubstitutionModel.IsHom.comp_pullback (stageMap p.hom Z) (N.programModel.stageRestage h)
      (replacementStageHom N P E p i Z).isHom (N.restageHom h).isHom)
  have same : (N.stageModel Z').pullback
      (FreeBindingClone.Hom.comp (stageMap p.hom Z) (N.programModel.stageRestage h)) =
      ((N.stageModel Z').pullback (stageMap p.hom Z')).pullback
        (P.interpretation.model.stageRestage h) :=
    (congrArg (fun φ => (N.stageModel Z').pullback φ) (stageMap_restage p.hom h)).trans
      (SubstitutionModel.pullback_comp _ _ _)
  exact SubstitutionModel.Hom.comp R _ (changeStageTarget same first)
    (SubstitutionModel.Hom.pullback (P.interpretation.model.stageRestage h)
      (replacementStageInvHom N P E p i Z'))

set_option backward.isDefEq.respectTransparency false in
/-- Its evidence map is ordinary precomposition of the replacement event arrows. -/
theorem replacementRestageHom_apply {Z Z' : D} (h : Z' ⟶ Z)
    (j : Judgment (P.interpretation.model.stage Z)) (e : E.StageEvent Z j) :
    (replacementRestageHom N P E p i h).evidence.toFun () j e = E.restage h e := by
  apply (i.stageEquiv Z' (mapJudgment (P.interpretation.model.stageRestage h) j)).injective
  dsimp only [replacementRestageHom, SubstitutionModel.Hom.comp,
    SubstitutionModel.Hom.pullback, IndexedRuleAlgebraPullback.pullbackHom,
    IndexedPolynomial.Algebra.Hom.comp, replacementStageInvHom,
    SubstitutionModel.transportCarrierHom]
  refine ((i.stageEquiv Z' (mapJudgment (P.interpretation.model.stageRestage h) j)).apply_symm_apply _).trans ?_
  refine eq_of_heq ((changeStageTarget_apply (X := replacementStage N P E p i Z) _ _ j e).trans ?_)
  exact (i.stage_restage h j e).symm

/-- Ordinary precomposition preserves both replacement actions. -/
theorem replacementRestageIsHom {Z Z' : D} (h : Z' ⟶ Z) :
    SubstitutionModel.IsHom R _ (replacementStage N P E p i Z)
      ((replacementStage N P E p i Z').pullback (P.interpretation.model.stageRestage h))
      (fun _ e => E.restage h e) :=
  SubstitutionModel.IsHom.congr R _ (replacementRestageHom_apply N P E p i h)
    (replacementRestageHom N P E p i h).isHom

set_option allowUnsafeReducibility true
attribute [local irreducible] RulesLaw

/-- Replacement contextual substitution, on its explicitly typed fibers. -/
def replacementAct (Z : D) : IntrinsicScopedJudgmentAction.ActionOn
    (P.interpretation.model.stage Z) (E.StageEvent Z) :=
  ((N.stageModel Z).pullback (stageMap p.hom Z)).carrierAct
    (fun j => (i.stageEquiv Z j).symm)

/-- Replacement rule action, preserving the original rule-local positions. -/
def replacementRules (Z : D) : (IntrinsicScopedLocalPolynomial.rules R
    (P.interpretation.model.stage Z)).Algebra (fun _ j => E.StageEvent Z j) :=
  ((N.stageModel Z).pullback (stageMap p.hom Z)).carrierRules
    (fun j => (i.stageEquiv Z j).symm)

/-- The typed rule projection agrees with the transported stage algebra. -/
theorem replacementRules_eq (Z : D) : replacementRules N P E p i Z =
    (replacementStage N P E p i Z).rules := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rule/substitution law inherited from the stage model. -/
theorem replacementRulesLaw (Z : D) : RulesLaw R (P.interpretation.model.stage Z)
    (replacementAct N P E p i Z) (replacementRules N P E p i Z) := by
  unfold replacementAct replacementRules
  exact @SubstitutionModel.carrierRulesLaw _ R (P.interpretation.model.stage Z)
    ((N.stageModel Z).pullback (stageMap p.hom Z)) (E.StageEvent Z)
    (fun j => (i.stageEquiv Z j).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The replacement rule actions commute with precomposition of stages. -/
theorem replacementRulesRestage {Z Z' : D} (h : Z' ⟶ Z)
    {j : Judgment (P.interpretation.model.stage Z)}
    (shape : Shape R (P.interpretation.model.stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      E.StageEvent Z (childJudgment R _ shape.1 position)) :
    E.restage h ((replacementRules N P E p i Z).act () j ⟨shape, children⟩) =
      (replacementRules N P E p i Z').act ()
        (mapJudgment (P.interpretation.model.stageRestage h) j)
        ⟨mapShape R (P.interpretation.model.stageRestage h) shape, fun position =>
          ((mapInstance_child R (P.interpretation.model.stageRestage h) shape.1 position).symm ▸
            E.restage h (children position) : E.StageEvent Z'
              (childJudgment R _ (mapInstance R (P.interpretation.model.stageRestage h) shape.1) position))⟩ := by
  have law := rulesAlong_of_isHom (replacementStage N P E p i Z)
    (P.interpretation.model.stageRestage h) (replacementStage N P E p i Z')
    (fun _ e => E.restage h e) (replacementRestageIsHom N P E p i h) j shape children
  rw [replacementRules_eq, replacementRules_eq]
  simp only [] at law
  with_reducible exact law

/-- A lawful operational model on the specified replacement objects. -/
def rehost : CategoricalModel R equations (D := D) where
  program := P
  objects := E
  act := replacementAct N P E p i
  act_identity := fun Z => (replacementStage N P E p i Z).act_identity
  act_comp := fun Z => (replacementStage N P E p i Z).act_comp
  rules := replacementRules N P E p i
  act_rules := replacementRulesLaw N P E p i
  act_restage := by
    intro Z Z' h j e Δ σ target same
    exact (replacementRestageIsHom N P E p i h).act j e σ target same
  rules_restage := fun h _ shape children => replacementRulesRestage N P E p i h shape children

/-- The replacement isomorphisms define a genuine map of operational models. -/
def rehostHom : rehost N P E p i ⟶ N where
  program := p.hom
  events := i.hom
  stage := fun Z => (replacementStageHom N P E p i Z).isHom

/-- Replacement of the program and event objects gives an isomorphic model. -/
def rehostIso : rehost N P E p i ≅ N := by
  letI : IsIso (rehostHom N P E p i).program := by
    change IsIso p.hom
    infer_instance
  letI : ∀ Γ s, IsIso ((rehostHom N P E p i).events.event Γ s) := fun Γ s => by
    change IsIso (i.event Γ s).hom
    infer_instance
  exact Hom.isoOfComponents (rehostHom N P E p i)

@[simp] theorem rehostIso_hom_program : (rehostIso N P E p i).hom.program = p.hom := rfl

@[simp] theorem rehostIso_hom_event (Γ : Ctx S) (s : S.Srt) :
    (rehostIso N P E p i).hom.events.event Γ s = (i.event Γ s).hom := rfl

@[simp] theorem rehostIso_inv_program : (rehostIso N P E p i).inv.program = p.inv := by
  apply (cancel_mono p.hom).mp
  exact (congrArg (fun f => f.program) (rehostIso N P E p i).inv_hom_id).trans
    p.inv_hom_id.symm

@[simp] theorem rehostIso_inv_event (Γ : Ctx S) (s : S.Srt) :
    (rehostIso N P E p i).inv.events.event Γ s = (i.event Γ s).inv := by
  apply (cancel_mono (i.event Γ s).hom).mp
  exact (congrArg (fun f => f.events.event Γ s) (rehostIso N P E p i).inv_hom_id).trans
    (i.event Γ s).inv_hom_id.symm

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
