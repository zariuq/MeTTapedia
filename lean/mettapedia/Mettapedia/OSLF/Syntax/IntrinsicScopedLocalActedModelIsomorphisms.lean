import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelMaps

/-!
# Componentwise isomorphisms of operational models

An invertible program map and invertible maps of the event objects determine
an inverse map of operational models. Preservation of substitution and rule
actions by the inverse follows from preservation by the forward map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment mapJudgment_substJudgment heq_transport)

universe u v

section RulesInverse

universe ua ub wa wb

variable {S : Signature} {R : List (LocalRule S)}
variable {A : BindingCloneAlgebra.Algebra.{ua} S} {B : BindingCloneAlgebra.Algebra.{ub} S}

/-- Inverting an indexed evidence map preserves the rule actions. This law
is independent of the choice of categorical realization of the evidence. -/
theorem inverse_rulesAlong (h : FreeBindingClone.Hom A B) (k : FreeBindingClone.Hom B A)
    (X : SubstitutionModel.{ua, wa} R A) (Y : SubstitutionModel.{ub, wb} R B)
    (F : ∀ j, X.carrier j → Y.carrier (mapJudgment h j))
    (G : ∀ j, Y.carrier j → X.carrier (mapJudgment k j))
    (roundtrip : FreeBindingClone.Hom.comp k h = FreeBindingClone.Hom.id B)
    (left : ∀ j e, HEq (G (mapJudgment h j) (F j e)) e)
    (right : ∀ j e, HEq (F (mapJudgment k j) (G j e)) e)
    (preserves : RulesAlong h X Y.rules F) : RulesAlong k Y X.rules G := by
  intro j shape children
  let shape' := mapShape R k shape
  let children' : ∀ position : Fin (R.get shape'.1.index).2.premises.length,
      X.carrier (childJudgment R A shape'.1 position) :=
    fun position => (mapInstance_child R k shape.1 position).symm ▸ G _ (children position)
  let value := X.rules.act () (mapJudgment k j) ⟨shape', children'⟩
  have judgment : mapJudgment h (mapJudgment k j) = j :=
    (AuthoredPositionedRulePolynomial.mapJudgment_comp k h j).symm.trans
      ((congrArg (fun map => mapJudgment map j) roundtrip).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_id B j))
  have occurrence : mapInstance R h (mapInstance R k shape.1) = shape.1 :=
    (mapInstance_comp R k h shape.1).symm.trans
      ((congrArg (fun map => mapInstance R map shape.1) roundtrip).trans
        (mapInstance_id R B shape.1))
  have moved := preserves (mapJudgment k j) shape' children'
  have acted : HEq (F (mapJudgment k j) value) (Y.rules.act () j ⟨shape, children⟩) := by
    refine (heq_of_eq moved).trans ?_
    refine rulesAct_heq R Y.rules judgment occurrence _ _ _ _ ?_
    intro position position' same
    cases same
    have input : HEq (children' position) (G _ (children position)) := heq_transport _ _
    have mapped : HEq (F (childJudgment R A shape'.1 position) (children' position))
        (F (mapJudgment k (childJudgment R B shape.1 position)) (G _ (children position))) :=
      image_heq (image := F) (mapInstance_child R k shape.1 position) input
    have casted : HEq
        ((mapInstance_child R h shape'.1 position).symm ▸ F _ (children' position) :
          Y.carrier (childJudgment R B (mapInstance R h shape'.1) position))
        (F _ (children' position)) := heq_transport _ _
    exact casted.trans (mapped.trans (right _ _))
  exact eq_of_heq ((image_heq (image := G) judgment acted).symm.trans (left _ value))

end RulesInverse

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace EventObjects

/-- A stage map respects equal judgments and equal generalized events. -/
theorem Hom.stage_heq {A B : Model S D} {E : EventObjects A} {F : EventObjects B}
    {h : CategoricalBindingInterpretationMaps.Hom A B} (f : Hom E F h) {Z : D}
    {j j' : Judgment (A.stage Z)} (same : j = j')
    {e : E.StageEvent Z j} {e' : E.StageEvent Z j'} (equal : HEq e e') :
    HEq (f.stage Z j e) (f.stage Z j' e') := by
  subst same
  cases equal
  rfl

end EventObjects

namespace CategoricalModel

variable {M N : CategoricalModel R equations (D := D)}

/-- Inverse component data do not assume any operational law for the inverse. -/
structure Hom.InverseComponents (f : M ⟶ N) where
  program : N.program ⟶ M.program
  program_hom_inv : f.program ≫ program = 𝟙 M.program
  program_inv_hom : program ≫ f.program = 𝟙 N.program
  event : ∀ Γ s, N.objects.event Γ s ⟶ M.objects.event Γ s
  event_hom_inv : ∀ Γ s, f.events.event Γ s ≫ event Γ s = 𝟙 _
  event_inv_hom : ∀ Γ s, event Γ s ≫ f.events.event Γ s = 𝟙 _

namespace Hom.InverseComponents

variable {f : M ⟶ N} (i : InverseComponents f)

theorem power_hom_inv (Γ : Ctx S) (s : S.Srt) :
    f.program.underlying.power Γ s ≫ i.program.underlying.power Γ s = 𝟙 _ :=
  congrArg (fun h => h.underlying.power Γ s) i.program_hom_inv

theorem power_inv_hom (Γ : Ctx S) (s : S.Srt) :
    i.program.underlying.power Γ s ≫ f.program.underlying.power Γ s = 𝟙 _ :=
  congrArg (fun h => h.underlying.power Γ s) i.program_inv_hom

/-- Inverse event components also commute with source and target. -/
def events : N.objects.Hom M.objects i.program where
  event := i.event
  source Γ s := by
    calc
      i.event Γ s ≫ M.objects.source Γ s =
          i.event Γ s ≫ M.objects.source Γ s ≫
            (f.program.underlying.power Γ s ≫ i.program.underlying.power Γ s) := by
              rw [i.power_hom_inv, Category.comp_id]
      _ = (i.event Γ s ≫ f.events.event Γ s) ≫ N.objects.source Γ s ≫
          i.program.underlying.power Γ s := by
            simpa only [Category.assoc] using congrArg
              (fun m => i.event Γ s ≫ m ≫ i.program.underlying.power Γ s)
              (f.events.source Γ s).symm
      _ = N.objects.source Γ s ≫ i.program.underlying.power Γ s := by
            rw [i.event_inv_hom, Category.id_comp]
  target Γ s := by
    calc
      i.event Γ s ≫ M.objects.target Γ s =
          i.event Γ s ≫ M.objects.target Γ s ≫
            (f.program.underlying.power Γ s ≫ i.program.underlying.power Γ s) := by
              rw [i.power_hom_inv, Category.comp_id]
      _ = (i.event Γ s ≫ f.events.event Γ s) ≫ N.objects.target Γ s ≫
          i.program.underlying.power Γ s := by
            simpa only [Category.assoc] using congrArg
              (fun m => i.event Γ s ≫ m ≫ i.program.underlying.power Γ s)
              (f.events.target Γ s).symm
      _ = N.objects.target Γ s ≫ i.program.underlying.power Γ s := by
            rw [i.event_inv_hom, Category.id_comp]

theorem stage_hom_inv (Z : D) :
    FreeBindingClone.Hom.comp (stageMap f.program Z) (stageMap i.program Z) =
      FreeBindingClone.Hom.id (M.programModel.stage Z) :=
  (stageMap_comp f.program i.program Z).symm.trans
    ((congrArg (fun h => stageMap h Z) i.program_hom_inv).trans
      (stageMap_id M.programModel Z))

theorem stage_inv_hom (Z : D) :
    FreeBindingClone.Hom.comp (stageMap i.program Z) (stageMap f.program Z) =
      FreeBindingClone.Hom.id (N.programModel.stage Z) :=
  (stageMap_comp i.program f.program Z).symm.trans
    ((congrArg (fun h => stageMap h Z) i.program_inv_hom).trans
      (stageMap_id N.programModel Z))

theorem judgment_inv_hom (Z : D) (j : Judgment (N.programModel.stage Z)) :
    mapJudgment (stageMap f.program Z) (mapJudgment (stageMap i.program Z) j) = j :=
  (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ j).symm.trans
    ((congrArg (fun h => mapJudgment h j) (i.stage_inv_hom Z)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ j))

theorem judgment_hom_inv (Z : D) (j : Judgment (M.programModel.stage Z)) :
    mapJudgment (stageMap i.program Z) (mapJudgment (stageMap f.program Z) j) = j :=
  (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ j).symm.trans
    ((congrArg (fun h => mapJudgment h j) (i.stage_hom_inv Z)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ j))

theorem instance_inv_hom (Z : D) (occurrence : Instance R (N.programModel.stage Z)) :
    mapInstance R (stageMap f.program Z) (mapInstance R (stageMap i.program Z) occurrence) =
      occurrence :=
  (mapInstance_comp R _ _ occurrence).symm.trans
    ((congrArg (fun h => mapInstance R h occurrence) (i.stage_inv_hom Z)).trans
      (mapInstance_id R _ occurrence))

/-- The composite of the inverse and forward generalized-event maps is the
original event, with its original judgment. -/
theorem stage_event_inv_hom (Z : D) (j : Judgment (N.programModel.stage Z))
    (e : N.objects.StageEvent Z j) :
    HEq (f.events.stage Z _ (i.events.stage Z j e)) e := by
  apply N.objects.stageEvent_heq (i.judgment_inv_hom Z j)
  exact heq_of_eq ((Category.assoc e.1 _ _).trans
    ((congrArg (e.1 ≫ ·) (i.event_inv_hom _ _)).trans (Category.comp_id e.1)))

theorem stage_event_hom_inv (Z : D) (j : Judgment (M.programModel.stage Z))
    (e : M.objects.StageEvent Z j) :
    HEq (i.events.stage Z _ (f.events.stage Z j e)) e := by
  apply M.objects.stageEvent_heq (i.judgment_hom_inv Z j)
  exact heq_of_eq ((Category.assoc e.1 _ _).trans
    ((congrArg (e.1 ≫ ·) (i.event_hom_inv _ _)).trans (Category.comp_id e.1)))

theorem elem_inv_hom (Z : D) {Γ : Ctx S} {s : S.Srt}
    (x : N.programModel.ElemOver Z Γ s) :
    (stageMap f.program Z).raw.map ((stageMap i.program Z).raw.map x) = x :=
  congrArg (fun h => h.raw.map x) (i.stage_inv_hom Z)

/-- The inverse event maps preserve substitution, by cancelling the forward
maps and using their substitution law. -/
theorem actsAlong (Z : D) :
    ActsAlong (stageMap i.program Z) (N.stageModel Z) (M.stageModel Z).act
      (i.events.stage Z) := by
  intro j e Δ σ
  let a := mapJudgment (stageMap i.program Z) j
  let a' := mapJudgment (stageMap i.program Z) (substJudgment j σ)
  let σ' := fun t v => (stageMap i.program Z).raw.map (σ t v)
  let value := (M.stageModel Z).act a (i.events.stage Z j e) σ' a'
    (mapJudgment_substJudgment (stageMap i.program Z) j σ).symm
  have moved := (f.stage Z).act a (i.events.stage Z j e) σ' a'
    (mapJudgment_substJudgment (stageMap i.program Z) j σ).symm
  have acted : HEq (f.events.stage Z a' value)
      ((N.stageModel Z).act j e σ (substJudgment j σ) rfl) := by
    refine (heq_of_eq moved).trans ?_
    exact (N.stageModel Z).toAction.act_heq (i.judgment_inv_hom Z j)
      (i.stage_event_inv_hom Z j e)
      (heq_of_eq (funext fun t => funext fun v => i.elem_inv_hom Z (σ t v)))
      (i.judgment_inv_hom Z (substJudgment j σ)) _ _
  have read : value.1 ≫ f.events.event Δ j.2.1 =
      ((N.stageModel Z).act j e σ (substJudgment j σ) rfl).1 :=
    eq_of_heq (N.objects.stageEvent_val_heq
      (i.judgment_inv_hom Z (substJudgment j σ)) acted)
  apply Subtype.ext
  change ((N.stageModel Z).act j e σ (substJudgment j σ) rfl).1 ≫
    i.event Δ j.2.1 = value.1
  exact (congrArg (fun m : Z ⟶ N.objects.event Δ j.2.1 => m ≫ i.event Δ j.2.1)
    read.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (value.1 ≫ ·) (i.event_hom_inv Δ j.2.1)).trans (Category.comp_id _)))

/-- The inverse event maps preserve rule actions. Each premise retains its
local binder context and its ordered position. -/
theorem rulesAlong (Z : D) :
    RulesAlong (stageMap i.program Z) (N.stageModel Z) (M.stageModel Z).rules
      (i.events.stage Z) := by
  apply inverse_rulesAlong (stageMap f.program Z) (stageMap i.program Z)
    (M.stageModel Z) (N.stageModel Z) (f.events.stage Z) (i.events.stage Z)
    (i.stage_inv_hom Z) (i.stage_event_hom_inv Z) (i.stage_event_inv_hom Z)
  intro j shape children
  exact ((f.stage Z).rules j ⟨shape, children⟩).trans
    (pullback_rulesMap_act_map (stageMap f.program Z) (N.stageModel Z).rules
      (f.events.stage Z) shape children)

/-- Component inverses form a map of models, with both operational laws
derived from the forward map. -/
noncomputable def inverse : N ⟶ M where
  program := i.program
  events := i.events
  stage Z := isHom_of_along (i.actsAlong Z) (i.rulesAlong Z)

theorem hom_inverse : f ≫ i.inverse = 𝟙 M :=
  Hom.ext' i.program_hom_inv i.event_hom_inv

theorem inverse_hom : i.inverse ≫ f = 𝟙 N :=
  Hom.ext' i.program_inv_hom i.event_inv_hom

/-- A model isomorphism constructed from invertible program and event maps. -/
noncomputable def iso : M ≅ N where
  hom := f
  inv := i.inverse
  hom_inv_id := i.hom_inverse
  inv_hom_id := i.inverse_hom

@[simp] theorem inverse_program : i.inverse.program = i.program := rfl

@[simp] theorem inverse_event (Γ : Ctx S) (s : S.Srt) :
    i.inverse.events.event Γ s = i.event Γ s := rfl

@[simp] theorem iso_hom : i.iso.hom = f := rfl

@[simp] theorem iso_inv : i.iso.inv = i.inverse := rfl

end Hom.InverseComponents

/-- Typeclass inverses of the program and event components supply precisely
the component data needed for a model inverse. -/
noncomputable def Hom.inverseComponentsOfIsIso (f : M ⟶ N) [IsIso f.program]
    [∀ Γ s, IsIso (f.events.event Γ s)] : Hom.InverseComponents f where
  program := inv f.program
  program_hom_inv := IsIso.hom_inv_id f.program
  program_inv_hom := IsIso.inv_hom_id f.program
  event Γ s := inv (f.events.event Γ s)
  event_hom_inv Γ s := IsIso.hom_inv_id (f.events.event Γ s)
  event_inv_hom Γ s := IsIso.inv_hom_id (f.events.event Γ s)

/-- A componentwise isomorphism is an isomorphism in the full model category. -/
theorem Hom.isIso_of_components (f : M ⟶ N) [IsIso f.program]
    [∀ Γ s, IsIso (f.events.event Γ s)] : IsIso f :=
  ⟨⟨(Hom.inverseComponentsOfIsIso f).inverse,
    (Hom.inverseComponentsOfIsIso f).hom_inverse,
    (Hom.inverseComponentsOfIsIso f).inverse_hom⟩⟩

/-- The model isomorphism furnished by the program and event isomorphisms. -/
noncomputable def Hom.isoOfComponents (f : M ⟶ N) [IsIso f.program]
    [∀ Γ s, IsIso (f.events.event Γ s)] : M ≅ N :=
  (Hom.inverseComponentsOfIsIso f).iso

@[simp] theorem Hom.isoOfComponents_hom (f : M ⟶ N) [IsIso f.program]
    [∀ Γ s, IsIso (f.events.event Γ s)] : (Hom.isoOfComponents f).hom = f := rfl

/-- A model isomorphism has an invertible program component. -/
theorem Hom.isIso_program (f : M ⟶ N) [IsIso f] : IsIso f.program :=
  ⟨⟨(inv f).program,
    congrArg (fun h => h.program) (IsIso.hom_inv_id f),
    congrArg (fun h => h.program) (IsIso.inv_hom_id f)⟩⟩

/-- A model isomorphism has invertible event components at every judgment
context and endpoint sort. -/
theorem Hom.isIso_event (f : M ⟶ N) [IsIso f] (Γ : Ctx S) (s : S.Srt) :
    IsIso (f.events.event Γ s) :=
  ⟨⟨(inv f).events.event Γ s,
    congrArg (fun h => h.events.event Γ s) (IsIso.hom_inv_id f),
    congrArg (fun h => h.events.event Γ s) (IsIso.inv_hom_id f)⟩⟩

/-- Invertibility in the operational model category is exactly invertibility
of the program map and each event-object map. -/
theorem Hom.isIso_iff_components (f : M ⟶ N) :
    IsIso f ↔ IsIso f.program ∧ ∀ Γ s, IsIso (f.events.event Γ s) := by
  constructor
  · intro isIso
    let := isIso
    exact ⟨Hom.isIso_program f, Hom.isIso_event f⟩
  · rintro ⟨program, events⟩
    let := program
    let := events
    exact Hom.isIso_of_components f

end CategoricalModel

#print axioms inverse_rulesAlong
#print axioms CategoricalModel.Hom.InverseComponents.actsAlong
#print axioms CategoricalModel.Hom.InverseComponents.rulesAlong
#print axioms CategoricalModel.Hom.InverseComponents.inverse
#print axioms CategoricalModel.Hom.InverseComponents.iso
#print axioms CategoricalModel.Hom.isIso_iff_components

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
