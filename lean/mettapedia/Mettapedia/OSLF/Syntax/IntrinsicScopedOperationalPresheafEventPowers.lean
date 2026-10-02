import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafContextHom
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafPrograms
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedCategoricalModels

/-!
# Actual retained-event function objects

The existing retained evidence presheaf supplies context-indexed categorical
event objects. Their source and target are the real program function objects;
the comparison reads precisely the retained evidence's original endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEventPowers

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open IntrinsicScopedConditionalPresheaf
open IntrinsicScopedJudgmentAction (JudgmentAction)
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedOperationalPresheafContextHom
open MultiBinderPresheaf

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The sorted retained-event source into the original clone's programs. -/
def sourceSemantic (Y : JudgmentAction.{u,u} A) (s : S.Srt) :
    sortEvents Y s ⟶ semanticPrograms A s where
  app X := TypeCat.ofHom (fun event => event.2 ▸ event.1.2.1.1)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl

/-- The sorted retained-event target into the original clone's programs. -/
def targetSemantic (Y : JudgmentAction.{u,u} A) (s : S.Srt) :
    sortEvents Y s ⟶ semanticPrograms A s where
  app X := TypeCat.ofHom (fun event => event.2 ▸ event.1.2.1.2)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl

/-- The genuine sorted source in the represented program presheaf. -/
def source (Y : JudgmentAction.{u,u} A) (s : S.Srt) : sortEvents Y s ⟶ programs A s :=
  sourceSemantic Y s ≫ (programsIso A s).inv

/-- The genuine sorted target in the represented program presheaf. -/
def target (Y : JudgmentAction.{u,u} A) (s : S.Srt) : sortEvents Y s ⟶ programs A s :=
  targetSemantic Y s ≫ (programsIso A s).inv

/-- Retained contextual evidence is the actual whole-context function object. -/
def eventPowerIso (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ≅ (binders A Γ).functorHom (sortEvents Y s) :=
  (contextHomIso A Γ (sortEvents Y s)).symm

/-- Source of a contextual retained event, with every binder represented. -/
def sourcePower (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ IntrinsicScopedOperationalPresheafPrograms.power A Γ s :=
  (eventPowerIso Y Γ s).hom ≫ (FunctorToTypes.rightAdj (binders A Γ)).map (source Y s)

/-- Target of the same contextual retained event. -/
def targetPower (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ IntrinsicScopedOperationalPresheafPrograms.power A Γ s :=
  (eventPowerIso Y Γ s).hom ≫ (FunctorToTypes.rightAdj (binders A Γ)).map (target Y s)

/-- The source function reads the exact original source at the extended context. -/
theorem sourcePower_body (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (X : Base A) (event : (events Y Γ s).obj X) :
    scopedBodyEquiv A X.unop Γ s ((sourcePower Y Γ s).app X event) =
      (sourceBody Y Γ s).app X event := by
  have compared := contextHomAtEquiv_map A Γ (source Y s) X
    ((eventPowerIso Y Γ s).hom.app X event)
  have recovered : contextHomAtEquiv A Γ (sortEvents Y s) X
      ((eventPowerIso Y Γ s).hom.app X event) = event :=
    (contextHomAtEquiv A Γ (sortEvents Y s) X).apply_symm_apply event
  rw [recovered] at compared
  have evaluated := congrArg (programsAtEquiv A s ((binderExtension A Γ).obj X)) compared
  change scopedBodyEquiv A X.unop Γ s ((sourcePower Y Γ s).app X event) =
    programsAtEquiv A s ((binderExtension A Γ).obj X)
      ((source Y s).app ((binderExtension A Γ).obj X) event) at evaluated
  exact evaluated

/-- The target function reads the exact original target at the same extended context. -/
theorem targetPower_body (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt)
    (X : Base A) (event : (events Y Γ s).obj X) :
    scopedBodyEquiv A X.unop Γ s ((targetPower Y Γ s).app X event) =
      (targetBody Y Γ s).app X event := by
  have compared := contextHomAtEquiv_map A Γ (target Y s) X
    ((eventPowerIso Y Γ s).hom.app X event)
  have recovered : contextHomAtEquiv A Γ (sortEvents Y s) X
      ((eventPowerIso Y Γ s).hom.app X event) = event :=
    (contextHomAtEquiv A Γ (sortEvents Y s) X).apply_symm_apply event
  rw [recovered] at compared
  have evaluated := congrArg (programsAtEquiv A s ((binderExtension A Γ).obj X)) compared
  change scopedBodyEquiv A X.unop Γ s ((targetPower Y Γ s).app X event) =
    programsAtEquiv A s ((binderExtension A Γ).obj X)
      ((target Y s).app ((binderExtension A Γ).obj X) event) at evaluated
  exact evaluated

/-- The actual categorical event objects of any existing substitution action. -/
def objects (Y : JudgmentAction.{u,u} A) :
    IntrinsicScopedLocalActedCategoricalModels.EventObjects
      (IntrinsicScopedOperationalPresheafPrograms.model A) where
  event := events Y
  source := sourcePower Y
  target := targetPower Y

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEventPowers
