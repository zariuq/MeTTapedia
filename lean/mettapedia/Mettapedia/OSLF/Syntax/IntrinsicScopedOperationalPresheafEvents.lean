import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentActionPresheaf
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# Context-indexed operational events in the clone presheaf target

The event object for an explicit program context is the fixed-sort fiber of
actual retained evidence after extending each ambient stage by that context.
Its endpoints are the existing binder-body presheaves. Larger evidence
universes are retained by explicitly raising the endpoint universe.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEvents

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedJudgmentAction (JudgmentAction)
open MultiBinderPresheaf

universe u w
variable {S : Signature}

/-- The actual ambient-context functor leaves every selected binder untouched. -/
def binderExtension (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) : Base A ⥤ Base A where
  obj X := Opposite.op (concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone Γ) X.unop)
  map f := Quiver.Hom.op (extendScope A Γ f.unop)
  map_id X := congrArg Quiver.Hom.op (extendScope_id A Γ X.unop)
  map_comp f g := congrArg Quiver.Hom.op (extendScope_comp A Γ g.unop f.unop)

/-- The selected-sort fiber of the common retained-event presheaf. -/
def sortEvents {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,w} A) (s : S.Srt) : Base A ⥤ Type (max u w) where
  obj X := {event : (IntrinsicScopedJudgmentActionPresheaf.events Y).obj X // event.1 = s}
  map f := TypeCat.ofHom (fun event =>
    ⟨(IntrinsicScopedJudgmentActionPresheaf.events Y).map f event.1, event.2⟩)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((IntrinsicScopedJudgmentActionPresheaf.events Y).map_id X) event.1
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((IntrinsicScopedJudgmentActionPresheaf.events Y).map_comp f g) event.1

/-- The contextual event object retains every actual evidence value of the selected sort. -/
abbrev events {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,w} A) (Γ : Ctx S) (s : S.Srt) : Base A ⥤ Type (max u w) :=
  binderExtension A Γ ⋙ sortEvents Y s

/-- The indexed fiber has precisely the actual context/sort/endpoint carrier. -/
def eventAtEquiv {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,w} A) (Γ : Ctx S) (s : S.Srt) (X : Base A) :
    (events Y Γ s).obj X ≃
      Σ pair : A.substitution.Carrier (Γ ++ X.unop.context) s ×
        A.substitution.Carrier (Γ ++ X.unop.context) s,
        Y.carrier ⟨Γ ++ X.unop.context, s, pair⟩ where
  toFun event := event.2 ▸ event.1.2
  invFun value := ⟨⟨s, value.1, value.2⟩, rfl⟩
  left_inv event := by
    rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl
  right_inv value := rfl

/-- The endpoint presheaf raised to the actual evidence universe. -/
abbrev liftedBodies (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (s : S.Srt) :=
  scopedBodies A Γ s ⋙ uliftFunctor.{w,u}

/-- The retained event's actual source is natural under every ambient substitution. -/
def liftedSource {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,w} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ liftedBodies.{u,w} A Γ s where
  app X := TypeCat.ofHom (fun event => ULift.up (event.2 ▸ event.1.2.1.1))
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl

/-- The retained event's actual target is natural under the same substitution action. -/
def liftedTarget {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,w} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ liftedBodies.{u,w} A Γ s where
  app X := TypeCat.ofHom (fun event => ULift.up (event.2 ▸ event.1.2.1.2))
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl

/-- At matching universes the explicit endpoint lift has a natural inverse. -/
def bodiesLiftIso (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (s : S.Srt) :
    liftedBodies.{u,u} A Γ s ≅ scopedBodies A Γ s where
  hom := { app X := TypeCat.ofHom ULift.down, naturality := by intros; rfl }
  inv := { app X := TypeCat.ofHom ULift.up, naturality := by intros; rfl }
  hom_inv_id := by ext X body; cases body; rfl
  inv_hom_id := by ext X body; rfl

/-- The actual source arrow to the existing binder-body presheaf. -/
def sourceBody {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ scopedBodies A Γ s :=
  liftedSource Y Γ s ≫ (bodiesLiftIso A Γ s).hom

/-- The actual target arrow to the existing binder-body presheaf. -/
def targetBody {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u,u} A) (Γ : Ctx S) (s : S.Srt) :
    events Y Γ s ⟶ scopedBodies A Γ s :=
  liftedTarget Y Γ s ≫ (bodiesLiftIso A Γ s).hom

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEvents
