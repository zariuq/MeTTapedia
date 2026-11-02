import Mettapedia.Logic.HOL.ConstructorProjections

/-!
# Constructor projections restricted to an admitted argument relation

The admission predicate may relate all three arguments. Both the uniqueness
law and the selected witness retain that predicate. The constructor may erase
its first argument; the selected second and third fields are recovered only
at admitted inputs. No behavior outside the admitted image is specified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.GuardedConstructorProjections
open ConstructorProjections (Constructor apply)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {first second third carrier : Ty Base}

abbrev Admission (first second third : Ty Base) := first ⇒ second ⇒ third ⇒ .prop

def admitted (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) : Formula Const Γ :=
  apply domain a b c

def components (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) : Formula Const Γ :=
  .all (.all (.all (.imp
    (admitted (weaken (weaken (weaken domain))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
    (.imp
      (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
        (weaken (weaken (weaken (apply constructor a b c)))))
      (.and (.eq (.var (.vs .vz)) (weaken (weaken (weaken b))))
        (.eq (.var .vz) (weaken (weaken (weaken c)))))))))

def fieldInjective (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) : Formula Const Γ :=
  .all (.all (.all (.imp
    (admitted (weaken (weaken (weaken domain))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
    (components (weaken (weaken (weaken constructor))) (weaken (weaken (weaken domain)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))))

def secondBody (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) : Formula Const (second :: Γ) :=
  .ex (σ := first) (.ex (σ := third) (.and
    (admitted (weaken (weaken (weaken domain))) (.var (.vs .vz)) (.var (.vs (.vs .vz))) (.var .vz))
    (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs .vz)) (.var (.vs (.vs .vz))) (.var .vz))
      (weaken (weaken (weaken value))))))

def thirdBody (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) : Formula Const (third :: Γ) :=
  .ex (σ := first) (.ex (σ := second) (.and
    (admitted (weaken (weaken (weaken domain))) (.var (.vs .vz)) (.var .vz) (.var (.vs (.vs .vz))))
    (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs .vz)) (.var .vz) (.var (.vs (.vs .vz))))
      (weaken (weaken (weaken value))))))

def secondValue (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) : Term Const Γ second :=
  SelectionProofs.selected selection (secondBody constructor domain value)

def thirdValue (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) : Term Const Γ third :=
  SelectionProofs.selected selection (thirdBody constructor domain value)

def secondProjection (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) : Term Const Γ (carrier ⇒ second) :=
  .lam (secondValue (weaken selection) (weaken constructor) (weaken domain) (.var .vz))

def thirdProjection (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) : Term Const Γ (carrier ⇒ third) :=
  .lam (thirdValue (weaken selection) (weaken constructor) (weaken domain) (.var .vz))

@[simp] theorem subst_admitted (images : Subst Const Γ Ξ)
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    subst images (admitted domain a b c) = admitted (subst images domain) (subst images a) (subst images b) (subst images c) := rfl

@[simp] theorem subst_components (images : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    subst images (components constructor domain a b c) =
      components (subst images constructor) (subst images domain) (subst images a) (subst images b) (subst images c) := by
  simp [components,admitted,subst,subst_weaken,Subst.lift,Rename.weaken]

@[simp] theorem subst_fieldInjective (images : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) :
    subst images (fieldInjective constructor domain) = fieldInjective (subst images constructor) (subst images domain) := by
  simp [fieldInjective,admitted,subst,subst_weaken,Subst.lift,Rename.weaken]

theorem rename_components (images : Rename Base Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    rename images (components constructor domain a b c) =
      components (rename images constructor) (rename images domain) (rename images a) (rename images b) (rename images c) := by
  simpa only [subst_ofRename] using subst_components (Subst.ofRename images) constructor domain a b c

@[simp] theorem subst_secondBody (images : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    subst (Subst.lift images) (secondBody constructor domain value) =
      secondBody (subst images constructor) (subst images domain) (subst images value) := by
  simp [secondBody,admitted,subst,subst_weaken,Subst.lift,Rename.weaken]

@[simp] theorem subst_thirdBody (images : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    subst (Subst.lift images) (thirdBody constructor domain value) =
      thirdBody (subst images constructor) (subst images domain) (subst images value) := by
  simp [thirdBody,admitted,subst,subst_weaken,Subst.lift,Rename.weaken]

@[simp] theorem subst_secondProjection (images : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) :
    subst images (secondProjection selection constructor domain) =
      secondProjection (subst images selection) (subst images constructor) (subst images domain) := by
  simp [secondProjection,secondValue,SelectionProofs.selected,subst,Subst.lift]

@[simp] theorem subst_thirdProjection (images : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) :
    subst images (thirdProjection selection constructor domain) =
      thirdProjection (subst images selection) (subst images constructor) (subst images domain) := by
  simp [thirdProjection,thirdValue,SelectionProofs.selected,subst,Subst.lift]

@[simp] theorem subst_secondValue (images : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    subst images (secondValue selection constructor domain value) =
      secondValue (subst images selection) (subst images constructor) (subst images domain) (subst images value) := by
  simp [secondValue,SelectionProofs.selected,subst]

@[simp] theorem subst_thirdValue (images : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    subst images (thirdValue selection constructor domain value) =
      thirdValue (subst images selection) (subst images constructor) (subst images domain) (subst images value) := by
  simp [thirdValue,SelectionProofs.selected,subst]

end Mettapedia.Logic.HOL.GuardedConstructorProjections
