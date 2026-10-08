import Mettapedia.OSLF.Syntax.DeterministicGSOSSignature

/-!
# Arbitrary-action labelwise deterministic behavior

A state supplies at most one successor for each action. Renaming preserves
action availability and maps the complete successor. The action carriers
are independent of the variable families and may be infinite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

/-- A complete labelwise deterministic behavior at one sort. -/
abbrev Behaviour (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt) :=
  Actions sort → Option (X base sort)

/-- Relabel all successors; absence of an action is preserved. -/
def behaviourMap {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (behaviour : Behaviour S Actions X base sort) :
    Behaviour S Actions Y base sort :=
  fun action => (behaviour action).map (mapping base sort)

/-- The actual endofunctor of deterministic labeled transition readouts. -/
def behaviourFunctor : S.Families ⥤ S.Families where
  obj X := Behaviour S Actions X
  map mapping := fun base sort => ↾(behaviourMap S Actions mapping base sort)
  map_id X := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    change (behaviour action).map (fun value => value) = behaviour action
    cases behaviour action <;> rfl
  map_comp earlier later := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    change (behaviour action).map (fun value => later base sort (earlier base sort value)) =
      ((behaviour action).map (earlier base sort)).map (later base sort)
    cases behaviour action <;> rfl

/-- Each argument retains its source value and complete behavior. -/
def sourceBehaviourFunctor : S.Families ⥤ S.Families where
  obj X := fun base sort => X base sort × Behaviour S Actions X base sort
  map mapping := fun base sort => ↾(fun pair =>
    (mapping base sort pair.1, behaviourMap S Actions mapping base sort pair.2))
  map_id X := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · funext action
      change (pair.2 action).map (fun value => value) = pair.2 action
      cases pair.2 action <;> rfl
  map_comp earlier later := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · funext action
      change (pair.2 action).map (fun value => later base sort (earlier base sort value)) =
        ((pair.2 action).map (earlier base sort)).map (later base sort)
      cases pair.2 action <;> rfl

/-- Constructor inputs include original arguments and their full behaviors. -/
abbrev BehaviourArguments (X : S.Families) {sort : S.Srt}
    (operator : S.Operator sort) :=
  (position : S.Position operator) →
    X PUnit.unit (S.argument operator position) ×
      Behaviour S Actions X PUnit.unit (S.argument operator position)

/-- Abstract GSOS laws are actual natural transformations of indexed families. -/
abbrev Law :=
  sourceBehaviourFunctor S Actions ⋙ S.syntaxFunctor ⟶
    S.termMonad.toFunctor ⋙ behaviourFunctor S Actions

end Mettapedia.OSLF.DeterministicGSOS
