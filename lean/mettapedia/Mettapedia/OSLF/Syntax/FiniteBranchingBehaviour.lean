import Mettapedia.CategoryTheory.FinitePowerset
import Mettapedia.OSLF.Syntax.DeterministicGSOSBehaviour

/-!
# Actual labelwise finitely branching behavior

Each action has finitely many successors. The action carrier remains arbitrary,
so infinitely many different actions may be enabled. Direct image relabels the
complete finite successor set. The deterministic profile embeds naturally;
neither total finite support nor receipt recovery is inferred.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

abbrev Behaviour (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt) :=
  Actions sort → Finset (X base sort)

def behaviourMap {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (behaviour : Behaviour S Actions X base sort) : Behaviour S Actions Y base sort :=
  fun action => Mettapedia.CategoryTheory.FinitePowerset.map (mapping base sort) (behaviour action)

def behaviourFunctor : S.Families ⥤ S.Families where
  obj X := Behaviour S Actions X
  map mapping := fun base sort => ↾(behaviourMap S Actions mapping base sort)
  map_id _ := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    exact Mettapedia.CategoryTheory.FinitePowerset.map_identity (behaviour action)
  map_comp before after := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    exact (Mettapedia.CategoryTheory.FinitePowerset.map_compose
      (before base sort) (after base sort) (behaviour action)).symm

def sourceBehaviourFunctor : S.Families ⥤ S.Families where
  obj X := fun base sort => X base sort × Behaviour S Actions X base sort
  map mapping := fun base sort => ↾(fun pair =>
    (mapping base sort pair.1, behaviourMap S Actions mapping base sort pair.2))
  map_id _ := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · funext action
      exact Mettapedia.CategoryTheory.FinitePowerset.map_identity (pair.2 action)
  map_comp before after := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro pair
    apply Prod.ext
    · rfl
    · funext action
      exact (Mettapedia.CategoryTheory.FinitePowerset.map_compose
        (before base sort) (after base sort) (pair.2 action)).symm

abbrev Law := sourceBehaviourFunctor S Actions ⋙ S.syntaxFunctor ⟶
  S.termMonad.toFunctor ⋙ behaviourFunctor S Actions

def deterministicEmbedding : DeterministicGSOS.behaviourFunctor S Actions ⟶
    behaviourFunctor S Actions where
  app X := fun base sort => ↾(fun behaviour action =>
    (behaviour action : Option (X base sort)).toFinset)
  naturality {X Y} mapping := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro behaviour
    funext action
    exact (Mettapedia.CategoryTheory.FinitePowerset.map_option
      (mapping base sort) (behaviour action)).symm

theorem deterministicEmbedding_injective (X : S.Families)
    (base : PUnit.{u + 1}) (sort : S.Srt) :
    Function.Injective ((deterministicEmbedding S Actions).app X base sort) := by
  intro first second same
  funext action
  exact Mettapedia.CategoryTheory.FinitePowerset.option_injective
    (congrArg (fun behaviour : Behaviour S Actions X base sort => behaviour action) same)

theorem availability_preserved {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (behaviour : Behaviour S Actions X base sort) (action : Actions sort) :
    behaviourMap S Actions mapping base sort behaviour action = ∅ ↔ behaviour action = ∅ :=
  Mettapedia.CategoryTheory.FinitePowerset.map_eq_empty_iff _ _

end Mettapedia.OSLF.FiniteBranching
