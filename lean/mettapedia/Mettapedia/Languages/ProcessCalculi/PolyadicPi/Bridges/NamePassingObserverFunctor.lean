import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContexts
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.NatTrans

/-!
# Context translation as a functor and compilation as a natural transformation

The two categories contain independently authored scoped one-hole contexts.
They are observer-context categories, not a claim that a variable-substitution
CwF or the whole native-type functor has been constructed. Plugging interprets
each category in program families; the actual compiler is a natural
transformation between those interpretations along context translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingLambda NamePassingContexts

structure SourceScope where
  context : Ctx sig

structure ProtocolScope where
  context : Ctx sig

instance : Category SourceScope where
  Hom Γ Δ := SourceContext Γ.context Δ.context
  id _ := .hole
  comp first second := second.compose first
  id_comp first := NamePassing.Context.compose_hole first
  comp_id _ := rfl
  assoc first middle last := (NamePassing.Context.compose_assoc last middle first).symm

instance : Category ProtocolScope where
  Hom Γ Δ := ProtocolContexts.Context Γ.context Δ.context
  id _ := .hole
  comp first second := second.compose first
  id_comp first := ProtocolContexts.Context.compose_hole first
  comp_id _ := rfl
  assoc first middle last := (ProtocolContexts.Context.compose_assoc last middle first).symm

def translation : SourceScope ⥤ ProtocolScope where
  obj scope := ⟨scope.context⟩
  map := translate
  map_id _ := rfl
  map_comp first second := translate_compose second first

def sourceInterpretation : SourceScope ⥤ Type where
  obj scope := Expr scope.context
  map context := TypeCat.ofHom (fun source => context.plug source)
  map_id _ := rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro source
    exact NamePassing.Context.plug_compose second first source

def protocolInterpretation : ProtocolScope ⥤ Type where
  obj scope := ProtocolContexts.Program scope.context
  map {before} {after} context := TypeCat.ofHom
    (fun component : ProtocolContexts.Program before.context =>
      (context.plug component : ProtocolContexts.Program after.context))
  map_id _ := rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro component
    exact ProtocolContexts.Context.plug_compose second first component

/-- Naturality is the proved comparison between two independently authored
grammars, at every scope and for every inserted source program. -/
def compilation : sourceInterpretation ⟶ translation ⋙ protocolInterpretation where
  app _ := TypeCat.ofHom program
  naturality := by
    intro before after context
    apply ConcreteCategory.hom_ext
    intro source
    exact (plug_agreement context source).symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverFunctor
