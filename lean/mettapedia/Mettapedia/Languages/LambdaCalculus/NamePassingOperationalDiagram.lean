import Mettapedia.Languages.LambdaCalculus.NamePassingPresentationEquations
import Mettapedia.OSLF.Syntax.BindingInstantiationNaturality
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mettapedia.CategoryTheory.InternalCategoryPathMaps

/-!
# The retained operational diagram of open name-passing lambda terms

The independent occurrence tree has precisely the displayed beta and fetch
roots and the active application, definition and carrier positions. Its
substitution action changes stored terms and respects the reference binder.
The complete context-presheaf graph generates an actual internal path
category; its edge object is not equality of terms or a reachability flag.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.OperationalDiagram

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Presentation

inductive Event : Ctx signature → Type where
  | beta {Γ} (body : Program (.nm :: Γ)) (argument : Name Γ) : Event Γ
  | fetch {Γ} (name : Name Γ) (value : Program Γ) : Event Γ
  | application {Γ} (argument : Name Γ) (before : Event Γ) : Event Γ
  | definition {Γ} (value : Program Γ) (before : Event (.nm :: Γ)) : Event Γ
  | carrier {Γ} (name : Name Γ) (value : Program Γ) (before : Event Γ) : Event Γ

namespace Event

def source : {Γ : Ctx signature} → Event Γ → Program Γ
  | _, .beta body argument => Presentation.application (abstraction body) argument
  | _, .fetch name value => Presentation.carrier name value (reference name)
  | _, .application argument before => Presentation.application before.source argument
  | _, .definition value before => Presentation.definition value before.source
  | _, .carrier name value before => Presentation.carrier name value before.source

def target : {Γ : Ctx signature} → Event Γ → Program Γ
  | _, .beta body argument => inst body argument
  | _, .fetch _ value => value
  | _, .application argument before => Presentation.application before.target argument
  | _, .definition value before => Presentation.definition value before.target
  | _, .carrier name value before => Presentation.carrier name value before.target

def occurrence : {Γ : Ctx signature} → (event : Event Γ) → ActiveEdge event.source event.target
  | _, .beta body argument => .root (.beta body argument)
  | _, .fetch name value => .root (.fetch name value)
  | _, .application argument before => .application argument before.occurrence
  | _, .definition value before => .definition value before.occurrence
  | _, .carrier name value before => .carrier name value before.occurrence

def fromOccurrence : {Γ : Ctx signature} → {first last : Program Γ} → ActiveEdge first last → Event Γ
  | _, _, _, .root (.beta body argument) => .beta body argument
  | _, _, _, .root (.fetch name value) => .fetch name value
  | _, _, _, .application argument before => .application argument (fromOccurrence before)
  | _, _, _, .definition value before => .definition value (fromOccurrence before)
  | _, _, _, .carrier name value before => .carrier name value (fromOccurrence before)

theorem from_occurrence {Γ : Ctx signature} (event : Event Γ) :
    fromOccurrence event.occurrence = event := by
  induction event with
  | beta => rfl
  | fetch => rfl
  | application argument before ih => exact congrArg (Event.application argument) ih
  | definition value before ih => exact congrArg (Event.definition value) ih
  | carrier name value before ih => exact congrArg (Event.carrier name value) ih

def substitute : {Γ Δ : Ctx signature} → Sub signature Γ Δ → Event Γ → Event Δ
  | _, _, assigned, .beta body argument =>
      .beta (bind (liftSub assigned [.nm]) body) (bind assigned argument)
  | _, _, assigned, .fetch name value => .fetch (bind assigned name) (bind assigned value)
  | _, _, assigned, .application argument before =>
      .application (bind assigned argument) (substitute assigned before)
  | _, _, assigned, .definition value before =>
      .definition (bind assigned value) (substitute (liftSub assigned [.nm]) before)
  | _, _, assigned, .carrier name value before =>
      .carrier (bind assigned name) (bind assigned value) (substitute assigned before)

theorem substitute_identity {Γ : Ctx signature} (event : Event Γ) :
    event.substitute (fun _ position => .var position) = event := by
  induction event with
  | beta body argument => simp only [substitute, liftSub_var, bind_id]
  | fetch name value => simp only [substitute, bind_id]
  | application argument before ih => simp only [substitute, bind_id, ih]
  | definition value before ih =>
      simp only [substitute, liftSub_var, bind_id]
      exact congrArg (Event.definition value) ih
  | carrier name value before ih => simp only [substitute, bind_id, ih]

theorem substitute_composition {Γ Δ Ξ : Ctx signature} (event : Event Γ)
    (first : Sub signature Γ Δ) (second : Sub signature Δ Ξ) :
    (event.substitute first).substitute second =
      event.substitute (fun sort position => bind second (first sort position)) := by
  induction event generalizing Δ Ξ with
  | beta body argument =>
      simp only [substitute, bind_comp]
      rw [liftSub_comp first second [.nm]]
  | fetch name value => simp only [substitute, bind_comp]
  | application argument before ih => simp only [substitute, bind_comp, ih]
  | definition value before ih =>
      simp only [substitute, bind_comp, ih]
      exact congrArg
        (fun assigned => Event.definition (bind (fun s v => bind second (first s v)) value)
          (substitute assigned before)) (liftSub_comp first second [.nm])
  | carrier name value before ih => simp only [substitute, bind_comp, ih]

theorem instantiate_substitution {Γ Δ : Ctx signature} (body : Program (.nm :: Γ))
    (argument : Name Γ) (assigned : Sub signature Γ Δ) :
    bind assigned (inst body argument) =
      inst (bind (liftSub assigned [.nm]) body) (bind assigned argument) :=
  inst_substitution body argument assigned

theorem source_substitution {Γ Δ : Ctx signature} (event : Event Γ)
    (assigned : Sub signature Γ Δ) :
    (event.substitute assigned).source = bind assigned event.source := by
  induction event generalizing Δ with
  | beta body argument => rfl
  | fetch name value => rfl
  | application argument before ih =>
      exact congrArg (fun function => Presentation.application function (bind assigned argument)) (ih assigned)
  | definition value before ih =>
      exact congrArg (Presentation.definition (bind assigned value)) (ih (liftSub assigned [.nm]))
  | carrier name value before ih =>
      exact congrArg (Presentation.carrier (bind assigned name) (bind assigned value)) (ih assigned)

theorem target_substitution {Γ Δ : Ctx signature} (event : Event Γ)
    (assigned : Sub signature Γ Δ) :
    (event.substitute assigned).target = bind assigned event.target := by
  induction event generalizing Δ with
  | beta body argument => exact (instantiate_substitution body argument assigned).symm
  | fetch name value => rfl
  | application argument before ih =>
      exact congrArg (fun function => Presentation.application function (bind assigned argument)) (ih assigned)
  | definition value before ih =>
      exact congrArg (Presentation.definition (bind assigned value)) (ih (liftSub assigned [.nm]))
  | carrier name value before ih =>
      exact congrArg (Presentation.carrier (bind assigned name) (bind assigned value)) (ih assigned)

end Event

abbrev Base := (Syntactic.Ctxt signature)ᵒᵖ
abbrev programs : Base ⥤ Type := Syntactic.termPresheaf signature .tm

def events : Base ⥤ Type where
  obj X := Event X.unop.vars
  map change := TypeCat.ofHom (Event.substitute change.unop)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.substitute_identity
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (event.substitute_composition first.unop second.unop).symm

def source : events ⟶ programs where
  app _ := TypeCat.ofHom Event.source
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.source_substitution change.unop

def target : events ⟶ programs where
  app _ := TypeCat.ofHom Event.target
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro event
    exact event.target_substitution change.unop

def graph : Mettapedia.CategoryTheory.InternalGraph (Base ⥤ Type) :=
  ⟨programs, events, source, target⟩

noncomputable def internalCategory : Mettapedia.CategoryTheory.InternalCategory (Base ⥤ Type) :=
  Mettapedia.CategoryTheory.InternalCategoryPathDiagram.category graph

end Mettapedia.Languages.LambdaCalculus.NamePassing.OperationalDiagram
