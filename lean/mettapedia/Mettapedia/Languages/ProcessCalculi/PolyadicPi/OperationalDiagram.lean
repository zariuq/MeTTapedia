import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.OSLF.Syntax.BindingInstantiationNaturality
import Mettapedia.CategoryTheory.InternalCategoryPathMaps

/-!
# Complete COMM occurrence diagrams with structural endpoints

The independent reaction tree retains unary or binary communication and
every parallel or private-scope descent. Structural endpoint envelopes are
separate from that tree. Their complete substitution action and endpoint
readouts give an actual internal path category on the context presheaf.
Neither inactive input bodies nor replication are operational descent sites.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.OperationalDiagram

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding

inductive Reaction : Ctx sig → Type where
  | unary {Γ} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) : Reaction Γ
  | binary {Γ} (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) : Reaction Γ
  | parallelLeft {Γ} (before : Reaction Γ) (frame : Proc Γ) : Reaction Γ
  | parallelRight {Γ} (frame : Proc Γ) (before : Reaction Γ) : Reaction Γ
  | restriction {Γ} (before : Reaction (.nm :: Γ)) : Reaction Γ

namespace Reaction

theorem pairSub_comparison {Γ : Ctx sig} (first second : Name Γ) :
    pairSub first second = extendTwo first second := by
  funext sort position
  cases position <;> rfl

def source : {Γ : Ctx sig} → Reaction Γ → Proc Γ
  | _, .unary channel datum body => par (out1 channel datum) (inp1 channel body)
  | _, .binary channel first second body => par (out2 channel first second) (inp2 channel body)
  | _, .parallelLeft before frame => par before.source frame
  | _, .parallelRight frame before => par frame before.source
  | _, .restriction before => nu before.source

def target : {Γ : Ctx sig} → Reaction Γ → Proc Γ
  | _, .unary _ datum body => inst body datum
  | _, .binary _ first second body => openPair body first second
  | _, .parallelLeft before frame => par before.target frame
  | _, .parallelRight frame before => par frame before.target
  | _, .restriction before => nu before.target

theorem sound {Γ : Ctx sig} (reaction : Reaction Γ) : Step reaction.source reaction.target := by
  induction reaction with
  | unary channel datum body => exact .comm1 channel datum body
  | binary channel first second body => exact .comm2 channel first second body
  | parallelLeft before frame ih => exact .parL frame ih
  | parallelRight frame before ih => exact .parR frame ih
  | restriction before ih => exact .nu ih

theorem complete {Γ : Ctx sig} {first last : Proc Γ} (step : Step first last) :
    ∃ reaction : Reaction Γ, reaction.source = first ∧ reaction.target = last := by
  induction step with
  | comm1 channel datum body => exact ⟨.unary channel datum body, rfl, rfl⟩
  | comm2 channel first second body => exact ⟨.binary channel first second body, rfl, rfl⟩
  | parL frame step ih =>
      obtain ⟨reaction, rfl, rfl⟩ := ih
      exact ⟨.parallelLeft reaction frame, rfl, rfl⟩
  | parR frame step ih =>
      obtain ⟨reaction, rfl, rfl⟩ := ih
      exact ⟨.parallelRight frame reaction, rfl, rfl⟩
  | nu step ih =>
      obtain ⟨reaction, rfl, rfl⟩ := ih
      exact ⟨.restriction reaction, rfl, rfl⟩

def substitute : {Γ Δ : Ctx sig} → Sub sig Γ Δ → Reaction Γ → Reaction Δ
  | _, _, assigned, .unary channel datum body =>
      .unary (bind assigned channel) (bind assigned datum) (bind (liftSub assigned [.nm]) body)
  | _, _, assigned, .binary channel first second body =>
      .binary (bind assigned channel) (bind assigned first) (bind assigned second)
        (bind (liftSub assigned [.nm, .nm]) body)
  | _, _, assigned, .parallelLeft before frame => .parallelLeft (substitute assigned before) (bind assigned frame)
  | _, _, assigned, .parallelRight frame before => .parallelRight (bind assigned frame) (substitute assigned before)
  | _, _, assigned, .restriction before => .restriction (substitute (liftSub assigned [.nm]) before)

theorem substitute_identity {Γ : Ctx sig} (reaction : Reaction Γ) :
    reaction.substitute (fun _ position => .var position) = reaction := by
  induction reaction with
  | unary channel datum body => simp only [substitute, liftSub_var, bind_id]
  | binary channel first second body => simp only [substitute, liftSub_var, bind_id]
  | parallelLeft before frame ih => simp only [substitute, bind_id, ih]
  | parallelRight frame before ih => simp only [substitute, bind_id, ih]
  | restriction before ih =>
      simp only [substitute, liftSub_var]
      exact congrArg Reaction.restriction ih

theorem substitute_composition {Γ Δ Ξ : Ctx sig} (reaction : Reaction Γ)
    (first : Sub sig Γ Δ) (second : Sub sig Δ Ξ) :
    (reaction.substitute first).substitute second =
      reaction.substitute (fun sort position => bind second (first sort position)) := by
  induction reaction generalizing Δ Ξ with
  | unary channel datum body =>
      simp only [substitute, bind_comp]
      rw [liftSub_comp first second [.nm]]
  | binary channel arg return_ body =>
      simp only [substitute, bind_comp]
      rw [liftSub_comp first second [.nm, .nm]]
  | parallelLeft before frame ih => simp only [substitute, bind_comp, ih]
  | parallelRight frame before ih => simp only [substitute, bind_comp, ih]
  | restriction before ih =>
      simp only [substitute, ih]
      exact congrArg (fun assigned => Reaction.restriction (substitute assigned before))
        (liftSub_comp first second [.nm])

theorem source_substitution {Γ Δ : Ctx sig} (reaction : Reaction Γ) (assigned : Sub sig Γ Δ) :
    (reaction.substitute assigned).source = bind assigned reaction.source := by
  induction reaction generalizing Δ with
  | unary => rfl
  | binary => rfl
  | parallelLeft before frame ih => exact congrArg (fun p => par p (bind assigned frame)) (ih assigned)
  | parallelRight frame before ih => exact congrArg (par (bind assigned frame)) (ih assigned)
  | restriction before ih => exact congrArg nu (ih (liftSub assigned [.nm]))

theorem target_substitution {Γ Δ : Ctx sig} (reaction : Reaction Γ) (assigned : Sub sig Γ Δ) :
    (reaction.substitute assigned).target = bind assigned reaction.target := by
  induction reaction generalizing Δ with
  | unary channel datum body => exact (inst_substitution body datum assigned).symm
  | binary channel first second body =>
      simp only [target, substitute, openPair]
      rw [pairSub_comparison, pairSub_comparison]
      exact (instTwo_substitution body first second assigned).symm
  | parallelLeft before frame ih => exact congrArg (fun p => par p (bind assigned frame)) (ih assigned)
  | parallelRight frame before ih => exact congrArg (par (bind assigned frame)) (ih assigned)
  | restriction before ih => exact congrArg nu (ih (liftSub assigned [.nm]))

end Reaction

theorem structural_substitution {Γ Δ : Ctx sig} {first last : Proc Γ}
    (equal : StructuralEq first last) (assigned : Sub sig Γ Δ) :
    StructuralEq (bind assigned first) (bind assigned last) :=
  (AuthoredEquations.eqClosure_iff_structuralEq _ _).mp
    (eqClosure_bind assigned (AuthoredEquations.structuralEq_complete equal))

structure Event (Γ : Ctx sig) where
  source : Proc Γ
  target : Proc Γ
  reaction : Reaction Γ
  source_readout : StructuralEq source reaction.source
  target_readout : StructuralEq reaction.target target

namespace Event

def ofReaction {Γ : Ctx sig} (reaction : Reaction Γ) : Event Γ :=
  ⟨reaction.source, reaction.target, reaction, .refl _, .refl _⟩

def parallelLeft {Γ : Ctx sig} (event : Event Γ) (frame : Proc Γ) : Event Γ where
  source := par event.source frame
  target := par event.target frame
  reaction := .parallelLeft event.reaction frame
  source_readout := .par event.source_readout (.refl frame)
  target_readout := .par event.target_readout (.refl frame)

def parallelRight {Γ : Ctx sig} (frame : Proc Γ) (event : Event Γ) : Event Γ where
  source := par frame event.source
  target := par frame event.target
  reaction := .parallelRight frame event.reaction
  source_readout := .par (.refl frame) event.source_readout
  target_readout := .par (.refl frame) event.target_readout

def restriction {Γ : Ctx sig} (event : Event (.nm :: Γ)) : Event Γ where
  source := nu event.source
  target := nu event.target
  reaction := .restriction event.reaction
  source_readout := .nu event.source_readout
  target_readout := .nu event.target_readout

theorem sound {Γ : Ctx sig} (event : Event Γ) : StepModulo event.source event.target :=
  ⟨event.reaction.source, event.reaction.target,
    event.source_readout, event.reaction.sound, event.target_readout⟩

theorem complete {Γ : Ctx sig} {first last : Proc Γ} (step : StepModulo first last) :
    ∃ event : Event Γ, event.source = first ∧ event.target = last := by
  obtain ⟨before, after, sourceEqual, firing, targetEqual⟩ := step
  obtain ⟨reaction, reactionSource, reactionTarget⟩ := Reaction.complete firing
  exact ⟨⟨first, last, reaction, reactionSource ▸ sourceEqual,
    reactionTarget ▸ targetEqual⟩, rfl, rfl⟩

def substitute {Γ Δ : Ctx sig} (assigned : Sub sig Γ Δ) (event : Event Γ) : Event Δ where
  source := bind assigned event.source
  target := bind assigned event.target
  reaction := event.reaction.substitute assigned
  source_readout := by
    rw [Reaction.source_substitution]
    exact structural_substitution event.source_readout assigned
  target_readout := by
    rw [Reaction.target_substitution]
    exact structural_substitution event.target_readout assigned

@[ext] theorem ext {Γ : Ctx sig} {first second : Event Γ}
    (sourceEqual : first.source = second.source) (targetEqual : first.target = second.target)
    (reactionEqual : first.reaction = second.reaction) : first = second := by
  cases first
  cases second
  cases sourceEqual
  cases targetEqual
  cases reactionEqual
  rfl

theorem substitute_identity {Γ : Ctx sig} (event : Event Γ) :
    event.substitute (fun _ position => .var position) = event := by
  apply Event.ext
  · exact bind_id event.source
  · exact bind_id event.target
  · exact event.reaction.substitute_identity

theorem substitute_composition {Γ Δ Ξ : Ctx sig} (event : Event Γ)
    (first : Sub sig Γ Δ) (second : Sub sig Δ Ξ) :
    (event.substitute first).substitute second =
      event.substitute (fun sort position => bind second (first sort position)) := by
  apply Event.ext
  · exact bind_comp first second event.source
  · exact bind_comp first second event.target
  · exact event.reaction.substitute_composition first second

end Event

abbrev Base := (Syntactic.Ctxt sig)ᵒᵖ
abbrev programs : Base ⥤ Type := Syntactic.termPresheaf sig .pr

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
  naturality _ _ _ := rfl

def target : events ⟶ programs where
  app _ := TypeCat.ofHom Event.target
  naturality _ _ _ := rfl

def graph : Mettapedia.CategoryTheory.InternalGraph (Base ⥤ Type) :=
  ⟨programs, events, source, target⟩

noncomputable def internalCategory : Mettapedia.CategoryTheory.InternalCategory (Base ⥤ Type) :=
  Mettapedia.CategoryTheory.InternalCategoryPathDiagram.category graph

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.OperationalDiagram
