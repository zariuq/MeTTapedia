import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceLambdaSemantics

/-!
# Context morphisms for native trace semantics

The semantic contexts used by the native trace fragment have a contextual
substitution calculus.  A morphism is oriented like a syntactic substitution:
its environment map runs from the target environment to the source.  Context
comprehension lifts the map while retaining the newest component.

Trace products, abstractions and applications commute with these maps by the
actual Aczel-trace substitution laws.  This categorical spine is kept separate
from the subsequent syntax attachment: equating whole dependent context
records would hide transports through their projection fibres.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceContextMorphisms

open Presentation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension extensionSubstitution)
open NativeTraceLambdaSemantics

universe u

/-- Select variables from a semantic context without changing its
environment. -/
def selectContext {n m : Nat} (target : Context.{u} m) (rho : Fin n → Fin m) :
    Context n where
  Environment := target.Environment
  family index := target.family (rho index)
  projection index := target.projection (rho index)

/-- Pull a semantic context back along an environment map. -/
def pullbackContext {n : Nat} (source : Context.{u} n) {Delta : Type (u + 1)}
    (theta : Delta → source.Environment) : Context n where
  Environment := Delta
  family index := source.family index ∘ theta
  projection index point := source.projection index (theta point)

@[simp] theorem selectContext_family {n m : Nat} (target : Context.{u} m)
    (rho : Fin n → Fin m) (index : Fin n) :
    (selectContext target rho).family index = target.family (rho index) := rfl

@[simp] theorem selectContext_projection {n m : Nat} (target : Context.{u} m)
    (rho : Fin n → Fin m) (index : Fin n) :
    (selectContext target rho).projection index = target.projection (rho index) := rfl

@[simp] theorem pullbackContext_family {n : Nat} (source : Context.{u} n)
    {Delta : Type (u + 1)} (theta : Delta → source.Environment) (index : Fin n) :
    (pullbackContext source theta).family index = source.family index ∘ theta := rfl

@[simp] theorem pullbackContext_projection {n : Nat} (source : Context.{u} n)
    {Delta : Type (u + 1)} (theta : Delta → source.Environment) (index : Fin n) :
    (pullbackContext source theta).projection index =
      fun point => source.projection index (theta point) := rfl

/-- A contextual morphism is oriented like substitution: a morphism from a
source context to a target context maps target environments back to source
environments. -/
structure Morphism {n m : Nat} (source : Context.{u} n) (target : Context.{u} m) where
  environment : target.Environment → source.Environment

def Morphism.identity {n : Nat} (context : Context.{u} n) :
    Morphism context context := ⟨id⟩

def Morphism.comp {n m k : Nat} {source : Context.{u} n}
    {middle : Context.{u} m} {target : Context.{u} k}
    (first : Morphism source middle) (second : Morphism middle target) :
    Morphism source target := ⟨first.environment ∘ second.environment⟩

@[simp] theorem Morphism.identity_environment {n : Nat} (context : Context.{u} n) :
    (Morphism.identity context).environment = id := rfl

@[simp] theorem Morphism.comp_environment {n m k : Nat} {source : Context.{u} n}
    {middle : Context.{u} m} {target : Context.{u} k}
    (first : Morphism source middle) (second : Morphism middle target) :
    (first.comp second).environment = first.environment ∘ second.environment := rfl

theorem Morphism.identity_left {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target) :
    (Morphism.identity source).comp morphism = morphism := by
  cases morphism
  rfl

theorem Morphism.identity_right {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target) :
    morphism.comp (Morphism.identity target) = morphism := by
  cases morphism
  rfl

theorem Morphism.comp_assoc {n m k l : Nat} {first : Context.{u} n}
    {second : Context.{u} m} {third : Context.{u} k} {fourth : Context.{u} l}
    (f : Morphism first second) (g : Morphism second third)
    (h : Morphism third fourth) : (f.comp g).comp h = f.comp (g.comp h) := by
  cases f
  cases g
  cases h
  rfl

def Morphism.reindexFamily {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    (family : SetFamily source.Environment) : SetFamily target.Environment :=
  family ∘ morphism.environment

def Morphism.reindexSection {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    {family : SetFamily source.Environment} (termSection : Section family) :
    Section (morphism.reindexFamily family) :=
  fun point => termSection (morphism.environment point)

@[simp] theorem Morphism.reindexFamily_identity {n : Nat}
    (context : Context.{u} n) (family : SetFamily context.Environment) :
    (Morphism.identity context).reindexFamily family = family := rfl

@[simp] theorem Morphism.reindexSection_identity {n : Nat}
    (context : Context.{u} n) {family : SetFamily context.Environment}
    (termSection : Section family) :
    (Morphism.identity context).reindexSection termSection = termSection := rfl

theorem Morphism.reindexFamily_comp {n m k : Nat} {source : Context.{u} n}
    {middle : Context.{u} m} {target : Context.{u} k}
    (first : Morphism source middle) (second : Morphism middle target)
    (family : SetFamily source.Environment) :
    (first.comp second).reindexFamily family =
      second.reindexFamily (first.reindexFamily family) := rfl

theorem Morphism.reindexSection_comp {n m k : Nat} {source : Context.{u} n}
    {middle : Context.{u} m} {target : Context.{u} k}
    (first : Morphism source middle) (second : Morphism middle target)
    {family : SetFamily source.Environment} (termSection : Section family) :
    (first.comp second).reindexSection termSection =
      second.reindexSection (first.reindexSection termSection) := rfl

/-- The comprehension projection is weakening as a contextual morphism. -/
def Morphism.weaken {n : Nat} (context : Context.{u} n)
    (family : SetFamily context.Environment) :
    Morphism context (context.snoc family) :=
  ⟨Sigma.fst⟩

@[simp] theorem Morphism.weaken_environment {n : Nat} (context : Context.{u} n)
    (family : SetFamily context.Environment) :
    (Morphism.weaken context family).environment = Sigma.fst := rfl

/-- Context comprehension lifts a substitution and keeps the newest
component unchanged. -/
def Morphism.lift {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    (family : SetFamily source.Environment) :
    Morphism (source.snoc family)
      (target.snoc (morphism.reindexFamily family)) :=
  ⟨extensionSubstitution morphism.environment family⟩

@[simp] theorem Morphism.lift_base {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    (family : SetFamily source.Environment)
    (point : Extension (morphism.reindexFamily family)) :
    ((morphism.lift family).environment point).1 =
      morphism.environment point.1 := rfl

@[simp] theorem Morphism.lift_newest {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    (family : SetFamily source.Environment)
    (point : Extension (morphism.reindexFamily family)) :
    ((morphism.lift family).environment point).2 = point.2 := rfl

theorem Morphism.lift_identity {n : Nat} (context : Context.{u} n)
    (family : SetFamily context.Environment) :
    (Morphism.identity context).lift family =
      Morphism.identity (context.snoc family) := by
  rfl

theorem Morphism.lift_comp {n m k : Nat} {source : Context.{u} n}
    {middle : Context.{u} m} {target : Context.{u} k}
    (first : Morphism source middle) (second : Morphism middle target)
    (family : SetFamily source.Environment) :
    (first.comp second).lift family =
      (first.lift family).comp (second.lift (first.reindexFamily family)) := by
  rfl

/-- Trace dependent products commute strictly with contextual reindexing. -/
theorem Morphism.tracePi_reindex {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    (domain : SetFamily source.Environment)
    (codomain : SetFamily (Extension domain)) :
    morphism.reindexFamily (ZFSetTraceContextual.piFamily domain codomain) =
      ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
        (codomain ∘ (morphism.lift domain).environment) :=
  ZFSetTraceContextual.piFamily_substitution morphism.environment domain codomain

/-- Trace abstraction commutes with contextual reindexing. -/
theorem Morphism.traceLam_reindex {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    {domain : SetFamily source.Environment}
    {codomain : SetFamily (Extension domain)} (body : Section codomain) :
    morphism.reindexSection (ZFSetTraceContextual.lam body) =
      ZFSetTraceContextual.lam
        (fun point => body ((morphism.lift domain).environment point)) :=
  ZFSetTraceContextual.lam_substitution morphism.environment body

/-- Trace application commutes with contextual reindexing. -/
theorem Morphism.traceApp_reindex {n m : Nat} {source : Context.{u} n}
    {target : Context.{u} m} (morphism : Morphism source target)
    {domain : SetFamily source.Environment}
    {codomain : SetFamily (Extension domain)}
    (function : Section (ZFSetTraceContextual.piFamily domain codomain))
    (argument : Section domain) :
    morphism.reindexSection (ZFSetTraceContextual.app function argument) =
      ZFSetTraceContextual.app
        (b := codomain ∘ (morphism.lift domain).environment)
        (morphism.reindexSection function) (morphism.reindexSection argument) :=
  ZFSetTraceContextual.app_substitution morphism.environment function argument

namespace Controls

def booleanContext : Context.{u} 0 where
  Environment := ULift Bool
  family := fun index => Fin.elim0 index
  projection := fun index => Fin.elim0 index

def unitContext : Context.{u} 0 where
  Environment := PUnit
  family := fun index => Fin.elim0 index
  projection := fun index => Fin.elim0 index

/-- Context morphisms need not reflect source distinctions: this map selects
one Boolean environment.  Conservativity therefore cannot be inferred from
reindexing alone. -/
def collapse : Morphism booleanContext unitContext :=
  ⟨fun _ => ULift.up false⟩

theorem collapse_not_surjective : ¬ Function.Surjective collapse.environment := by
  intro surjective
  obtain ⟨point, impossible⟩ := surjective (ULift.up true)
  cases point
  have contradiction := congrArg ULift.down impossible
  simp [collapse] at contradiction

end Controls

#print axioms Morphism.identity_left
#print axioms Morphism.identity_right
#print axioms Morphism.comp_assoc
#print axioms Morphism.weaken_environment
#print axioms Morphism.lift_comp
#print axioms Morphism.tracePi_reindex
#print axioms Morphism.traceLam_reindex
#print axioms Morphism.traceApp_reindex
#print axioms Controls.collapse_not_surjective

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeTraceContextMorphisms
