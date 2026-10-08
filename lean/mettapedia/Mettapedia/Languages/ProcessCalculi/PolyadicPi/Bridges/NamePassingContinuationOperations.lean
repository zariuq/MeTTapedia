import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Categorical continuation arrows of the five name-passing constructors

An independently supplied target constructor algebra has actual name and
process objects, unary and binary communications, fresh-name binding and
replication. The five source operations are built from those primitive arrows
using genuine products, evaluation and abstraction. In particular the source
term object is the function object from target names to target processes.

This constructs the categorical constructor interpretation. Target structural
and operational equations are additional model obligations, rather than
implicit fields of this constructor algebra.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (evaluation abstraction)

universe u v

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- Independent target primitive arrows; no interpretation, equation or
compiler-correctness theorem is supplied as a field. -/
structure Operations where
  names : C
  processes : C
  empty : 𝟙_ C ⟶ processes
  parallel : processes ⊗ processes ⟶ processes
  output : names ⊗ names ⟶ processes
  send : names ⊗ (names ⊗ names) ⟶ processes
  input : names ⊗ (names ⟶[C] processes) ⟶ processes
  receive : names ⊗ ((names ⊗ names) ⟶[C] processes) ⟶ processes
  fresh : (names ⟶[C] processes) ⟶ processes
  replication : processes ⟶ processes

variable {C}

def call {X A B : C} (function : X ⟶ (A ⟶[C] B)) (argument : X ⟶ A) : X ⟶ B :=
  CartesianMonoidalCategory.lift function argument ≫ evaluation A B

def bindFresh (operations : Operations C) {X : C}
    (body : X ⊗ operations.names ⟶ operations.processes) : X ⟶ operations.processes :=
  abstraction body ≫ operations.fresh

namespace Operations

variable (operations : Operations C)

abbrev termObject : C := operations.names ⟶[C] operations.processes
abbrev boundBodyObject : C := operations.names ⟶[C] operations.termObject

def reference : operations.names ⟶ operations.termObject :=
  abstraction operations.output

/-- A received argument is first, and its return channel is second. The
external function result names the binary receiver itself. -/
def abstraction : operations.boundBodyObject ⟶ operations.termObject := by
  let outer := operations.boundBodyObject ⊗ operations.names
  let arguments := operations.names ⊗ operations.names
  let function : outer ⊗ arguments ⟶ operations.boundBodyObject :=
    CartesianMonoidalCategory.fst outer arguments ≫
      CartesianMonoidalCategory.fst operations.boundBodyObject operations.names
  let argument : outer ⊗ arguments ⟶ operations.names :=
    CartesianMonoidalCategory.snd outer arguments ≫
      CartesianMonoidalCategory.fst operations.names operations.names
  let result : outer ⊗ arguments ⟶ operations.names :=
    CartesianMonoidalCategory.snd outer arguments ≫
      CartesianMonoidalCategory.snd operations.names operations.names
  let received := Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (call (call function argument) result)
  exact Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.snd operations.boundBodyObject operations.names) received ≫ operations.receive)

/-- Application allocates a private call name. The supplied function is
called at that name, while the original argument and return are transmitted. -/
def application : operations.termObject ⊗ operations.names ⟶ operations.termObject := by
  let context := operations.termObject ⊗ operations.names
  let outer := context ⊗ operations.names
  let function : outer ⊗ operations.names ⟶ operations.termObject :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.fst operations.termObject operations.names
  let argument : outer ⊗ operations.names ⟶ operations.names :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.snd operations.termObject operations.names
  let result : outer ⊗ operations.names ⟶ operations.names :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.snd context operations.names
  let privateName := CartesianMonoidalCategory.snd outer operations.names
  let transmission := CartesianMonoidalCategory.lift privateName
    (CartesianMonoidalCategory.lift argument result) ≫ operations.send
  let body := CartesianMonoidalCategory.lift (call function privateName) transmission ≫ operations.parallel
  exact Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction (bindFresh operations body)

/-- The stored value is formed outside the reference binder. The reference
is passed to the body and supplies the replicated request channel. -/
def definition : operations.termObject ⊗ operations.boundBodyObject ⟶ operations.termObject := by
  let context := operations.termObject ⊗ operations.boundBodyObject
  let outer := context ⊗ operations.names
  let value : outer ⊗ operations.names ⟶ operations.termObject :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.fst operations.termObject operations.boundBodyObject
  let body : outer ⊗ operations.names ⟶ operations.boundBodyObject :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.snd operations.termObject operations.boundBodyObject
  let result : outer ⊗ operations.names ⟶ operations.names :=
    CartesianMonoidalCategory.fst outer operations.names ≫
      CartesianMonoidalCategory.snd context operations.names
  let reference := CartesianMonoidalCategory.snd outer operations.names
  let retained := CartesianMonoidalCategory.lift reference value ≫ operations.input ≫ operations.replication
  let active := call (call body reference) result
  exact Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (bindFresh operations (CartesianMonoidalCategory.lift active retained ≫ operations.parallel))

def carrier : operations.names ⊗ (operations.termObject ⊗ operations.termObject) ⟶ operations.termObject := by
  let context := operations.names ⊗ (operations.termObject ⊗ operations.termObject)
  let name : context ⊗ operations.names ⟶ operations.names :=
    CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.fst operations.names (operations.termObject ⊗ operations.termObject)
  let pair : context ⊗ operations.names ⟶ operations.termObject ⊗ operations.termObject :=
    CartesianMonoidalCategory.fst context operations.names ≫
      CartesianMonoidalCategory.snd operations.names (operations.termObject ⊗ operations.termObject)
  let value := pair ≫ CartesianMonoidalCategory.fst operations.termObject operations.termObject
  let body := pair ≫ CartesianMonoidalCategory.snd operations.termObject operations.termObject
  let result := CartesianMonoidalCategory.snd context operations.names
  exact Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (CartesianMonoidalCategory.lift (call body result)
      (CartesianMonoidalCategory.lift name value ≫ operations.input) ≫ operations.parallel)

end Operations

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationOperations
