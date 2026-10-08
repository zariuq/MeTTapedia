import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed

/-!
# Typed raw product and abstraction expressions

These operations construct complete admitted raw expressions before taking
their equation classes. Product projections and abstraction use the actual
generated formation trees; no semantic interpreter provides their admission.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.RawHom

open _root_.CategoryTheory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def toTerminal (source : Object signature) : RawHom source (GeneratedCategory.terminal signature) :=
  ⟨.terminal source.code, ⟨.terminalArrow source.formed.some⟩⟩

def first (left right : Object signature) : RawHom (product left right) left :=
  ⟨.first left.code right.code, ⟨.first left.formed.some right.formed.some⟩⟩

def second (left right : Object signature) : RawHom (product left right) right :=
  ⟨.second left.code right.code, ⟨.second left.formed.some right.formed.some⟩⟩

def pair {source left right : Object signature} (before : RawHom source left)
    (after : RawHom source right) : RawHom source (product left right) :=
  ⟨.pair before.code after.code, ⟨.pair before.admitted.some after.admitted.some⟩⟩

def exchange (left right : Object signature) : RawHom (product left right) (product right left) :=
  pair (second left right) (first left right)

def abstract {context argument result : Object signature}
    (body : RawHom (product context argument) result) :
    RawHom context (exponentialObject argument result) :=
  ⟨.curry context.code argument.code result.code body.code,
    ⟨.curry context.formed.some argument.formed.some result.formed.some body.admitted.some⟩⟩

def curry {argument context result : Object signature}
    (body : RawHom (product argument context) result) :
    RawHom context (exponentialObject argument result) :=
  abstract (compose (exchange context argument) body)

theorem classOf_pair {source left right : Object signature} (before : RawHom source left)
    (after : RawHom source right) :
    classOf (pair before after) = pairing (classOf before) (classOf after) := rfl

theorem classOf_abstract {context argument result : Object signature}
    (body : RawHom (product context argument) result) :
    classOf (abstract body) = abstraction (classOf body) := rfl

theorem pair_first {source left right : Object signature} (before : RawHom source left)
    (after : RawHom source right) : compose (pair before after) (first left right) ≈ before :=
  ⟨.firstBeta left.formed.some right.formed.some before.admitted.some after.admitted.some⟩

theorem pair_second {source left right : Object signature} (before : RawHom source left)
    (after : RawHom source right) : compose (pair before after) (second left right) ≈ after :=
  ⟨.secondBeta left.formed.some right.formed.some before.admitted.some after.admitted.some⟩

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.RawHom
