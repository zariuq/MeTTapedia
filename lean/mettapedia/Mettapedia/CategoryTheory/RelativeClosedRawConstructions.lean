import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedEqualizers

/-!
# Independently authored raw categorical diagrams

The constructors retain complete raw arrows and their actual formation
trees before equation declarations are added. Product and exponential
equations are generated derivations. Equalizer presentations use their
authored arrows and supplied commutativity tree; their comparison with
chosen quotient limits remains the earned presented-equalizer comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.RawHom

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a
variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def terminal (source : Object signature) : RawHom source (GeneratedCategory.terminal signature) :=
  ⟨.terminal source.code, ⟨.terminalArrow source.formed.some⟩⟩

def tensor {left right nextLeft nextRight : Object signature}
    (before : RawHom left nextLeft) (after : RawHom right nextRight) :
    RawHom (product left right) (product nextLeft nextRight) :=
  pair ((first left right).compose before) ((second left right).compose after)

def evaluation (argument result : Object signature) :
    RawHom (product (exponentialObject argument result) argument) result :=
  ⟨.evaluation argument.code result.code,
    ⟨.evaluation argument.formed.some result.formed.some⟩⟩

def uncurry {context argument result : Object signature}
    (function : RawHom context (exponentialObject argument result)) :
    RawHom (product context argument) result :=
  (pair ((first context argument).compose function) (second context argument)).compose
    (evaluation argument result)

def quote {context argument result : Object signature}
    (body : RawHom (product argument context) result) :
    RawHom context (exponentialObject argument result) :=
  abstract ((exchange context argument).compose body)

def read {context argument result : Object signature}
    (function : RawHom context (exponentialObject argument result)) :
    RawHom (product argument context) result :=
  (exchange argument context).compose (uncurry function)

def inclusion {source target : Object signature} (before after : RawHom source target) :
    RawHom (PresentedEqualizer.object before after) source :=
  ⟨.equalizerArrow source.code target.code before.code after.code,
    ⟨.equalizerArrow source.formed.some target.formed.some before.admitted.some after.admitted.some⟩⟩

def equalizerLift {source target context : Object signature}
    (before after : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code before.code) (.compose candidate.code after.code))) :
    RawHom context (PresentedEqualizer.object before after) :=
  ⟨.equalizerLift source.code target.code before.code after.code context.code candidate.code,
    ⟨.equalizerLift source.formed.some target.formed.some context.formed.some
      before.admitted.some after.admitted.some candidate.admitted.some commutes⟩⟩

theorem uncurry_abstract {context argument result : Object signature}
    (body : RawHom (product context argument) result) : Equivalent (uncurry (abstract body)) body :=
  ⟨.exponentialBeta context.formed.some argument.formed.some result.formed.some body.admitted.some⟩

theorem abstract_uncurry {context argument result : Object signature}
    (function : RawHom context (exponentialObject argument result)) :
    Equivalent (abstract (uncurry function)) function :=
  ⟨.exponentialEta context.formed.some argument.formed.some result.formed.some function.admitted.some⟩

theorem equalizer_condition {source target : Object signature} (before after : RawHom source target) :
    Equivalent ((inclusion before after).compose before) ((inclusion before after).compose after) :=
  ⟨.equalizerCondition source.formed.some target.formed.some before.admitted.some after.admitted.some⟩

theorem equalizer_beta {source target context : Object signature}
    (before after : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code before.code) (.compose candidate.code after.code))) :
    Equivalent ((equalizerLift before after candidate commutes).compose (inclusion before after)) candidate :=
  ⟨.equalizerBeta source.formed.some target.formed.some context.formed.some
    before.admitted.some after.admitted.some candidate.admitted.some commutes⟩

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.RawHom
