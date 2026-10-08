import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxCategory

/-!
# Complete generated translation and typed-arrow descent

Local translated declarations earn preservation of every one of the forty
generated rule cases. This includes the actual base functor's identity and
composition equations and all supplied equalizer commutativity trees.
The complete translated arrows descend through the generated equation
quotient and retain their independently authored target expressions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a w z b

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}

namespace Translation

variable (mapping : Translation signature next)

abbrev judgment : Judgment C symbols → Judgment D nextSymbols :=
  Judgment.translate mapping.data

def derivation (mapping : Translation signature next) : {j : Judgment C symbols} → Derivation signature j →
    Derivation next (mapping.judgment j)
  | _, .baseObject object => .baseObject (mapping.data.base.obj object)
  | _, .objectName origin => mapping.objectTyped origin
  | _, .terminalObject => .terminalObject
  | _, .productObject first second => .productObject (derivation mapping first) (derivation mapping second)
  | _, .exponentialObject argument result =>
      .exponentialObject (derivation mapping argument) (derivation mapping result)
  | _, .equalizerObject source target before after => .equalizerObject
      (derivation mapping source) (derivation mapping target)
      (derivation mapping before) (derivation mapping after)
  | _, .baseArrow arrow => .baseArrow (mapping.data.base.map arrow)
  | _, .arrowName origin _ _ => mapping.arrowTyped origin
  | _, .identity formed => .identity (derivation mapping formed)
  | _, .compose before after => .compose (derivation mapping before) (derivation mapping after)
  | _, .terminalArrow formed => .terminalArrow (derivation mapping formed)
  | _, .first left right => .first (derivation mapping left) (derivation mapping right)
  | _, .second left right => .second (derivation mapping left) (derivation mapping right)
  | _, .pair before after => .pair (derivation mapping before) (derivation mapping after)
  | _, .evaluation argument result => .evaluation (derivation mapping argument) (derivation mapping result)
  | _, .curry context argument result body => .curry
      (derivation mapping context) (derivation mapping argument)
      (derivation mapping result) (derivation mapping body)
  | _, .equalizerArrow source target before after => .equalizerArrow
      (derivation mapping source) (derivation mapping target)
      (derivation mapping before) (derivation mapping after)
  | _, .equalizerLift source target context before after candidate commutes => .equalizerLift
      (derivation mapping source) (derivation mapping target) (derivation mapping context)
      (derivation mapping before) (derivation mapping after)
      (derivation mapping candidate) (derivation mapping commutes)
  | _, .reflexivity typed => .reflexivity (derivation mapping typed)
  | _, .symmetry same => .symmetry (derivation mapping same)
  | _, .transitivity before after => .transitivity (derivation mapping before) (derivation mapping after)
  | _, .compositionCongruence before after =>
      .compositionCongruence (derivation mapping before) (derivation mapping after)
  | _, .pairCongruence before after => .pairCongruence (derivation mapping before) (derivation mapping after)
  | _, .curryCongruence context argument result same => .curryCongruence
      (derivation mapping context) (derivation mapping argument)
      (derivation mapping result) (derivation mapping same)
  | _, .leftIdentity formed typed => .leftIdentity (derivation mapping formed) (derivation mapping typed)
  | _, .rightIdentity formed typed => .rightIdentity (derivation mapping formed) (derivation mapping typed)
  | _, .associativity before middle after => .associativity
      (derivation mapping before) (derivation mapping middle) (derivation mapping after)
  | _, .terminalUniqueness before after =>
      .terminalUniqueness (derivation mapping before) (derivation mapping after)
  | _, .firstBeta left right before after => .firstBeta
      (derivation mapping left) (derivation mapping right)
      (derivation mapping before) (derivation mapping after)
  | _, .secondBeta left right before after => .secondBeta
      (derivation mapping left) (derivation mapping right)
      (derivation mapping before) (derivation mapping after)
  | _, .productEta left right typed => .productEta
      (derivation mapping left) (derivation mapping right) (derivation mapping typed)
  | _, .exponentialBeta context argument result body => .exponentialBeta
      (derivation mapping context) (derivation mapping argument)
      (derivation mapping result) (derivation mapping body)
  | _, .exponentialEta context argument result typed => .exponentialEta
      (derivation mapping context) (derivation mapping argument)
      (derivation mapping result) (derivation mapping typed)
  | _, .equalizerCondition source target before after => .equalizerCondition
      (derivation mapping source) (derivation mapping target)
      (derivation mapping before) (derivation mapping after)
  | _, .equalizerBeta source target context before after candidate commutes => .equalizerBeta
      (derivation mapping source) (derivation mapping target) (derivation mapping context)
      (derivation mapping before) (derivation mapping after)
      (derivation mapping candidate) (derivation mapping commutes)
  | _, .equalizerUniqueness before after same => .equalizerUniqueness
      (derivation mapping before) (derivation mapping after) (derivation mapping same)
  | _, .baseIdentity object => .transitivity
      (.baseEquality (mapping.data.base.map_id object)) (.baseIdentity (mapping.data.base.obj object))
  | _, .baseComposition before after => .transitivity
      (.baseEquality (mapping.data.base.map_comp before after))
      (.baseComposition (mapping.data.base.map before) (mapping.data.base.map after))
  | _, .baseEquality same => .baseEquality (congrArg mapping.data.base.map same)
  | _, .declaredEquation origin _ _ => mapping.equationTyped origin

def object (source : GeneratedCategory.Object signature) : GeneratedCategory.Object next :=
  ⟨source.code.translate mapping.data,
    ⟨derivation mapping source.formed.some⟩⟩

def rawArrow {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    GeneratedCategory.RawHom (mapping.object source) (mapping.object target) :=
  ⟨arrow.code.translate mapping.data,
    ⟨derivation mapping arrow.admitted.some⟩⟩

theorem rawArrow_equivalent {source target : GeneratedCategory.Object signature}
    {before after : GeneratedCategory.RawHom source target}
    (same : GeneratedCategory.RawHom.Equivalent before after) :
    GeneratedCategory.RawHom.Equivalent (mapping.rawArrow before) (mapping.rawArrow after) :=
  ⟨derivation mapping same.some⟩

def arrow {source target : GeneratedCategory.Object signature} (value : source ⟶ target) :
    mapping.object source ⟶ mapping.object target :=
  Quotient.lift (fun representative => GeneratedCategory.classOf (mapping.rawArrow representative))
    (fun _ _ same => Quotient.sound (mapping.rawArrow_equivalent same)) value

def functor : GeneratedCategory.Object signature ⥤ GeneratedCategory.Object next where
  obj := mapping.object
  map := mapping.arrow
  map_id _ := rfl
  map_comp before after := by
    refine Quotient.inductionOn₂ before after ?_
    intro first second
    rfl

@[simp] theorem functor_classOf {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    mapping.functor.map (GeneratedCategory.classOf arrow) =
      GeneratedCategory.classOf (mapping.rawArrow arrow) := rfl

theorem functor_base : GeneratedCategory.baseFunctor signature ⋙ mapping.functor =
    mapping.data.base ⋙ GeneratedCategory.baseFunctor next := by
  refine _root_.CategoryTheory.Functor.ext
    (F := GeneratedCategory.baseFunctor signature ⋙ mapping.functor)
    (G := mapping.data.base ⋙ GeneratedCategory.baseFunctor next) (fun _ => rfl) ?_
  intro source target arrow
  change mapping.arrow (GeneratedCategory.baseArrow arrow) =
    𝟙 (GeneratedCategory.baseObject next (mapping.data.base.obj source)) ≫
      GeneratedCategory.baseArrow (signature := next) (mapping.data.base.map arrow) ≫
        𝟙 (GeneratedCategory.baseObject next (mapping.data.base.obj target))
  rw [Category.id_comp, Category.comp_id]
  rfl


end Translation
end Mettapedia.CategoryTheory.RelativeClosedSyntax
