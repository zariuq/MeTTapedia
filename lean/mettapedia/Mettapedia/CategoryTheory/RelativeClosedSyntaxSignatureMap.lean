import Mettapedia.CategoryTheory.RelativeClosedSyntaxCategory

/-!
# Declaration-local maps of relative presentations

A map retains an actual base functor and maps the independently authored
object, arrow and equation names. Only the local headers and equation sides
are required to agree. All forty generated rule cases are transported here,
including the base functor's actual identity and composition equations.
The resulting functor descends through the generated typed-arrow quotient.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a w z b

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable (signature : Signature (C := C) (symbols := symbols))
variable (next : Signature (C := D) (symbols := nextSymbols))

structure SignatureMap where
  base : C ⥤ D
  objects : symbols.ObjectName → nextSymbols.ObjectName
  arrows : symbols.ArrowName → nextSymbols.ArrowName
  equations : symbols.EquationName → nextSymbols.EquationName
  source (origin : symbols.ArrowName) :
    next.source (arrows origin) = (signature.source origin).map base objects arrows
  target (origin : symbols.ArrowName) :
    next.target (arrows origin) = (signature.target origin).map base objects arrows
  equationSource (origin : symbols.EquationName) :
    next.equationSource (equations origin) =
      (signature.equationSource origin).map base objects arrows
  equationTarget (origin : symbols.EquationName) :
    next.equationTarget (equations origin) =
      (signature.equationTarget origin).map base objects arrows
  left (origin : symbols.EquationName) :
    next.left (equations origin) = (signature.left origin).map base objects arrows
  right (origin : symbols.EquationName) :
    next.right (equations origin) = (signature.right origin).map base objects arrows

namespace SignatureMap

variable {signature next} (mapping : SignatureMap signature next)

def judgment : Judgment C symbols → Judgment D nextSymbols
  | .object object => .object (object.map mapping.base mapping.objects mapping.arrows)
  | .arrow source target arrow => .arrow
      (source.map mapping.base mapping.objects mapping.arrows)
      (target.map mapping.base mapping.objects mapping.arrows)
      (arrow.map mapping.base mapping.objects mapping.arrows)
  | .equation source target before after => .equation
      (source.map mapping.base mapping.objects mapping.arrows)
      (target.map mapping.base mapping.objects mapping.arrows)
      (before.map mapping.base mapping.objects mapping.arrows)
      (after.map mapping.base mapping.objects mapping.arrows)

def derivation (mapping : SignatureMap signature next) : {j : Judgment C symbols} → Derivation signature j →
    Derivation next (mapping.judgment j)
  | _, .baseObject object => .baseObject (mapping.base.obj object)
  | _, .objectName origin => .objectName (mapping.objects origin)
  | _, .terminalObject => .terminalObject
  | _, .productObject first second => .productObject (derivation mapping first) (derivation mapping second)
  | _, .exponentialObject argument result =>
      .exponentialObject (derivation mapping argument) (derivation mapping result)
  | _, .equalizerObject source target before after => .equalizerObject
      (derivation mapping source) (derivation mapping target)
      (derivation mapping before) (derivation mapping after)
  | _, .baseArrow arrow => .baseArrow (mapping.base.map arrow)
  | _, .arrowName origin source target => by
      have source' : Derivation next (.object (next.source (mapping.arrows origin))) := by
        simpa only [judgment, mapping.source origin] using derivation mapping source
      have target' : Derivation next (.object (next.target (mapping.arrows origin))) := by
        simpa only [judgment, mapping.target origin] using derivation mapping target
      simpa only [judgment, ArrowCode.map, mapping.source origin, mapping.target origin] using
        Derivation.arrowName (signature := next) (mapping.arrows origin) source' target'
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
      (.baseEquality (mapping.base.map_id object)) (.baseIdentity (mapping.base.obj object))
  | _, .baseComposition before after => .transitivity
      (.baseEquality (mapping.base.map_comp before after))
      (.baseComposition (mapping.base.map before) (mapping.base.map after))
  | _, .baseEquality same => .baseEquality (congrArg mapping.base.map same)
  | _, .declaredEquation origin left right => by
      have left' : Derivation next (.arrow (next.equationSource (mapping.equations origin))
          (next.equationTarget (mapping.equations origin)) (next.left (mapping.equations origin))) := by
        simpa only [judgment, mapping.equationSource origin, mapping.equationTarget origin,
          mapping.left origin] using derivation mapping left
      have right' : Derivation next (.arrow (next.equationSource (mapping.equations origin))
          (next.equationTarget (mapping.equations origin)) (next.right (mapping.equations origin))) := by
        simpa only [judgment, mapping.equationSource origin, mapping.equationTarget origin,
          mapping.right origin] using derivation mapping right
      simpa only [judgment, mapping.equationSource origin, mapping.equationTarget origin,
        mapping.left origin, mapping.right origin] using
          Derivation.declaredEquation (signature := next) (mapping.equations origin) left' right'

def object (source : GeneratedCategory.Object signature) : GeneratedCategory.Object next :=
  ⟨source.code.map mapping.base mapping.objects mapping.arrows,
    ⟨derivation mapping source.formed.some⟩⟩

def rawArrow {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    GeneratedCategory.RawHom (mapping.object source) (mapping.object target) :=
  ⟨arrow.code.map mapping.base mapping.objects mapping.arrows,
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
    mapping.base ⋙ GeneratedCategory.baseFunctor next := by
  refine _root_.CategoryTheory.Functor.ext
    (F := GeneratedCategory.baseFunctor signature ⋙ mapping.functor)
    (G := mapping.base ⋙ GeneratedCategory.baseFunctor next) (fun _ => rfl) ?_
  intro source target arrow
  change mapping.arrow (GeneratedCategory.baseArrow arrow) =
    𝟙 (GeneratedCategory.baseObject next (mapping.base.obj source)) ≫
      GeneratedCategory.baseArrow (signature := next) (mapping.base.map arrow) ≫
        𝟙 (GeneratedCategory.baseObject next (mapping.base.obj target))
  rw [Category.id_comp, Category.comp_id]
  rfl

end SignatureMap

end Mettapedia.CategoryTheory.RelativeClosedSyntax
