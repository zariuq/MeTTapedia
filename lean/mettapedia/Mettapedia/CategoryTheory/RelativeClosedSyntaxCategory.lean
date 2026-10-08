import Mettapedia.CategoryTheory.RelativeClosedSyntaxRelations
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The category of admitted relative arrows

Objects retain their independently authored raw expressions. Arrows are
admitted expressions modulo the generated typed equations. Composition and
its laws descend from the local composition rules, and the formal terminal
and binary-product expressions have their full universal properties.

The canonical functor from the base preserves identities and composition. Its
preservation of base limits and exponentials requires additional relative
diagram comparisons; it does not follow merely from adjoining formal limit
and exponential expressions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}

structure Object (signature : Signature (C := C) (symbols := symbols)) where
  code : ObjectCode C symbols
  formed : Nonempty (Derivation signature (.object code))

@[ext] theorem Object.ext {signature : Signature (C := C) (symbols := symbols)}
    {first second : Object signature} (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

structure RawHom {signature : Signature (C := C) (symbols := symbols)}
    (source target : Object signature) where
  code : ArrowCode C symbols
  admitted : Nonempty (Derivation signature (.arrow source.code target.code code))

@[ext] theorem RawHom.ext {signature : Signature (C := C) (symbols := symbols)}
    {source target : Object signature} {first second : RawHom source target}
    (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

namespace RawHom

variable {signature : Signature (C := C) (symbols := symbols)}

def identity (object : Object signature) : RawHom object object :=
  ⟨.identity object.code, ⟨.identity object.formed.some⟩⟩

def compose {source middle target : Object signature}
    (first : RawHom source middle) (second : RawHom middle target) : RawHom source target :=
  ⟨.compose first.code second.code, ⟨.compose first.admitted.some second.admitted.some⟩⟩

def Equivalent {source target : Object signature} (first second : RawHom source target) : Prop :=
  Nonempty (Derivation signature (.equation source.code target.code first.code second.code))

instance setoid (source target : Object signature) : Setoid (RawHom source target) where
  r := Equivalent
  iseqv :=
    ⟨fun arrow => ⟨.reflexivity arrow.admitted.some⟩,
      fun same => ⟨.symmetry same.some⟩,
      fun before after => ⟨.transitivity before.some after.some⟩⟩

theorem compose_respects {source middle target : Object signature}
    {first first' : RawHom source middle} {second second' : RawHom middle target}
    (firstSame : first ≈ first') (secondSame : second ≈ second') :
    compose first second ≈ compose first' second' :=
  ⟨.compositionCongruence firstSame.some secondSame.some⟩

end RawHom

abbrev Hom {signature : Signature (C := C) (symbols := symbols)}
    (source target : Object signature) := Quotient (RawHom.setoid source target)

variable {signature : Signature (C := C) (symbols := symbols)}

def classOf {source target : Object signature} (arrow : RawHom source target) : Hom source target :=
  Quotient.mk _ arrow

def composition {source middle target : Object signature}
    (first : Hom source middle) (second : Hom middle target) : Hom source target :=
  Quotient.map₂ RawHom.compose (fun _ _ before _ _ after =>
    RawHom.compose_respects before after) first second

instance category (signature : Signature (C := C) (symbols := symbols)) :
    Category (Object signature) where
  Hom := Hom
  id object := classOf (RawHom.identity object)
  comp := composition
  id_comp := by
    intro source target arrow
    refine Quotient.inductionOn arrow ?_
    intro representative
    exact Quotient.sound ⟨.leftIdentity source.formed.some representative.admitted.some⟩
  comp_id := by
    intro source target arrow
    refine Quotient.inductionOn arrow ?_
    intro representative
    exact Quotient.sound ⟨.rightIdentity target.formed.some representative.admitted.some⟩
  assoc := by
    intro first second third fourth before middle after
    refine Quotient.inductionOn₃ before middle after ?_
    intro before middle after
    exact Quotient.sound ⟨.associativity before.admitted.some middle.admitted.some after.admitted.some⟩

@[simp] theorem classOf_identity (object : Object signature) :
    classOf (RawHom.identity object) = 𝟙 object := rfl

@[simp] theorem classOf_compose {source middle target : Object signature}
    (first : RawHom source middle) (second : RawHom middle target) :
    classOf (RawHom.compose first second) =
      @CategoryStruct.comp (Object signature) (category signature).toCategoryStruct
        source middle target (classOf first) (classOf second) := rfl

theorem classOf_equation {source target : Object signature} {first second : RawHom source target}
    (same : Nonempty (Derivation signature
      (.equation source.code target.code first.code second.code))) :
    classOf first = classOf second := Quotient.sound same

theorem classOf_eq_iff {source target : Object signature} {first second : RawHom source target} :
    classOf first = classOf second ↔
      Nonempty (Derivation signature (.equation source.code target.code first.code second.code)) :=
  Quotient.eq

def representative {source target : Object signature} (arrow : source ⟶ target) :
    RawHom source target := Quotient.out arrow

@[simp] theorem classOf_representative {source target : Object signature}
    (arrow : source ⟶ target) : classOf (representative arrow) = arrow := Quotient.out_eq arrow

def baseObject (signature : Signature (C := C) (symbols := symbols))
    (object : C) : Object signature := ⟨.base object, ⟨.baseObject object⟩⟩

def baseArrow {source target : C} (arrow : source ⟶ target) :
    baseObject signature source ⟶ baseObject signature target :=
  classOf ⟨.base arrow, ⟨.baseArrow arrow⟩⟩

def baseFunctor (signature : Signature (C := C) (symbols := symbols)) : C ⥤ Object signature where
  obj := baseObject signature
  map := baseArrow
  map_id object := Quotient.sound ⟨.baseIdentity object⟩
  map_comp first second := Quotient.sound ⟨.baseComposition first second⟩

def terminal (signature : Signature (C := C) (symbols := symbols)) : Object signature :=
  ⟨.terminal, ⟨.terminalObject⟩⟩

def toTerminal (source : Object signature) : source ⟶ terminal signature :=
  classOf ⟨.terminal source.code, ⟨.terminalArrow source.formed.some⟩⟩

theorem toTerminal_unique {source : Object signature} (arrow : source ⟶ terminal signature) :
    arrow = toTerminal source := by
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact Quotient.sound ⟨.terminalUniqueness representative.admitted.some
    (.terminalArrow source.formed.some)⟩

def terminalIsTerminal (signature : Signature (C := C) (symbols := symbols)) :
    IsTerminal (terminal signature) :=
  IsTerminal.ofUniqueHom toTerminal (fun _ arrow => toTerminal_unique arrow)

instance hasTerminal (signature : Signature (C := C) (symbols := symbols)) :
    HasTerminal (Object signature) :=
  (terminalIsTerminal signature).hasTerminal

def product (left right : Object signature) : Object signature :=
  ⟨.product left.code right.code, ⟨.productObject left.formed.some right.formed.some⟩⟩

def first (left right : Object signature) : product left right ⟶ left :=
  classOf ⟨.first left.code right.code, ⟨.first left.formed.some right.formed.some⟩⟩

def second (left right : Object signature) : product left right ⟶ right :=
  classOf ⟨.second left.code right.code, ⟨.second left.formed.some right.formed.some⟩⟩

def pairing {source left right : Object signature} (before : source ⟶ left)
    (after : source ⟶ right) : source ⟶ product left right :=
  Quotient.map₂
    (sa := RawHom.setoid source left) (sb := RawHom.setoid source right)
    (sc := RawHom.setoid source (product left right))
    (fun (first : RawHom source left) (second : RawHom source right) => (⟨.pair first.code second.code,
      ⟨.pair first.admitted.some second.admitted.some⟩⟩ : RawHom source (product left right)))
    (fun _ _ firstSame _ _ secondSame => ⟨.pairCongruence firstSame.some secondSame.some⟩)
    before after

@[simp] theorem pairing_first {source left right : Object signature}
    (before : source ⟶ left) (after : source ⟶ right) :
    pairing before after ≫ first left right = before := by
  refine Quotient.inductionOn₂ before after ?_
  intro before after
  exact Quotient.sound ⟨.firstBeta left.formed.some right.formed.some
    before.admitted.some after.admitted.some⟩

@[simp] theorem pairing_second {source left right : Object signature}
    (before : source ⟶ left) (after : source ⟶ right) :
    pairing before after ≫ second left right = after := by
  refine Quotient.inductionOn₂ before after ?_
  intro before after
  exact Quotient.sound ⟨.secondBeta left.formed.some right.formed.some
    before.admitted.some after.admitted.some⟩

@[simp] theorem pairing_eta {source left right : Object signature}
    (arrow : source ⟶ product left right) :
    pairing (arrow ≫ first left right) (arrow ≫ second left right) = arrow := by
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact Quotient.sound ⟨.productEta left.formed.some right.formed.some representative.admitted.some⟩

theorem product_joint_cancel {source left right : Object signature}
    {before after : source ⟶ product left right}
    (firstSame : before ≫ first left right = after ≫ first left right)
    (secondSame : before ≫ second left right = after ≫ second left right) : before = after := by
  calc
    before = pairing (before ≫ first left right) (before ≫ second left right) :=
      (pairing_eta before).symm
    _ = pairing (after ≫ first left right) (after ≫ second left right) :=
      congrArg₂ pairing firstSame secondSame
    _ = after := pairing_eta after

theorem pairing_precompose {source middle left right : Object signature}
    (earlier : source ⟶ middle) (before : middle ⟶ left) (after : middle ⟶ right) :
    earlier ≫ pairing before after = pairing (earlier ≫ before) (earlier ≫ after) := by
  apply product_joint_cancel <;> simp only [Category.assoc, pairing_first, pairing_second]

def productIsLimit (left right : Object signature) :
    IsLimit (BinaryFan.mk (first left right) (second left right)) :=
  BinaryFan.isLimitMk (fun cone => pairing cone.fst cone.snd)
    (fun _ => pairing_first _ _) (fun _ => pairing_second _ _)
    (fun _ _arrow firstSame secondSame =>
      product_joint_cancel (firstSame.trans (pairing_first _ _).symm)
        (secondSame.trans (pairing_second _ _).symm))

instance productHasLimit (left right : Object signature) : HasLimit (pair left right) :=
  ⟨⟨BinaryFan.mk (first left right) (second left right), productIsLimit left right⟩⟩

instance hasBinaryProducts (signature : Signature (C := C) (symbols := symbols)) :
    HasBinaryProducts (Object signature) := hasBinaryProducts_of_hasLimit_pair (Object signature)

instance hasFiniteProducts (signature : Signature (C := C) (symbols := symbols)) :
    HasFiniteProducts (Object signature) :=
  hasFiniteProducts_of_has_binary_and_terminal

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
