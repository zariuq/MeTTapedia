import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMap
import Mettapedia.CategoryTheory.RelativeClosedBaseComparisonSignature

/-!
# Adjoining the base comparison diagrams to an arbitrary presentation

Original object, arrow and equation origins remain separate from the local
base comparison origins. Their declaration ranks are raised by three; the
base inverse names and their equations occupy the preceding two stages.
Actual syntactic rank calculations and the forty-rule map give both source
inclusions and real formation certificates. No base preservation or free
universal property is supplied as a field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}

def extendedSymbols (C : Type u) [Category.{v} C] (symbols : Symbols.{a}) :
    Symbols.{max u v a} where
  ObjectName := ULift.{max u v} symbols.ObjectName
  ArrowName := BaseComparisons.Choice C ⊕ ULift.{max u v} symbols.ArrowName
  EquationName := (BaseComparisons.Choice C × Bool) ⊕ ULift.{max u v} symbols.EquationName

def originalObjects (origin : symbols.ObjectName) : (extendedSymbols C symbols).ObjectName :=
  ULift.up origin

def originalArrows (origin : symbols.ArrowName) : (extendedSymbols C symbols).ArrowName :=
  Sum.inr (ULift.up origin)

def comparisonObjects (origin : (BaseComparisons.symbols C).ObjectName) :
    (extendedSymbols C symbols).ObjectName := origin.down.elim

def comparisonArrows (origin : BaseComparisons.Choice C) : (extendedSymbols C symbols).ArrowName :=
  Sum.inl origin

def originalObjectCode (code : ObjectCode C symbols) : ObjectCode C (extendedSymbols C symbols) :=
  code.map (Functor.id C) originalObjects originalArrows

def originalArrowCode (code : ArrowCode C symbols) : ArrowCode C (extendedSymbols C symbols) :=
  code.map (Functor.id C) originalObjects originalArrows

def comparisonObjectCode (code : ObjectCode C (BaseComparisons.symbols C)) :
    ObjectCode C (extendedSymbols C symbols) :=
  code.map (Functor.id C) comparisonObjects comparisonArrows

def comparisonArrowCode (code : ArrowCode C (BaseComparisons.symbols C)) :
    ArrowCode C (extendedSymbols C symbols) :=
  code.map (Functor.id C) comparisonObjects comparisonArrows

variable (signature : Signature (C := C) (symbols := symbols))

def objectRank (origin : (extendedSymbols C symbols).ObjectName) : Nat :=
  signature.objectRank origin.down + 3

def arrowRank : (extendedSymbols C symbols).ArrowName → Nat
  | .inl _ => 1
  | .inr origin => signature.arrowRank origin.down + 3

mutual

theorem original_object_before (bound : Nat) : (code : ObjectCode C symbols) →
    (code.map (Functor.id C) originalObjects originalArrows).before
      (objectRank signature) (arrowRank signature) (bound + 3) ↔
    code.before signature.objectRank signature.arrowRank bound
  | .base _ => Iff.rfl
  | .name _ => by
      change (_ + 3 < bound + 3) ↔ _
      exact Nat.add_lt_add_iff_right
  | .terminal => Iff.rfl
  | .product _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, original_object_before]
  | .exponential _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, original_object_before]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, original_object_before, original_arrow_before]

theorem original_arrow_before (bound : Nat) : (code : ArrowCode C symbols) →
    (code.map (Functor.id C) originalObjects originalArrows).before
      (objectRank signature) (arrowRank signature) (bound + 3) ↔
    code.before signature.objectRank signature.arrowRank bound
  | .base _ => Iff.rfl
  | .name _ => by
      change (_ + 3 < bound + 3) ↔ _
      exact Nat.add_lt_add_iff_right
  | .identity _ => by simp only [ArrowCode.map, ArrowCode.before, original_object_before]
  | .compose _ _ => by simp only [ArrowCode.map, ArrowCode.before, original_arrow_before]
  | .terminal _ => by simp only [ArrowCode.map, ArrowCode.before, original_object_before]
  | .first _ _ => by simp only [ArrowCode.map, ArrowCode.before, original_object_before]
  | .second _ _ => by simp only [ArrowCode.map, ArrowCode.before, original_object_before]
  | .pair _ _ => by simp only [ArrowCode.map, ArrowCode.before, original_arrow_before]
  | .evaluation _ _ => by simp only [ArrowCode.map, ArrowCode.before, original_object_before]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, original_object_before, original_arrow_before]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, original_object_before, original_arrow_before]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, original_object_before, original_arrow_before]

end

mutual

theorem comparison_object_before (bound : Nat) : (code : ObjectCode C (BaseComparisons.symbols C)) →
    (code.map (Functor.id C) comparisonObjects comparisonArrows).before
      (objectRank signature) (arrowRank signature) bound ↔
    code.before (fun _ => 0) (fun _ => 1) bound
  | .base _ => Iff.rfl
  | .name origin => origin.down.elim
  | .terminal => Iff.rfl
  | .product _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, comparison_object_before]
  | .exponential _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, comparison_object_before]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, comparison_object_before, comparison_arrow_before]

theorem comparison_arrow_before (bound : Nat) : (code : ArrowCode C (BaseComparisons.symbols C)) →
    (code.map (Functor.id C) comparisonObjects comparisonArrows).before
      (objectRank signature) (arrowRank signature) bound ↔
    code.before (fun _ => 0) (fun _ => 1) bound
  | .base _ => Iff.rfl
  | .name _ => Iff.rfl
  | .identity _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_object_before]
  | .compose _ _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_arrow_before]
  | .terminal _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_object_before]
  | .first _ _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_object_before]
  | .second _ _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_object_before]
  | .pair _ _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_arrow_before]
  | .evaluation _ _ => by simp only [ArrowCode.map, ArrowCode.before, comparison_object_before]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, comparison_object_before, comparison_arrow_before]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, comparison_object_before, comparison_arrow_before]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, comparison_object_before, comparison_arrow_before]

end

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def source : (extendedSymbols C symbols).ArrowName → ObjectCode C (extendedSymbols C symbols)
  | .inl choice => comparisonObjectCode (BaseComparisons.sourceCode choice)
  | .inr origin => originalObjectCode (signature.source origin.down)

def target : (extendedSymbols C symbols).ArrowName → ObjectCode C (extendedSymbols C symbols)
  | .inl choice => comparisonObjectCode (BaseComparisons.targetCode choice)
  | .inr origin => originalObjectCode (signature.target origin.down)

def equationRank : (extendedSymbols C symbols).EquationName → Nat
  | .inl _ => 2
  | .inr origin => signature.equationRank origin.down + 3

def equationSource : (extendedSymbols C symbols).EquationName → ObjectCode C (extendedSymbols C symbols)
  | .inl origin => comparisonObjectCode (BaseComparisons.equationObject origin)
  | .inr origin => originalObjectCode (signature.equationSource origin.down)

def equationTarget : (extendedSymbols C symbols).EquationName → ObjectCode C (extendedSymbols C symbols)
  | .inl origin => comparisonObjectCode (BaseComparisons.equationObject origin)
  | .inr origin => originalObjectCode (signature.equationTarget origin.down)

def left : (extendedSymbols C symbols).EquationName → ArrowCode C (extendedSymbols C symbols)
  | .inl origin => comparisonArrowCode (BaseComparisons.leftCode origin)
  | .inr origin => originalArrowCode (signature.left origin.down)

def right : (extendedSymbols C symbols).EquationName → ArrowCode C (extendedSymbols C symbols)
  | .inl origin => comparisonArrowCode (BaseComparisons.rightCode origin)
  | .inr origin => originalArrowCode (signature.right origin.down)

def extend : Signature (C := C) (symbols := extendedSymbols C symbols) where
  objectRank := objectRank signature
  arrowRank := arrowRank signature
  source := source signature
  target := target signature
  source_before origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_before signature 1 _).mpr
          ((BaseComparisons.signature (C := C)).source_before choice)
    | inr origin =>
        exact (original_object_before signature (signature.arrowRank origin.down) _).mpr
          (signature.source_before origin.down)
  target_before origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_before signature 1 _).mpr
          ((BaseComparisons.signature (C := C)).target_before choice)
    | inr origin =>
        exact (original_object_before signature (signature.arrowRank origin.down) _).mpr
          (signature.target_before origin.down)
  equationRank := equationRank signature
  equationSource := equationSource signature
  equationTarget := equationTarget signature
  left := left signature
  right := right signature
  equation_before origin := by
    cases origin with
    | inl origin =>
        obtain ⟨first, second, before, after⟩ :=
          (BaseComparisons.signature (C := C)).equation_before origin
        exact ⟨(comparison_object_before signature 2 _).mpr first,
          (comparison_object_before signature 2 _).mpr second,
          (comparison_arrow_before signature 2 _).mpr before,
          (comparison_arrow_before signature 2 _).mpr after⟩
    | inr origin =>
        obtain ⟨first, second, before, after⟩ := signature.equation_before origin.down
        exact ⟨(original_object_before signature (signature.equationRank origin.down) _).mpr first,
          (original_object_before signature (signature.equationRank origin.down) _).mpr second,
          (original_arrow_before signature (signature.equationRank origin.down) _).mpr before,
          (original_arrow_before signature (signature.equationRank origin.down) _).mpr after⟩

def originalMap : SignatureMap signature (extend signature) where
  base := Functor.id C
  objects := originalObjects
  arrows := originalArrows
  equations origin := .inr (ULift.up origin)
  source _ := rfl
  target _ := rfl
  equationSource _ := rfl
  equationTarget _ := rfl
  left _ := rfl
  right _ := rfl

def comparisonMap : SignatureMap (BaseComparisons.signature (C := C)) (extend signature) where
  base := Functor.id C
  objects := comparisonObjects
  arrows := comparisonArrows
  equations := Sum.inl
  source _ := rfl
  target _ := rfl
  equationSource _ := rfl
  equationTarget _ := rfl
  left _ := rfl
  right _ := rfl

def headers (formed : HeaderFormation signature) : HeaderFormation (extend signature) where
  source origin := match origin with
    | .inl choice => (comparisonMap signature).derivation (BaseComparisons.sourceFormation choice)
    | .inr origin => (originalMap signature).derivation (formed.source origin.down)
  target origin := match origin with
    | .inl choice => (comparisonMap signature).derivation (BaseComparisons.targetFormation choice)
    | .inr origin => (originalMap signature).derivation (formed.target origin.down)
  left origin := match origin with
    | .inl origin => (comparisonMap signature).derivation (BaseComparisons.leftTyped origin)
    | .inr origin => (originalMap signature).derivation (formed.left origin.down)
  right origin := match origin with
    | .inl origin => (comparisonMap signature).derivation (BaseComparisons.rightTyped origin)
    | .inr origin => (originalMap signature).derivation (formed.right origin.down)

theorem original_base_recovery :
    GeneratedCategory.baseFunctor signature ⋙ (originalMap signature).functor =
      GeneratedCategory.baseFunctor (extend signature) := by
  exact (originalMap signature).functor_base.trans (Functor.id_comp _)

theorem comparison_base_recovery :
    GeneratedCategory.baseFunctor (BaseComparisons.signature (C := C)) ⋙
        (comparisonMap signature).functor = GeneratedCategory.baseFunctor (extend signature) := by
  exact (comparisonMap signature).functor_base.trans (Functor.id_comp _)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension
