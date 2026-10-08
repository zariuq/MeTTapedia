import Mettapedia.CategoryTheory.RelativeClosedSyntaxRelations

/-!
# Context-expression translations of local declarations

Fresh object and arrow declarations may be translated to complete target
expressions, including products, abstraction and composition. They need not
be mapped to individual target names. The raw translation is independent of
semantic carriers. Its admission consists only of actual target derivations
for each local object, primitive arrow and declared equation.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a w z b

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}

structure TranslationData where
  base : C ⥤ D
  objects : symbols.ObjectName → ObjectCode D nextSymbols
  arrows : symbols.ArrowName → ArrowCode D nextSymbols

mutual

def ObjectCode.translate (data : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)) : ObjectCode C symbols → ObjectCode D nextSymbols
  | .base object => .base (data.base.obj object)
  | .name origin => data.objects origin
  | .terminal => .terminal
  | .product first second => .product (first.translate data) (second.translate data)
  | .exponential argument result => .exponential (argument.translate data) (result.translate data)
  | .equalizer source target first second => .equalizer (source.translate data) (target.translate data)
      (first.translate data) (second.translate data)

def ArrowCode.translate (data : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)) : ArrowCode C symbols → ArrowCode D nextSymbols
  | .base arrow => .base (data.base.map arrow)
  | .name origin => data.arrows origin
  | .identity object => .identity (object.translate data)
  | .compose first second => .compose (first.translate data) (second.translate data)
  | .terminal source => .terminal (source.translate data)
  | .first first second => .first (first.translate data) (second.translate data)
  | .second first second => .second (first.translate data) (second.translate data)
  | .pair first second => .pair (first.translate data) (second.translate data)
  | .evaluation argument result => .evaluation (argument.translate data) (result.translate data)
  | .curry context argument result body => .curry (context.translate data) (argument.translate data)
      (result.translate data) (body.translate data)
  | .equalizerArrow source target first second => .equalizerArrow
      (source.translate data) (target.translate data) (first.translate data) (second.translate data)
  | .equalizerLift source target first second context candidate => .equalizerLift
      (source.translate data) (target.translate data) (first.translate data) (second.translate data)
      (context.translate data) (candidate.translate data)

end

def Judgment.translate (data : TranslationData (C := C) (symbols := symbols)
    (D := D) (nextSymbols := nextSymbols)) : Judgment C symbols → Judgment D nextSymbols
  | Judgment.object source => Judgment.object (source.translate data)
  | Judgment.arrow source target code => Judgment.arrow (source.translate data) (target.translate data) (code.translate data)
  | Judgment.equation source target first second => Judgment.equation (source.translate data) (target.translate data)
      (first.translate data) (second.translate data)

variable (signature : Signature (C := C) (symbols := symbols))
variable (next : Signature (C := D) (symbols := nextSymbols))

/-- Admission is declaration-local generated evidence, not a whole-tree
preservation or interpretation field. -/
structure Translation where
  data : TranslationData (C := C) (symbols := symbols) (D := D) (nextSymbols := nextSymbols)
  objectTyped (origin : symbols.ObjectName) : Derivation next (.object (data.objects origin))
  arrowTyped (origin : symbols.ArrowName) : Derivation next
    (.arrow ((signature.source origin).translate data) ((signature.target origin).translate data)
      (data.arrows origin))
  equationTyped (origin : symbols.EquationName) : Derivation next
    (.equation ((signature.equationSource origin).translate data)
      ((signature.equationTarget origin).translate data)
      ((signature.left origin).translate data) ((signature.right origin).translate data))

end Mettapedia.CategoryTheory.RelativeClosedSyntax
