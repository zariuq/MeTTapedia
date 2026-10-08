import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationBaseExtension
import Mettapedia.CategoryTheory.RelativeClosedBaseCanonicalReadout

/-!
# Authored native inverse expressions for a weak base translation

An added source inverse is translated to the target's corresponding native
inverse followed by the embedded inverse of the actual canonical comparison
of the weak base functor. These are independently typed target expressions.
Old object and arrow expressions commute with the original inclusions by
constructor recursion. No carrier-indexed semantic grammar is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeData

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

def mappedChoice : BaseComparisons.Choice C → BaseComparisons.Choice D
  | .terminal => .terminal
  | .product first second => .product (mapping.data.base.obj first) (mapping.data.base.obj second)
  | .equalizer first second => .equalizer (mapping.data.base.map first) (mapping.data.base.map second)
  | .exponential argument result => .exponential (mapping.data.base.obj argument) (mapping.data.base.obj result)

def inverseCode : BaseComparisons.Choice C → ArrowCode D (BaseExtension.extendedSymbols D nextSymbols)
  | .terminal => .compose (.name (.inl .terminal))
      (.base (inv (CartesianMonoidalCategory.terminalComparison mapping.data.base)))
  | .product first second => .compose
      (.name (.inl (.product (mapping.data.base.obj first) (mapping.data.base.obj second))))
      (.base (inv (CartesianMonoidalCategory.prodComparison mapping.data.base first second)))
  | .equalizer first second => .compose
      (.name (.inl (.equalizer (mapping.data.base.map first) (mapping.data.base.map second))))
      (.base (inv (equalizerComparison first second mapping.data.base)))
  | .exponential argument result => .compose
      (.name (.inl (.exponential (mapping.data.base.obj argument) (mapping.data.base.obj result))))
      (.base (inv ((expComparison mapping.data.base argument).natTrans.app result)))

def data : TranslationData (C := C) (symbols := BaseExtension.extendedSymbols C symbols)
    (D := D) (nextSymbols := BaseExtension.extendedSymbols D nextSymbols) where
  base := mapping.data.base
  objects origin := BaseExtension.originalObjectCode (mapping.data.objects origin.down)
  arrows origin := match origin with
    | .inl choice => inverseCode mapping choice
    | .inr name => BaseExtension.originalArrowCode (mapping.data.arrows name.down)

mutual

theorem original_object (code : ObjectCode C symbols) :
    (BaseExtension.originalObjectCode code).translate (data mapping) =
      BaseExtension.originalObjectCode (code.translate mapping.data) := by
  cases code with
  | base _ => rfl
  | name _ => rfl
  | terminal => rfl
  | product first second =>
      exact congrArg₂ ObjectCode.product (original_object first) (original_object second)
  | exponential first second =>
      exact congrArg₂ ObjectCode.exponential (original_object first) (original_object second)
  | equalizer source target first second =>
      change ObjectCode.equalizer
        ((BaseExtension.originalObjectCode source).translate (data mapping))
        ((BaseExtension.originalObjectCode target).translate (data mapping))
        ((BaseExtension.originalArrowCode first).translate (data mapping))
        ((BaseExtension.originalArrowCode second).translate (data mapping)) =
          ObjectCode.equalizer (BaseExtension.originalObjectCode (source.translate mapping.data))
            (BaseExtension.originalObjectCode (target.translate mapping.data))
            (BaseExtension.originalArrowCode (first.translate mapping.data))
            (BaseExtension.originalArrowCode (second.translate mapping.data))
      congr 1
      · exact original_object source
      · exact original_object target
      · exact original_arrow first
      · exact original_arrow second

theorem original_arrow (code : ArrowCode C symbols) :
    (BaseExtension.originalArrowCode code).translate (data mapping) =
      BaseExtension.originalArrowCode (code.translate mapping.data) := by
  cases code with
  | base _ => rfl
  | name _ => rfl
  | identity current => exact congrArg ArrowCode.identity (original_object current)
  | compose first second => exact congrArg₂ ArrowCode.compose (original_arrow first) (original_arrow second)
  | terminal current => exact congrArg ArrowCode.terminal (original_object current)
  | first left right => exact congrArg₂ ArrowCode.first (original_object left) (original_object right)
  | second left right => exact congrArg₂ ArrowCode.second (original_object left) (original_object right)
  | pair first second => exact congrArg₂ ArrowCode.pair (original_arrow first) (original_arrow second)
  | evaluation argument result =>
      exact congrArg₂ ArrowCode.evaluation (original_object argument) (original_object result)
  | curry context argument result body =>
      dsimp only [BaseExtension.originalArrowCode, ArrowCode.map, ArrowCode.translate]
      congr 1
      · exact original_object context
      · exact original_object argument
      · exact original_object result
      · exact original_arrow body
  | equalizerArrow source target first second =>
      dsimp only [BaseExtension.originalArrowCode, ArrowCode.map, ArrowCode.translate]
      congr 1
      · exact original_object source
      · exact original_object target
      · exact original_arrow first
      · exact original_arrow second
  | equalizerLift source target first second context candidate =>
      dsimp only [BaseExtension.originalArrowCode, ArrowCode.map, ArrowCode.translate]
      congr 1
      · exact original_object source
      · exact original_object target
      · exact original_arrow first
      · exact original_arrow second
      · exact original_object context
      · exact original_arrow candidate

end

theorem native_source (choice : BaseComparisons.Choice C) :
    (BaseExtension.source signature (.inl choice)).translate (data mapping) =
      BaseExtension.comparisonObjectCode (BaseComparisons.sourceCode (mappedChoice mapping choice)) := by
  cases choice <;> rfl

theorem native_target (choice : BaseComparisons.Choice C) :
    (BaseExtension.target signature (.inl choice)).translate (data mapping) =
      .base (mapping.data.base.obj (BaseComparisons.selected choice)) := by
  cases choice <;> rfl

def native_arrow_typed (choice : BaseComparisons.Choice C) :
    Derivation (BaseExtension.extend next)
      (.arrow ((BaseExtension.source signature (.inl choice)).translate (data mapping))
        ((BaseExtension.target signature (.inl choice)).translate (data mapping)) (inverseCode mapping choice)) := by
  rw [native_source, native_target]
  cases choice with
  | terminal =>
      exact .compose ((BaseExtension.comparisonMap next).derivation (BaseComparisons.inverseTyped .terminal))
        (.baseArrow (inv (CartesianMonoidalCategory.terminalComparison mapping.data.base)))
  | product first second =>
      exact .compose ((BaseExtension.comparisonMap next).derivation
        (BaseComparisons.inverseTyped (.product (mapping.data.base.obj first) (mapping.data.base.obj second))))
        (.baseArrow (inv (CartesianMonoidalCategory.prodComparison mapping.data.base first second)))
  | equalizer first second =>
      exact .compose ((BaseExtension.comparisonMap next).derivation
        (BaseComparisons.inverseTyped (.equalizer (mapping.data.base.map first) (mapping.data.base.map second))))
        (.baseArrow (inv (equalizerComparison first second mapping.data.base)))
  | exponential argument result =>
      exact .compose ((BaseExtension.comparisonMap next).derivation
        (BaseComparisons.inverseTyped (.exponential (mapping.data.base.obj argument) (mapping.data.base.obj result))))
        (.baseArrow (inv ((expComparison mapping.data.base argument).natTrans.app result)))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeData
