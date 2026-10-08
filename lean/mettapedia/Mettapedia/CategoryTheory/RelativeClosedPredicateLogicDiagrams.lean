import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicPresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionPreservation

/-!
# Generated finite predicate-law declarations

Thirteen local diagram families are independently authored parallel raw
arrows. Ordered-function and ordered-consequent scopes retain their actual
equalizer presentations. The generated equation extension computes ranks
from complete expressions and supplies every formation and equation tree.
The subsequent base extension earns a finite-limit and closed base map.

No target interpretation, all-context logical law or whole-model soundness
is supplied by a field of this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C]

inductive Law (C : Type k) [Category.{k} C] where
  | commutativity
  | associativity
  | idempotence
  | truthUnit
  | implicationMonotonicity
  | implicationUnit
  | implicationCounit
  | universalMonotonicity {source target : C} (route : source ⟶ target)
  | universalUnit {source target : C} (route : source ⟶ target)
  | universalCounit {source target : C} (route : source ⟶ target)
  | existentialMonotonicity {source target : C} (route : source ⟶ target)
  | existentialUnit {source target : C} (route : source ⟶ target)
  | existentialCounit {source target : C} (route : source ⟶ target)

private def parallelPair {source target : Object (signature (C := C))}
    (first second : RawHom source target) : EquationExtension.Declaration (signature (C := C)) where
  source := source
  target := target
  left := first
  right := second

def commutativePair : EquationExtension.Declaration (signature (C := C)) :=
  parallelPair ((RawHom.exchange omega omega).compose conjunctionRaw) conjunctionRaw

def associativePair : EquationExtension.Declaration (signature (C := C)) :=
  let first := RawHom.first (product omega omega) omega
  let last := RawHom.second (product omega omega) omega
  let left := meetRaw (first.compose conjunctionRaw) last
  let right := meetRaw (first.compose (RawHom.first omega omega))
    (meetRaw (first.compose (RawHom.second omega omega)) last)
  parallelPair left right

def idempotentPair : EquationExtension.Declaration (signature (C := C)) :=
  parallelPair (meetRaw (RawHom.identity omega) (RawHom.identity omega)) (RawHom.identity omega)

def truthUnitPair : EquationExtension.Declaration (signature (C := C)) :=
  parallelPair (meetRaw (RawHom.identity omega) (constantTruthRaw omega)) (RawHom.identity omega)

def implicationMonotonicityPair : EquationExtension.Declaration (signature (C := C)) :=
  let fixed := RawHom.first omega orderedPredicates
  let before := (RawHom.second omega orderedPredicates).compose smallerRaw
  let after := (RawHom.second omega orderedPredicates).compose largerRaw
  parallelPair (meetRaw (implyRaw fixed after) (implyRaw fixed before)) (implyRaw fixed before)

def implicationUnitPair : EquationExtension.Declaration (signature (C := C)) :=
  let first := RawHom.first omega omega
  let second := RawHom.second omega omega
  parallelPair (meetRaw (implyRaw first (meetRaw first second)) second) second

def implicationCounitPair : EquationExtension.Declaration (signature (C := C)) :=
  let first := RawHom.first omega omega
  let second := RawHom.second omega omega
  let output := meetRaw first (implyRaw first second)
  parallelPair (meetRaw second output) output

def universalMonotonicityPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let first := (smallerFunctionRaw source).compose (universalRaw route)
  let second := (largerFunctionRaw source).compose (universalRaw route)
  parallelPair (powerMeetRaw target second first) first

def universalUnitPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let complete := (precompositionRaw route).compose (universalRaw route)
  let input := RawHom.identity (power target)
  parallelPair (powerMeetRaw target complete input) input

def universalCounitPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let complete := (universalRaw route).compose (precompositionRaw route)
  parallelPair (powerMeetRaw source (RawHom.identity (power source)) complete) complete

def existentialMonotonicityPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let first := (smallerFunctionRaw source).compose (existentialRaw route)
  let second := (largerFunctionRaw source).compose (existentialRaw route)
  parallelPair (powerMeetRaw target second first) first

def existentialUnitPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let complete := (existentialRaw route).compose (precompositionRaw route)
  let input := RawHom.identity (power source)
  parallelPair (powerMeetRaw source complete input) input

def existentialCounitPair {source target : C} (route : source ⟶ target) :
    EquationExtension.Declaration (signature (C := C)) :=
  let complete := (precompositionRaw route).compose (existentialRaw route)
  parallelPair (powerMeetRaw target (RawHom.identity (power target)) complete) complete

def declaration : Law C → EquationExtension.Declaration (signature (C := C))
  | .commutativity => commutativePair
  | .associativity => associativePair
  | .idempotence => idempotentPair
  | .truthUnit => truthUnitPair
  | .implicationMonotonicity => implicationMonotonicityPair
  | .implicationUnit => implicationUnitPair
  | .implicationCounit => implicationCounitPair
  | .universalMonotonicity route => universalMonotonicityPair route
  | .universalUnit route => universalUnitPair route
  | .universalCounit route => universalCounitPair route
  | .existentialMonotonicity route => existentialMonotonicityPair route
  | .existentialUnit route => existentialUnitPair route
  | .existentialCounit route => existentialCounitPair route

def lawfulSignature : Signature (C := C)
    (symbols := EquationExtension.extendedSymbols (symbols C) (Law C)) :=
  EquationExtension.extend signature declaration

def lawfulHeaders : HeaderFormation (lawfulSignature (C := C)) :=
  EquationExtension.headers signature declaration headers

def equationInclusion : SignatureMap (signature (C := C)) (lawfulSignature (C := C)) :=
  EquationExtension.inclusion (signature (C := C)) (declaration (C := C))

theorem declared_law (origin : Law C) :
    (equationInclusion (C := C)).functor.map (classOf (declaration origin).left) =
      (equationInclusion (C := C)).functor.map (classOf (declaration origin).right) :=
  EquationExtension.equation_class signature declaration origin

def nativeSignature [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :=
  BaseExtension.extend (lawfulSignature (C := C))

def nativeHeaders [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    HeaderFormation (nativeSignature (C := C)) :=
  BaseExtension.headers lawfulSignature lawfulHeaders

def nativeInclusion [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :=
  BaseExtension.originalMap (lawfulSignature (C := C))

def theory [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    Mettapedia.GSLT.Core.LambdaTheory.{k,k} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (nativeSignature (C := C)))

def baseMap [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] :
    Mettapedia.GSLT.Core.LambdaTheoryMap (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C)
      (theory (C := C)) where
  functor := baseFunctor nativeSignature
  preservesFiniteLimits := BaseExtension.extended_base_preservesFiniteLimits lawfulSignature
  preservesExponentials := BaseExtension.extended_base_closed lawfulSignature

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic
