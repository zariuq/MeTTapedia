import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionPreservation

/-!
# Authored truth and conjunction in relative closed theories

The new proposition object and its two operation names are independent raw
declarations. Four independently typed parallel pairs impose commutativity,
associativity, idempotence and the truth unit. Their ranks are computed from
the complete expressions by the equation-extension construction.

The final presentation also retains the actual native base comparisons, so
its base inclusion preserves finite limits and canonical exponentials.
This is the conjunctive stratum; it supplies neither joins nor implication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k

inductive Operation where
  | truth
  | conjunction

inductive Law where
  | commutativity
  | associativity
  | idempotence
  | truthUnit

def symbols : Symbols.{k} where
  ObjectName := ULift.{k} Unit
  ArrowName := ULift.{k} Operation
  EquationName := ULift.{k} Empty

variable {C : Type k} [Category.{k} C]

def omegaCode : ObjectCode C symbols := .name (ULift.up ())

def operationSource : Operation → ObjectCode C symbols
  | .truth => .terminal
  | .conjunction => .product omegaCode omegaCode

def signature : Signature (C := C) (symbols := symbols) where
  objectRank _ := 0
  arrowRank _ := 1
  source origin := operationSource origin.down
  target _ := omegaCode
  source_before origin := by
    cases origin with
    | up origin => cases origin <;> simp [operationSource, omegaCode, ObjectCode.before]
  target_before _ := by simp [omegaCode, ObjectCode.before]
  equationRank origin := origin.down.elim
  equationSource origin := origin.down.elim
  equationTarget origin := origin.down.elim
  left origin := origin.down.elim
  right origin := origin.down.elim
  equation_before origin := origin.down.elim

def omegaFormed : Derivation (signature (C := C)) (.object (omegaCode (C := C))) := by
  change Derivation (signature (C := C)) (.object (.name (ULift.up ())))
  exact .objectName (signature := signature (C := C)) (ULift.up ())

def omega : Object (signature (C := C)) :=
  ⟨omegaCode, ⟨omegaFormed⟩⟩

def truthRaw : RawHom (terminal (signature (C := C))) omega :=
  ⟨.name (ULift.up Operation.truth),
    ⟨.arrowName (signature := signature) (ULift.up Operation.truth) .terminalObject omegaFormed⟩⟩

def conjunctionRaw : RawHom (product (omega (C := C)) omega) omega :=
  ⟨.name (ULift.up Operation.conjunction),
    ⟨.arrowName (signature := signature) (ULift.up Operation.conjunction)
      (.productObject omegaFormed omegaFormed) omegaFormed⟩⟩

private def firstRaw {names : Symbols.{k}} {presentation : Signature (C := C) (symbols := names)}
    (left right : Object presentation) : RawHom (product left right) left :=
  ⟨.first left.code right.code, ⟨.first left.formed.some right.formed.some⟩⟩

private def secondRaw {names : Symbols.{k}} {presentation : Signature (C := C) (symbols := names)}
    (left right : Object presentation) : RawHom (product left right) right :=
  ⟨.second left.code right.code, ⟨.second left.formed.some right.formed.some⟩⟩

private def pairRaw {names : Symbols.{k}} {presentation : Signature (C := C) (symbols := names)}
    {context left right : Object presentation} (before : RawHom context left) (after : RawHom context right) :
    RawHom context (product left right) :=
  ⟨.pair before.code after.code, ⟨.pair before.admitted.some after.admitted.some⟩⟩

def commutativePair : EquationExtension.Declaration (signature (C := C)) where
  source := product omega omega
  target := omega
  left := (pairRaw (secondRaw omega omega) (firstRaw omega omega)).compose conjunctionRaw
  right := conjunctionRaw

def associativePair : EquationExtension.Declaration (signature (C := C)) where
  source := product (product omega omega) omega
  target := omega
  left := (pairRaw ((firstRaw (product omega omega) omega).compose conjunctionRaw)
    (secondRaw (product omega omega) omega)).compose conjunctionRaw
  right := (pairRaw ((firstRaw (product omega omega) omega).compose (firstRaw omega omega))
    ((pairRaw ((firstRaw (product omega omega) omega).compose (secondRaw omega omega))
      (secondRaw (product omega omega) omega)).compose conjunctionRaw)).compose conjunctionRaw

def idempotentPair : EquationExtension.Declaration (signature (C := C)) where
  source := omega
  target := omega
  left := (pairRaw (RawHom.identity omega) (RawHom.identity omega)).compose conjunctionRaw
  right := RawHom.identity omega

def truthUnitPair : EquationExtension.Declaration (signature (C := C)) where
  source := omega
  target := omega
  left := (pairRaw (RawHom.identity omega)
    ((⟨.terminal omegaCode, ⟨.terminalArrow omegaFormed⟩⟩ :
      RawHom omega (terminal signature)).compose truthRaw)).compose conjunctionRaw
  right := RawHom.identity omega

def declaration (origin : ULift.{k} Law) : EquationExtension.Declaration (signature (C := C)) :=
  match origin.down with
  | .commutativity => commutativePair
  | .associativity => associativePair
  | .idempotence => idempotentPair
  | .truthUnit => truthUnitPair

def operationHeaders : HeaderFormation (signature (C := C)) where
  source origin := by
    cases origin with
    | up origin =>
      cases origin with
      | truth => exact .terminalObject
      | conjunction => exact .productObject omegaFormed omegaFormed
  target _ := omegaFormed
  left origin := origin.down.elim
  right origin := origin.down.elim

def lawfulSignature : Signature (C := C)
    (symbols := EquationExtension.extendedSymbols symbols (ULift.{k} Law)) :=
  EquationExtension.extend signature declaration

def lawfulHeaders : HeaderFormation (lawfulSignature (C := C)) :=
  EquationExtension.headers signature declaration operationHeaders

def equationInclusion : SignatureMap (signature (C := C)) (lawfulSignature (C := C)) :=
  EquationExtension.inclusion (signature (C := C)) (declaration (C := C))

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
    Mettapedia.GSLT.Core.LambdaTheoryMap (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) (theory (C := C)) where
  functor := baseFunctor nativeSignature
  preservesFiniteLimits := BaseExtension.extended_base_preservesFiniteLimits lawfulSignature
  preservesExponentials := BaseExtension.extended_base_closed lawfulSignature

theorem declared_law (origin : ULift.{k} Law) :
    (equationInclusion (C := C)).functor.map (classOf (declaration (C := C) origin).left) =
      (equationInclusion (C := C)).functor.map (classOf (declaration (C := C) origin).right) :=
  EquationExtension.equation_class signature declaration origin

end Mettapedia.CategoryTheory.RelativeClosedConjunctive
