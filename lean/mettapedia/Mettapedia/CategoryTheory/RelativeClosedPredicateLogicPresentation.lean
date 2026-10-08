import Mettapedia.CategoryTheory.RelativeClosedRawConstructions
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationExtension

/-!
# Authored quantified and implicative predicate declarations

The proposition name and all operation names are raw declarations,
independent of any target predicate carrier. Quantifier names retain their
actual base-arrow index. Their function inputs are complete exponential
objects, and monotonicity is imposed on authored ordered-pair equalizers.
Only finitely many diagrams are imposed per operation.

This presentation supplies the quantified and implicative stratum on its
declared base-arrow footprint. All-context logical rules and native
interpretation are subsequent theorems. Quantifiers along newly generated
arrows, the positioned modal layer and the entire free-extension adjunction
are not consequences merely of this raw presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k

inductive Operation (C : Type k) [Category.{k} C] where
  | truth
  | conjunction
  | implication
  | universal {source target : C} (route : source ⟶ target)
  | existential {source target : C} (route : source ⟶ target)

variable {C : Type k} [Category.{k} C]

def symbols (C : Type k) [Category.{k} C] : Symbols.{k} where
  ObjectName := ULift.{k} Unit
  ArrowName := Operation C
  EquationName := ULift.{k} Empty

def omegaCode : ObjectCode C (symbols C) := .name (ULift.up ())

def powerCode (value : C) : ObjectCode C (symbols C) := .exponential (.base value) omegaCode

def operationSource : Operation C → ObjectCode C (symbols C)
  | .truth => .terminal
  | .conjunction => .product omegaCode omegaCode
  | .implication => .product omegaCode omegaCode
  | .universal (source := source) _ => powerCode source
  | .existential (source := source) _ => powerCode source

def operationTarget : Operation C → ObjectCode C (symbols C)
  | .truth => omegaCode
  | .conjunction => omegaCode
  | .implication => omegaCode
  | .universal (target := target) _ => powerCode target
  | .existential (target := target) _ => powerCode target

def signature : Signature (C := C) (symbols := symbols C) where
  objectRank _ := 0
  arrowRank _ := 1
  source := operationSource
  target := operationTarget
  source_before origin := by
    cases origin <;> simp [operationSource, omegaCode, powerCode, ObjectCode.before]
  target_before origin := by
    cases origin <;> simp [operationTarget, omegaCode, powerCode, ObjectCode.before]
  equationRank origin := origin.down.elim
  equationSource origin := origin.down.elim
  equationTarget origin := origin.down.elim
  left origin := origin.down.elim
  right origin := origin.down.elim
  equation_before origin := origin.down.elim

def omega : Object (signature (C := C)) :=
  ⟨omegaCode, ⟨.objectName (signature := signature) (ULift.up ())⟩⟩

def power (value : C) : Object (signature (C := C)) :=
  exponentialObject (baseObject signature value) omega

def truthRaw : RawHom (terminal (signature (C := C))) omega :=
  ⟨.name (Operation.truth (C := C)),
    ⟨.arrowName (signature := signature) (Operation.truth (C := C)) .terminalObject omega.formed.some⟩⟩

def conjunctionRaw : RawHom (product (omega (C := C)) omega) omega :=
  ⟨.name (Operation.conjunction (C := C)),
    ⟨.arrowName (signature := signature) (Operation.conjunction (C := C))
    (.productObject omega.formed.some omega.formed.some) omega.formed.some⟩⟩

def implicationRaw : RawHom (product (omega (C := C)) omega) omega :=
  ⟨.name (Operation.implication (C := C)),
    ⟨.arrowName (signature := signature) (Operation.implication (C := C))
    (.productObject omega.formed.some omega.formed.some) omega.formed.some⟩⟩

def universalRaw {source target : C} (route : source ⟶ target) : RawHom (power source) (power target) :=
  ⟨.name (Operation.universal route), ⟨.arrowName (signature := signature) (Operation.universal route)
    (power source).formed.some (power target).formed.some⟩⟩

def existentialRaw {source target : C} (route : source ⟶ target) : RawHom (power source) (power target) :=
  ⟨.name (Operation.existential route), ⟨.arrowName (signature := signature) (Operation.existential route)
    (power source).formed.some (power target).formed.some⟩⟩

def meetRaw {context : Object (signature (C := C))}
    (first second : RawHom context omega) : RawHom context omega :=
  (RawHom.pair first second).compose conjunctionRaw

def implyRaw {context : Object (signature (C := C))}
    (first second : RawHom context omega) : RawHom context omega :=
  (RawHom.pair first second).compose implicationRaw

def constantTruthRaw (context : Object (signature (C := C))) : RawHom context omega :=
  (RawHom.terminal context).compose truthRaw

def powerConjunctionRaw (value : C) : RawHom (product (power value) (power value)) (power value) :=
  let context := product (power value) (power value)
  let argument := baseObject signature value
  let firstFunction := (RawHom.first context argument).compose (RawHom.first (power value) (power value))
  let secondFunction := (RawHom.first context argument).compose (RawHom.second (power value) (power value))
  let atFirst := (RawHom.pair firstFunction (RawHom.second context argument)).compose
    (RawHom.evaluation argument omega)
  let atSecond := (RawHom.pair secondFunction (RawHom.second context argument)).compose
    (RawHom.evaluation argument omega)
  RawHom.abstract (meetRaw atFirst atSecond)

def powerMeetRaw {context : Object (signature (C := C))} (value : C)
    (first second : RawHom context (power value)) : RawHom context (power value) :=
  (RawHom.pair first second).compose (powerConjunctionRaw value)

def precompositionRaw {source target : C} (route : source ⟶ target) :
    RawHom (power target) (power source) :=
  let original : RawHom (baseObject signature source) (baseObject signature target) :=
    ⟨.base route, ⟨.baseArrow route⟩⟩
  let input := RawHom.pair (RawHom.first (power target) (baseObject signature source))
    ((RawHom.second (power target) (baseObject signature source)).compose original)
  RawHom.abstract (input.compose (RawHom.evaluation (baseObject signature target) omega))

def orderedPredicates : Object (signature (C := C)) :=
  PresentedEqualizer.object conjunctionRaw (RawHom.first omega omega)

def smallerRaw : RawHom (orderedPredicates (C := C)) omega :=
  (RawHom.inclusion conjunctionRaw (RawHom.first omega omega)).compose (RawHom.first omega omega)

def largerRaw : RawHom (orderedPredicates (C := C)) omega :=
  (RawHom.inclusion conjunctionRaw (RawHom.first omega omega)).compose (RawHom.second omega omega)

def orderedFunctions (value : C) : Object (signature (C := C)) :=
  PresentedEqualizer.object (powerConjunctionRaw value) (RawHom.first (power value) (power value))

def smallerFunctionRaw (value : C) : RawHom (orderedFunctions value) (power value) :=
  (RawHom.inclusion (powerConjunctionRaw value) (RawHom.first (power value) (power value))).compose
    (RawHom.first (power value) (power value))

def largerFunctionRaw (value : C) : RawHom (orderedFunctions value) (power value) :=
  (RawHom.inclusion (powerConjunctionRaw value) (RawHom.first (power value) (power value))).compose
    (RawHom.second (power value) (power value))

def headers : HeaderFormation (signature (C := C)) where
  source origin := by
    cases origin with
    | truth => exact .terminalObject
    | conjunction => exact .productObject omega.formed.some omega.formed.some
    | implication => exact .productObject omega.formed.some omega.formed.some
    | universal route => exact (power _).formed.some
    | existential route => exact (power _).formed.some
  target origin := by
    cases origin with
    | truth => exact omega.formed.some
    | conjunction => exact omega.formed.some
    | implication => exact omega.formed.some
    | universal route => exact (power _).formed.some
    | existential route => exact (power _).formed.some
  left origin := origin.down.elim
  right origin := origin.down.elim

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic
