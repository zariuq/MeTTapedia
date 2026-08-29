import Mettapedia.GSLT.LanguageDef.Extension

/-!
# Many-sorted construction provenance

Language engineering pipelines do not remain inside one carrier type.  A
source GSLT may produce a language definition, a generated typing language,
or a compiled machine; gluing may consume several differently indexed inputs.
This module gives construction provenance the corresponding many-sorted
shape.

`ManySortedConstructionAlgebra` is a typed operation signature together with
its interpretation.  Each operation declares an ordered list of input kinds
and one output kind.  Its freely generated construction trees are indexed by
their output kind, so an ill-sorted pipeline cannot be represented.

An exact receipt is displayed over the evaluated result.  The checked view
forgets the receipt; the reflective view retains it.  The authored construction
GSLT evaluates a `make` request to a terminal `ready` result carrying that
receipt.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension

universe uKind uObject uSource uOperation

/-- A heterogeneous list indexed by the kinds of its entries. -/
inductive FamilyList {Kind : Type uKind} (Family : Kind → Type uObject) :
    List Kind → Type (max uKind uObject) where
  | nil : FamilyList Family []
  | cons {kind : Kind} {kinds : List Kind} :
      Family kind → FamilyList Family kinds →
        FamilyList Family (kind :: kinds)

namespace FamilyList

variable {Kind : Type uKind}
  {First : Kind → Type uObject} {Second : Kind → Type uSource}

/-- Apply a kind-preserving map entrywise. -/
def map (function : ∀ kind, First kind → Second kind) :
    {kinds : List Kind} → FamilyList First kinds → FamilyList Second kinds
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (function _ head) (map function tail)

@[simp] theorem map_nil (function : ∀ kind, First kind → Second kind) :
    map function (.nil : FamilyList First []) = .nil :=
  rfl

@[simp] theorem map_cons (function : ∀ kind, First kind → Second kind)
    {kind : Kind} {kinds : List Kind} (head : First kind)
    (tail : FamilyList First kinds) :
    map function (.cons head tail) =
      .cons (function kind head) (map function tail) :=
  rfl

end FamilyList

/-- A many-sorted algebra of language-construction operations.  Operation
values may carry revisions, policies, gluing witnesses, target definitions,
or other typed parameters. -/
structure ManySortedConstructionAlgebra where
  Kind : Type uKind
  Object : Kind → Type uObject
  Source : Kind → Type uSource
  Operation : List Kind → Kind → Type uOperation
  interpretSource : ∀ {kind}, Source kind → Object kind
  interpretOperation : ∀ {inputs output},
    Operation inputs output → FamilyList Object inputs → Object output

variable (algebra :
  ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation})

/- Well-sorted construction trees and their ordered argument lists. -/
mutual
  /-- A construction route whose result kind is part of its type. -/
  inductive ConstructionTree
      (algebra :
        ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation}) :
      algebra.Kind → Type (max uKind (max uSource uOperation))
    | source {kind : algebra.Kind} (value : algebra.Source kind) :
        ConstructionTree algebra kind
    | apply {inputs : List algebra.Kind} {output : algebra.Kind}
        (operation : algebra.Operation inputs output)
        (arguments : ConstructionArguments algebra inputs) :
        ConstructionTree algebra output

  /-- The ordered, kind-indexed children of one operation node. -/
  inductive ConstructionArguments
      (algebra :
        ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation}) :
      List algebra.Kind → Type (max uKind (max uSource uOperation))
    | nil : ConstructionArguments algebra []
    | cons {kind : algebra.Kind} {kinds : List algebra.Kind}
        (head : ConstructionTree algebra kind)
        (tail : ConstructionArguments algebra kinds) :
        ConstructionArguments algebra (kind :: kinds)
end

namespace ManySortedConstructionAlgebra

/- The mutual evaluator uses `ULift` only to place its two dependent result
families in one universe.  The public functions immediately project the same
values back to their original object families. -/
mutual
  private def evaluateLift {kind : algebra.Kind} :
      ConstructionTree algebra kind → ULift.{uKind} (algebra.Object kind)
    | .source value => ⟨algebra.interpretSource value⟩
    | .apply operation arguments =>
        ⟨algebra.interpretOperation operation
          (evaluateArgumentsLift arguments).down⟩

  private def evaluateArgumentsLift {kinds : List algebra.Kind} :
      ConstructionArguments algebra kinds →
        ULift.{uObject} (FamilyList algebra.Object kinds)
    | .nil => ⟨.nil⟩
    | .cons head tail =>
        ⟨.cons (evaluateLift head).down
          (evaluateArgumentsLift tail).down⟩
end

/-- Evaluate one typed construction route. -/
def evaluate {kind : algebra.Kind}
    (route : ConstructionTree algebra kind) : algebra.Object kind :=
  (evaluateLift algebra route).down

/-- Evaluate the ordered children of an operation. -/
def evaluateArguments {kinds : List algebra.Kind}
    (arguments : ConstructionArguments algebra kinds) :
    FamilyList algebra.Object kinds :=
  (evaluateArgumentsLift algebra arguments).down

@[simp] theorem evaluate_source {kind : algebra.Kind}
    (value : algebra.Source kind) :
    algebra.evaluate (.source value) = algebra.interpretSource value :=
  rfl

@[simp] theorem evaluate_apply {inputs : List algebra.Kind}
    {output : algebra.Kind} (operation : algebra.Operation inputs output)
    (arguments : ConstructionArguments algebra inputs) :
    algebra.evaluate (.apply operation arguments) =
      algebra.interpretOperation operation
        (algebra.evaluateArguments arguments) :=
  rfl

@[simp] theorem evaluateArguments_nil :
    algebra.evaluateArguments (.nil : ConstructionArguments algebra []) =
      .nil :=
  rfl

@[simp] theorem evaluateArguments_cons {kind : algebra.Kind}
    {kinds : List algebra.Kind} (head : ConstructionTree algebra kind)
    (tail : ConstructionArguments algebra kinds) :
    algebra.evaluateArguments (.cons head tail) =
      .cons (algebra.evaluate head) (algebra.evaluateArguments tail) :=
  rfl

end ManySortedConstructionAlgebra

/-- Evidence that one well-sorted construction route evaluates exactly to the
indexed result. -/
structure ConstructionReceipt {kind : algebra.Kind}
    (result : algebra.Object kind) where
  route : ConstructionTree algebra kind
  evaluates : algebra.evaluate route = result

namespace ConstructionReceipt

/-- A typed source is a receipt for its interpreted object. -/
def source {kind : algebra.Kind} (value : algebra.Source kind) :
    ConstructionReceipt algebra (algebra.interpretSource value) where
  route := .source value
  evaluates := rfl

/-- Apply a unary typed operation while retaining the input route. -/
def unary {inputKind outputKind : algebra.Kind}
    (operation : algebra.Operation [inputKind] outputKind)
    {input : algebra.Object inputKind}
    (receipt : ConstructionReceipt algebra input) :
    ConstructionReceipt algebra
      (algebra.interpretOperation operation (.cons input .nil)) where
  route := .apply operation (.cons receipt.route .nil)
  evaluates := by simp [receipt.evaluates]

/-- Apply a binary typed operation while retaining both input routes. -/
def binary {leftKind rightKind outputKind : algebra.Kind}
    (operation : algebra.Operation [leftKind, rightKind] outputKind)
    {left : algebra.Object leftKind} {right : algebra.Object rightKind}
    (leftReceipt : ConstructionReceipt algebra left)
    (rightReceipt : ConstructionReceipt algebra right) :
    ConstructionReceipt algebra
      (algebra.interpretOperation operation
        (.cons left (.cons right .nil))) where
  route := .apply operation
    (.cons leftReceipt.route (.cons rightReceipt.route .nil))
  evaluates := by
    simp [leftReceipt.evaluates, rightReceipt.evaluates]

@[simp] theorem source_route {kind : algebra.Kind}
    (value : algebra.Source kind) :
    (source algebra value).route = .source value :=
  rfl

@[simp] theorem unary_route {inputKind outputKind : algebra.Kind}
    (operation : algebra.Operation [inputKind] outputKind)
    {input : algebra.Object inputKind}
    (receipt : ConstructionReceipt algebra input) :
    (unary algebra operation receipt).route =
      ConstructionTree.apply operation
        (ConstructionArguments.cons receipt.route ConstructionArguments.nil) :=
  rfl

@[simp] theorem binary_route
    {leftKind rightKind outputKind : algebra.Kind}
    (operation : algebra.Operation [leftKind, rightKind] outputKind)
    {left : algebra.Object leftKind} {right : algebra.Object rightKind}
    (leftReceipt : ConstructionReceipt algebra left)
    (rightReceipt : ConstructionReceipt algebra right) :
    (binary algebra operation leftReceipt rightReceipt).route =
      ConstructionTree.apply operation
        (ConstructionArguments.cons leftReceipt.route
          (ConstructionArguments.cons rightReceipt.route
            ConstructionArguments.nil)) :=
  rfl

end ConstructionReceipt

/-- The dependent sum of all object kinds. -/
abbrev Result := Σ kind, algebra.Object kind

/-- Exact construction receipts displayed over their evaluated results. -/
def constructionReceiptLayer : ExtensionLayer (Result algebra) where
  Fiber := fun result => ConstructionReceipt algebra result.2

namespace constructionReceiptLayer

/-- Package one well-sorted route with its evaluated result. -/
def record {kind : algebra.Kind} (route : ConstructionTree algebra kind) :
    (constructionReceiptLayer algebra).Total :=
  ⟨⟨kind, algebra.evaluate route⟩, ⟨route, rfl⟩⟩

/-- The dependent sum of construction trees of every output kind. -/
abbrev AnyTree := Σ kind, ConstructionTree algebra kind

/-- Read the exact route retained by a reflective construction result. -/
def route (recorded : (constructionReceiptLayer algebra).Total) : AnyTree algebra :=
  ⟨recorded.1.1, recorded.2.route⟩

@[simp] theorem erase_record {kind : algebra.Kind}
    (construction : ConstructionTree algebra kind) :
    (constructionReceiptLayer algebra).erase (record algebra construction) =
      ⟨kind, algebra.evaluate construction⟩ :=
  rfl

@[simp] theorem route_record {kind : algebra.Kind}
    (construction : ConstructionTree algebra kind) :
    route algebra (record algebra construction) = ⟨kind, construction⟩ :=
  rfl

end constructionReceiptLayer

/-! ## Authored construction GSLT -/

/-- Commands of the many-sorted construction machine. -/
inductive ConstructionCommand
    (algebra :
      ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation}) where
  | make (route : constructionReceiptLayer.AnyTree algebra)
  | ready (result : (constructionReceiptLayer algebra).Total)

/-- One `make` request evaluates to a terminal result with its exact receipt. -/
inductive ConstructionCommandStep
    (algebra :
      ManySortedConstructionAlgebra.{uKind, uObject, uSource, uOperation}) :
    ConstructionCommand algebra → ConstructionCommand algebra → Prop where
  | make {kind : algebra.Kind} (route : ConstructionTree algebra kind) :
      ConstructionCommandStep algebra (.make ⟨kind, route⟩)
        (.ready (constructionReceiptLayer.record algebra route))

/-- The operational GSLT that authors and evaluates typed construction
routes. -/
def constructionProvenanceGSLT : GSLT where
  Term := ConstructionCommand algebra
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := ConstructionCommandStep algebra
  rewrites_resp_left := by
    intro source source' target equivalent step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    subst target'
    exact step

/-- Pending and completed commands denote the same provenanced result. -/
def elaborateCommand :
    ConstructionCommand algebra → Option (constructionReceiptLayer algebra).Total
  | .make ⟨_, route⟩ => some (constructionReceiptLayer.record algebra route)
  | .ready result => some result

theorem elaborateCommand_equation
    {source target : ConstructionCommand algebra}
    (equivalent : (constructionProvenanceGSLT algebra).Equiv source target) :
    elaborateCommand algebra source = elaborateCommand algebra target := by
  subst target
  rfl

theorem elaborateCommand_rewrite
    {source target : ConstructionCommand algebra}
    (step : (constructionProvenanceGSLT algebra).Step source target) :
    elaborateCommand algebra source = elaborateCommand algebra target := by
  cases step
  rfl

/-- The many-sorted construction machine as one exact authored coGSLT layer.
Its total fibre is the composite object: an ordinary evaluated result paired
with a route that is certified to evaluate to that result. -/
def constructionProvenanceCoGSLT : CoGSLTLayer Unit where
  Fiber := fun _ => (constructionReceiptLayer algebra).Total
  sourceGSLT := fun _ => constructionProvenanceGSLT algebra
  elaborate := fun _ => elaborateCommand algebra
  quote := fun _ result => .ready result
  elaborate_quote := fun _ _ => rfl
  elaborate_equation := by
    intro _ source target equivalent
    exact elaborateCommand_equation algebra equivalent
  elaborate_rewrite := by
    intro _ source target step
    exact elaborateCommand_rewrite algebra step

/-! ## Heterogeneous positive and negative controls -/

namespace Canary

inductive Kind where
  | number
  | truth
deriving DecidableEq

def Object : Kind → Type
  | .number => Nat
  | .truth => Bool

def Source : Kind → Type
  | .number => Nat
  | .truth => Bool

inductive Operation : List Kind → Kind → Type
  | successor : Operation [.number] .number
  | addition : Operation [.number, .number] .number
  | isZero : Operation [.number] .truth

def interpretSource : {kind : Kind} → Source kind → Object kind
  | .number, value => value
  | .truth, value => value

def natIsZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

def interpretOperation : {inputs : List Kind} → {output : Kind} →
    Operation inputs output → FamilyList Object inputs → Object output
  | _, _, .successor, .cons value .nil => Nat.succ value
  | _, _, .addition, .cons left (.cons right .nil) => Nat.add left right
  | _, _, .isZero, .cons value .nil => natIsZero value

def arithmetic : ManySortedConstructionAlgebra where
  Kind := Kind
  Object := Object
  Source := Source
  Operation := Operation
  interpretSource := interpretSource
  interpretOperation := interpretOperation

def one : ConstructionReceipt (algebra := arithmetic)
    (kind := Kind.number) (1 : Nat) :=
  ConstructionReceipt.source arithmetic (kind := Kind.number) (1 : Nat)

def twoBySuccessor : ConstructionReceipt (algebra := arithmetic)
    (kind := Kind.number) (2 : Nat) :=
  ConstructionReceipt.unary arithmetic Operation.successor one

def three : ConstructionReceipt (algebra := arithmetic)
    (kind := Kind.number) (3 : Nat) :=
  ConstructionReceipt.source arithmetic (kind := Kind.number) (3 : Nat)

def fiveByAddition : ConstructionReceipt (algebra := arithmetic)
    (kind := Kind.number) (5 : Nat) :=
  ConstructionReceipt.binary arithmetic Operation.addition
    twoBySuccessor three

/-- Positive: same-kind binary composition remains exactly typed. -/
theorem fiveByAddition_evaluates :
    arithmetic.evaluate fiveByAddition.route =
      (show Object Kind.number from (5 : Nat)) :=
  fiveByAddition.evaluates

def twoIsNotZero : ConstructionReceipt (algebra := arithmetic)
    (kind := Kind.truth) false :=
  ConstructionReceipt.unary arithmetic Operation.isZero twoBySuccessor

/-- Positive: a construction operation may change result kind while retaining
an exact receipt. -/
theorem twoIsNotZero_evaluates :
    arithmetic.evaluate twoIsNotZero.route = false :=
  twoIsNotZero.evaluates

def twoDirectRoute : ConstructionTree arithmetic .number :=
  .source (2 : Nat)

def twoComposedRoute : ConstructionTree arithmetic .number :=
  .apply Operation.addition
    (.cons (.source (1 : Nat)) (.cons (.source (1 : Nat)) .nil))

def twoDirect : (constructionReceiptLayer arithmetic).Total :=
  constructionReceiptLayer.record arithmetic twoDirectRoute

def twoComposed : (constructionReceiptLayer arithmetic).Total :=
  constructionReceiptLayer.record arithmetic twoComposedRoute

theorem two_routes_evaluate_equally :
    arithmetic.evaluate twoDirectRoute =
      arithmetic.evaluate twoComposedRoute :=
  by
    change (2 : Nat) = Nat.add 1 1
    rfl

def rootIsOperation : constructionReceiptLayer.AnyTree arithmetic → Bool
  | ⟨_, .source _⟩ => false
  | ⟨_, .apply _ _⟩ => true

theorem two_routes_are_distinct :
    (⟨Kind.number, twoDirectRoute⟩ : constructionReceiptLayer.AnyTree arithmetic) ≠
      ⟨Kind.number, twoComposedRoute⟩ := by
  intro equal
  have rootEqual := congrArg rootIsOperation equal
  exact Bool.noConfusion rootEqual

/-- Negative: even in the many-sorted setting, flat erasure loses route
identity. -/
theorem erase_not_injective :
    ¬ Function.Injective (constructionReceiptLayer arithmetic).erase := by
  intro injective
  have recordsEqual : twoDirect = twoComposed := by
    apply injective
    simp [twoDirect, twoComposed, two_routes_evaluate_equally]
  exact two_routes_are_distinct
    (congrArg (constructionReceiptLayer.route arithmetic) recordsEqual)

/-- Negative: no function of the kind-indexed flat result can reconstruct all
construction histories. -/
theorem no_universal_history_recovery :
    ¬ ∃ recover : Result arithmetic →
          (constructionReceiptLayer arithmetic).Total,
        Function.LeftInverse recover
          (constructionReceiptLayer arithmetic).erase := by
  rintro ⟨recover, recovers⟩
  have recordsEqual : twoDirect = twoComposed := by
    calc
      twoDirect = recover
          ((constructionReceiptLayer arithmetic).erase twoDirect) :=
        (recovers twoDirect).symm
      _ = recover
          ((constructionReceiptLayer arithmetic).erase twoComposed) := by rfl
      _ = twoComposed := recovers twoComposed
  exact two_routes_are_distinct
    (congrArg (constructionReceiptLayer.route arithmetic) recordsEqual)

def makeTwoComposed : ConstructionCommand arithmetic :=
  .make ⟨.number, twoComposedRoute⟩

def readyTwoComposed : ConstructionCommand arithmetic :=
  .ready twoComposed

/-- Positive: the heterogeneous authoring GSLT performs a real construction
transition. -/
theorem makeTwoComposed_step :
    (constructionProvenanceGSLT arithmetic).Step
      makeTwoComposed readyTwoComposed := by
  change ConstructionCommandStep arithmetic makeTwoComposed readyTwoComposed
  simpa [makeTwoComposed, readyTwoComposed, twoComposed] using
    (ConstructionCommandStep.make (algebra := arithmetic) twoComposedRoute)

/-- Negative: completed construction results are terminal. -/
theorem readyTwoComposed_has_no_step :
    ∀ target,
      ¬ (constructionProvenanceGSLT arithmetic).Step
        readyTwoComposed target := by
  intro target step
  cases step

#print axioms fiveByAddition_evaluates
#print axioms twoIsNotZero_evaluates
#print axioms two_routes_evaluate_equally
#print axioms two_routes_are_distinct
#print axioms erase_not_injective
#print axioms no_universal_history_recovery
#print axioms makeTwoComposed_step
#print axioms readyTwoComposed_has_no_step

end Canary

end Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
