import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.LanguageConstruction
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.RouteComposition

/-!
# Construction provenance

The authoritative construction calculus is many-sorted: language-engineering
operations may change carrier, combine differently typed inputs, or produce a
compiled target. It lives in `ConstructionProvenance.ManySorted`.

This module is the public entry point and supplies only the useful one-sort
specialization. The specialization is interpreted into the many-sorted core;
it does not define a second construction semantics. Its operation arities are
therefore checked by the same indexed construction trees, exact receipts, and
authored construction GSLT as heterogeneous pipelines.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructionProvenance

universe uObject uSource uUnary uBinary

/-! ## One-sort specialization -/

/-- Ergonomic input data for construction systems whose sources, intermediate
values, and results all have one object type. `toManySorted` gives this data
its sole operational meaning. -/
structure SingleSortedConstructionAlgebra (Object : Type uObject) where
  Source : Type uSource
  UnaryOperation : Type uUnary
  BinaryOperation : Type uBinary
  interpretSource : Source → Object
  interpretUnary : UnaryOperation → Object → Object
  interpretBinary : BinaryOperation → Object → Object → Object

namespace SingleSortedConstructionAlgebra

variable {Object : Type uObject}

/-- Arity-indexed operations generated from the unary and binary convenience
fields of a one-sort algebra. -/
inductive Operation
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object) :
    List Unit → Unit → Type (max uUnary uBinary) where
  | unary (operation : algebra.UnaryOperation) :
      Operation algebra [()] ()
  | binary (operation : algebra.BinaryOperation) :
      Operation algebra [(), ()] ()

private def interpretOperation
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    {inputs : List Unit} {output : Unit}
    (operation : Operation algebra inputs output)
    (arguments : ManySorted.FamilyList (fun _ => Object) inputs) : Object :=
  match operation, arguments with
  | .unary operation, .cons input .nil =>
      algebra.interpretUnary operation input
  | .binary operation, .cons left (.cons right .nil) =>
      algebra.interpretBinary operation left right

/-- Interpret a one-sort construction signature in the authoritative
many-sorted construction algebra. -/
def toManySorted
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object) :
    ManySorted.ManySortedConstructionAlgebra.{
      0, uObject, uSource, max uUnary uBinary} where
  Kind := Unit
  Object := fun _ => Object
  Source := fun _ => algebra.Source
  Operation := Operation algebra
  interpretSource := fun value => algebra.interpretSource value
  interpretOperation := interpretOperation algebra

/-- Construction trees for the one-sort specialization. -/
abbrev Tree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object) :=
  ManySorted.ConstructionTree algebra.toManySorted ()

/-- Embed one source as a typed construction tree. -/
def sourceTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (source : algebra.Source) : algebra.Tree :=
  .source source

/-- Apply a unary operation in the indexed construction core. -/
def unaryTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (operation : algebra.UnaryOperation) (input : algebra.Tree) :
    algebra.Tree :=
  .apply (Operation.unary operation) (.cons input .nil)

/-- Apply a binary operation in the indexed construction core. -/
def binaryTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (operation : algebra.BinaryOperation) (left right : algebra.Tree) :
    algebra.Tree :=
  .apply (Operation.binary operation) (.cons left (.cons right .nil))

/-- Evaluation is exactly evaluation by the many-sorted core. -/
def evaluate
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (route : algebra.Tree) : Object :=
  algebra.toManySorted.evaluate route

@[simp] theorem evaluate_sourceTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (source : algebra.Source) :
    algebra.evaluate (algebra.sourceTree source) =
      algebra.interpretSource source :=
  rfl

@[simp] theorem evaluate_unaryTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (operation : algebra.UnaryOperation) (input : algebra.Tree) :
    algebra.evaluate (algebra.unaryTree operation input) =
      algebra.interpretUnary operation (algebra.evaluate input) :=
  rfl

@[simp] theorem evaluate_binaryTree
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (operation : algebra.BinaryOperation) (left right : algebra.Tree) :
    algebra.evaluate (algebra.binaryTree operation left right) =
      algebra.interpretBinary operation
        (algebra.evaluate left) (algebra.evaluate right) :=
  rfl

/-- Exact one-sort receipts are fibers of the many-sorted receipt layer. -/
abbrev Receipt
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (result : Object) :=
  ManySorted.ConstructionReceipt (algebra := algebra.toManySorted)
    (kind := ()) result

/-- Package a one-sort route with the exact evaluation theorem supplied by
the many-sorted core. -/
def receipt
    (algebra :
      SingleSortedConstructionAlgebra.{uObject, uSource, uUnary, uBinary}
        Object)
    (route : algebra.Tree) : algebra.Receipt (algebra.evaluate route) where
  route := route
  evaluates := rfl

end SingleSortedConstructionAlgebra

/-! ## Positive and negative specialization controls -/

namespace SingleSortedCanary

inductive UnaryOperation where
  | successor
deriving DecidableEq

inductive BinaryOperation where
  | addition
deriving DecidableEq

def arithmetic : SingleSortedConstructionAlgebra Nat where
  Source := Nat
  UnaryOperation := UnaryOperation
  BinaryOperation := BinaryOperation
  interpretSource := id
  interpretUnary
    | .successor => Nat.succ
  interpretBinary
    | .addition => Nat.add

def one : arithmetic.Tree := arithmetic.sourceTree (1 : Nat)

def twoBySuccessor : arithmetic.Tree :=
  arithmetic.unaryTree .successor one

def three : arithmetic.Tree := arithmetic.sourceTree (3 : Nat)

def fiveByComposition : arithmetic.Tree :=
  arithmetic.binaryTree .addition twoBySuccessor three

/-- Positive: the convenience API has precisely the many-sorted evaluator's
meaning. -/
theorem fiveByComposition_evaluates :
    arithmetic.evaluate fiveByComposition = 5 :=
  rfl

def twoDirect : arithmetic.Tree := arithmetic.sourceTree (2 : Nat)

def twoComposed : arithmetic.Tree :=
  arithmetic.binaryTree .addition
    (arithmetic.sourceTree (1 : Nat)) (arithmetic.sourceTree (1 : Nat))

theorem two_routes_evaluate_equally :
    arithmetic.evaluate twoDirect = arithmetic.evaluate twoComposed :=
  rfl

/-- Negative: specializing to one sort does not collapse distinct construction
routes that happen to evaluate to the same result. -/
theorem two_routes_are_distinct : twoDirect ≠ twoComposed := by
  intro equality
  cases equality

/-- Negative: result equality does not imply route equality, even through the
one-sort convenience interface. -/
theorem evaluation_not_injective :
    ¬ Function.Injective arithmetic.evaluate := by
  intro injective
  exact two_routes_are_distinct (injective two_routes_evaluate_equally)

#print axioms fiveByComposition_evaluates
#print axioms two_routes_evaluate_equally
#print axioms two_routes_are_distinct
#print axioms evaluation_not_injective

end SingleSortedCanary

end Mettapedia.GSLT.LanguageDef.ConstructionProvenance
