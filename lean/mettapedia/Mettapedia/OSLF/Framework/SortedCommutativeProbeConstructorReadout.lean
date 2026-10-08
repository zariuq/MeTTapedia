import Mettapedia.OSLF.Syntax.SortedCommutativeConstructorReadout
import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentProfile

/-!
# Complete administrative-head readout through the equation quotient

The free-head inventory is mapped to its actual declared constructors.
Comparing whole get/build redex classes therefore compares the entire
instrument, including its constructor and selected position. AC1 may change
source decompositions; it cannot identify these fresh administrative heads.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

private def headConstructor {sort : Srt arity}
    (head : Head (signature := signature arity) (Parallel := Parallel arity) sort) : Constructor arity :=
  match head with
  | .node constructor _arguments => constructor

def constructorInventory {sort : Srt arity} (supplied : ValueClass arity sort) : Multiset (Constructor arity) :=
  (inventoryQ supplied).map headConstructor

theorem constructorInventory_probeCut (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    constructorInventory (classOf (cut arity instrument (probe arity instrument) body)) =
      {Constructor.cut instrument} := rfl

theorem get_get_head_readout (first second : SourceSymbol Symbols)
    (firstPosition : Fin (sourceArity arity first)) (secondPosition : Fin (sourceArity arity second))
    (firstBody : Value arity (.arguments first)) (secondBody : Value arity (.arguments second))
    (same : classOf (cut arity (.get first firstPosition) (probe arity (.get first firstPosition)) firstBody) =
      classOf (cut arity (.get second secondPosition) (probe arity (.get second secondPosition)) secondBody)) :
    (InstrumentCutContexts.Probe.get first firstPosition : Probe arity) = .get second secondPosition :=
  Constructor.cut.inj (Multiset.singleton_inj.mp (congrArg constructorInventory same))

theorem get_build_head_separate (first second : SourceSymbol Symbols)
    (position : Fin (sourceArity arity first))
    (firstBody : Value arity (.arguments first)) (secondBody : Value arity (.arguments second)) :
    classOf (cut arity (.get first position) (probe arity (.get first position)) firstBody) ≠
      classOf (cut arity (.build second) (probe arity (.build second)) secondBody) := by
  intro same
  have impossible := Constructor.cut.inj (Multiset.singleton_inj.mp (congrArg constructorInventory same))
  cases impossible

theorem build_build_head_readout (first second : SourceSymbol Symbols)
    (firstBody : Value arity (.arguments first)) (secondBody : Value arity (.arguments second))
    (same : classOf (cut arity (.build first) (probe arity (.build first)) firstBody) =
      classOf (cut arity (.build second) (probe arity (.build second)) secondBody)) :
    first = second :=
  InstrumentCutContexts.Probe.build.inj
    (Constructor.cut.inj (Multiset.singleton_inj.mp (congrArg constructorInventory same)))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
