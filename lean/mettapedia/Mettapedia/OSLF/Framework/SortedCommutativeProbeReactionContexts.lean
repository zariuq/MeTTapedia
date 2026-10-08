import Mettapedia.OSLF.Framework.SortedCommutativeProbeBundleContexts
import Mettapedia.OSLF.Syntax.SortedCommutativeSourceErasureAction
import Mettapedia.OSLF.Syntax.SortedCommutativeUnitContexts

/-!
# Identity reconstruction for pure administrative reaction contexts

Complete hereditary support reconstructs the source context. Its action on
the erased whole input then preserves the source unit; the independent AC1
unit theorem identifies that entire context class with the identity. This
uses neither faithful ground action nor an equation chosen for the output.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem pure_context_unit_erasure_identity
    (context : ContextClass (signature arity) (Parallel arity) .base .base)
    (pure : classContextObserverCount context = 0)
    (input : ValueClass arity .base)
    (inputRead : Source.classRetraction input =
      classOf (.zero rfl : Source.Value arity))
    (outputRead : Source.classRetraction (context.fill input) =
      classOf (.zero rfl : Source.Value arity)) :
    context = ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) .base := by
  let original := Source.contextRetraction context
  have contextRead : Source.contextEmbedding original = context :=
    classContextObserverCount_zero_readback context pure
  have erasureSquare : Source.classRetraction (context.fill input) =
      original.fill (Source.classRetraction input) :=
    (congrArg (fun context => Source.classRetraction (context.fill input)) contextRead).symm.trans
      (Source.retraction_embedded_context_fill original input)
  have unitRead : original.fill (classOf (.zero rfl : Source.Value arity)) =
      classOf (.zero rfl : Source.Value arity) := by
    exact (congrArg original.fill inputRead.symm).trans (erasureSquare.symm.trans outputRead)
  have originalIdentity := (ContextClass.fill_unit_iff_identity rfl original).mp unitRead
  calc
    context = Source.contextEmbedding original := contextRead.symm
    _ = Source.contextEmbedding
        (ContextClass.identity (signature := Source.signature arity) (Parallel := Source.Parallel arity) (ULift.up ())) :=
      congrArg Source.contextEmbedding originalIdentity
    _ = ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) .base := rfl

theorem erasure_probeCut (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    Source.classRetraction (classOf (cut arity instrument (probe arity instrument) body)) =
      classOf (.zero rfl : Source.Value arity) := rfl

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
