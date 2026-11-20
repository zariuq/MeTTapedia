import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows0
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows1
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows2
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows3
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows4
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows5

/-! Expected typed syntax of the native record case theorem. This data grants no admission: the complete table must pass NativeClauseReadback against the received cache. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open NativeClauseReadback

def table? (symbols : ExportCodec.Symbols) : Option (Σ signature : Signature, List signature.Clause) := do
  let ops ← operations? symbols
  return ⟨signature ops, [clause0 ops, clause1 ops, clause2 ops, clause3 ops, clause4 ops, clause5 ops, clause6 ops, clause7 ops, clause8 ops, clause9 ops, clause10 ops, clause11 ops, clause12 ops, clause13 ops, clause14 ops, clause15 ops, clause16 ops, clause17 ops, clause18 ops, clause19 ops, clause20 ops, clause21 ops, clause22 ops, clause23 ops, clause24 ops, clause25 ops, clause26 ops, clause27 ops, clause28 ops]⟩

def tableWithoutPolicy? (symbols : ExportCodec.Symbols) : Option (Σ signature : Signature, List signature.Clause) := do
  let ops ← operations? symbols
  return ⟨signature ops, [clause0 ops, clause1 ops, clause2 ops, clause3 ops, clause4 ops, clause5 ops, clause6 ops, clause7 ops, clause8 ops, clause9 ops, clause10 ops, clause11 ops, clause12 ops, clause13 ops, clause14 ops, clause15 ops, clause16 ops, clause17 ops, clause18 ops, clause19 ops, clause20 ops, clause21 ops, clause22 ops, clause23 ops, clause24 ops, clause25 ops, clause26WithoutPolicy ops, clause27 ops, clause28 ops]⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData
