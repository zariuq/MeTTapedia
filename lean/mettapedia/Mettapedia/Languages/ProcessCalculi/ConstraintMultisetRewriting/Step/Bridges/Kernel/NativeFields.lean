import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows0
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows1
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows2
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows3
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows4
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldRows5

/-! The finite interpreted native record table. This table alone is not a native implementation correspondence. -/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields

open NativeClauseData NativeFieldSchema

def table (ops : Operations) : Fin 29 → Syntax ops :=
  ![schema0 ops, schema1 ops, schema2 ops, schema3 ops, schema4 ops, schema5 ops, schema6 ops, schema7 ops, schema8 ops, schema9 ops, schema10 ops, schema11 ops, schema12 ops, schema13 ops, schema14 ops, schema15 ops, schema16 ops, schema17 ops, schema18 ops, schema19 ops, schema20 ops, schema21 ops, schema22 ops, schema23 ops, schema24 ops, schema25 ops, schema26 ops, schema27 ops, schema28 ops]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields
