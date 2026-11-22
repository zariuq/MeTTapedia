import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldReconstruction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows4

/-! Typed field expressions decomposed from the native case theorem. Reception and source-clause correspondence are separate checks. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema

-- RDropType
def schema20 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.var (.vs (.vs .vz)))
    | .policy => (.var (.vs .vz))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.app (.app (.const (.constant ops.c7 (t166 ops) (t166_meaning ops))) (.app (.app (.const (.constant ops.c4 (t121 ops) (t121_meaning ops))) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops)))))) (.var .vz))) (.var (.vs (.vs .vz))))
    | .policy => (.var (.vs .vz))
  record := (.app (.const (.constant ops.c81 (t74 ops) (t74_meaning ops))) (.var .vz))
  guard := (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))))))))) (.app (.const (.constant ops.c81 (t74 ops) (t74_meaning ops))) (.var .vz)))
  writes := [.drops]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema20_reconstructs (ops : Operations) :
    (schema20 ops).sourceClause = NativeClauseData.clause20 ops := by rfl

-- RDropTerm
def schema21 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.var (.vs (.vs .vz)))
    | .policy => (.var (.vs .vz))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.app (.app (.const (.constant ops.c7 (t166 ops) (t166_meaning ops))) (.app (.app (.const (.constant ops.c4 (t121 ops) (t121_meaning ops))) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c37 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops))))))) (.var .vz))) (.var (.vs (.vs .vz))))
    | .policy => (.var (.vs .vz))
  record := (.app (.const (.constant ops.c82 (t74 ops) (t74_meaning ops))) (.var .vz))
  guard := (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))))))))) (.app (.const (.constant ops.c82 (t74 ops) (t74_meaning ops))) (.var .vz)))
  writes := [.drops]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema21_reconstructs (ops : Operations) :
    (schema21 ops).sourceClause = NativeClauseData.clause21 ops := by rfl

-- RDropThm
def schema22 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.var (.vs (.vs .vz)))
    | .policy => (.var (.vs .vz))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.app (.app (.const (.constant ops.c7 (t166 ops) (t166_meaning ops))) (.app (.app (.const (.constant ops.c4 (t121 ops) (t121_meaning ops))) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops))))))) (.var .vz))) (.var (.vs (.vs .vz))))
    | .policy => (.var (.vs .vz))
  record := (.app (.const (.constant ops.c83 (t74 ops) (t74_meaning ops))) (.var .vz))
  guard := (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))))))))) (.app (.const (.constant ops.c83 (t74 ops) (t74_meaning ops))) (.var .vz)))
  writes := [.drops]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema22_reconstructs (ops : Operations) :
    (schema22 ops).sourceClause = NativeClauseData.clause22 ops := by rfl

-- RPolicy
def schema23 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.var (.vs (.vs .vz)))
    | .policy => (.var (.vs .vz))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .typeMap => (.var (.vs (.vs (.vs .vz))))
    | .drops => (.var (.vs (.vs .vz)))
    | .policy => (.app (.app (.const (.constant ops.c85 (t233 ops) (t233_meaning ops))) (.var (.vs .vz))) (.var .vz))
  record := (.app (.const (.constant ops.c84 (t74 ops) (t74_meaning ops))) (.var .vz))
  guard := (.app (.app (.const (.constant ops.c86 (t68 ops) (t68_meaning ops))) (.var .vz)) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c37 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops)))))))
  writes := [.policy]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema23_reconstructs (ops : Operations) :
    (schema23 ops).sourceClause = NativeClauseData.clause23 ops := by rfl

-- RNewType
def schema24 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .drops => (.var (.vs (.vs (.vs .vz))))
    | .policy => (.var (.vs (.vs .vz)))
  after
    | .context => (.app (.app (.const (.constant ops.c7 (t235 ops) (t235_meaning ops))) (.app (.app (.const (.constant ops.c88 (t237 ops) (t237_meaning ops))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs .vz))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var .vz))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .drops => (.var (.vs (.vs (.vs .vz))))
    | .policy => (.var (.vs (.vs .vz)))
  record := (.app (.app (.const (.constant ops.c87 (t109 ops) (t109_meaning ops))) (.var (.vs .vz))) (.var .vz))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var (.vs .vz))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.eq (.app (.app (.const (.constant ops.c21 (t101 ops) (t101_meaning ops))) (.app (.const (.constant ops.c22 (t102 ops) (t102_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs .vz))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.const (.constant ops.c89 (t99 ops) (t99_meaning ops)))))
  writes := [.context]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema24_reconstructs (ops : Operations) :
    (schema24 ops).sourceClause = NativeClauseData.clause24 ops := by rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields
