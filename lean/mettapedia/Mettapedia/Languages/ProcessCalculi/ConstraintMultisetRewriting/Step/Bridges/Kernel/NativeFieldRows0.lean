import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldReconstruction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseRows0

/-! Typed field expressions decomposed from the native case theorem. Reception and source-clause correspondence are separate checks. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema

-- RName
def schema0 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t4 ops, t13 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .drops => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .policy => (.var (.vs (.vs (.vs .vz))))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .names => (.app (.app (.const (.constant ops.c6 (t64 ops) (t64_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .nameMap => (.app (.app (.const (.constant ops.c6 (t66 ops) (t66_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c7 (t67 ops) (t67_meaning ops))) (.var .vz)) (.const (.constant ops.c8 (t13 ops) (t13_meaning ops)))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .drops => (.var (.vs (.vs (.vs (.vs .vz)))))
    | .policy => (.var (.vs (.vs (.vs .vz))))
  record := (.app (.const (.constant ops.c5 (t62 ops) (t62_meaning ops))) (.var (.vs (.vs .vz))))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var .vz)) (.app (.const (.constant ops.c10 (t69 ops) (t69_meaning ops))) (.app (.app (.const (.constant ops.c6 (t64 ops) (t64_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.eq (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.var .vz)) (.app (.app (.const (.constant ops.c6 (t64 ops) (t64_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))) (.app (.const (.constant ops.c12 (t72 ops) (t72_meaning ops))) (.var (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c13 (t73 ops) (t73_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))))
  writes := [.names, .nameMap]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema0_reconstructs (ops : Operations) :
    (schema0 ops).sourceClause = NativeClauseData.clause0 ops := by rfl

-- RTyVar
def schema1 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t8 ops, t8 ops, t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .policy => (.var (.vs (.vs (.vs (.vs .vz)))))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .typeRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs .vz))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .dbRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.var (.vs .vz)))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .typeMap => (.app (.app (.const (.constant ops.c6 (t66 ops) (t66_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c7 (t67 ops) (t67_meaning ops))) (.var .vz)) (.const (.constant ops.c8 (t13 ops) (t13_meaning ops)))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
    | .policy => (.var (.vs (.vs (.vs (.vs .vz)))))
  record := (.app (.const (.constant ops.c14 (t74 ops) (t74_meaning ops))) (.var (.vs (.vs (.vs .vz)))))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c15 (t80 ops) (t80_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.app (.const (.constant ops.c16 (t83 ops) (t83_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))) (.app (.app (.app (.app (.const (.constant ops.c17 (t88 ops) (t88_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs .vz))))) (.var .vz)) (.app (.const (.constant ops.c18 (t89 ops) (t89_meaning ops))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))))
  writes := [.typeRows, .dbRows, .typeMap]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema1_reconstructs (ops : Operations) :
    (schema1 ops).sourceClause = NativeClauseData.clause1 ops := by rfl

-- RTyApp
def schema2 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t8 ops, t8 ops, t91 ops, t13 ops, t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
    | .typeRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .dbRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeMap => (.app (.app (.const (.constant ops.c6 (t66 ops) (t66_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c7 (t67 ops) (t67_meaning ops))) (.var .vz)) (.const (.constant ops.c8 (t13 ops) (t13_meaning ops)))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  record := (.app (.app (.const (.constant ops.c19 (t94 ops) (t94_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs .vz))))))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c19 (t94 ops) (t94_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.eq (.app (.app (.const (.constant ops.c21 (t101 ops) (t101_meaning ops))) (.app (.const (.constant ops.c22 (t102 ops) (t102_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.const (.constant ops.c23 (t103 ops) (t103_meaning ops))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.const (.constant ops.c24 (t105 ops) (t105_meaning ops))) (.lam (.lam (.app (.app (.app (.app (.const (.constant ops.c17 (t88 ops) (t88_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs .vz))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var .vz))))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c15 (t80 ops) (t80_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.app (.const (.constant ops.c16 (t83 ops) (t83_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))) (.app (.app (.app (.app (.const (.constant ops.c17 (t88 ops) (t88_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))) (.var .vz)) (.app (.app (.const (.constant ops.c25 (t107 ops) (t107_meaning ops))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs (.vs .vz))))))))))))
  writes := [.typeRows, .dbRows, .typeMap]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema2_reconstructs (ops : Operations) :
    (schema2 ops).sourceClause = NativeClauseData.clause2 ops := by rfl

-- RVar
def schema3 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t8 ops, t8 ops, t84 ops, t5 ops, t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
    | .typeRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))
    | .termRows => (.app (.app (.const (.constant ops.c6 (t111 ops) (t111_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c7 (t112 ops) (t112_meaning ops))) (.app (.app (.const (.constant ops.c4 (t114 ops) (t114_meaning ops))) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops))))) (.app (.app (.const (.constant ops.c4 (t117 ops) (t117_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t119 ops) (t119_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t121 ops) (t121_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.var .vz)))))) (.const (.constant ops.c8 (t11 ops) (t11_meaning ops)))))
    | .dbRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
  record := (.app (.app (.const (.constant ops.c26 (t109 ops) (t109_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs .vz))))))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c26 (t109 ops) (t109_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c17 (t88 ops) (t88_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.var (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c15 (t80 ops) (t80_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.app (.const (.constant ops.c16 (t83 ops) (t83_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))) (.app (.app (.app (.app (.app (.const (.constant ops.c29 (t127 ops) (t127_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs .vz)))) (.var .vz)) (.app (.app (.const (.constant ops.c30 (t129 ops) (t129_meaning ops))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs .vz))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs (.vs .vz)))))))))))
  writes := [.typeRows, .termRows, .dbRows]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema3_reconstructs (ops : Operations) :
    (schema3 ops).sourceClause = NativeClauseData.clause3 ops := by rfl

-- RConst
def schema4 (ops : Operations) : Syntax ops where
  locals := [t5 ops, t8 ops, t8 ops, t131 ops, t84 ops, t84 ops, t5 ops, t5 ops, t5 ops, t12 ops, t13 ops, t13 ops, t12 ops, t8 ops, t11 ops, t8 ops, t4 ops, t1 ops]
  before
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))
    | .typeRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))
    | .termRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
    | .dbRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
  after
    | .context => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))
    | .names => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))
    | .typeRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs .vz))))
    | .termRows => (.app (.app (.const (.constant ops.c6 (t111 ops) (t111_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c7 (t112 ops) (t112_meaning ops))) (.app (.app (.const (.constant ops.c4 (t114 ops) (t114_meaning ops))) (.app (.const (.constant ops.c27 (t115 ops) (t115_meaning ops))) (.app (.const (.constant ops.c32 (t115 ops) (t115_meaning ops))) (.const (.constant ops.c28 (t5 ops) (t5_meaning ops)))))) (.app (.app (.const (.constant ops.c4 (t117 ops) (t117_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c4 (t119 ops) (t119_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c4 (t121 ops) (t121_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var .vz)))))) (.const (.constant ops.c8 (t11 ops) (t11_meaning ops)))))
    | .dbRows => (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs .vz)))
    | .theoremRows => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))
    | .nameMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))
    | .typeMap => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))
    | .drops => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))
    | .policy => (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))
  record := (.app (.app (.const (.constant ops.c31 (t109 ops) (t109_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
  guard := (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c20 (t96 ops) (t96_meaning ops))) (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))) (.app (.app (.const (.constant ops.c31 (t109 ops) (t109_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.const (.constant ops.c9 (t68 ops) (t68_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.app (.const (.constant ops.c10 (t77 ops) (t77_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.eq (.app (.app (.const (.constant ops.c21 (t138 ops) (t138_meaning ops))) (.app (.const (.constant ops.c33 (t139 ops) (t139_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))) (.app (.const (.constant ops.c23 (t140 ops) (t140_meaning ops))) (.var (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c17 (t88 ops) (t88_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.eq (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.app (.app (.const (.constant ops.c34 (t142 ops) (t142_meaning ops))) (.var (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs (.vs .vz)))))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.const (.constant ops.c15 (t80 ops) (t80_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c3 (t29 ops) (t29_meaning ops))) (.app (.app (.app (.app (.app (.const (.constant ops.c16 (t83 ops) (t83_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))) (.app (.app (.app (.app (.app (.const (.constant ops.c29 (t127 ops) (t127_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))) (.var (.vs (.vs .vz))))) (.app (.app (.const (.constant ops.c6 (t76 ops) (t76_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))) (.var (.vs .vz)))) (.var .vz)) (.app (.app (.const (.constant ops.c35 (t129 ops) (t129_meaning ops))) (.app (.app (.const (.constant ops.c11 (t71 ops) (t71_meaning ops))) (.app (.app (.const (.constant ops.c11 (t90 ops) (t90_meaning ops))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))))))))))))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))))))))))
  writes := [.typeRows, .termRows, .dbRows]
  writes_distinct := by decide
  unchanged := by
    intro field absent
    cases field <;> simp_all

theorem schema4_reconstructs (ops : Operations) :
    (schema4 ops).sourceClause = NativeClauseData.clause4 ops := by rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFields
