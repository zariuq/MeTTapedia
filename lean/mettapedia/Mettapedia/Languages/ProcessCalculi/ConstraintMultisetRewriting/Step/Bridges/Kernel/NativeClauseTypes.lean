import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeClauseSymbols

/-! Expected typed syntax of the native record case theorem. This data grants no admission: the complete table must pass NativeClauseReadback against the received cache. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open NativeClauseReadback

def t0 (_ops : Operations) : Ty := .op _ops.o0 []
def h0 (ops : Operations) : HOL.Ty AtomicTy := (t0 ops).toHOL
theorem t0_meaning (ops : Operations) : (t0 ops).toHOL = h0 ops := rfl

def t1 (_ops : Operations) : Ty := .op _ops.o1 [(t0 _ops)]
def h1 (ops : Operations) : HOL.Ty AtomicTy := (t1 ops).toHOL
theorem t1_meaning (ops : Operations) : (t1 ops).toHOL = h1 ops := rfl

def t2 (_ops : Operations) : Ty := .op _ops.o2 []
def h2 (ops : Operations) : HOL.Ty AtomicTy := (t2 ops).toHOL
theorem t2_meaning (ops : Operations) : (t2 ops).toHOL = h2 ops := rfl

def t3 (_ops : Operations) : Ty := .op _ops.o1 [(t2 _ops)]
def h3 (ops : Operations) : HOL.Ty AtomicTy := (t3 ops).toHOL
theorem t3_meaning (ops : Operations) : (t3 ops).toHOL = h3 ops := rfl

def t4 (_ops : Operations) : Ty := .op _ops.o1 [(t3 _ops)]
def h4 (ops : Operations) : HOL.Ty AtomicTy := (t4 ops).toHOL
theorem t4_meaning (ops : Operations) : (t4 ops).toHOL = h4 ops := rfl

def t5 (_ops : Operations) : Ty := .op _ops.o3 []
def h5 (ops : Operations) : HOL.Ty AtomicTy := (t5 ops).toHOL
theorem t5_meaning (ops : Operations) : (t5 ops).toHOL = h5 ops := rfl

def t6 (_ops : Operations) : Ty := .op _ops.o4 [(t5 _ops), (t5 _ops)]
def h6 (ops : Operations) : HOL.Ty AtomicTy := (t6 ops).toHOL
theorem t6_meaning (ops : Operations) : (t6 ops).toHOL = h6 ops := rfl

def t7 (_ops : Operations) : Ty := .op _ops.o4 [(t5 _ops), (t6 _ops)]
def h7 (ops : Operations) : HOL.Ty AtomicTy := (t7 ops).toHOL
theorem t7_meaning (ops : Operations) : (t7 ops).toHOL = h7 ops := rfl

def t8 (_ops : Operations) : Ty := .op _ops.o1 [(t7 _ops)]
def h8 (ops : Operations) : HOL.Ty AtomicTy := (t8 ops).toHOL
theorem t8_meaning (ops : Operations) : (t8 ops).toHOL = h8 ops := rfl

def t9 (_ops : Operations) : Ty := .op _ops.o4 [(t5 _ops), (t7 _ops)]
def h9 (ops : Operations) : HOL.Ty AtomicTy := (t9 ops).toHOL
theorem t9_meaning (ops : Operations) : (t9 ops).toHOL = h9 ops := rfl

def t10 (_ops : Operations) : Ty := .op _ops.o4 [(t5 _ops), (t9 _ops)]
def h10 (ops : Operations) : HOL.Ty AtomicTy := (t10 ops).toHOL
theorem t10_meaning (ops : Operations) : (t10 ops).toHOL = h10 ops := rfl

def t11 (_ops : Operations) : Ty := .op _ops.o1 [(t10 _ops)]
def h11 (ops : Operations) : HOL.Ty AtomicTy := (t11 ops).toHOL
theorem t11_meaning (ops : Operations) : (t11 ops).toHOL = h11 ops := rfl

def t12 (_ops : Operations) : Ty := .op _ops.o1 [(t6 _ops)]
def h12 (ops : Operations) : HOL.Ty AtomicTy := (t12 ops).toHOL
theorem t12_meaning (ops : Operations) : (t12 ops).toHOL = h12 ops := rfl

def t13 (_ops : Operations) : Ty := .op _ops.o1 [(t5 _ops)]
def h13 (ops : Operations) : HOL.Ty AtomicTy := (t13 ops).toHOL
theorem t13_meaning (ops : Operations) : (t13 ops).toHOL = h13 ops := rfl

def t14 (_ops : Operations) : Ty := .op _ops.o4 [(t12 _ops), (t5 _ops)]
def h14 (ops : Operations) : HOL.Ty AtomicTy := (t14 ops).toHOL
theorem t14_meaning (ops : Operations) : (t14 ops).toHOL = h14 ops := rfl

def t15 (_ops : Operations) : Ty := .op _ops.o4 [(t13 _ops), (t14 _ops)]
def h15 (ops : Operations) : HOL.Ty AtomicTy := (t15 ops).toHOL
theorem t15_meaning (ops : Operations) : (t15 ops).toHOL = h15 ops := rfl

def t16 (_ops : Operations) : Ty := .op _ops.o4 [(t13 _ops), (t15 _ops)]
def h16 (ops : Operations) : HOL.Ty AtomicTy := (t16 ops).toHOL
theorem t16_meaning (ops : Operations) : (t16 ops).toHOL = h16 ops := rfl

def t17 (_ops : Operations) : Ty := .op _ops.o4 [(t12 _ops), (t16 _ops)]
def h17 (ops : Operations) : HOL.Ty AtomicTy := (t17 ops).toHOL
theorem t17_meaning (ops : Operations) : (t17 ops).toHOL = h17 ops := rfl

def t18 (_ops : Operations) : Ty := .op _ops.o4 [(t8 _ops), (t17 _ops)]
def h18 (ops : Operations) : HOL.Ty AtomicTy := (t18 ops).toHOL
theorem t18_meaning (ops : Operations) : (t18 ops).toHOL = h18 ops := rfl

def t19 (_ops : Operations) : Ty := .op _ops.o4 [(t11 _ops), (t18 _ops)]
def h19 (ops : Operations) : HOL.Ty AtomicTy := (t19 ops).toHOL
theorem t19_meaning (ops : Operations) : (t19 ops).toHOL = h19 ops := rfl

def t20 (_ops : Operations) : Ty := .op _ops.o4 [(t8 _ops), (t19 _ops)]
def h20 (ops : Operations) : HOL.Ty AtomicTy := (t20 ops).toHOL
theorem t20_meaning (ops : Operations) : (t20 ops).toHOL = h20 ops := rfl

def t21 (_ops : Operations) : Ty := .op _ops.o4 [(t4 _ops), (t20 _ops)]
def h21 (ops : Operations) : HOL.Ty AtomicTy := (t21 ops).toHOL
theorem t21_meaning (ops : Operations) : (t21 ops).toHOL = h21 ops := rfl

def t22 (_ops : Operations) : Ty := .op _ops.o4 [(t1 _ops), (t21 _ops)]
def h22 (ops : Operations) : HOL.Ty AtomicTy := (t22 ops).toHOL
theorem t22_meaning (ops : Operations) : (t22 ops).toHOL = h22 ops := rfl

def t23 (_ops : Operations) : Ty := .op _ops.o5 []
def h23 (ops : Operations) : HOL.Ty AtomicTy := (t23 ops).toHOL
theorem t23_meaning (ops : Operations) : (t23 ops).toHOL = h23 ops := rfl

def t24 (_ops : Operations) : Ty := Ty.bool
def h24 (_ops : Operations) : HOL.Ty AtomicTy := .prop
theorem t24_meaning (ops : Operations) : (t24 ops).toHOL = h24 ops := by simp only [t24, h24, Ty.toHOL_bool]

def t25 (_ops : Operations) : Ty := .function (t22 _ops) (t24 _ops)
def h25 (ops : Operations) : HOL.Ty AtomicTy := (h22 ops).arr (h24 ops)
theorem t25_meaning (ops : Operations) : (t25 ops).toHOL = h25 ops := by
  simp only [t25, h25, Ty.toHOL_function, t22_meaning, t24_meaning]

def t26 (_ops : Operations) : Ty := .function (t23 _ops) (t25 _ops)
def h26 (ops : Operations) : HOL.Ty AtomicTy := (h23 ops).arr (h25 ops)
theorem t26_meaning (ops : Operations) : (t26 ops).toHOL = h26 ops := by
  simp only [t26, h26, Ty.toHOL_function, t23_meaning, t25_meaning]

def t27 (_ops : Operations) : Ty := .function (t22 _ops) (t26 _ops)
def h27 (ops : Operations) : HOL.Ty AtomicTy := (h22 ops).arr (h26 ops)
theorem t27_meaning (ops : Operations) : (t27 ops).toHOL = h27 ops := by
  simp only [t27, h27, Ty.toHOL_function, t22_meaning, t26_meaning]

def t28 (_ops : Operations) : Ty := .function (t24 _ops) (t24 _ops)
def h28 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h24 ops)
theorem t28_meaning (ops : Operations) : (t28 ops).toHOL = h28 ops := by
  simp only [t28, h28, Ty.toHOL_function, t24_meaning]

def t29 (_ops : Operations) : Ty := .function (t24 _ops) (t28 _ops)
def h29 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h28 ops)
theorem t29_meaning (ops : Operations) : (t29 ops).toHOL = h29 ops := by
  simp only [t29, h29, Ty.toHOL_function, t24_meaning, t28_meaning]

def t30 (_ops : Operations) : Ty := .function (t1 _ops) (t24 _ops)
def h30 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h24 ops)
theorem t30_meaning (ops : Operations) : (t30 ops).toHOL = h30 ops := by
  simp only [t30, h30, Ty.toHOL_function, t1_meaning, t24_meaning]

def t31 (_ops : Operations) : Ty := .function (t30 _ops) (t24 _ops)
def h31 (ops : Operations) : HOL.Ty AtomicTy := (h30 ops).arr (h24 ops)
theorem t31_meaning (ops : Operations) : (t31 ops).toHOL = h31 ops := by
  simp only [t31, h31, Ty.toHOL_function, t30_meaning, t24_meaning]

def t32 (_ops : Operations) : Ty := .function (t4 _ops) (t24 _ops)
def h32 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h24 ops)
theorem t32_meaning (ops : Operations) : (t32 ops).toHOL = h32 ops := by
  simp only [t32, h32, Ty.toHOL_function, t4_meaning, t24_meaning]

def t33 (_ops : Operations) : Ty := .function (t32 _ops) (t24 _ops)
def h33 (ops : Operations) : HOL.Ty AtomicTy := (h32 ops).arr (h24 ops)
theorem t33_meaning (ops : Operations) : (t33 ops).toHOL = h33 ops := by
  simp only [t33, h33, Ty.toHOL_function, t32_meaning, t24_meaning]

def t34 (_ops : Operations) : Ty := .function (t8 _ops) (t24 _ops)
def h34 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h24 ops)
theorem t34_meaning (ops : Operations) : (t34 ops).toHOL = h34 ops := by
  simp only [t34, h34, Ty.toHOL_function, t8_meaning, t24_meaning]

def t35 (_ops : Operations) : Ty := .function (t34 _ops) (t24 _ops)
def h35 (ops : Operations) : HOL.Ty AtomicTy := (h34 ops).arr (h24 ops)
theorem t35_meaning (ops : Operations) : (t35 ops).toHOL = h35 ops := by
  simp only [t35, h35, Ty.toHOL_function, t34_meaning, t24_meaning]

def t36 (_ops : Operations) : Ty := .function (t11 _ops) (t24 _ops)
def h36 (ops : Operations) : HOL.Ty AtomicTy := (h11 ops).arr (h24 ops)
theorem t36_meaning (ops : Operations) : (t36 ops).toHOL = h36 ops := by
  simp only [t36, h36, Ty.toHOL_function, t11_meaning, t24_meaning]

def t37 (_ops : Operations) : Ty := .function (t36 _ops) (t24 _ops)
def h37 (ops : Operations) : HOL.Ty AtomicTy := (h36 ops).arr (h24 ops)
theorem t37_meaning (ops : Operations) : (t37 ops).toHOL = h37 ops := by
  simp only [t37, h37, Ty.toHOL_function, t36_meaning, t24_meaning]

def t38 (_ops : Operations) : Ty := .function (t12 _ops) (t24 _ops)
def h38 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h24 ops)
theorem t38_meaning (ops : Operations) : (t38 ops).toHOL = h38 ops := by
  simp only [t38, h38, Ty.toHOL_function, t12_meaning, t24_meaning]

def t39 (_ops : Operations) : Ty := .function (t38 _ops) (t24 _ops)
def h39 (ops : Operations) : HOL.Ty AtomicTy := (h38 ops).arr (h24 ops)
theorem t39_meaning (ops : Operations) : (t39 ops).toHOL = h39 ops := by
  simp only [t39, h39, Ty.toHOL_function, t38_meaning, t24_meaning]

def t40 (_ops : Operations) : Ty := .function (t13 _ops) (t24 _ops)
def h40 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h24 ops)
theorem t40_meaning (ops : Operations) : (t40 ops).toHOL = h40 ops := by
  simp only [t40, h40, Ty.toHOL_function, t13_meaning, t24_meaning]

def t41 (_ops : Operations) : Ty := .function (t40 _ops) (t24 _ops)
def h41 (ops : Operations) : HOL.Ty AtomicTy := (h40 ops).arr (h24 ops)
theorem t41_meaning (ops : Operations) : (t41 ops).toHOL = h41 ops := by
  simp only [t41, h41, Ty.toHOL_function, t40_meaning, t24_meaning]

def t42 (_ops : Operations) : Ty := .function (t5 _ops) (t24 _ops)
def h42 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h24 ops)
theorem t42_meaning (ops : Operations) : (t42 ops).toHOL = h42 ops := by
  simp only [t42, h42, Ty.toHOL_function, t5_meaning, t24_meaning]

def t43 (_ops : Operations) : Ty := .function (t42 _ops) (t24 _ops)
def h43 (ops : Operations) : HOL.Ty AtomicTy := (h42 ops).arr (h24 ops)
theorem t43_meaning (ops : Operations) : (t43 ops).toHOL = h43 ops := by
  simp only [t43, h43, Ty.toHOL_function, t42_meaning, t24_meaning]

def t44 (_ops : Operations) : Ty := .function (t21 _ops) (t22 _ops)
def h44 (ops : Operations) : HOL.Ty AtomicTy := (h21 ops).arr (h22 ops)
theorem t44_meaning (ops : Operations) : (t44 ops).toHOL = h44 ops := by
  simp only [t44, h44, Ty.toHOL_function, t21_meaning, t22_meaning]

def t45 (_ops : Operations) : Ty := .function (t1 _ops) (t44 _ops)
def h45 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h44 ops)
theorem t45_meaning (ops : Operations) : (t45 ops).toHOL = h45 ops := by
  simp only [t45, h45, Ty.toHOL_function, t1_meaning, t44_meaning]

def t46 (_ops : Operations) : Ty := .function (t20 _ops) (t21 _ops)
def h46 (ops : Operations) : HOL.Ty AtomicTy := (h20 ops).arr (h21 ops)
theorem t46_meaning (ops : Operations) : (t46 ops).toHOL = h46 ops := by
  simp only [t46, h46, Ty.toHOL_function, t20_meaning, t21_meaning]

def t47 (_ops : Operations) : Ty := .function (t4 _ops) (t46 _ops)
def h47 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h46 ops)
theorem t47_meaning (ops : Operations) : (t47 ops).toHOL = h47 ops := by
  simp only [t47, h47, Ty.toHOL_function, t4_meaning, t46_meaning]

def t48 (_ops : Operations) : Ty := .function (t19 _ops) (t20 _ops)
def h48 (ops : Operations) : HOL.Ty AtomicTy := (h19 ops).arr (h20 ops)
theorem t48_meaning (ops : Operations) : (t48 ops).toHOL = h48 ops := by
  simp only [t48, h48, Ty.toHOL_function, t19_meaning, t20_meaning]

def t49 (_ops : Operations) : Ty := .function (t8 _ops) (t48 _ops)
def h49 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h48 ops)
theorem t49_meaning (ops : Operations) : (t49 ops).toHOL = h49 ops := by
  simp only [t49, h49, Ty.toHOL_function, t8_meaning, t48_meaning]

def t50 (_ops : Operations) : Ty := .function (t18 _ops) (t19 _ops)
def h50 (ops : Operations) : HOL.Ty AtomicTy := (h18 ops).arr (h19 ops)
theorem t50_meaning (ops : Operations) : (t50 ops).toHOL = h50 ops := by
  simp only [t50, h50, Ty.toHOL_function, t18_meaning, t19_meaning]

def t51 (_ops : Operations) : Ty := .function (t11 _ops) (t50 _ops)
def h51 (ops : Operations) : HOL.Ty AtomicTy := (h11 ops).arr (h50 ops)
theorem t51_meaning (ops : Operations) : (t51 ops).toHOL = h51 ops := by
  simp only [t51, h51, Ty.toHOL_function, t11_meaning, t50_meaning]

def t52 (_ops : Operations) : Ty := .function (t17 _ops) (t18 _ops)
def h52 (ops : Operations) : HOL.Ty AtomicTy := (h17 ops).arr (h18 ops)
theorem t52_meaning (ops : Operations) : (t52 ops).toHOL = h52 ops := by
  simp only [t52, h52, Ty.toHOL_function, t17_meaning, t18_meaning]

def t53 (_ops : Operations) : Ty := .function (t8 _ops) (t52 _ops)
def h53 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h52 ops)
theorem t53_meaning (ops : Operations) : (t53 ops).toHOL = h53 ops := by
  simp only [t53, h53, Ty.toHOL_function, t8_meaning, t52_meaning]

def t54 (_ops : Operations) : Ty := .function (t16 _ops) (t17 _ops)
def h54 (ops : Operations) : HOL.Ty AtomicTy := (h16 ops).arr (h17 ops)
theorem t54_meaning (ops : Operations) : (t54 ops).toHOL = h54 ops := by
  simp only [t54, h54, Ty.toHOL_function, t16_meaning, t17_meaning]

def t55 (_ops : Operations) : Ty := .function (t12 _ops) (t54 _ops)
def h55 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h54 ops)
theorem t55_meaning (ops : Operations) : (t55 ops).toHOL = h55 ops := by
  simp only [t55, h55, Ty.toHOL_function, t12_meaning, t54_meaning]

def t56 (_ops : Operations) : Ty := .function (t15 _ops) (t16 _ops)
def h56 (ops : Operations) : HOL.Ty AtomicTy := (h15 ops).arr (h16 ops)
theorem t56_meaning (ops : Operations) : (t56 ops).toHOL = h56 ops := by
  simp only [t56, h56, Ty.toHOL_function, t15_meaning, t16_meaning]

def t57 (_ops : Operations) : Ty := .function (t13 _ops) (t56 _ops)
def h57 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h56 ops)
theorem t57_meaning (ops : Operations) : (t57 ops).toHOL = h57 ops := by
  simp only [t57, h57, Ty.toHOL_function, t13_meaning, t56_meaning]

def t58 (_ops : Operations) : Ty := .function (t14 _ops) (t15 _ops)
def h58 (ops : Operations) : HOL.Ty AtomicTy := (h14 ops).arr (h15 ops)
theorem t58_meaning (ops : Operations) : (t58 ops).toHOL = h58 ops := by
  simp only [t58, h58, Ty.toHOL_function, t14_meaning, t15_meaning]

def t59 (_ops : Operations) : Ty := .function (t13 _ops) (t58 _ops)
def h59 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h58 ops)
theorem t59_meaning (ops : Operations) : (t59 ops).toHOL = h59 ops := by
  simp only [t59, h59, Ty.toHOL_function, t13_meaning, t58_meaning]

def t60 (_ops : Operations) : Ty := .function (t5 _ops) (t14 _ops)
def h60 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h14 ops)
theorem t60_meaning (ops : Operations) : (t60 ops).toHOL = h60 ops := by
  simp only [t60, h60, Ty.toHOL_function, t5_meaning, t14_meaning]

def t61 (_ops : Operations) : Ty := .function (t12 _ops) (t60 _ops)
def h61 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h60 ops)
theorem t61_meaning (ops : Operations) : (t61 ops).toHOL = h61 ops := by
  simp only [t61, h61, Ty.toHOL_function, t12_meaning, t60_meaning]

def t62 (_ops : Operations) : Ty := .function (t13 _ops) (t23 _ops)
def h62 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h23 ops)
theorem t62_meaning (ops : Operations) : (t62 ops).toHOL = h62 ops := by
  simp only [t62, h62, Ty.toHOL_function, t13_meaning, t23_meaning]

def t63 (_ops : Operations) : Ty := .function (t4 _ops) (t4 _ops)
def h63 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h4 ops)
theorem t63_meaning (ops : Operations) : (t63 ops).toHOL = h63 ops := by
  simp only [t63, h63, Ty.toHOL_function, t4_meaning]

def t64 (_ops : Operations) : Ty := .function (t4 _ops) (t63 _ops)
def h64 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h63 ops)
theorem t64_meaning (ops : Operations) : (t64 ops).toHOL = h64 ops := by
  simp only [t64, h64, Ty.toHOL_function, t4_meaning, t63_meaning]

def t65 (_ops : Operations) : Ty := .function (t13 _ops) (t13 _ops)
def h65 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h13 ops)
theorem t65_meaning (ops : Operations) : (t65 ops).toHOL = h65 ops := by
  simp only [t65, h65, Ty.toHOL_function, t13_meaning]

def t66 (_ops : Operations) : Ty := .function (t13 _ops) (t65 _ops)
def h66 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h65 ops)
theorem t66_meaning (ops : Operations) : (t66 ops).toHOL = h66 ops := by
  simp only [t66, h66, Ty.toHOL_function, t13_meaning, t65_meaning]

def t67 (_ops : Operations) : Ty := .function (t5 _ops) (t65 _ops)
def h67 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h65 ops)
theorem t67_meaning (ops : Operations) : (t67 ops).toHOL = h67 ops := by
  simp only [t67, h67, Ty.toHOL_function, t5_meaning, t65_meaning]

def t68 (_ops : Operations) : Ty := .function (t5 _ops) (t42 _ops)
def h68 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h42 ops)
theorem t68_meaning (ops : Operations) : (t68 ops).toHOL = h68 ops := by
  simp only [t68, h68, Ty.toHOL_function, t5_meaning, t42_meaning]

def t69 (_ops : Operations) : Ty := .function (t4 _ops) (t5 _ops)
def h69 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h5 ops)
theorem t69_meaning (ops : Operations) : (t69 ops).toHOL = h69 ops := by
  simp only [t69, h69, Ty.toHOL_function, t4_meaning, t5_meaning]

def t70 (_ops : Operations) : Ty := .function (t4 _ops) (t3 _ops)
def h70 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h3 ops)
theorem t70_meaning (ops : Operations) : (t70 ops).toHOL = h70 ops := by
  simp only [t70, h70, Ty.toHOL_function, t4_meaning, t3_meaning]

def t71 (_ops : Operations) : Ty := .function (t5 _ops) (t70 _ops)
def h71 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h70 ops)
theorem t71_meaning (ops : Operations) : (t71 ops).toHOL = h71 ops := by
  simp only [t71, h71, Ty.toHOL_function, t5_meaning, t70_meaning]

def t72 (_ops : Operations) : Ty := .function (t13 _ops) (t3 _ops)
def h72 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h3 ops)
theorem t72_meaning (ops : Operations) : (t72 ops).toHOL = h72 ops := by
  simp only [t72, h72, Ty.toHOL_function, t13_meaning, t3_meaning]

def t73 (_ops : Operations) : Ty := .function (t4 _ops) (t32 _ops)
def h73 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h32 ops)
theorem t73_meaning (ops : Operations) : (t73 ops).toHOL = h73 ops := by
  simp only [t73, h73, Ty.toHOL_function, t4_meaning, t32_meaning]

def t74 (_ops : Operations) : Ty := .function (t5 _ops) (t23 _ops)
def h74 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h23 ops)
theorem t74_meaning (ops : Operations) : (t74 ops).toHOL = h74 ops := by
  simp only [t74, h74, Ty.toHOL_function, t5_meaning, t23_meaning]

def t75 (_ops : Operations) : Ty := .function (t8 _ops) (t8 _ops)
def h75 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h8 ops)
theorem t75_meaning (ops : Operations) : (t75 ops).toHOL = h75 ops := by
  simp only [t75, h75, Ty.toHOL_function, t8_meaning]

def t76 (_ops : Operations) : Ty := .function (t8 _ops) (t75 _ops)
def h76 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h75 ops)
theorem t76_meaning (ops : Operations) : (t76 ops).toHOL = h76 ops := by
  simp only [t76, h76, Ty.toHOL_function, t8_meaning, t75_meaning]

def t77 (_ops : Operations) : Ty := .function (t13 _ops) (t5 _ops)
def h77 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h5 ops)
theorem t77_meaning (ops : Operations) : (t77 ops).toHOL = h77 ops := by
  simp only [t77, h77, Ty.toHOL_function, t13_meaning, t5_meaning]

def t78 (_ops : Operations) : Ty := .function (t8 _ops) (t34 _ops)
def h78 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h34 ops)
theorem t78_meaning (ops : Operations) : (t78 ops).toHOL = h78 ops := by
  simp only [t78, h78, Ty.toHOL_function, t8_meaning, t34_meaning]

def t79 (_ops : Operations) : Ty := .function (t4 _ops) (t78 _ops)
def h79 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h78 ops)
theorem t79_meaning (ops : Operations) : (t79 ops).toHOL = h79 ops := by
  simp only [t79, h79, Ty.toHOL_function, t4_meaning, t78_meaning]

def t80 (_ops : Operations) : Ty := .function (t1 _ops) (t79 _ops)
def h80 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h79 ops)
theorem t80_meaning (ops : Operations) : (t80 ops).toHOL = h80 ops := by
  simp only [t80, h80, Ty.toHOL_function, t1_meaning, t79_meaning]

def t81 (_ops : Operations) : Ty := .function (t8 _ops) (t78 _ops)
def h81 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h78 ops)
theorem t81_meaning (ops : Operations) : (t81 ops).toHOL = h81 ops := by
  simp only [t81, h81, Ty.toHOL_function, t8_meaning, t78_meaning]

def t82 (_ops : Operations) : Ty := .function (t8 _ops) (t81 _ops)
def h82 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h81 ops)
theorem t82_meaning (ops : Operations) : (t82 ops).toHOL = h82 ops := by
  simp only [t82, h82, Ty.toHOL_function, t8_meaning, t81_meaning]

def t83 (_ops : Operations) : Ty := .function (t4 _ops) (t82 _ops)
def h83 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h82 ops)
theorem t83_meaning (ops : Operations) : (t83 ops).toHOL = h83 ops := by
  simp only [t83, h83, Ty.toHOL_function, t4_meaning, t82_meaning]

def t84 (_ops : Operations) : Ty := .op _ops.o6 []
def h84 (ops : Operations) : HOL.Ty AtomicTy := (t84 ops).toHOL
theorem t84_meaning (ops : Operations) : (t84 ops).toHOL = h84 ops := rfl

def t85 (_ops : Operations) : Ty := .function (t84 _ops) (t24 _ops)
def h85 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h24 ops)
theorem t85_meaning (ops : Operations) : (t85 ops).toHOL = h85 ops := by
  simp only [t85, h85, Ty.toHOL_function, t84_meaning, t24_meaning]

def t86 (_ops : Operations) : Ty := .function (t5 _ops) (t85 _ops)
def h86 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h85 ops)
theorem t86_meaning (ops : Operations) : (t86 ops).toHOL = h86 ops := by
  simp only [t86, h86, Ty.toHOL_function, t5_meaning, t85_meaning]

def t87 (_ops : Operations) : Ty := .function (t8 _ops) (t86 _ops)
def h87 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h86 ops)
theorem t87_meaning (ops : Operations) : (t87 ops).toHOL = h87 ops := by
  simp only [t87, h87, Ty.toHOL_function, t8_meaning, t86_meaning]

def t88 (_ops : Operations) : Ty := .function (t4 _ops) (t87 _ops)
def h88 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h87 ops)
theorem t88_meaning (ops : Operations) : (t88 ops).toHOL = h88 ops := by
  simp only [t88, h88, Ty.toHOL_function, t4_meaning, t87_meaning]

def t89 (_ops : Operations) : Ty := .function (t3 _ops) (t84 _ops)
def h89 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h84 ops)
theorem t89_meaning (ops : Operations) : (t89 ops).toHOL = h89 ops := by
  simp only [t89, h89, Ty.toHOL_function, t3_meaning, t84_meaning]

def t90 (_ops : Operations) : Ty := .function (t5 _ops) (t77 _ops)
def h90 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h77 ops)
theorem t90_meaning (ops : Operations) : (t90 ops).toHOL = h90 ops := by
  simp only [t90, h90, Ty.toHOL_function, t5_meaning, t77_meaning]

def t91 (_ops : Operations) : Ty := .op _ops.o1 [(t84 _ops)]
def h91 (ops : Operations) : HOL.Ty AtomicTy := (t91 ops).toHOL
theorem t91_meaning (ops : Operations) : (t91 ops).toHOL = h91 ops := rfl

def t92 (_ops : Operations) : Ty := .function (t91 _ops) (t24 _ops)
def h92 (ops : Operations) : HOL.Ty AtomicTy := (h91 ops).arr (h24 ops)
theorem t92_meaning (ops : Operations) : (t92 ops).toHOL = h92 ops := by
  simp only [t92, h92, Ty.toHOL_function, t91_meaning, t24_meaning]

def t93 (_ops : Operations) : Ty := .function (t92 _ops) (t24 _ops)
def h93 (ops : Operations) : HOL.Ty AtomicTy := (h92 ops).arr (h24 ops)
theorem t93_meaning (ops : Operations) : (t93 ops).toHOL = h93 ops := by
  simp only [t93, h93, Ty.toHOL_function, t92_meaning, t24_meaning]

def t94 (_ops : Operations) : Ty := .function (t5 _ops) (t62 _ops)
def h94 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h62 ops)
theorem t94_meaning (ops : Operations) : (t94 ops).toHOL = h94 ops := by
  simp only [t94, h94, Ty.toHOL_function, t5_meaning, t62_meaning]

def t95 (_ops : Operations) : Ty := .function (t23 _ops) (t24 _ops)
def h95 (ops : Operations) : HOL.Ty AtomicTy := (h23 ops).arr (h24 ops)
theorem t95_meaning (ops : Operations) : (t95 ops).toHOL = h95 ops := by
  simp only [t95, h95, Ty.toHOL_function, t23_meaning, t24_meaning]

def t96 (_ops : Operations) : Ty := .function (t22 _ops) (t95 _ops)
def h96 (ops : Operations) : HOL.Ty AtomicTy := (h22 ops).arr (h95 ops)
theorem t96_meaning (ops : Operations) : (t96 ops).toHOL = h96 ops := by
  simp only [t96, h96, Ty.toHOL_function, t22_meaning, t95_meaning]

def t97 (_ops : Operations) : Ty := .op _ops.o4 [(t3 _ops), (t5 _ops)]
def h97 (ops : Operations) : HOL.Ty AtomicTy := (t97 ops).toHOL
theorem t97_meaning (ops : Operations) : (t97 ops).toHOL = h97 ops := rfl

def t98 (_ops : Operations) : Ty := .op _ops.o1 [(t97 _ops)]
def h98 (ops : Operations) : HOL.Ty AtomicTy := (t98 ops).toHOL
theorem t98_meaning (ops : Operations) : (t98 ops).toHOL = h98 ops := rfl

def t99 (_ops : Operations) : Ty := .op _ops.o7 [(t5 _ops)]
def h99 (ops : Operations) : HOL.Ty AtomicTy := (t99 ops).toHOL
theorem t99_meaning (ops : Operations) : (t99 ops).toHOL = h99 ops := rfl

def t100 (_ops : Operations) : Ty := .function (t3 _ops) (t99 _ops)
def h100 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h99 ops)
theorem t100_meaning (ops : Operations) : (t100 ops).toHOL = h100 ops := by
  simp only [t100, h100, Ty.toHOL_function, t3_meaning, t99_meaning]

def t101 (_ops : Operations) : Ty := .function (t98 _ops) (t100 _ops)
def h101 (ops : Operations) : HOL.Ty AtomicTy := (h98 ops).arr (h100 ops)
theorem t101_meaning (ops : Operations) : (t101 ops).toHOL = h101 ops := by
  simp only [t101, h101, Ty.toHOL_function, t98_meaning, t100_meaning]

def t102 (_ops : Operations) : Ty := .function (t1 _ops) (t98 _ops)
def h102 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h98 ops)
theorem t102_meaning (ops : Operations) : (t102 ops).toHOL = h102 ops := by
  simp only [t102, h102, Ty.toHOL_function, t1_meaning, t98_meaning]

def t103 (_ops : Operations) : Ty := .function (t5 _ops) (t99 _ops)
def h103 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h99 ops)
theorem t103_meaning (ops : Operations) : (t103 ops).toHOL = h103 ops := by
  simp only [t103, h103, Ty.toHOL_function, t5_meaning, t99_meaning]

def t104 (_ops : Operations) : Ty := .function (t13 _ops) (t92 _ops)
def h104 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h92 ops)
theorem t104_meaning (ops : Operations) : (t104 ops).toHOL = h104 ops := by
  simp only [t104, h104, Ty.toHOL_function, t13_meaning, t92_meaning]

def t105 (_ops : Operations) : Ty := .function (t86 _ops) (t104 _ops)
def h105 (ops : Operations) : HOL.Ty AtomicTy := (h86 ops).arr (h104 ops)
theorem t105_meaning (ops : Operations) : (t105 ops).toHOL = h105 ops := by
  simp only [t105, h105, Ty.toHOL_function, t86_meaning, t104_meaning]

def t106 (_ops : Operations) : Ty := .function (t91 _ops) (t84 _ops)
def h106 (ops : Operations) : HOL.Ty AtomicTy := (h91 ops).arr (h84 ops)
theorem t106_meaning (ops : Operations) : (t106 ops).toHOL = h106 ops := by
  simp only [t106, h106, Ty.toHOL_function, t91_meaning, t84_meaning]

def t107 (_ops : Operations) : Ty := .function (t3 _ops) (t106 _ops)
def h107 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h106 ops)
theorem t107_meaning (ops : Operations) : (t107 ops).toHOL = h107 ops := by
  simp only [t107, h107, Ty.toHOL_function, t3_meaning, t106_meaning]

def t108 (_ops : Operations) : Ty := .function (t85 _ops) (t24 _ops)
def h108 (ops : Operations) : HOL.Ty AtomicTy := (h85 ops).arr (h24 ops)
theorem t108_meaning (ops : Operations) : (t108 ops).toHOL = h108 ops := by
  simp only [t108, h108, Ty.toHOL_function, t85_meaning, t24_meaning]

def t109 (_ops : Operations) : Ty := .function (t5 _ops) (t74 _ops)
def h109 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h74 ops)
theorem t109_meaning (ops : Operations) : (t109 ops).toHOL = h109 ops := by
  simp only [t109, h109, Ty.toHOL_function, t5_meaning, t74_meaning]

def t110 (_ops : Operations) : Ty := .function (t11 _ops) (t11 _ops)
def h110 (ops : Operations) : HOL.Ty AtomicTy := (h11 ops).arr (h11 ops)
theorem t110_meaning (ops : Operations) : (t110 ops).toHOL = h110 ops := by
  simp only [t110, h110, Ty.toHOL_function, t11_meaning]

def t111 (_ops : Operations) : Ty := .function (t11 _ops) (t110 _ops)
def h111 (ops : Operations) : HOL.Ty AtomicTy := (h11 ops).arr (h110 ops)
theorem t111_meaning (ops : Operations) : (t111 ops).toHOL = h111 ops := by
  simp only [t111, h111, Ty.toHOL_function, t11_meaning, t110_meaning]

def t112 (_ops : Operations) : Ty := .function (t10 _ops) (t110 _ops)
def h112 (ops : Operations) : HOL.Ty AtomicTy := (h10 ops).arr (h110 ops)
theorem t112_meaning (ops : Operations) : (t112 ops).toHOL = h112 ops := by
  simp only [t112, h112, Ty.toHOL_function, t10_meaning, t110_meaning]

def t113 (_ops : Operations) : Ty := .function (t9 _ops) (t10 _ops)
def h113 (ops : Operations) : HOL.Ty AtomicTy := (h9 ops).arr (h10 ops)
theorem t113_meaning (ops : Operations) : (t113 ops).toHOL = h113 ops := by
  simp only [t113, h113, Ty.toHOL_function, t9_meaning, t10_meaning]

def t114 (_ops : Operations) : Ty := .function (t5 _ops) (t113 _ops)
def h114 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h113 ops)
theorem t114_meaning (ops : Operations) : (t114 ops).toHOL = h114 ops := by
  simp only [t114, h114, Ty.toHOL_function, t5_meaning, t113_meaning]

def t115 (_ops : Operations) : Ty := .function (t5 _ops) (t5 _ops)
def h115 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h5 ops)
theorem t115_meaning (ops : Operations) : (t115 ops).toHOL = h115 ops := by
  simp only [t115, h115, Ty.toHOL_function, t5_meaning]

def t116 (_ops : Operations) : Ty := .function (t7 _ops) (t9 _ops)
def h116 (ops : Operations) : HOL.Ty AtomicTy := (h7 ops).arr (h9 ops)
theorem t116_meaning (ops : Operations) : (t116 ops).toHOL = h116 ops := by
  simp only [t116, h116, Ty.toHOL_function, t7_meaning, t9_meaning]

def t117 (_ops : Operations) : Ty := .function (t5 _ops) (t116 _ops)
def h117 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h116 ops)
theorem t117_meaning (ops : Operations) : (t117 ops).toHOL = h117 ops := by
  simp only [t117, h117, Ty.toHOL_function, t5_meaning, t116_meaning]

def t118 (_ops : Operations) : Ty := .function (t6 _ops) (t7 _ops)
def h118 (ops : Operations) : HOL.Ty AtomicTy := (h6 ops).arr (h7 ops)
theorem t118_meaning (ops : Operations) : (t118 ops).toHOL = h118 ops := by
  simp only [t118, h118, Ty.toHOL_function, t6_meaning, t7_meaning]

def t119 (_ops : Operations) : Ty := .function (t5 _ops) (t118 _ops)
def h119 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h118 ops)
theorem t119_meaning (ops : Operations) : (t119 ops).toHOL = h119 ops := by
  simp only [t119, h119, Ty.toHOL_function, t5_meaning, t118_meaning]

def t120 (_ops : Operations) : Ty := .function (t5 _ops) (t6 _ops)
def h120 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h6 ops)
theorem t120_meaning (ops : Operations) : (t120 ops).toHOL = h120 ops := by
  simp only [t120, h120, Ty.toHOL_function, t5_meaning, t6_meaning]

def t121 (_ops : Operations) : Ty := .function (t5 _ops) (t120 _ops)
def h121 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h120 ops)
theorem t121_meaning (ops : Operations) : (t121 ops).toHOL = h121 ops := by
  simp only [t121, h121, Ty.toHOL_function, t5_meaning, t120_meaning]

def t122 (_ops : Operations) : Ty := .op _ops.o8 []
def h122 (ops : Operations) : HOL.Ty AtomicTy := (t122 ops).toHOL
theorem t122_meaning (ops : Operations) : (t122 ops).toHOL = h122 ops := rfl

def t123 (_ops : Operations) : Ty := .function (t122 _ops) (t24 _ops)
def h123 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h24 ops)
theorem t123_meaning (ops : Operations) : (t123 ops).toHOL = h123 ops := by
  simp only [t123, h123, Ty.toHOL_function, t122_meaning, t24_meaning]

def t124 (_ops : Operations) : Ty := .function (t5 _ops) (t123 _ops)
def h124 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h123 ops)
theorem t124_meaning (ops : Operations) : (t124 ops).toHOL = h124 ops := by
  simp only [t124, h124, Ty.toHOL_function, t5_meaning, t123_meaning]

def t125 (_ops : Operations) : Ty := .function (t8 _ops) (t124 _ops)
def h125 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h124 ops)
theorem t125_meaning (ops : Operations) : (t125 ops).toHOL = h125 ops := by
  simp only [t125, h125, Ty.toHOL_function, t8_meaning, t124_meaning]

def t126 (_ops : Operations) : Ty := .function (t8 _ops) (t125 _ops)
def h126 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h125 ops)
theorem t126_meaning (ops : Operations) : (t126 ops).toHOL = h126 ops := by
  simp only [t126, h126, Ty.toHOL_function, t8_meaning, t125_meaning]

def t127 (_ops : Operations) : Ty := .function (t4 _ops) (t126 _ops)
def h127 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h126 ops)
theorem t127_meaning (ops : Operations) : (t127 ops).toHOL = h127 ops := by
  simp only [t127, h127, Ty.toHOL_function, t4_meaning, t126_meaning]

def t128 (_ops : Operations) : Ty := .function (t84 _ops) (t122 _ops)
def h128 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h122 ops)
theorem t128_meaning (ops : Operations) : (t128 ops).toHOL = h128 ops := by
  simp only [t128, h128, Ty.toHOL_function, t84_meaning, t122_meaning]

def t129 (_ops : Operations) : Ty := .function (t3 _ops) (t128 _ops)
def h129 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h128 ops)
theorem t129_meaning (ops : Operations) : (t129 ops).toHOL = h129 ops := by
  simp only [t129, h129, Ty.toHOL_function, t3_meaning, t128_meaning]

def t130 (_ops : Operations) : Ty := .op _ops.o4 [(t84 _ops), (t84 _ops)]
def h130 (ops : Operations) : HOL.Ty AtomicTy := (t130 ops).toHOL
theorem t130_meaning (ops : Operations) : (t130 ops).toHOL = h130 ops := rfl

def t131 (_ops : Operations) : Ty := .op _ops.o1 [(t130 _ops)]
def h131 (ops : Operations) : HOL.Ty AtomicTy := (t131 ops).toHOL
theorem t131_meaning (ops : Operations) : (t131 ops).toHOL = h131 ops := rfl

def t132 (_ops : Operations) : Ty := .function (t131 _ops) (t24 _ops)
def h132 (ops : Operations) : HOL.Ty AtomicTy := (h131 ops).arr (h24 ops)
theorem t132_meaning (ops : Operations) : (t132 ops).toHOL = h132 ops := by
  simp only [t132, h132, Ty.toHOL_function, t131_meaning, t24_meaning]

def t133 (_ops : Operations) : Ty := .function (t132 _ops) (t24 _ops)
def h133 (ops : Operations) : HOL.Ty AtomicTy := (h132 ops).arr (h24 ops)
theorem t133_meaning (ops : Operations) : (t133 ops).toHOL = h133 ops := by
  simp only [t133, h133, Ty.toHOL_function, t132_meaning, t24_meaning]

def t134 (_ops : Operations) : Ty := .op _ops.o4 [(t3 _ops), (t84 _ops)]
def h134 (ops : Operations) : HOL.Ty AtomicTy := (t134 ops).toHOL
theorem t134_meaning (ops : Operations) : (t134 ops).toHOL = h134 ops := rfl

def t135 (_ops : Operations) : Ty := .op _ops.o1 [(t134 _ops)]
def h135 (ops : Operations) : HOL.Ty AtomicTy := (t135 ops).toHOL
theorem t135_meaning (ops : Operations) : (t135 ops).toHOL = h135 ops := rfl

def t136 (_ops : Operations) : Ty := .op _ops.o7 [(t84 _ops)]
def h136 (ops : Operations) : HOL.Ty AtomicTy := (t136 ops).toHOL
theorem t136_meaning (ops : Operations) : (t136 ops).toHOL = h136 ops := rfl

def t137 (_ops : Operations) : Ty := .function (t3 _ops) (t136 _ops)
def h137 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h136 ops)
theorem t137_meaning (ops : Operations) : (t137 ops).toHOL = h137 ops := by
  simp only [t137, h137, Ty.toHOL_function, t3_meaning, t136_meaning]

def t138 (_ops : Operations) : Ty := .function (t135 _ops) (t137 _ops)
def h138 (ops : Operations) : HOL.Ty AtomicTy := (h135 ops).arr (h137 ops)
theorem t138_meaning (ops : Operations) : (t138 ops).toHOL = h138 ops := by
  simp only [t138, h138, Ty.toHOL_function, t135_meaning, t137_meaning]

def t139 (_ops : Operations) : Ty := .function (t1 _ops) (t135 _ops)
def h139 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h135 ops)
theorem t139_meaning (ops : Operations) : (t139 ops).toHOL = h139 ops := by
  simp only [t139, h139, Ty.toHOL_function, t1_meaning, t135_meaning]

def t140 (_ops : Operations) : Ty := .function (t84 _ops) (t136 _ops)
def h140 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h136 ops)
theorem t140_meaning (ops : Operations) : (t140 ops).toHOL = h140 ops := by
  simp only [t140, h140, Ty.toHOL_function, t84_meaning, t136_meaning]

def t141 (_ops : Operations) : Ty := .function (t84 _ops) (t84 _ops)
def h141 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h84 ops)
theorem t141_meaning (ops : Operations) : (t141 ops).toHOL = h141 ops := by
  simp only [t141, h141, Ty.toHOL_function, t84_meaning]

def t142 (_ops : Operations) : Ty := .function (t131 _ops) (t141 _ops)
def h142 (ops : Operations) : HOL.Ty AtomicTy := (h131 ops).arr (h141 ops)
theorem t142_meaning (ops : Operations) : (t142 ops).toHOL = h142 ops := by
  simp only [t142, h142, Ty.toHOL_function, t131_meaning, t141_meaning]

def t143 (_ops : Operations) : Ty := .op _ops.o9 []
def h143 (ops : Operations) : HOL.Ty AtomicTy := (t143 ops).toHOL
theorem t143_meaning (ops : Operations) : (t143 ops).toHOL = h143 ops := rfl

def t144 (_ops : Operations) : Ty := .function (t143 _ops) (t24 _ops)
def h144 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h24 ops)
theorem t144_meaning (ops : Operations) : (t144 ops).toHOL = h144 ops := by
  simp only [t144, h144, Ty.toHOL_function, t143_meaning, t24_meaning]

def t145 (_ops : Operations) : Ty := .function (t144 _ops) (t24 _ops)
def h145 (ops : Operations) : HOL.Ty AtomicTy := (h144 ops).arr (h24 ops)
theorem t145_meaning (ops : Operations) : (t145 ops).toHOL = h145 ops := by
  simp only [t145, h145, Ty.toHOL_function, t144_meaning, t24_meaning]

def t146 (_ops : Operations) : Ty := .function (t5 _ops) (t144 _ops)
def h146 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h144 ops)
theorem t146_meaning (ops : Operations) : (t146 ops).toHOL = h146 ops := by
  simp only [t146, h146, Ty.toHOL_function, t5_meaning, t144_meaning]

def t147 (_ops : Operations) : Ty := .function (t11 _ops) (t146 _ops)
def h147 (ops : Operations) : HOL.Ty AtomicTy := (h11 ops).arr (h146 ops)
theorem t147_meaning (ops : Operations) : (t147 ops).toHOL = h147 ops := by
  simp only [t147, h147, Ty.toHOL_function, t11_meaning, t146_meaning]

def t148 (_ops : Operations) : Ty := .function (t8 _ops) (t147 _ops)
def h148 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h147 ops)
theorem t148_meaning (ops : Operations) : (t148 ops).toHOL = h148 ops := by
  simp only [t148, h148, Ty.toHOL_function, t8_meaning, t147_meaning]

def t149 (_ops : Operations) : Ty := .function (t4 _ops) (t148 _ops)
def h149 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h148 ops)
theorem t149_meaning (ops : Operations) : (t149 ops).toHOL = h149 ops := by
  simp only [t149, h149, Ty.toHOL_function, t4_meaning, t148_meaning]

def t150 (_ops : Operations) : Ty := .function (t143 _ops) (t84 _ops)
def h150 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h84 ops)
theorem t150_meaning (ops : Operations) : (t150 ops).toHOL = h150 ops := by
  simp only [t150, h150, Ty.toHOL_function, t143_meaning, t84_meaning]

def t151 (_ops : Operations) : Ty := .function (t84 _ops) (t141 _ops)
def h151 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h141 ops)
theorem t151_meaning (ops : Operations) : (t151 ops).toHOL = h151 ops := by
  simp only [t151, h151, Ty.toHOL_function, t84_meaning, t141_meaning]

def t152 (_ops : Operations) : Ty := .function (t122 _ops) (t122 _ops)
def h152 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h122 ops)
theorem t152_meaning (ops : Operations) : (t152 ops).toHOL = h152 ops := by
  simp only [t152, h152, Ty.toHOL_function, t122_meaning]

def t153 (_ops : Operations) : Ty := .function (t122 _ops) (t152 _ops)
def h153 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h152 ops)
theorem t153_meaning (ops : Operations) : (t153 ops).toHOL = h153 ops := by
  simp only [t153, h153, Ty.toHOL_function, t122_meaning, t152_meaning]

def t154 (_ops : Operations) : Ty := .function (t143 _ops) (t122 _ops)
def h154 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h122 ops)
theorem t154_meaning (ops : Operations) : (t154 ops).toHOL = h154 ops := by
  simp only [t154, h154, Ty.toHOL_function, t143_meaning, t122_meaning]

def t155 (_ops : Operations) : Ty := .function (t3 _ops) (t24 _ops)
def h155 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h24 ops)
theorem t155_meaning (ops : Operations) : (t155 ops).toHOL = h155 ops := by
  simp only [t155, h155, Ty.toHOL_function, t3_meaning, t24_meaning]

def t156 (_ops : Operations) : Ty := .function (t155 _ops) (t24 _ops)
def h156 (ops : Operations) : HOL.Ty AtomicTy := (h155 ops).arr (h24 ops)
theorem t156_meaning (ops : Operations) : (t156 ops).toHOL = h156 ops := by
  simp only [t156, h156, Ty.toHOL_function, t155_meaning, t24_meaning]

def t157 (_ops : Operations) : Ty := .function (t84 _ops) (t143 _ops)
def h157 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h143 ops)
theorem t157_meaning (ops : Operations) : (t157 ops).toHOL = h157 ops := by
  simp only [t157, h157, Ty.toHOL_function, t84_meaning, t143_meaning]

def t158 (_ops : Operations) : Ty := .function (t3 _ops) (t157 _ops)
def h158 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h157 ops)
theorem t158_meaning (ops : Operations) : (t158 ops).toHOL = h158 ops := by
  simp only [t158, h158, Ty.toHOL_function, t3_meaning, t157_meaning]

def t159 (_ops : Operations) : Ty := .function (t84 _ops) (t152 _ops)
def h159 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h152 ops)
theorem t159_meaning (ops : Operations) : (t159 ops).toHOL = h159 ops := by
  simp only [t159, h159, Ty.toHOL_function, t84_meaning, t152_meaning]

def t160 (_ops : Operations) : Ty := .function (t5 _ops) (t152 _ops)
def h160 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h152 ops)
theorem t160_meaning (ops : Operations) : (t160 ops).toHOL = h160 ops := by
  simp only [t160, h160, Ty.toHOL_function, t5_meaning, t152_meaning]

def t161 (_ops : Operations) : Ty := .function (t134 _ops) (t160 _ops)
def h161 (ops : Operations) : HOL.Ty AtomicTy := (h134 ops).arr (h160 ops)
theorem t161_meaning (ops : Operations) : (t161 ops).toHOL = h161 ops := by
  simp only [t161, h161, Ty.toHOL_function, t134_meaning, t160_meaning]

def t162 (_ops : Operations) : Ty := .function (t84 _ops) (t134 _ops)
def h162 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h134 ops)
theorem t162_meaning (ops : Operations) : (t162 ops).toHOL = h162 ops := by
  simp only [t162, h162, Ty.toHOL_function, t84_meaning, t134_meaning]

def t163 (_ops : Operations) : Ty := .function (t3 _ops) (t162 _ops)
def h163 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h162 ops)
theorem t163_meaning (ops : Operations) : (t163 ops).toHOL = h163 ops := by
  simp only [t163, h163, Ty.toHOL_function, t3_meaning, t162_meaning]

def t164 (_ops : Operations) : Ty := .function (t12 _ops) (t12 _ops)
def h164 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h12 ops)
theorem t164_meaning (ops : Operations) : (t164 ops).toHOL = h164 ops := by
  simp only [t164, h164, Ty.toHOL_function, t12_meaning]

def t165 (_ops : Operations) : Ty := .function (t12 _ops) (t164 _ops)
def h165 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h164 ops)
theorem t165_meaning (ops : Operations) : (t165 ops).toHOL = h165 ops := by
  simp only [t165, h165, Ty.toHOL_function, t12_meaning, t164_meaning]

def t166 (_ops : Operations) : Ty := .function (t6 _ops) (t164 _ops)
def h166 (ops : Operations) : HOL.Ty AtomicTy := (h6 ops).arr (h164 ops)
theorem t166_meaning (ops : Operations) : (t166 ops).toHOL = h166 ops := by
  simp only [t166, h166, Ty.toHOL_function, t6_meaning, t164_meaning]

def t167 (_ops : Operations) : Ty := .op _ops.o1 [(t122 _ops)]
def h167 (ops : Operations) : HOL.Ty AtomicTy := (t167 ops).toHOL
theorem t167_meaning (ops : Operations) : (t167 ops).toHOL = h167 ops := rfl

def t168 (_ops : Operations) : Ty := .function (t167 _ops) (t24 _ops)
def h168 (ops : Operations) : HOL.Ty AtomicTy := (h167 ops).arr (h24 ops)
theorem t168_meaning (ops : Operations) : (t168 ops).toHOL = h168 ops := by
  simp only [t168, h168, Ty.toHOL_function, t167_meaning, t24_meaning]

def t169 (_ops : Operations) : Ty := .function (t5 _ops) (t168 _ops)
def h169 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h168 ops)
theorem t169_meaning (ops : Operations) : (t169 ops).toHOL = h169 ops := by
  simp only [t169, h169, Ty.toHOL_function, t5_meaning, t168_meaning]

def t170 (_ops : Operations) : Ty := .function (t8 _ops) (t169 _ops)
def h170 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h169 ops)
theorem t170_meaning (ops : Operations) : (t170 ops).toHOL = h170 ops := by
  simp only [t170, h170, Ty.toHOL_function, t8_meaning, t169_meaning]

def t171 (_ops : Operations) : Ty := .function (t8 _ops) (t170 _ops)
def h171 (ops : Operations) : HOL.Ty AtomicTy := (h8 ops).arr (h170 ops)
theorem t171_meaning (ops : Operations) : (t171 ops).toHOL = h171 ops := by
  simp only [t171, h171, Ty.toHOL_function, t8_meaning, t170_meaning]

def t172 (_ops : Operations) : Ty := .function (t4 _ops) (t171 _ops)
def h172 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h171 ops)
theorem t172_meaning (ops : Operations) : (t172 ops).toHOL = h172 ops := by
  simp only [t172, h172, Ty.toHOL_function, t4_meaning, t171_meaning]

def t173 (_ops : Operations) : Ty := .function (t143 _ops) (t143 _ops)
def h173 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h143 ops)
theorem t173_meaning (ops : Operations) : (t173 ops).toHOL = h173 ops := by
  simp only [t173, h173, Ty.toHOL_function, t143_meaning]

def t174 (_ops : Operations) : Ty := .function (t143 _ops) (t173 _ops)
def h174 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h173 ops)
theorem t174_meaning (ops : Operations) : (t174 ops).toHOL = h174 ops := by
  simp only [t174, h174, Ty.toHOL_function, t143_meaning, t173_meaning]

def t175 (_ops : Operations) : Ty := .function (t168 _ops) (t24 _ops)
def h175 (ops : Operations) : HOL.Ty AtomicTy := (h168 ops).arr (h24 ops)
theorem t175_meaning (ops : Operations) : (t175 ops).toHOL = h175 ops := by
  simp only [t175, h175, Ty.toHOL_function, t168_meaning, t24_meaning]

def t176 (_ops : Operations) : Ty := .function (t123 _ops) (t24 _ops)
def h176 (ops : Operations) : HOL.Ty AtomicTy := (h123 ops).arr (h24 ops)
theorem t176_meaning (ops : Operations) : (t176 ops).toHOL = h176 ops := by
  simp only [t176, h176, Ty.toHOL_function, t123_meaning, t24_meaning]

def t177 (_ops : Operations) : Ty := .function (t6 _ops) (t5 _ops)
def h177 (ops : Operations) : HOL.Ty AtomicTy := (h6 ops).arr (h5 ops)
theorem t177_meaning (ops : Operations) : (t177 ops).toHOL = h177 ops := by
  simp only [t177, h177, Ty.toHOL_function, t6_meaning, t5_meaning]

def t178 (_ops : Operations) : Ty := .function (t12 _ops) (t6 _ops)
def h178 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h6 ops)
theorem t178_meaning (ops : Operations) : (t178 ops).toHOL = h178 ops := by
  simp only [t178, h178, Ty.toHOL_function, t12_meaning, t6_meaning]

def t179 (_ops : Operations) : Ty := .function (t5 _ops) (t178 _ops)
def h179 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h178 ops)
theorem t179_meaning (ops : Operations) : (t179 ops).toHOL = h179 ops := by
  simp only [t179, h179, Ty.toHOL_function, t5_meaning, t178_meaning]

def t180 (_ops : Operations) : Ty := .function (t3 _ops) (t3 _ops)
def h180 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h3 ops)
theorem t180_meaning (ops : Operations) : (t180 ops).toHOL = h180 ops := by
  simp only [t180, h180, Ty.toHOL_function, t3_meaning]

def t181 (_ops : Operations) : Ty := .function (t2 _ops) (t180 _ops)
def h181 (ops : Operations) : HOL.Ty AtomicTy := (h2 ops).arr (h180 ops)
theorem t181_meaning (ops : Operations) : (t181 ops).toHOL = h181 ops := by
  simp only [t181, h181, Ty.toHOL_function, t2_meaning, t180_meaning]

def t182 (_ops : Operations) : Ty := .function (t24 _ops) (t2 _ops)
def h182 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h2 ops)
theorem t182_meaning (ops : Operations) : (t182 ops).toHOL = h182 ops := by
  simp only [t182, h182, Ty.toHOL_function, t24_meaning, t2_meaning]

def t183 (_ops : Operations) : Ty := .function (t24 _ops) (t182 _ops)
def h183 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h182 ops)
theorem t183_meaning (ops : Operations) : (t183 ops).toHOL = h183 ops := by
  simp only [t183, h183, Ty.toHOL_function, t24_meaning, t182_meaning]

def t184 (_ops : Operations) : Ty := .function (t24 _ops) (t183 _ops)
def h184 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h183 ops)
theorem t184_meaning (ops : Operations) : (t184 ops).toHOL = h184 ops := by
  simp only [t184, h184, Ty.toHOL_function, t24_meaning, t183_meaning]

def t185 (_ops : Operations) : Ty := .function (t24 _ops) (t184 _ops)
def h185 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h184 ops)
theorem t185_meaning (ops : Operations) : (t185 ops).toHOL = h185 ops := by
  simp only [t185, h185, Ty.toHOL_function, t24_meaning, t184_meaning]

def t186 (_ops : Operations) : Ty := .function (t24 _ops) (t185 _ops)
def h186 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h185 ops)
theorem t186_meaning (ops : Operations) : (t186 ops).toHOL = h186 ops := by
  simp only [t186, h186, Ty.toHOL_function, t24_meaning, t185_meaning]

def t187 (_ops : Operations) : Ty := .function (t24 _ops) (t186 _ops)
def h187 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h186 ops)
theorem t187_meaning (ops : Operations) : (t187 ops).toHOL = h187 ops := by
  simp only [t187, h187, Ty.toHOL_function, t24_meaning, t186_meaning]

def t188 (_ops : Operations) : Ty := .function (t24 _ops) (t187 _ops)
def h188 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h187 ops)
theorem t188_meaning (ops : Operations) : (t188 ops).toHOL = h188 ops := by
  simp only [t188, h188, Ty.toHOL_function, t24_meaning, t187_meaning]

def t189 (_ops : Operations) : Ty := .function (t24 _ops) (t188 _ops)
def h189 (ops : Operations) : HOL.Ty AtomicTy := (h24 ops).arr (h188 ops)
theorem t189_meaning (ops : Operations) : (t189 ops).toHOL = h189 ops := by
  simp only [t189, h189, Ty.toHOL_function, t24_meaning, t188_meaning]

def t190 (_ops : Operations) : Ty := .function (t122 _ops) (t168 _ops)
def h190 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h168 ops)
theorem t190_meaning (ops : Operations) : (t190 ops).toHOL = h190 ops := by
  simp only [t190, h190, Ty.toHOL_function, t122_meaning, t168_meaning]

def t191 (_ops : Operations) : Ty := .function (t122 _ops) (t123 _ops)
def h191 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h123 ops)
theorem t191_meaning (ops : Operations) : (t191 ops).toHOL = h191 ops := by
  simp only [t191, h191, Ty.toHOL_function, t122_meaning, t123_meaning]

def t192 (_ops : Operations) : Ty := .function (t12 _ops) (t74 _ops)
def h192 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h74 ops)
theorem t192_meaning (ops : Operations) : (t192 ops).toHOL = h192 ops := by
  simp only [t192, h192, Ty.toHOL_function, t12_meaning, t74_meaning]

def t193 (_ops : Operations) : Ty := .function (t130 _ops) (t24 _ops)
def h193 (ops : Operations) : HOL.Ty AtomicTy := (h130 ops).arr (h24 ops)
theorem t193_meaning (ops : Operations) : (t193 ops).toHOL = h193 ops := by
  simp only [t193, h193, Ty.toHOL_function, t130_meaning, t24_meaning]

def t194 (_ops : Operations) : Ty := .function (t6 _ops) (t193 _ops)
def h194 (ops : Operations) : HOL.Ty AtomicTy := (h6 ops).arr (h193 ops)
theorem t194_meaning (ops : Operations) : (t194 ops).toHOL = h194 ops := by
  simp only [t194, h194, Ty.toHOL_function, t6_meaning, t193_meaning]

def t195 (_ops : Operations) : Ty := .function (t12 _ops) (t132 _ops)
def h195 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h132 ops)
theorem t195_meaning (ops : Operations) : (t195 ops).toHOL = h195 ops := by
  simp only [t195, h195, Ty.toHOL_function, t12_meaning, t132_meaning]

def t196 (_ops : Operations) : Ty := .function (t194 _ops) (t195 _ops)
def h196 (ops : Operations) : HOL.Ty AtomicTy := (h194 ops).arr (h195 ops)
theorem t196_meaning (ops : Operations) : (t196 ops).toHOL = h196 ops := by
  simp only [t196, h196, Ty.toHOL_function, t194_meaning, t195_meaning]

def t197 (_ops : Operations) : Ty := .function (t130 _ops) (t84 _ops)
def h197 (ops : Operations) : HOL.Ty AtomicTy := (h130 ops).arr (h84 ops)
theorem t197_meaning (ops : Operations) : (t197 ops).toHOL = h197 ops := by
  simp only [t197, h197, Ty.toHOL_function, t130_meaning, t84_meaning]

def t198 (_ops : Operations) : Ty := .function (t131 _ops) (t152 _ops)
def h198 (ops : Operations) : HOL.Ty AtomicTy := (h131 ops).arr (h152 ops)
theorem t198_meaning (ops : Operations) : (t198 ops).toHOL = h198 ops := by
  simp only [t198, h198, Ty.toHOL_function, t131_meaning, t152_meaning]

def t199 (_ops : Operations) : Ty := .op _ops.o4 [(t143 _ops), (t143 _ops)]
def h199 (ops : Operations) : HOL.Ty AtomicTy := (t199 ops).toHOL
theorem t199_meaning (ops : Operations) : (t199 ops).toHOL = h199 ops := rfl

def t200 (_ops : Operations) : Ty := .op _ops.o1 [(t199 _ops)]
def h200 (ops : Operations) : HOL.Ty AtomicTy := (t200 ops).toHOL
theorem t200_meaning (ops : Operations) : (t200 ops).toHOL = h200 ops := rfl

def t201 (_ops : Operations) : Ty := .function (t200 _ops) (t24 _ops)
def h201 (ops : Operations) : HOL.Ty AtomicTy := (h200 ops).arr (h24 ops)
theorem t201_meaning (ops : Operations) : (t201 ops).toHOL = h201 ops := by
  simp only [t201, h201, Ty.toHOL_function, t200_meaning, t24_meaning]

def t202 (_ops : Operations) : Ty := .function (t201 _ops) (t24 _ops)
def h202 (ops : Operations) : HOL.Ty AtomicTy := (h201 ops).arr (h24 ops)
theorem t202_meaning (ops : Operations) : (t202 ops).toHOL = h202 ops := by
  simp only [t202, h202, Ty.toHOL_function, t201_meaning, t24_meaning]

def t203 (_ops : Operations) : Ty := .function (t199 _ops) (t24 _ops)
def h203 (ops : Operations) : HOL.Ty AtomicTy := (h199 ops).arr (h24 ops)
theorem t203_meaning (ops : Operations) : (t203 ops).toHOL = h203 ops := by
  simp only [t203, h203, Ty.toHOL_function, t199_meaning, t24_meaning]

def t204 (_ops : Operations) : Ty := .function (t6 _ops) (t203 _ops)
def h204 (ops : Operations) : HOL.Ty AtomicTy := (h6 ops).arr (h203 ops)
theorem t204_meaning (ops : Operations) : (t204 ops).toHOL = h204 ops := by
  simp only [t204, h204, Ty.toHOL_function, t6_meaning, t203_meaning]

def t205 (_ops : Operations) : Ty := .function (t12 _ops) (t201 _ops)
def h205 (ops : Operations) : HOL.Ty AtomicTy := (h12 ops).arr (h201 ops)
theorem t205_meaning (ops : Operations) : (t205 ops).toHOL = h205 ops := by
  simp only [t205, h205, Ty.toHOL_function, t12_meaning, t201_meaning]

def t206 (_ops : Operations) : Ty := .function (t204 _ops) (t205 _ops)
def h206 (ops : Operations) : HOL.Ty AtomicTy := (h204 ops).arr (h205 ops)
theorem t206_meaning (ops : Operations) : (t206 ops).toHOL = h206 ops := by
  simp only [t206, h206, Ty.toHOL_function, t204_meaning, t205_meaning]

def t207 (_ops : Operations) : Ty := .function (t199 _ops) (t143 _ops)
def h207 (ops : Operations) : HOL.Ty AtomicTy := (h199 ops).arr (h143 ops)
theorem t207_meaning (ops : Operations) : (t207 ops).toHOL = h207 ops := by
  simp only [t207, h207, Ty.toHOL_function, t199_meaning, t143_meaning]

def t208 (_ops : Operations) : Ty := .function (t199 _ops) (t201 _ops)
def h208 (ops : Operations) : HOL.Ty AtomicTy := (h199 ops).arr (h201 ops)
theorem t208_meaning (ops : Operations) : (t208 ops).toHOL = h208 ops := by
  simp only [t208, h208, Ty.toHOL_function, t199_meaning, t201_meaning]

def t209 (_ops : Operations) : Ty := .function (t143 _ops) (t199 _ops)
def h209 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h199 ops)
theorem t209_meaning (ops : Operations) : (t209 ops).toHOL = h209 ops := by
  simp only [t209, h209, Ty.toHOL_function, t143_meaning, t199_meaning]

def t210 (_ops : Operations) : Ty := .function (t143 _ops) (t209 _ops)
def h210 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h209 ops)
theorem t210_meaning (ops : Operations) : (t210 ops).toHOL = h210 ops := by
  simp only [t210, h210, Ty.toHOL_function, t143_meaning, t209_meaning]

def t211 (_ops : Operations) : Ty := .op _ops.o4 [(t122 _ops), (t122 _ops)]
def h211 (ops : Operations) : HOL.Ty AtomicTy := (t211 ops).toHOL
theorem t211_meaning (ops : Operations) : (t211 ops).toHOL = h211 ops := rfl

def t212 (_ops : Operations) : Ty := .op _ops.o1 [(t211 _ops)]
def h212 (ops : Operations) : HOL.Ty AtomicTy := (t212 ops).toHOL
theorem t212_meaning (ops : Operations) : (t212 ops).toHOL = h212 ops := rfl

def t213 (_ops : Operations) : Ty := .function (t212 _ops) (t152 _ops)
def h213 (ops : Operations) : HOL.Ty AtomicTy := (h212 ops).arr (h152 ops)
theorem t213_meaning (ops : Operations) : (t213 ops).toHOL = h213 ops := by
  simp only [t213, h213, Ty.toHOL_function, t212_meaning, t152_meaning]

def t214 (_ops : Operations) : Ty := .function (t199 _ops) (t211 _ops)
def h214 (ops : Operations) : HOL.Ty AtomicTy := (h199 ops).arr (h211 ops)
theorem t214_meaning (ops : Operations) : (t214 ops).toHOL = h214 ops := by
  simp only [t214, h214, Ty.toHOL_function, t199_meaning, t211_meaning]

def t215 (_ops : Operations) : Ty := .function (t200 _ops) (t212 _ops)
def h215 (ops : Operations) : HOL.Ty AtomicTy := (h200 ops).arr (h212 ops)
theorem t215_meaning (ops : Operations) : (t215 ops).toHOL = h215 ops := by
  simp only [t215, h215, Ty.toHOL_function, t200_meaning, t212_meaning]

def t216 (_ops : Operations) : Ty := .function (t214 _ops) (t215 _ops)
def h216 (ops : Operations) : HOL.Ty AtomicTy := (h214 ops).arr (h215 ops)
theorem t216_meaning (ops : Operations) : (t216 ops).toHOL = h216 ops := by
  simp only [t216, h216, Ty.toHOL_function, t214_meaning, t215_meaning]

def t217 (_ops : Operations) : Ty := .function (t214 _ops) (t24 _ops)
def h217 (ops : Operations) : HOL.Ty AtomicTy := (h214 ops).arr (h24 ops)
theorem t217_meaning (ops : Operations) : (t217 ops).toHOL = h217 ops := by
  simp only [t217, h217, Ty.toHOL_function, t214_meaning, t24_meaning]

def t218 (_ops : Operations) : Ty := .function (t217 _ops) (t214 _ops)
def h218 (ops : Operations) : HOL.Ty AtomicTy := (h217 ops).arr (h214 ops)
theorem t218_meaning (ops : Operations) : (t218 ops).toHOL = h218 ops := by
  simp only [t218, h218, Ty.toHOL_function, t217_meaning, t214_meaning]

def t219 (_ops : Operations) : Ty := .function (t211 _ops) (t24 _ops)
def h219 (ops : Operations) : HOL.Ty AtomicTy := (h211 ops).arr (h24 ops)
theorem t219_meaning (ops : Operations) : (t219 ops).toHOL = h219 ops := by
  simp only [t219, h219, Ty.toHOL_function, t211_meaning, t24_meaning]

def t220 (_ops : Operations) : Ty := .function (t211 _ops) (t219 _ops)
def h220 (ops : Operations) : HOL.Ty AtomicTy := (h211 ops).arr (h219 ops)
theorem t220_meaning (ops : Operations) : (t220 ops).toHOL = h220 ops := by
  simp only [t220, h220, Ty.toHOL_function, t211_meaning, t219_meaning]

def t221 (_ops : Operations) : Ty := .function (t122 _ops) (t211 _ops)
def h221 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h211 ops)
theorem t221_meaning (ops : Operations) : (t221 ops).toHOL = h221 ops := by
  simp only [t221, h221, Ty.toHOL_function, t122_meaning, t211_meaning]

def t222 (_ops : Operations) : Ty := .function (t122 _ops) (t221 _ops)
def h222 (ops : Operations) : HOL.Ty AtomicTy := (h122 ops).arr (h221 ops)
theorem t222_meaning (ops : Operations) : (t222 ops).toHOL = h222 ops := by
  simp only [t222, h222, Ty.toHOL_function, t122_meaning, t221_meaning]

def t223 (_ops : Operations) : Ty := .op _ops.o1 [(t143 _ops)]
def h223 (ops : Operations) : HOL.Ty AtomicTy := (t223 ops).toHOL
theorem t223_meaning (ops : Operations) : (t223 ops).toHOL = h223 ops := rfl

def t224 (_ops : Operations) : Ty := .function (t223 _ops) (t24 _ops)
def h224 (ops : Operations) : HOL.Ty AtomicTy := (h223 ops).arr (h24 ops)
theorem t224_meaning (ops : Operations) : (t224 ops).toHOL = h224 ops := by
  simp only [t224, h224, Ty.toHOL_function, t223_meaning, t24_meaning]

def t225 (_ops : Operations) : Ty := .function (t224 _ops) (t24 _ops)
def h225 (ops : Operations) : HOL.Ty AtomicTy := (h224 ops).arr (h24 ops)
theorem t225_meaning (ops : Operations) : (t225 ops).toHOL = h225 ops := by
  simp only [t225, h225, Ty.toHOL_function, t224_meaning, t24_meaning]

def t226 (_ops : Operations) : Ty := .function (t13 _ops) (t74 _ops)
def h226 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h74 ops)
theorem t226_meaning (ops : Operations) : (t226 ops).toHOL = h226 ops := by
  simp only [t226, h226, Ty.toHOL_function, t13_meaning, t74_meaning]

def t227 (_ops : Operations) : Ty := .function (t5 _ops) (t226 _ops)
def h227 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h226 ops)
theorem t227_meaning (ops : Operations) : (t227 ops).toHOL = h227 ops := by
  simp only [t227, h227, Ty.toHOL_function, t5_meaning, t226_meaning]

def t228 (_ops : Operations) : Ty := .function (t13 _ops) (t224 _ops)
def h228 (ops : Operations) : HOL.Ty AtomicTy := (h13 ops).arr (h224 ops)
theorem t228_meaning (ops : Operations) : (t228 ops).toHOL = h228 ops := by
  simp only [t228, h228, Ty.toHOL_function, t13_meaning, t224_meaning]

def t229 (_ops : Operations) : Ty := .function (t146 _ops) (t228 _ops)
def h229 (ops : Operations) : HOL.Ty AtomicTy := (h146 ops).arr (h228 ops)
theorem t229_meaning (ops : Operations) : (t229 ops).toHOL = h229 ops := by
  simp only [t229, h229, Ty.toHOL_function, t146_meaning, t228_meaning]

def t230 (_ops : Operations) : Ty := .function (t144 _ops) (t224 _ops)
def h230 (ops : Operations) : HOL.Ty AtomicTy := (h144 ops).arr (h224 ops)
theorem t230_meaning (ops : Operations) : (t230 ops).toHOL = h230 ops := by
  simp only [t230, h230, Ty.toHOL_function, t144_meaning, t224_meaning]

def t231 (_ops : Operations) : Ty := .function (t223 _ops) (t167 _ops)
def h231 (ops : Operations) : HOL.Ty AtomicTy := (h223 ops).arr (h167 ops)
theorem t231_meaning (ops : Operations) : (t231 ops).toHOL = h231 ops := by
  simp only [t231, h231, Ty.toHOL_function, t223_meaning, t167_meaning]

def t232 (_ops : Operations) : Ty := .function (t154 _ops) (t231 _ops)
def h232 (ops : Operations) : HOL.Ty AtomicTy := (h154 ops).arr (h231 ops)
theorem t232_meaning (ops : Operations) : (t232 ops).toHOL = h232 ops := by
  simp only [t232, h232, Ty.toHOL_function, t154_meaning, t231_meaning]

def t233 (_ops : Operations) : Ty := .function (t5 _ops) (t115 _ops)
def h233 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h115 ops)
theorem t233_meaning (ops : Operations) : (t233 ops).toHOL = h233 ops := by
  simp only [t233, h233, Ty.toHOL_function, t5_meaning, t115_meaning]

def t234 (_ops : Operations) : Ty := .function (t1 _ops) (t1 _ops)
def h234 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h1 ops)
theorem t234_meaning (ops : Operations) : (t234 ops).toHOL = h234 ops := by
  simp only [t234, h234, Ty.toHOL_function, t1_meaning]

def t235 (_ops : Operations) : Ty := .function (t0 _ops) (t234 _ops)
def h235 (ops : Operations) : HOL.Ty AtomicTy := (h0 ops).arr (h234 ops)
theorem t235_meaning (ops : Operations) : (t235 ops).toHOL = h235 ops := by
  simp only [t235, h235, Ty.toHOL_function, t0_meaning, t234_meaning]

def t236 (_ops : Operations) : Ty := .function (t5 _ops) (t0 _ops)
def h236 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h0 ops)
theorem t236_meaning (ops : Operations) : (t236 ops).toHOL = h236 ops := by
  simp only [t236, h236, Ty.toHOL_function, t5_meaning, t0_meaning]

def t237 (_ops : Operations) : Ty := .function (t3 _ops) (t236 _ops)
def h237 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h236 ops)
theorem t237_meaning (ops : Operations) : (t237 ops).toHOL = h237 ops := by
  simp only [t237, h237, Ty.toHOL_function, t3_meaning, t236_meaning]

def t238 (_ops : Operations) : Ty := .function (t84 _ops) (t0 _ops)
def h238 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h0 ops)
theorem t238_meaning (ops : Operations) : (t238 ops).toHOL = h238 ops := by
  simp only [t238, h238, Ty.toHOL_function, t84_meaning, t0_meaning]

def t239 (_ops : Operations) : Ty := .function (t3 _ops) (t238 _ops)
def h239 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h238 ops)
theorem t239_meaning (ops : Operations) : (t239 ops).toHOL = h239 ops := by
  simp only [t239, h239, Ty.toHOL_function, t3_meaning, t238_meaning]

def t240 (_ops : Operations) : Ty := .function (t143 _ops) (t0 _ops)
def h240 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h0 ops)
theorem t240_meaning (ops : Operations) : (t240 ops).toHOL = h240 ops := by
  simp only [t240, h240, Ty.toHOL_function, t143_meaning, t0_meaning]

def t241 (_ops : Operations) : Ty := .function (t1 _ops) (t144 _ops)
def h241 (ops : Operations) : HOL.Ty AtomicTy := (h1 ops).arr (h144 ops)
theorem t241_meaning (ops : Operations) : (t241 ops).toHOL = h241 ops := by
  simp only [t241, h241, Ty.toHOL_function, t1_meaning, t144_meaning]

def t242 (_ops : Operations) : Ty := .function (t5 _ops) (t241 _ops)
def h242 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h241 ops)
theorem t242_meaning (ops : Operations) : (t242 ops).toHOL = h242 ops := by
  simp only [t242, h242, Ty.toHOL_function, t5_meaning, t241_meaning]

def t243 (_ops : Operations) : Ty := .op _ops.o4 [(t3 _ops), (t143 _ops)]
def h243 (ops : Operations) : HOL.Ty AtomicTy := (t243 ops).toHOL
theorem t243_meaning (ops : Operations) : (t243 ops).toHOL = h243 ops := rfl

def t244 (_ops : Operations) : Ty := .op _ops.o1 [(t243 _ops)]
def h244 (ops : Operations) : HOL.Ty AtomicTy := (t244 ops).toHOL
theorem t244_meaning (ops : Operations) : (t244 ops).toHOL = h244 ops := rfl

def t245 (_ops : Operations) : Ty := .function (t244 _ops) (t240 _ops)
def h245 (ops : Operations) : HOL.Ty AtomicTy := (h244 ops).arr (h240 ops)
theorem t245_meaning (ops : Operations) : (t245 ops).toHOL = h245 ops := by
  simp only [t245, h245, Ty.toHOL_function, t244_meaning, t240_meaning]

def t246 (_ops : Operations) : Ty := .function (t244 _ops) (t244 _ops)
def h246 (ops : Operations) : HOL.Ty AtomicTy := (h244 ops).arr (h244 ops)
theorem t246_meaning (ops : Operations) : (t246 ops).toHOL = h246 ops := by
  simp only [t246, h246, Ty.toHOL_function, t244_meaning]

def t247 (_ops : Operations) : Ty := .function (t243 _ops) (t246 _ops)
def h247 (ops : Operations) : HOL.Ty AtomicTy := (h243 ops).arr (h246 ops)
theorem t247_meaning (ops : Operations) : (t247 ops).toHOL = h247 ops := by
  simp only [t247, h247, Ty.toHOL_function, t243_meaning, t246_meaning]

def t248 (_ops : Operations) : Ty := .function (t143 _ops) (t243 _ops)
def h248 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h243 ops)
theorem t248_meaning (ops : Operations) : (t248 ops).toHOL = h248 ops := by
  simp only [t248, h248, Ty.toHOL_function, t143_meaning, t243_meaning]

def t249 (_ops : Operations) : Ty := .function (t3 _ops) (t248 _ops)
def h249 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h248 ops)
theorem t249_meaning (ops : Operations) : (t249 ops).toHOL = h249 ops := by
  simp only [t249, h249, Ty.toHOL_function, t3_meaning, t248_meaning]

def t250 (_ops : Operations) : Ty := .function (t3 _ops) (t32 _ops)
def h250 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h32 ops)
theorem t250_meaning (ops : Operations) : (t250 ops).toHOL = h250 ops := by
  simp only [t250, h250, Ty.toHOL_function, t3_meaning, t32_meaning]

def t251 (_ops : Operations) : Ty := .function (t143 _ops) (t4 _ops)
def h251 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h4 ops)
theorem t251_meaning (ops : Operations) : (t251 ops).toHOL = h251 ops := by
  simp only [t251, h251, Ty.toHOL_function, t143_meaning, t4_meaning]

def t252 (_ops : Operations) : Ty := .function (t84 _ops) (t4 _ops)
def h252 (ops : Operations) : HOL.Ty AtomicTy := (h84 ops).arr (h4 ops)
theorem t252_meaning (ops : Operations) : (t252 ops).toHOL = h252 ops := by
  simp only [t252, h252, Ty.toHOL_function, t84_meaning, t4_meaning]

def t253 (_ops : Operations) : Ty := .function (t5 _ops) (t109 _ops)
def h253 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h109 ops)
theorem t253_meaning (ops : Operations) : (t253 ops).toHOL = h253 ops := by
  simp only [t253, h253, Ty.toHOL_function, t5_meaning, t109_meaning]

def t254 (_ops : Operations) : Ty := .function (t5 _ops) (t253 _ops)
def h254 (ops : Operations) : HOL.Ty AtomicTy := (h5 ops).arr (h253 ops)
theorem t254_meaning (ops : Operations) : (t254 ops).toHOL = h254 ops := by
  simp only [t254, h254, Ty.toHOL_function, t5_meaning, t253_meaning]

def t255 (_ops : Operations) : Ty := .function (t3 _ops) (t0 _ops)
def h255 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h0 ops)
theorem t255_meaning (ops : Operations) : (t255 ops).toHOL = h255 ops := by
  simp only [t255, h255, Ty.toHOL_function, t3_meaning, t0_meaning]

def t256 (_ops : Operations) : Ty := .function (t3 _ops) (t255 _ops)
def h256 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h255 ops)
theorem t256_meaning (ops : Operations) : (t256 ops).toHOL = h256 ops := by
  simp only [t256, h256, Ty.toHOL_function, t3_meaning, t255_meaning]

def t257 (_ops : Operations) : Ty := .function (t143 _ops) (t256 _ops)
def h257 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h256 ops)
theorem t257_meaning (ops : Operations) : (t257 ops).toHOL = h257 ops := by
  simp only [t257, h257, Ty.toHOL_function, t143_meaning, t256_meaning]

def t258 (_ops : Operations) : Ty := .function (t3 _ops) (t257 _ops)
def h258 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h257 ops)
theorem t258_meaning (ops : Operations) : (t258 ops).toHOL = h258 ops := by
  simp only [t258, h258, Ty.toHOL_function, t3_meaning, t257_meaning]

def t259 (_ops : Operations) : Ty := .function (t4 _ops) (t143 _ops)
def h259 (ops : Operations) : HOL.Ty AtomicTy := (h4 ops).arr (h143 ops)
theorem t259_meaning (ops : Operations) : (t259 ops).toHOL = h259 ops := by
  simp only [t259, h259, Ty.toHOL_function, t4_meaning, t143_meaning]

def t260 (_ops : Operations) : Ty := .function (t143 _ops) (t259 _ops)
def h260 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h259 ops)
theorem t260_meaning (ops : Operations) : (t260 ops).toHOL = h260 ops := by
  simp only [t260, h260, Ty.toHOL_function, t143_meaning, t259_meaning]

def t261 (_ops : Operations) : Ty := .function (t3 _ops) (t260 _ops)
def h261 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h260 ops)
theorem t261_meaning (ops : Operations) : (t261 ops).toHOL = h261 ops := by
  simp only [t261, h261, Ty.toHOL_function, t3_meaning, t260_meaning]

def t262 (_ops : Operations) : Ty := .function (t3 _ops) (t261 _ops)
def h262 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h261 ops)
theorem t262_meaning (ops : Operations) : (t262 ops).toHOL = h262 ops := by
  simp only [t262, h262, Ty.toHOL_function, t3_meaning, t261_meaning]

def t263 (_ops : Operations) : Ty := .function (t3 _ops) (t262 _ops)
def h263 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h262 ops)
theorem t263_meaning (ops : Operations) : (t263 ops).toHOL = h263 ops := by
  simp only [t263, h263, Ty.toHOL_function, t3_meaning, t262_meaning]

def t264 (_ops : Operations) : Ty := .function (t143 _ops) (t260 _ops)
def h264 (ops : Operations) : HOL.Ty AtomicTy := (h143 ops).arr (h260 ops)
theorem t264_meaning (ops : Operations) : (t264 ops).toHOL = h264 ops := by
  simp only [t264, h264, Ty.toHOL_function, t143_meaning, t260_meaning]

def t265 (_ops : Operations) : Ty := .function (t3 _ops) (t264 _ops)
def h265 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h264 ops)
theorem t265_meaning (ops : Operations) : (t265 ops).toHOL = h265 ops := by
  simp only [t265, h265, Ty.toHOL_function, t3_meaning, t264_meaning]

def t266 (_ops : Operations) : Ty := .function (t3 _ops) (t265 _ops)
def h266 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h265 ops)
theorem t266_meaning (ops : Operations) : (t266 ops).toHOL = h266 ops := by
  simp only [t266, h266, Ty.toHOL_function, t3_meaning, t265_meaning]

def t267 (_ops : Operations) : Ty := .function (t3 _ops) (t266 _ops)
def h267 (ops : Operations) : HOL.Ty AtomicTy := (h3 ops).arr (h266 ops)
theorem t267_meaning (ops : Operations) : (t267 ops).toHOL = h267 ops := by
  simp only [t267, h267, Ty.toHOL_function, t3_meaning, t266_meaning]

def signature (ops : Operations) : Signature := {
  state := h22 ops
  record := h23 ops
  step := (.const (.constant ops.c0 (t27 ops) (t27_meaning ops)))
  disjunction := (.const (.constant ops.c1 (t29 ops) (t29_meaning ops)))
}

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseData
