import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldSchema

/-! Reconstruction of the source case formula from its typed field schema. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldSchema

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData

def pack (ops : Operations) {context : HOL.Ctx AtomicTy}
    (fields : (field : Field) → HOL.Term Symbol context (field.type ops)) :
    HOL.Term Symbol context (signature ops).state :=
  (.app (.app (.const (.constant ops.c4 (t45 ops) (t45_meaning ops))) (fields .context)) (.app (.app (.const (.constant ops.c4 (t47 ops) (t47_meaning ops))) (fields .names)) (.app (.app (.const (.constant ops.c4 (t49 ops) (t49_meaning ops))) (fields .typeRows)) (.app (.app (.const (.constant ops.c4 (t51 ops) (t51_meaning ops))) (fields .termRows)) (.app (.app (.const (.constant ops.c4 (t53 ops) (t53_meaning ops))) (fields .dbRows)) (.app (.app (.const (.constant ops.c4 (t55 ops) (t55_meaning ops))) (fields .theoremRows)) (.app (.app (.const (.constant ops.c4 (t57 ops) (t57_meaning ops))) (fields .nameMap)) (.app (.app (.const (.constant ops.c4 (t59 ops) (t59_meaning ops))) (fields .typeMap)) (.app (.app (.const (.constant ops.c4 (t61 ops) (t61_meaning ops))) (fields .drops)) (fields .policy))))))))))

def appendRightVar {context tail : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy} :
    HOL.Var context type → HOL.Var (context ++ tail) type
  | .vz => .vz
  | .vs previous => .vs (appendRightVar previous)

def prependVar (front : HOL.Ctx AtomicTy) {tail : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (entry : HOL.Var tail type) : HOL.Var (front ++ tail) type :=
  match front with
  | [] => entry
  | _ :: rest => .vs (prependVar rest entry)

def conjunction (ops : Operations) {context : HOL.Ctx AtomicTy}
    (left right : HOL.Formula Symbol context) : HOL.Formula Symbol context :=
  .app (.app (.const (.constant ops.c3 (.function Ty.bool (.function Ty.bool Ty.bool))
    (by simp only [Ty.toHOL_function, Ty.toHOL_bool]))) left) right

def existsOne (ops : Operations) (type : Ty) {context : HOL.Ctx AtomicTy}
    (body : HOL.Formula Symbol (type.toHOL :: context)) : HOL.Formula Symbol context :=
  .app (.const (.constant ops.c2 (.function (.function type Ty.bool) Ty.bool)
    (by simp only [Ty.toHOL_function, Ty.toHOL_bool]))) (.lam body)

def existsMany (ops : Operations) (locals : List Ty) {context : HOL.Ctx AtomicTy} :
    HOL.Formula Symbol (locals.map Ty.toHOL ++ context) → HOL.Formula Symbol context :=
  match locals with
  | [] => fun body => body
  | first :: rest => fun body => existsMany ops rest (existsOne ops first body)

def Syntax.sourceClause {ops : Operations} (spec : Syntax ops) : (signature ops).Clause :=
  existsMany ops spec.locals
    (conjunction ops
      (.eq (.var (prependVar (spec.locals.map Ty.toHOL) (.vs (.vs .vz))))
        (HOL.rename appendRightVar (pack ops spec.before)))
      (conjunction ops
        (.eq (.var (prependVar (spec.locals.map Ty.toHOL) (.vs .vz)))
          (HOL.rename appendRightVar spec.record))
        (conjunction ops
          (.eq (.var (prependVar (spec.locals.map Ty.toHOL) .vz))
            (HOL.rename appendRightVar (pack ops spec.after)))
          (HOL.rename appendRightVar spec.guard))))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldSchema
