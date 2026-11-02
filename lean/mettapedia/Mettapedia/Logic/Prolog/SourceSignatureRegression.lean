import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.LP.RuntimeReadback

/-!
# Concrete Prolog source-signature canaries

These checks pin the representation choices that a source reader and the
canonical LP runtime must share.
-/

namespace Mettapedia.Logic.Prolog.SourceSignatureRegression

open SourceSignature

-- Prolog name/arity identity distinguishes `p/0` from `p/1`.
#guard decide (
  (predicate "p" []).symbol ≠
    (predicate "p" [atom "a"]).symbol)

-- Anonymous variables with distinct reader-assigned occurrences do not
-- alias before activation-scoped standardization apart.
#guard decide (
  ({ spelling := "_", occurrence := 0 } : Variable) ≠
    { spelling := "_", occurrence := 1 })

-- Bit-level float payloads retain the distinction between positive and
-- negative zero instead of collapsing them through host numeric equality.
#guard decide (
  (Constant.floatBits 0x0000000000000000) ≠
    Constant.floatBits 0x8000000000000000)

theorem cons_has_swi_list_indicator (head tail : Term) :
    match cons head tail with
    | .app indicator _ => indicator.name = "[|]" ∧ indicator.arity = 2
    | _ => False := by
  simp [cons, ListEncoding.cons, swiLists, compound]

theorem atom_and_zero_arity_compound_are_distinct (name : String) :
    atom name ≠ compound name [] :=
  atom_ne_zero_arity_compound name

theorem nil_is_distinct_constant : nil = .const .nil := rfl

theorem singleton_list_exact (element : Term) :
    list [element] = cons element nil := rfl

/-- The concrete source signature is not a detached reader AST: a source
goal executes directly in the canonical LP heap and typed Prolog session. -/
def concreteSignatureRunsCanonicalQuery : Bool :=
  let query : SourceSignature.Goal := .unify (var "X" 0) (atom "a")
  match RuntimeControl.openEmpty ([] : SourceSignature.Program) query with
  | .error _ => false
  | .ok session =>
      match RuntimeControl.pullSession 64 session with
      | .answer answer resumed =>
          match answer.queryVarMap with
          | [(_, address)] =>
              match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address,
                  RuntimeControl.pullSession 64 resumed with
              | .ok (.const (.atom "a")),
                  .terminal (.completed memory) _ =>
                    memory.heap.isEmpty && memory.trail.isEmpty
              | _, _ => false
          | _ => false
      | _ => false

#guard concreteSignatureRunsCanonicalQuery

end Mettapedia.Logic.Prolog.SourceSignatureRegression
