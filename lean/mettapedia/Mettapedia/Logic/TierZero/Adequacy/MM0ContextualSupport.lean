import Mettapedia.Languages.MM0.Kernel.Support
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

/-!
# MM0 occurrence dependencies as native contextual support

Bound MM0 variables are actual ABT indices. A regular variable is an opaque
guest symbol applied to its declared dependency indices. Consequently the
native thinning records exactly MM0's independent `HasVar` judgment, including
occurrences in bound argument slots. This is occurrence support, not MM0's
separate binder-sensitive free-variable analysis.

The encoding is injective, and the native support check is exact. Sorting,
admissible theorem substitution and full proof adequacy are separate judgments.
This module does not depend on the Kernel2 checker or its representation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- Guest symbols carried by the existing general ABT representation. -/
inductive Head where
  | constant (index : Nat)
  | regular (index : Nat)
  | undeclared (index : Nat)
  | application
  | judgment (name : String)
  deriving DecidableEq, Repr

def dependencyFields : List Nat → Fields Head
  | [] => .nil
  | index :: rest => .cons 0 (.idx index) (dependencyFields rest)

def encodeVariable (context : Context) (index : Nat) : Term Head :=
  match context[index]? with
  | some (.bound _) => .idx index
  | some (.regular _ dependencies) =>
      .node (.regular index) (dependencyFields (dependencies.sort (· ≤ ·)))
  | none => .node (.undeclared index) .nil

def encode (context : Context) : Preterm → Term Head
  | .var index => encodeVariable context index
  | .term symbol => .node (.constant symbol) .nil
  | .app f a => .node .application (.cons 0 (encode context f) (.cons 0 (encode context a) .nil))

def decode : Term Head → Option Preterm
  | .idx index => some (.var index)
  | .node (.regular index) _ => some (.var index)
  | .node (.undeclared index) _ => some (.var index)
  | .node (.constant symbol) .nil => some (.term symbol)
  | .node .application (.cons 0 f (.cons 0 a .nil)) => do
      let function ← decode f
      let argument ← decode a
      some (.app function argument)
  | _ => none

theorem decode_encode (context : Context) : ∀ expression : Preterm,
    decode (encode context expression) = some expression
  | .var index => by
    simp only [encode, encodeVariable]
    cases context[index]? with
    | none => rfl
    | some binder => cases binder <;> rfl
  | .term symbol => rfl
  | .app f a => by simp [encode, decode, decode_encode context f, decode_encode context a]

theorem encode_injective (context : Context) : Function.Injective (encode context) := by
  intro a b same
  have decoded := congrArg decode same
  simpa [decode_encode] using decoded

theorem dependencies_free (indices : List Nat) (index : Nat) :
    fieldsFreeAt (dependencyFields indices) index = true ↔ index ∈ indices := by
  induction indices with
  | nil => simp [dependencyFields]
  | cons i rest ih =>
    simp only [dependencyFields, fieldsFreeAt_cons, Nat.add_zero, freeAt_idx,
      Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

/-- Native ABT support equals the independently computed MM0 occurrence support. -/
theorem support_exact {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support) (index : Nat) :
    freeAt (encode context expression) index = true ↔ index ∈ support := by
  induction supported with
  | @bound i sort lookup =>
    simp [encode, encodeVariable, lookup, eq_comm]
  | @regular i sort dependencies lookup =>
    simp only [encode, encodeVariable, lookup, freeAt_node]
    rw [dependencies_free]
    simp
  | term symbol => simp [encode]
  | app function argument ihFunction ihArgument =>
    simp [encode, fieldsFreeAt_cons, ihFunction, ihArgument]

theorem hasVar_exact {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support) (index : Nat) :
    freeAt (encode context expression) index = true ↔ Preterm.HasVar context index expression :=
  (support_exact supported index).trans (supported.mem_iff_hasVar index)

/-- The shared store's actual support bits represent the MM0 judgment. -/
theorem reference_hasVar {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support)
    (store : Store Head) (canonical : Canonical store) (index : Nat) :
    Thin.bit (encodeR store (encode context expression)).2.thin index = true ↔
      Preterm.HasVar context index expression := by
  have encoded := encodeR_spec store canonical (encode context expression)
  rw [← freeAt_unfold encoded.2.1 encoded.2.2.1, encodeR_unfold canonical]
  exact hasVar_exact supported index

/-- The executable native check admits exactly the MM0 dependencies permitted by the mask. -/
theorem support_check_exact {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support)
    (store : Store Head) (canonical : Canonical store) (allowed : Thin) :
    ContextualMatching.subCheck (encodeR store (encode context expression)).2.thin allowed = true ↔
      ∀ index, Preterm.HasVar context index expression → Thin.bit allowed index = true := by
  rw [ContextualMatching.subCheck_iff]
  unfold Thin.Sub
  apply forall_congr'
  intro index
  rw [reference_hasVar supported store canonical index]

namespace Controls

def independentContext : Context := [.bound 0, .bound 0, .regular 0 {1}]
def dependentContext : Context := [.bound 0, .bound 0, .regular 0 {0}]

/-- Excluding formal `x` still permits the other ambient variable `y`. -/
theorem ambient_dependency_retained :
    ContextualMatching.subCheck (encodeR [] (encode independentContext (.var 2))).2.thin
      [false, true] = true := by
  simp only [encode, encodeVariable, independentContext, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Finset.sort_singleton]
  decide

theorem forbidden_dependency_refused :
    ContextualMatching.subCheck (encodeR [] (encode dependentContext (.var 2))).2.thin
      [false, true] = false := by
  simp only [encode, encodeVariable, dependentContext, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Finset.sort_singleton]
  decide

theorem bound_argument_occurrence_retained :
    freeAt (encode independentContext (.app (.term 0) (.var 0))) 0 = true := by decide

end Controls
end Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport
