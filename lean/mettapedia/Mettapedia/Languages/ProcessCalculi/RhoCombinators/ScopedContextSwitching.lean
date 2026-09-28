import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton
import Mettapedia.GSLT.Dynamics.ContextIndexedSwitching

/-!
# Scoped multi-hole contexts across execution representations

The existing rho `Skeleton` has arbitrarily nested message/parallel shapes,
constant quoted names, and any number of reads, including repeated reads.
This module compiles that syntax to a stack program, independently executes
the program, and connects a list-frontier tree evaluator to an indexed-frontier
executor. Both read the current activation environment at execution time.

The simulation preserves the whole pending occurrence list, full activation
keys, environment, and ordered output. Environment replacement (including
rollback), publication and cancellation are explicit boundary operations.
This is a context-assembly fragment, not the concurrent rho reaction scheduler,
the source rho compiler, or the semantics of a MeTTa quotation form.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators.ScopedContextSwitching

open Mettapedia.GSLT.Dynamics
open RegionHolePlan RepresentationSwitching OrderedOccurrenceBodyAlgebra
open Mettapedia.GraphTheory.Representation

/-! ## An independently executed compilation -/

inductive Instruction where
  | read (channel : Comb)
  | literal (value : Comb)
  | pair
  | message
  deriving DecidableEq, Repr

def compile : Skeleton → List Instruction
  | .read channel => [.read channel]
  | .const value => [.literal value]
  | .nodePar left right => compile left ++ compile right ++ [.pair]
  | .nodeMsg left right => compile left ++ compile right ++ [.message]

def execute (env : Comb → Comb) : List Instruction → List Comb → Option (List Comb)
  | [], stack => some stack
  | .read channel :: rest, stack => execute env rest (env channel :: stack)
  | .literal value :: rest, stack => execute env rest (value :: stack)
  | .pair :: rest, right :: left :: stack => execute env rest (.par left right :: stack)
  | .message :: rest, right :: left :: stack => execute env rest (.mm left right :: stack)
  | .pair :: _, _ => none
  | .message :: _, _ => none

theorem execute_append (env : Comb → Comb) (first second : List Instruction)
    (stack : List Comb) :
    execute env (first ++ second) stack =
      (execute env first stack).bind (execute env second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | read channel => simpa [execute] using ih (env channel :: stack)
      | literal value => simpa [execute] using ih (value :: stack)
      | pair | message =>
          cases stack with
          | nil => rfl
          | cons right stack =>
              cases stack with
              | nil => rfl
              | cons left stack => simp [execute, ih]

/-- Compilation is stack-polymorphic: an unrelated caller suffix survives. -/
theorem execute_compile (skeleton : Skeleton) (env : Comb → Comb) (stack : List Comb) :
    execute env (compile skeleton) stack = some (skeleton.fill env :: stack) := by
  induction skeleton generalizing stack with
  | read channel => rfl
  | const value => rfl
  | nodePar left right ihLeft ihRight | nodeMsg left right ihLeft ihRight =>
      simp [compile, execute_append, ihLeft, ihRight, execute, Skeleton.fill]

theorem compile_length (skeleton : Skeleton) :
    (compile skeleton).length = skeleton.cost := by
  induction skeleton <;> simp_all [compile, Skeleton.cost, Nat.add_assoc]

/-- Uniform relabeling of read coordinates has a contravariant environment
action. One environment supplies the entire context, including nested names. -/
def renameReads (rename : Comb → Comb) : Skeleton → Skeleton
  | .read channel => .read (rename channel)
  | .const value => .const value
  | .nodePar left right => .nodePar (renameReads rename left) (renameReads rename right)
  | .nodeMsg left right => .nodeMsg (renameReads rename left) (renameReads rename right)

theorem fill_renameReads (skeleton : Skeleton) (rename env : Comb → Comb) :
    (renameReads rename skeleton).fill env = skeleton.fill (env ∘ rename) := by
  induction skeleton <;> simp_all [renameReads, Skeleton.fill, Function.comp_def]

/-! ## Instance of the language-independent switching contract -/

/-- The compiler certificate discharges the generic kernel's local obligation.
Uncompiled malformed stacks may fail; compiled templates never do. -/
def kernel (program : Nat → Skeleton) : ContextIndexedSwitching.Kernel Comb Comb where
  Code := List Instruction
  source index env := (program index).fill env
  prepared index := compile (program index)
  execute code env := ((execute env code []).getD []).headD .nil
  correct index env := by simp [execute_compile]

/-! ## Nested quotations, repeated reads, and mixed-instance controls -/

def leftChannel : Comb := .nil
def rightChannel : Comb := .kk .nil

def nestedContext : Skeleton :=
  .nodePar
    (.nodeMsg (.read leftChannel) (.read rightChannel))
    (.nodeMsg (.read leftChannel)
      (.nodeMsg (.read rightChannel) (.const (.ev (.kk .nil)))))

def firstEnvironment : Comb → Comb := fun channel =>
  if channel = leftChannel then .kk .nil else .ev .nil

def secondEnvironment : Comb → Comb := fun channel =>
  if channel = leftChannel then .kk (.kk .nil) else .ev (.ev .nil)

/-- The entire compiled nested body uses one activation environment. Reads
may repeat without introducing a second environment authority. -/
theorem nested_context_exact :
    execute firstEnvironment (compile nestedContext) [] =
      some [.par (.mm (.kk .nil) (.ev .nil))
        (.mm (.kk .nil) (.mm (.ev .nil) (.ev (.kk .nil))))] := by decide

/-- One source instantiation expands to nine independently executed stack
instructions. The simulation therefore is not a one-step correspondence. -/
theorem instantiation_is_not_one_stack_step : (compile nestedContext).length = 9 := by decide

/-- Correct per-atom assembly does not license joining atoms from different
instances into one quotation. -/
theorem mixed_instances_change_quotation :
    (.par (.mm (firstEnvironment leftChannel) (firstEnvironment rightChannel))
      (.mm (secondEnvironment leftChannel)
        (.mm (secondEnvironment rightChannel) (.ev (.kk .nil))))) ≠
      nestedContext.fill firstEnvironment := by decide

theorem malformed_program_refuses : execute firstEnvironment [.message] [] = none := rfl

/-- Hygienic coordinate transport can be implemented without materializing
the body. The inverse is required on read coordinates, not on all names. -/
theorem compile_renamed_exact (skeleton : Skeleton) (rename : Comb → Comb)
    (original fresh : Comb → Comb)
    (agrees : ∀ channel ∈ skeleton.readChannels, fresh (rename channel) = original channel) :
    execute fresh (compile (renameReads rename skeleton)) [] =
      some [skeleton.fill original] := by
  rw [execute_compile, fill_renameReads]
  congr 2
  induction skeleton with
  | read channel => exact agrees channel (by simp [Skeleton.readChannels])
  | const value => rfl
  | nodePar left right ihLeft ihRight | nodeMsg left right ihLeft ihRight =>
      simp only [Skeleton.fill]
      congr 1
      · apply ihLeft
        intro channel member
        exact agrees channel (by simp [Skeleton.readChannels, member])
      · apply ihRight
        intro channel member
        exact agrees channel (by simp [Skeleton.readChannels, member])

#print axioms execute_compile
#print axioms compile_length
#print axioms fill_renameReads
#print axioms compile_renamed_exact
#print axioms mixed_instances_change_quotation

end Mettapedia.Languages.ProcessCalculi.RhoCombinators.ScopedContextSwitching
