import Mathlib.CategoryTheory.Monad.Algebra
import Mettapedia.TypeTheory.ContextualComputationAlgebraProducts

/-!
# Contextual sequencing into computation algebras

A returner can be sequenced into any algebra of the existing contextual
program monad, not only another free returner. The algebra laws give the
sequencing laws. Context-dependent algebra homomorphisms interpret stacks;
ordinary functions into algebra carriers interpret computations. Their actions
and context reindexing commute, and continuations on returned values transpose
to stacks from the free algebra.

This is a semantic interface over value contexts. It neither chooses Prime's
source calculus nor identifies a mathematical value with a normalized native
term. Its context substitutions are functions, not a replacement for scoped
object-language substitution. No free-program quotient or equality is added.
Interpreting into an algebra that forgets effects does not authorize erasing
those effects in free returners or in the Need machine.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualAlgebraSequencing

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open ContextualKleisliAdjunction (inducedMonad)

universe u

variable {State Intent Answer OtherAnswer Context OtherContext : Type u}
variable (target : Monad.Algebra (inducedMonad State Intent))

/-- Interpret the returned values in the target computation algebra. -/
def sequence (program : Program State Answer Intent) (next : Answer → target.A) :
    target.A :=
  target.a (Program.map next program)

@[simp] theorem action_pure (value : target.A) :
    target.a (.pure value) = value := by
  exact congrArg (fun function => function value) target.unit

/-- The algebra associativity law, expressed using the actual program bind. -/
theorem action_bind (program : Program State Answer Intent)
    (next : Answer → Program State target.A Intent) :
    target.a (Program.bind program next) =
      target.a (Program.map (fun answer => target.a (next answer)) program) := by
  have law := congrArg (fun function => function (Program.map next program)) target.assoc
  change target.a (Program.bind (Program.map next program) (fun body => body)) =
    target.a (Program.map (fun body => target.a body) (Program.map next program)) at law
  simpa only [Program.map, ContextualComputationKleisli.Program.bind_assoc,
    Program.pure_bind] using law

@[simp] theorem sequence_pure (answer : Answer) (next : Answer → target.A) :
    sequence target (.pure answer) next = next answer :=
  action_pure target (next answer)

theorem sequence_bind (program : Program State Answer Intent)
    (next : Answer → Program State OtherAnswer Intent)
    (later : OtherAnswer → target.A) :
    sequence target (Program.bind program next) later =
      sequence target program (fun answer => sequence target (next answer) later) := by
  unfold sequence Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc, action_bind]
  rfl

/-- Algebraic stacks preserve the contextual sequencing action. -/
theorem hom_sequence {other : Monad.Algebra (inducedMonad State Intent)}
    (stack : target ⟶ other) (program : Program State Answer Intent)
    (next : Answer → target.A) :
    stack.f (sequence target program next) =
      sequence other program (fun answer => stack.f (next answer)) := by
  have law := congrArg (fun function => function (Program.map next program)) stack.h
  change other.a (Program.map stack.f (Program.map next program)) =
    stack.f (target.a (Program.map next program)) at law
  rw [ContextualComputationKleisli.Program.map_comp] at law
  exact law.symm

/-- At a free returner, algebraic sequencing is exactly the existing bind. -/
theorem sequence_free (program : Program State Answer Intent)
    (next : Answer → Program State OtherAnswer Intent) :
    sequence ((inducedMonad State Intent).free.obj OtherAnswer) program next =
      Program.bind program next :=
  ContextualKleisliAdjunction.inducedMonad_bind State Intent program next

/-- A semantic computation may depend on ordinary values in its context. -/
abbrev Computation (Context : Type u)
    (target : Monad.Algebra (inducedMonad State Intent)) := Context → target.A

/-- A stack must preserve the algebraic operations at each fixed context. -/
abbrev Stack (Context : Type u)
    (source target : Monad.Algebra (inducedMonad State Intent)) :=
  Context → (source ⟶ target)

variable {source middle last : Monad.Algebra (inducedMonad State Intent)}

def resume (computation : Computation Context source)
    (stack : Stack Context source target) : Computation Context target :=
  fun context => (stack context).f (computation context)

def reindexComputation (substitution : OtherContext → Context)
    (computation : Computation Context target) : Computation OtherContext target :=
  fun context => computation (substitution context)

def reindexStack (substitution : OtherContext → Context)
    (stack : Stack Context source target) : Stack OtherContext source target :=
  fun context => stack (substitution context)

theorem resume_identity (computation : Computation Context target) :
    resume target computation (fun _ => 𝟙 target) = computation := rfl

theorem resume_comp (computation : Computation Context source)
    (first : Stack Context source middle) (second : Stack Context middle target) :
    resume target (resume middle computation first) second =
      resume target computation (fun context => first context ≫ second context) := rfl

theorem reindex_resume (substitution : OtherContext → Context)
    (computation : Computation Context source) (stack : Stack Context source target) :
    reindexComputation target substitution (resume target computation stack) =
      resume target (reindexComputation source substitution computation)
        (reindexStack target substitution stack) := rfl

theorem reindex_identity (computation : Computation Context target) :
    reindexComputation target (fun context => context) computation = computation := rfl

theorem reindex_comp {LastContext : Type u}
    (first : OtherContext → Context) (second : LastContext → OtherContext)
    (computation : Computation Context target) :
    reindexComputation target second (reindexComputation target first computation) =
      reindexComputation target (fun context => first (second context)) computation := rfl

/-- Transpose a value continuation to a stack from the free returner. -/
def continuationStack (next : Context → Answer → target.A) :
    Stack Context ((inducedMonad State Intent).free.obj Answer) target :=
  fun context => ((inducedMonad State Intent).adj.homEquiv Answer target).symm
    (TypeCat.ofHom (next context))

@[simp] theorem continuationStack_apply (next : Context → Answer → target.A)
    (context : Context) (program : Program State Answer Intent) :
    (continuationStack target next context).f program =
      sequence target program (next context) := by
  change target.a (Program.map (fun value => value) (Program.map (next context) program)) = _
  rw [ContextualComputationKleisli.Program.map_id]
  rfl

@[simp] theorem continuationStack_pure (next : Context → Answer → target.A)
    (context : Context) (answer : Answer) :
    (continuationStack target next context).f (.pure answer) = next context answer :=
  sequence_pure target answer (next context)

/-- A homomorphic consumer is determined by its behavior on returned values. -/
theorem continuationStack_recover
    (stack : Stack Context ((inducedMonad State Intent).free.obj Answer) target) :
    continuationStack target (fun context answer => (stack context).f (.pure answer)) =
      stack := by
  funext context
  exact ((inducedMonad State Intent).adj.homEquiv Answer target).symm_apply_apply
    (stack context)

/-- The context-indexed free-algebra universal property. -/
def continuationEquiv :
    (Context → Answer → target.A) ≃
      Stack Context ((inducedMonad State Intent).free.obj Answer) target where
  toFun := continuationStack target
  invFun stack context answer := (stack context).f (.pure answer)
  left_inv next := by funext context answer; exact continuationStack_pure target next context answer
  right_inv := continuationStack_recover target

theorem reindex_continuationStack (substitution : OtherContext → Context)
    (next : Context → Answer → target.A) :
    reindexStack target substitution (continuationStack target next) =
      continuationStack target (fun context => next (substitution context)) := rfl

theorem resume_continuationStack (computation : Context → Program State Answer Intent)
    (next : Context → Answer → target.A) :
    resume target computation (continuationStack target next) =
      fun context => sequence target (computation context) (next context) := by
  funext context
  exact continuationStack_apply target next context (computation context)

section TypeFormers

open ContextualComputationAlgebraProducts

variable {Index : Type u}

/-- Computation products also have their universal property in value contexts. -/
def computationProductEquiv (family : Index → Monad.Algebra (inducedMonad State Intent)) :
    Computation Context (product family) ≃ ((index : Index) → Computation Context (family index)) where
  toFun computation index context := computation context index
  invFun components context index := components index context
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stack products use algebra maps, not arbitrary maps of carriers. -/
def stackProductEquiv (family : Index → Monad.Algebra (inducedMonad State Intent)) :
    Stack Context source (product family) ≃ ((index : Index) → Stack Context source (family index)) where
  toFun stack index context := stack context ≫ projection family index
  invFun components context := lift (fun index => components index context)
  left_inv stack := by
    funext context
    exact (productHomEquiv source family).left_inv (stack context)
  right_inv components := by
    funext index context
    exact lift_projection (fun index => components index context) index

theorem resume_product (family : Index → Monad.Algebra (inducedMonad State Intent))
    (computation : Computation Context source) (stack : Stack Context source (product family))
    (index : Index) :
    computationProductEquiv family (resume (product family) computation stack) index =
      resume (family index) computation (stackProductEquiv family stack index) := rfl

theorem reindex_computationProduct (family : Index → Monad.Algebra (inducedMonad State Intent))
    (substitution : OtherContext → Context) (computation : Computation Context (product family))
    (index : Index) :
    computationProductEquiv family
      (reindexComputation (product family) substitution computation) index =
      reindexComputation (family index) substitution
        (computationProductEquiv family computation index) := rfl

theorem reindex_stackProduct (family : Index → Monad.Algebra (inducedMonad State Intent))
    (substitution : OtherContext → Context) (stack : Stack Context source (product family))
    (index : Index) :
    stackProductEquiv family (reindexStack (product family) substitution stack) index =
      reindexStack (family index) substitution (stackProductEquiv family stack index) := rfl

/-- A value-indexed computation function is the power algebra, not a
computation returning a plain function. -/
def computationFunctionEquiv :
    Computation (Context × Answer) target ≃ Computation Context (power Answer target) where
  toFun computation context answer := computation (context, answer)
  invFun computation pair := computation pair.1 pair.2
  left_inv _ := rfl
  right_inv _ := rfl

def stackFunctionEquiv :
    Stack (Context × Answer) source target ≃ Stack Context source (power Answer target) where
  toFun stack context := lift (fun answer => stack (context, answer))
  invFun stack pair := stack pair.1 ≫ projection (fun _ : Answer => target) pair.2
  left_inv stack := by
    funext pair
    exact lift_projection (fun answer => stack (pair.1, answer)) pair.2
  right_inv stack := by
    funext context
    exact (powerHomEquiv source target Answer).left_inv (stack context)

/-- Application commutes with acting on a computation by a function stack. -/
theorem resume_function (computation : Computation Context source)
    (stack : Stack (Context × Answer) source target) :
    resume (power Answer target) computation (stackFunctionEquiv target stack) =
      computationFunctionEquiv target
        (resume target (fun pair => computation pair.1) stack) := rfl

theorem reindex_computationFunction (substitution : OtherContext → Context)
    (computation : Computation (Context × Answer) target) :
    reindexComputation (power Answer target) substitution
      (computationFunctionEquiv target computation) =
      computationFunctionEquiv target
        (reindexComputation target (fun pair => (substitution pair.1, pair.2)) computation) := rfl

theorem reindex_stackFunction (substitution : OtherContext → Context)
    (stack : Stack (Context × Answer) source target) :
    reindexStack (power Answer target) substitution (stackFunctionEquiv target stack) =
      stackFunctionEquiv target
        (reindexStack target (fun pair => (substitution pair.1, pair.2)) stack) := rfl

/-- Projection distributes through sequencing because it is an algebra map. -/
theorem sequence_product_apply (family : Index → Monad.Algebra (inducedMonad State Intent))
    (program : Program State Answer Intent) (next : Answer → (product family).A) (index : Index) :
    sequence (product family) program next index =
      sequence (family index) program (fun answer => next answer index) :=
  hom_sequence (product family) (projection family index) program next

/-- Contextual coproduct elimination. Taking `Result` to be a value carrier,
a computation carrier, or an algebra-hom type gives their three respective
elimination interfaces without changing the selected effects. -/
def contextCoproductEquiv {Index : Type u} (Family : Index → Type u) (Result : Type u) :
    (Context × Sigma Family → Result) ≃ ((index : Index) → Context × Family index → Result) where
  toFun function index pair := function (pair.1, ⟨index, pair.2⟩)
  invFun branches pair := branches pair.2.1 (pair.1, pair.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem contextCoproduct_reindex {Index : Type u} (Family : Index → Type u) (Result : Type u)
    (substitution : OtherContext → Context) (function : Context × Sigma Family → Result)
    (index : Index) :
    contextCoproductEquiv Family Result (fun pair => function (substitution pair.1, pair.2)) index =
      fun pair => contextCoproductEquiv Family Result function index (substitution pair.1, pair.2) :=
  rfl

theorem resume_coproduct {Index : Type u} (Family : Index → Type u)
    (computation : Computation (Context × Sigma Family) source)
    (stack : Stack (Context × Sigma Family) source target) (index : Index) :
    contextCoproductEquiv Family target.A (resume target computation stack) index =
      resume target (contextCoproductEquiv Family source.A computation index)
        (contextCoproductEquiv Family (source ⟶ target) stack index) := rfl

end TypeFormers

section Controls

private def effectfulBody (selected : Bool) : Program Bool Bool Nat :=
  .intent 7 (.choose (.pure selected) (.pure (!selected)))

private abbrev freeBool : Monad.Algebra (inducedMonad Bool Nat) :=
  (inducedMonad Bool Nat).free.obj Bool

/-- A contextual stack retains the complete authored choice/effect program. -/
theorem contextual_effects_retained (selected : Bool) :
    (continuationStack freeBool (fun (_ : Unit) => effectfulBody) ()).f
      (.pure selected) = effectfulBody selected :=
  continuationStack_pure freeBool (fun (_ : Unit) => effectfulBody) () selected

theorem contextual_effect_observations :
    (runWorldsAt
      (resume freeBool (source := freeBool) (fun (_ : Unit) => Program.pure false)
        (continuationStack freeBool (fun (_ : Unit) => effectfulBody)) ())
      false []).map (fun result => (result.answer, result.intents)) =
      [(false, [7]), (true, [7])] := rfl

/-- An arbitrary value map is not necessarily a valid stack. This one drops
the syntax's choice and intents by assigning the same pure result to all input. -/
theorem constant_map_not_stack :
    ¬ ∃ stack : freeBool ⟶ freeBool,
      ∀ program, stack.f program = Program.pure false := by
  rintro ⟨stack, constant⟩
  have law := hom_sequence freeBool stack
    (Program.choose (.pure false) (.pure true)) Program.pure
  rw [constant] at law
  have right : sequence freeBool (.choose (.pure false) (.pure true))
      (fun answer => stack.f (.pure answer)) =
      Program.choose (.pure false) (.pure false) := by
    change Program.choose (stack.f (.pure false)) (stack.f (.pure true)) = _
    rw [constant, constant]
    rfl
  have impossible : (Program.pure false : Program Bool Bool Nat) =
      .choose (.pure false) (.pure false) := law.trans right
  cases impossible

end Controls

#print axioms action_bind
#print axioms sequence_bind
#print axioms hom_sequence
#print axioms sequence_free
#print axioms reindex_resume
#print axioms continuationEquiv
#print axioms continuationStack_recover
#print axioms reindex_continuationStack
#print axioms computationProductEquiv
#print axioms stackProductEquiv
#print axioms resume_product
#print axioms computationFunctionEquiv
#print axioms stackFunctionEquiv
#print axioms resume_function
#print axioms reindex_computationFunction
#print axioms reindex_stackFunction
#print axioms sequence_product_apply
#print axioms contextCoproductEquiv
#print axioms contextCoproduct_reindex
#print axioms resume_coproduct
#print axioms contextual_effects_retained
#print axioms contextual_effect_observations
#print axioms constant_map_not_stack

end Mettapedia.TypeTheory.ContextualAlgebraSequencing
